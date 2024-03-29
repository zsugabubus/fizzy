#define _POSIX_C_SOURCE 200809

#include "config.h"

#include <stdio.h>

#include <readline/readline.h>

#include <getopt.h>
#include <inttypes.h>
#include <limits.h>
#include <signal.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#if WITH_OMP
# include <omp.h>
#endif

#define IF1(cond, if_true) IF1_(cond, if_true)
#define IF1_(cond, if_true) IF1_##cond##_(if_true)
#define IF1_0_(x)
#define IF1_1_(x) x

#define REPEAT1(i) xmacro(i)
#define REPEAT2(i) REPEAT1(i) REPEAT1(1 + i)
#define REPEAT4(i) REPEAT2(i) REPEAT2(2 + i)
#define REPEAT8(i) REPEAT4(i) REPEAT4(4 + i)
#define REPEAT16(i) REPEAT8(i) REPEAT8(8 + i)
#define REPEAT32(i) REPEAT16(i) REPEAT16(16 + i)
#define REPEAT64(i) REPEAT32(i) REPEAT32(32 + i)
#define REPEAT128(i) REPEAT64(i) REPEAT64(64 + i)
#define REPEAT256(i) REPEAT128(i) REPEAT128(128 + i)

#define COMPARE(a, b) (((a) > (b)) - ((a) < (b)))

#define BITS_SIZE(n) (((n) + (CHAR_BIT - 1)) / CHAR_BIT)
#define BIT_OP(array, op, bit, i) (((array)[(i) / CHAR_BIT]) op ((bit) << ((i) % CHAR_BIT)))
#define BIT_SET_IF(array, i, cond) BIT_OP(array, |=, !!(cond), i)
#define BIT_TEST(array, i) BIT_OP(array, &, 1, i)

#if 0
# define dbgf(...) fprintf(__VA_ARGS__)
#else
# define dbgf(...) ((void)0)
#endif

enum {
	QUERY_SIZE = 32,
};

struct record {
	uint32_t score;
	uint32_t trail;
	uint32_t index;
	uint32_t size;
	uint8_t bytes[];
};

enum char_class {
	CC_NONE,
	CC_FIELD_BREAK,
	CC_WORD_BREAK,
	CC_SUBWORD_BREAK,
	CC_SPECIAL,
	CC_LOWER,
	CC_UPPER,
	CC_DIGIT,
	CC_NB,
};

static char const *opt_prompt = "> ";
static char const *opt_header = "";
static char const *opt_hi_start = "\033[7m";
static char const *opt_hi_end = "\033[27m";
static char const *opt_execute = "";
static char opt_query[QUERY_SIZE + 1 /* NUL */];
static char opt_delim = '\n';
static bool opt_interactive = true;
static bool opt_sort = true;
static bool opt_prefix_alpha = false;
static bool opt_print_changes = false;
static bool opt_print_indices = false;
static bool opt_auto_accept_only = false;
static int opt_lines = 0;

static FILE *tty;

static uint32_t nb_total_records, nb_records, nb_matches;
static bool records_changed;
static struct record **records;
/* [c]= (1 << i0) | ... <=> q[i0] matches (==) c */
static uint32_t qmat[UINT8_MAX + 1];
static char cur_query[sizeof opt_query];

static uint8_t const CLASSIFY[] = {
#define xmacro(c) \
	'\0' == c || \
	'\t' == c || \
	('_' - '@') == c ? CC_FIELD_BREAK : \
	' ' == c || \
	'"' == c || \
	'\'' == c || \
	'/' == c ? CC_WORD_BREAK : \
	'_' == c || \
	'-' == c ? CC_SUBWORD_BREAK : \
	'#' == c || \
	'$' == c || \
	'(' == c || \
	'.' == c || \
	':' == c || \
	'[' == c ? CC_SPECIAL : \
	'a' <= c && c <= 'z' ? CC_LOWER : \
	'A' <= c && c <= 'Z' ? CC_UPPER : \
	'0' <= c && c <= '9' ? CC_DIGIT : \
	CC_NONE,
	REPEAT256(0)
#undef xmacro
};

#define CC_MKBIT2(prev_cc, cur_cc) \
	(1UL << ((prev_cc) * CC_NB + (cur_cc)))

static uint64_t const IGNORE_NONMATCHING = 0
	| CC_MKBIT2(CC_LOWER, CC_LOWER)
	| CC_MKBIT2(CC_UPPER, CC_LOWER)
	| CC_MKBIT2(CC_DIGIT, CC_DIGIT)
	| CC_MKBIT2(CC_UPPER, CC_LOWER)
;

#define CC_ALL(x) \
	[CC_NONE] = (x), \
	[CC_FIELD_BREAK] = (x), \
	[CC_WORD_BREAK] = (x), \
	[CC_SUBWORD_BREAK] = (x), \
	[CC_SPECIAL] = (x), \
	[CC_LOWER] = (x), \
	[CC_UPPER] = (x), \
	[CC_DIGIT] = (x) \

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Woverride-init"
static uint8_t const BONUS[CC_NB][CC_NB] = {
	/* [previous] { [current] = bonus } */
	[CC_NONE] = {
		CC_ALL(1),
		[CC_UPPER] = 5,
	},
	[CC_FIELD_BREAK] = {
		CC_ALL(60),
		[CC_UPPER] = 60 + 5,
	},
	[CC_WORD_BREAK] = {
		CC_ALL(40),
		[CC_UPPER] = 40 + 5,
	},
	[CC_SUBWORD_BREAK] = {
		CC_ALL(15),
		[CC_UPPER] = 15 + 5,
	},
	[CC_SPECIAL] = {
		CC_ALL(8),
		[CC_UPPER] = 8 + 5,
	},
	[CC_LOWER] = {
		CC_ALL(1),
		/* randomtextwithlonelyletters */
		[CC_LOWER] = 3, /* About the length of a syllable. */
		/* camelCase */
		[CC_UPPER] = 15 + 5,
	},
	[CC_UPPER] = {
		CC_ALL(1),
		/* SCREAMINGCase */
		[CC_UPPER] = 15,
	},
};
#pragma GCC diagnostic pop

static void
setup_term(void)
{
	/* Disable wrapping. */
	fputs("\033[?7l", tty);
	if (!opt_lines)
		/* Switch to alt screen. */
		fputs("\033[?1049h", tty);
	fflush(tty);
}

static void
reset_term(void)
{
	fputs("\033[?7h", tty);
	fputs("\033[?1049l", tty);
	fflush(tty);
}

static void
clear_records(void)
{
	for (uint32_t i = 0; i < nb_total_records; ++i)
		free(records[i]);
	free(records);
	records = NULL;
	nb_total_records = 0;
}

static void
add_record(char const *pre, size_t presz, char const *buf, size_t bufsz)
{
	uint32_t sz = presz + bufsz;
	uint32_t allocsz = offsetof(struct record, bytes[BITS_SIZE(sz) + sz]);
	struct record *record = malloc(allocsz);
	if (!record)
		abort();

	record->index = nb_total_records;
	record->size = sz;
	memset(record->bytes, 0, BITS_SIZE(sz));
	uint8_t *str = record->bytes + BITS_SIZE(sz);
	memcpy(str, pre, presz);
	memcpy(record->bytes + BITS_SIZE(sz) + presz, buf, bufsz);

	bool escape = false;
	for (uint32_t i = 0; i < sz; ++i) {
		uint8_t c = str[i];

		escape |= ('[' - '@') == c;

		bool control = c < ' ' && !CLASSIFY[c];
		bool ignore = control || escape;
		BIT_SET_IF(record->bytes, i, ignore);

		/* End of SGR sequence. */
		escape &= 'm' != c;
	}

	/* Allocate 2^x sizes. */
	if (!(nb_total_records & (nb_total_records - 1))) {
		uint32_t nb_next = 2 * nb_total_records + !nb_total_records;
		records = realloc(records, nb_next * sizeof *records);
		if (!records)
			abort();
	}
	records[nb_total_records++] = record;

	records_changed = true;
}

static void
score_record(struct record *record, uint32_t *positions, uint32_t nb_positions)
{
	record->score = 0;
	record->trail = 0;

	uint32_t out_position = 0;
	if (nb_positions)
		positions[0] = UINT32_MAX;

	uint32_t n = record->size;
	uint8_t const *str = record->bytes + BITS_SIZE(record->size);

	uint32_t m = 0;
	for (uint8_t const *q = (uint8_t *)opt_query,
	     *ptr = str,
	     *end = ptr + n;
	     *q;
	     ++q, ++m)
	{
		for (uint32_t i;;) {
			uint8_t const *p = memchr(ptr, *q, end - ptr);

			if ('a' <= *q && *q <= 'z') {
				ptr = memchr(ptr, *q ^ ' ', (p ? p : end) - ptr);
				if (!ptr)
					ptr = p;
			} else
				ptr = p;
			if (!ptr)
				return;

			i = ptr - str;
			++ptr;

			if (!BIT_TEST(record->bytes, i))
				break;
		}
	}

	if (!m) {
		record->score = UINT32_MAX;
		return;
	}

	/*
	 *  subject string
	 * Q j i o -> n
	 * U ^
	 * E |
	 * R k
	 * Y m
	 */

	/* [i][i]=Matching position of the maximum for query[i].
	 * [i][j<i]=Path to [i][i]. */
	uint32_t max_paths[QUERY_SIZE - 1][QUERY_SIZE];
	/* [i]=Best score for the i-long prefix. Off by one so we need one more
	 * element.
	 *
	 * These scores fade away in the distance, i.e. there is penalty if
	 * next match occurs (far) after where previous byte reached its maximum.
	 * Gap penalty is always 1 and bonuses are configured based on this.
	 *
	 * To avoid decrementing max_scores[..] on every output byte, max_score
	 * is transformed using output index. */
	uint32_t max_scores[QUERY_SIZE + 1];
	/* Bonus for the maximum. */
	uint32_t max_bonuses[QUERY_SIZE + 1];
	/* Bonus for continuation. */
	uint32_t cont_bonuses[QUERY_SIZE + 1];

	memset(max_scores, 0, sizeof max_scores);
	memset(max_bonuses, 0, sizeof max_bonuses);
	memset(cont_bonuses, 0, sizeof cont_bonuses);

	enum char_class prev_cc = CC_FIELD_BREAK;
	uint32_t prev_mat = 0;
	uint32_t max_score = 0;
	uint32_t latest_pos = 0;
	uint32_t k = 0; /* Query prefix length. */
	uint32_t o = 0; /* Output byte index. */

	dbgf(stderr, "%.*s\n", n, str);

	for (uint32_t i = 0; i < n; ++i) {
		/* Test ignored input position. */
		if (BIT_TEST(record->bytes, i))
			continue;

		++o;

		uint8_t c = str[i];
		enum char_class cc = CLASSIFY[c];

		uint32_t mat = qmat[c];
		/* Disallow matches outside the k-length prefix. */
		mat &= (2 << k) - 1;
		/* Test if position is dynamically ignored. */
		uint32_t t = (prev_mat << 1) | prev_mat;
		if (!(CC_MKBIT2(prev_cc, cc) & IGNORE_NONMATCHING))
			t = ~0;
		mat &= t;
		if (!mat) {
			prev_mat = 0;
			prev_cc = cc;
			continue;
		}

		uint32_t cont_mat = prev_mat;
		prev_mat = mat;

		uint32_t bonus = BONUS[prev_cc][cc];
		prev_cc = cc;

		/* Allow matching next byte from query when complete prefix has
		 * been matched. This ensures that a later byte in the query
		 * cannot be matched without requiring all preceding bytes to
		 * be matched (at least once). */
		k += (mat >> k) && k + 1 < m;

		/* Go backwards so we can see the previous state of an upper
		 * cell. */
		for (uint32_t j;
		     mat && (j = 31 ^ __builtin_clz(mat), 1);
		     mat ^= 1 << j)
		{
			uint32_t score;

			score = o < max_scores[j]
				? max_scores[j] - o
				: 0;

			/* Prefer match of the same kind. A kind of distant
			 * continuation. */
			if (score /* Not too far. */ && bonus == max_bonuses[j])
				score += bonus;

			/* Bonus for matching this particular position. */
			score += bonus;

			/* Bonus for contiguous match. Take the better since
			 * we may have a continuation over a position that has
			 * a higher bonus (xaBcx). */
			uint32_t cont_bonus = cont_bonuses[j];
			if (cont_bonus < bonus)
				cont_bonus = bonus;
			/* Increase bonus so longer wins. */
			cont_bonus += 1;
			cont_bonuses[j + 1] = cont_bonus;
			/* New test that cont_bonus is really applicable. */
			if (!((cont_mat << 1) & (1 << j)))
				cont_bonus = 0;
			score += cont_bonus;

			dbgf(stderr, "%*.s%c:%*.sj=%2d/%-2d m=%-4u b=%-4u cm=%-4u cb=%-4u => %-4u %s\n",
					i, "", c,
					80 - i, "",
					j, k,
					max_scores[j],
					bonus,
					max_bonuses[j] == bonus ? max_bonuses[j] : 0,
					cont_bonus,
					score,
					o + score <= max_scores[j + 1] ? "" : "MAX");

			if (j + 1 == m) {
				latest_pos = i;
				if (nb_positions) {
					/* Reserve space for highest quality match. */
					uint32_t tmp = nb_positions - (
							j + /* Previous values. */
							1 + /* This one. */
							1 /* End marker. */
					);
					if (tmp < out_position)
						out_position = tmp;

					/* Append new positions. Old ones are already included
					 * in positions list because i is strict monotonic
					 * increasing. */
					uint32_t skip = 0;
					while (0 < out_position &&
					       skip < j &&
					       max_paths[j - 1][skip] <= positions[out_position - 1])
						++skip;

					memcpy(positions + out_position, max_paths[j - 1] + skip,
							(j - skip) * sizeof **max_paths);
					out_position += j - skip;
					positions[out_position] = i;
					out_position += 1;
				}
			}

			if (o + score <= max_scores[j + 1])
				continue;
			max_scores[j + 1] = o + score;
			max_bonuses[j + 1] = bonus;

			if (j + 1 < m) {
				/* Only the first `j * sizeof(uint32_t)` bytes
				 * are needed but it's faster with known size. */
				if (0 < j)
					memcpy(max_paths[j], max_paths[j - 1],
							sizeof *max_paths);
				max_paths[j][j] = i;
				continue;
			}

			if (max_score < score) {
				max_score = score;
				dbgf(stderr, "new_max=%u\n", max_score);
			}
		}
	}

	dbgf(stderr, " ==> %u\n\n", max_score);

	if (nb_positions)
		positions[out_position] = UINT32_MAX;

	record->score = max_score;
	record->trail = n - latest_pos;
}

static void
score_all(void)
{
	bool subquery = strstr(opt_query, cur_query);
	uint32_t n = !records_changed && subquery ? nb_matches : nb_records;
	memcpy(cur_query, opt_query, sizeof cur_query);

	memset(qmat, 0, sizeof qmat);
	for (uint8_t m = 0, c; (c = opt_query[m]); ++m) {
		qmat[c] |= 1 << m;
		if ('a' <= c && c <= 'z')
			qmat[c - 'a' + 'A'] |= 1 << m;
	}

#pragma omp parallel for schedule(dynamic)
	for (uint32_t i = 0; i < n; ++i) {
		struct record *record = records[i];
		score_record(record, NULL, 0);
	}

	nb_matches = 0;
	for (uint32_t i = 0; i < n; ++i) {
		struct record *record = records[i];
		if (!record->score)
			continue;

		struct record *t = records[nb_matches];
		records[nb_matches] = record;
		records[i] = t;
		++nb_matches;
	}

	records_changed = false;
}

static int
compare_records(void const *px, void const *py)
{
	struct record const *x = *(struct record **)px;
	struct record const *y = *(struct record **)py;
	int cmp;

	cmp = COMPARE(x->score, y->score);
	if (cmp)
		return -cmp;

	cmp = COMPARE(x->trail, y->trail);
	if (cmp)
		return cmp;

	cmp = COMPARE(x->size, y->size);
	if (UINT32_MAX == x->score)
		cmp = 0;
	if (cmp)
		return cmp;

	return COMPARE(x->index, y->index);
}

static void
sort_all(void)
{
	if (!opt_sort)
		return;
	qsort(records, nb_matches, sizeof *records, compare_records);
}

static char const *
gen_word(uint32_t i, char a, char z)
{
	static char buf[32];

	char *p = buf + 31;
	do {
		*--p = a + i % (z - a + 1);
		i /= (z - a + 1);
	} while (0 < i--);

	return p;
}

static void
read_records(FILE *stream)
{
	char *line = NULL;
	size_t linesz = 0;
	for (ssize_t linelen;
	     0 < (linelen = getdelim(&line, &linesz, opt_delim, stream));)
	{
		char pre[32];
		int presz = 0;
		if (opt_prefix_alpha) {
			char const *word = gen_word(nb_total_records, 'A', 'Z');
			presz = sprintf(pre, "%s:\t", word);
		}

		linelen -= opt_delim == line[linelen - 1];
		add_record(pre, presz, line, linelen);
	}
	free(line);
}

static uint32_t
print_records(int nb_lines)
{
	if (nb_lines < 0)
		return 0;

	uint32_t count = 0;
	for (uint32_t i = 0; i < nb_matches && i < (uint32_t)nb_lines; ++i) {
		fputs("\n\033[m", tty);
		++count;

		struct record *record = records[i];
		uint32_t positions[4 * QUERY_SIZE + 1];
		score_record(record, positions, sizeof positions / sizeof *positions);

#if 0
		fprintf(tty, "(%5d,%5d) ", record->score, record->trail);
#endif

		uint8_t const *str = record->bytes + BITS_SIZE(record->size);
		uint32_t start = 0;
		for (uint32_t k = 0;; ++k) {
			uint32_t end = positions[k];
			if (UINT32_MAX == end)
				break;

			fwrite(str + start, 1, end - start, tty);

			while ((start = positions[k] + 1) == positions[k + 1])
				++k;

			fputs(opt_hi_start, tty);
			fwrite(str + end, 1, start - end, tty);
			fputs(opt_hi_end, tty);
		}

		fwrite(str + start, 1, record->size - start, tty);
	}

	return count;
}

static void
print_record(struct record const *record, FILE *stream)
{
	uint8_t const *str = record->bytes + BITS_SIZE(record->size);
	uint32_t size = record->size;
	/* Cut prefix. */
	if (opt_prefix_alpha) {
		uint8_t const *p = memchr(str, '\t', size);
		p += 1;
		size -= p - str;
		str = p;
	}
	fwrite(str, 1, size, stream);
}

static void
emit_record(struct record const *record)
{
	if (opt_print_indices) {
		printf("%"PRIu32, record->index);
	} else {
		print_record(record, stdout);
	}
	fputc(opt_delim, stdout);
}

static bool
emit_one(void)
{
	if (!nb_matches)
		return false;

	emit_record(records[0]);
	fflush(stdout);

	return true;
}

static bool
emit_all(void)
{
	if (!nb_matches)
		return false;

	for (uint32_t i = 0; i < nb_matches; ++i)
		emit_record(records[i]);
	fflush(stdout);

	return true;
}

static void
accept_one(void)
{
	exit(emit_one() ? EXIT_SUCCESS : EXIT_FAILURE);
}

static void
accept_only(void)
{
	if (1 == nb_records)
		accept_one();
}

static void
accept_all(void)
{
	exit(emit_all() ? EXIT_SUCCESS : EXIT_FAILURE);
}

static void
edit_records(uint32_t n)
{
	char pathname[] = "/tmp/fizzyXXXXXX";
	int fd = mkstemp(pathname);
	if (fd < 0)
		return;
	FILE *f = fdopen(fd, "w");
	if (!f)
		abort();

	for (uint32_t i = 0; i < n; ++i) {
		struct record *record = records[i];
		print_record(record, f);
		fputc(opt_delim, f);
	}

	if (fclose(f))
		return;

	reset_term();

	pid_t pid = fork();
	if (!pid) {
		if (0 <= dup2(fileno(tty), STDIN_FILENO) &&
		    0 <= dup2(fileno(tty), STDOUT_FILENO) &&
		    0 <= dup2(fileno(tty), STDERR_FILENO))
			execlp("sh", "sh", "-c", "$EDITOR -- \"$1\"", "fizzy-editor", pathname, NULL);
		_exit(127);
	}

	int status;
	if (waitpid(pid, &status, 0) <= 0 ||
	    !WIFEXITED(status) ||
	    EXIT_SUCCESS != WEXITSTATUS(status))
	{
		setup_term();
		unlink(pathname);
		return;
	}

	setup_term();

	FILE *input = fopen(pathname, "r");
	unlink(pathname);
	if (!input)
		return;

	clear_records();
	read_records(input);
	nb_matches = nb_total_records;
	nb_records = nb_total_records;
	records_changed = true;

	fclose(input);
}

static void
fizzy_rl_handle_line(char *line)
{
	if (!line)
		exit(EXIT_FAILURE);
	accept_one();
}

static int
fizzy_rl_accept_all(int count, int c)
{
	(void)count, (void)c;
	accept_all();
	return 1;
}

static int
fizzy_rl_accept_one(int count, int c)
{
	(void)count, (void)c;
	accept_one();
	return 1;
}

static int
fizzy_rl_accept_only(int count, int c)
{
	(void)count, (void)c;
	accept_only();
	return 1;
}

static int
fizzy_rl_edit(int count, int c)
{
	(void)count, (void)c;
	edit_records(nb_records);
	/* Force redraw. */
	records_changed = true;
	return 1;
}

static int
fizzy_rl_emit_all(int count, int c)
{
	(void)count, (void)c;
	emit_all();
	return 1;
}

static int
fizzy_rl_emit_one(int count, int c)
{
	(void)count, (void)c;
	emit_one();
	return 1;
}

static int
fizzy_rl_exit(int count, int c)
{
	(void)c;
	exit(count);
}

static int
fizzy_rl_filter_matched(int count, int c)
{
	(void)count, (void)c;
	nb_records = nb_matches;
	records_changed = true;
	rl_replace_line("", true);
	return 1;
}

static int
fizzy_rl_filter_reset(int count, int c)
{
	(void)count, (void)c;
	nb_records = nb_total_records;
	records_changed = true;
	rl_replace_line("", true);
	return 1;
}

static void
handle_interrupt(int sig)
{
	(void)sig;
	/* readline handles (or at least should handle) signals or tell the
	 * terminal to not send them but it is actually... do not know what the
	 * fuck is going on or how to do this. exit() is not async thread safe,
	 * we should protected-poll tty and then do rl_callback_read_char(),
	 * but clearly, I do not want to waste more time/lines on it. It works
	 * in 99.9% of cases and it is enough. */
	exit(EXIT_FAILURE);
}

int
main(int argc, char *argv[])
{
	for (int opt; -1 != (opt = getopt(argc, argv, "01acfh:il:np:q:sux:" IF1(WITH_OMP, "j:")));)
		switch (opt) {
		case '0':
			opt_delim = '\0';
			break;

		case 'A':
			opt_delim = '^' - '@';
			break;

		case '1':
			opt_auto_accept_only = true;
			break;

		case 'a':
			opt_prefix_alpha = true;
			break;

		case 'c':
			opt_print_changes = true;
			break;

		case 'f':
			opt_interactive = false;
			break;

		case 'h':
			opt_header = optarg;
			break;

		case 'i':
			opt_print_indices = true;
			break;

#if WITH_OMP
		case 'j':
			omp_set_num_threads(atoi(optarg));
			break;
#endif

		case 'l':
			opt_lines = atoi(optarg);
			break;

		case 'p':
			opt_prompt = optarg;
			break;

		case 'q':
			snprintf(opt_query, sizeof opt_query, "%s", optarg);
			break;

		case 's':
			opt_sort = false;
			break;

		case 'u':
			opt_hi_start = "\033[4m";
			opt_hi_end = "\033[24m";
			break;

		case 'x':
			opt_execute = optarg;
			break;

		case '?':
			return EXIT_FAILURE;

		default:
			abort();
		}

	setvbuf(stdout, NULL, _IOFBF, BUFSIZ);

	FILE *input;
	if (isatty(STDIN_FILENO))
		input = popen("find", "r");
	else
		input = stdin;
	if (!input) {
		perror("Cannot open input");
		return EXIT_FAILURE;
	}

	clear_records();
	read_records(input);
	nb_matches = nb_total_records;
	nb_records = nb_total_records;

	fclose(input);

	if (opt_auto_accept_only)
		accept_only();

#if 0
	for (int i = 0; i < 3; ++i)
		for (int i = 20; --i > 0;) {
			strcpy(opt_query, "heeeeeeeeeeeeeeeeeeeeeeeee");
			opt_query[i] = '\0';
			/* sprintf(opt_query, "-/%d%d%d", i, i, i); */
			score_all();
		}
	return 0;
#endif

	if (!opt_interactive) {
		score_all();
		sort_all();
		accept_all();
	}

	tty = fopen(ctermid(NULL), "w+");
	if (!tty) {
		perror("Cannot open terminal");
		exit(EXIT_FAILURE);
	}
	setvbuf(tty, NULL, _IOFBF, BUFSIZ);

	rl_readline_name = argv[0];
	rl_instream = tty;
	rl_outstream = tty;

	rl_bind_key('\t', rl_insert);
	rl_add_defun("fizzy-accept-all", fizzy_rl_accept_all, -1);
	rl_add_defun("fizzy-accept-one", fizzy_rl_accept_one, -1);
	rl_add_defun("fizzy-accept-only", fizzy_rl_accept_only, -1);
	rl_add_defun("fizzy-edit", fizzy_rl_edit, -1);
	rl_add_defun("fizzy-emit-all", fizzy_rl_emit_all, -1);
	rl_add_defun("fizzy-emit-one", fizzy_rl_emit_one, -1);
	rl_add_defun("fizzy-exit", fizzy_rl_exit, -1);
	rl_add_defun("fizzy-filter-matched", fizzy_rl_filter_matched, -1);
	rl_add_defun("fizzy-filter-reset", fizzy_rl_filter_reset, -1);

	setup_term();
	atexit(reset_term);

	signal(SIGINT, handle_interrupt);
	signal(SIGTERM, handle_interrupt);
	signal(SIGQUIT, handle_interrupt);

	rl_callback_handler_install(opt_prompt, fizzy_rl_handle_line);
	rl_insert_text(opt_query);
	rl_resize_terminal();

	for (;;) {
		fputs(!opt_lines ? "\033[H\033[2J" : "\r\033[J", tty);
		fputs("\n\033[m", tty);

		int rows, cols;
		rl_get_screen_size(&rows, &cols);
		if (opt_lines && opt_lines + 2 < rows)
			rows = opt_lines + 2;

		score_all();
		sort_all();
		if (opt_print_changes)
			emit_one();

		if (nb_records == nb_total_records)
			fprintf(tty, "[%"PRIu32"/%"PRIu32"] ",
					nb_matches, nb_records);
		else
			fprintf(tty, "[%"PRIu32"/%"PRIu32" (%"PRIu32")] ",
					nb_matches, nb_records, nb_total_records);
		fputs(opt_header, tty);

		uint32_t n = print_records(rows - 2);

		if (!opt_lines)
			fputs("\033[H", tty);
		else
			fprintf(tty, "\033[%"PRIu32"A\r", n + 1);
		fputs("\033[m", tty);

		/* Otherwise no prompt in $(...). Should be reset also
		 * after catching signals because readline resets it for some
		 * reason (e.g. after C-z). */
		rl_tty_set_echoing(1);

		rl_forced_update_display();
		/* TODO: Maybe care about terminal resizing. */
		do {
			if (*opt_execute) {
				rl_stuff_char(*opt_execute);
				++opt_execute;
			}
			rl_callback_read_char();
		} while (!records_changed && !strcmp(opt_query, rl_line_buffer));
		snprintf(opt_query, sizeof opt_query, "%s", rl_line_buffer);
	}
}
