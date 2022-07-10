#define _POSIX_C_SOURCE 200809

#include "config.h"

#include <stdio.h>

#include <readline/readline.h>

#include <assert.h>
#include <curses.h>
#include <getopt.h>
#include <inttypes.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <term.h>
#include <unistd.h>

#if HAVE_OMP
# include <omp.h>
#endif

enum {
	QUERY_SIZE_MAX = 32,
};

static char opt_delim = '\n';
static bool opt_prefix_alpha = false;
static bool opt_print_changes = false;
static bool opt_interactive = true;
static char const *opt_header = "";
static bool opt_print_indices = false;
static char const *opt_prompt = "> ";
static char opt_query[QUERY_SIZE_MAX + 1 /* NUL */];
static bool opt_sort = true;

static FILE *tty;

struct record {
	uint32_t score;
	uint32_t index;
	uint32_t size;
	uint8_t bytes[];
};

static uint32_t nb_total_records, nb_records, nb_matches;
static struct record **records;

#define BITSET_SIZE(n) (((n) + (CHAR_BIT - 1)) / CHAR_BIT)
#define BITSET_OP_(x, op, bit, i) (((x)[(size_t)(i) / CHAR_BIT]) op ((bit) << ((size_t)(i) % CHAR_BIT)))
#define BITSET_SET_IF(x, i, cond) BITSET_OP_(x, |=, !!(cond), i)
#define BITSET_SET(x, i) BITSET_SET_IF(x, i, 1)
#define BITSET_TEST(x, i) BITSET_OP_(x, &, 1, i)

static void
add_record(char const *pre, size_t presz, char const *buf, size_t bufsz)
{
	uint32_t sz = presz + bufsz;
	uint32_t allocsz = offsetof(struct record, bytes[BITSET_SIZE(sz) + sz]);
	struct record *record = malloc(allocsz);
	if (!record)
		abort();

	record->index = nb_total_records;
	record->size = sz;
	memset(record->bytes, 0, BITSET_SIZE(sz));
	uint8_t *str = record->bytes + BITSET_SIZE(sz);
	memcpy(str, pre, presz);
	memcpy(record->bytes + BITSET_SIZE(sz) + presz, buf, bufsz);

	bool escape = false;
	for (uint32_t i = 0; i < sz; ++i) {
		uint8_t c = str[i];

		escape |= ('[' - '@') == c;

		bool control = c < ' ';
		bool ignore = control || escape;
		BITSET_SET_IF(record->bytes, i, ignore);

		if ('\r' == c)
			for (uint32_t j = 0; j < i; ++j)
				BITSET_SET(record->bytes, j);

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
}

enum char_class {
	CC_NONE,
	CC_FIELD_BREAK,
	CC_WORD_BREAK,
	CC_SUBWORD_BREAK,
	CC_SPECIAL,
	CC_LOWER,
	CC_UPPER,
	CC_NB,
};

#define REPEAT1(i) xmacro(i)
#define REPEAT2(i) REPEAT1(i) REPEAT1(1 + i)
#define REPEAT4(i) REPEAT2(i) REPEAT2(2 + i)
#define REPEAT8(i) REPEAT4(i) REPEAT4(4 + i)
#define REPEAT16(i) REPEAT8(i) REPEAT8(8 + i)
#define REPEAT32(i) REPEAT16(i) REPEAT16(16 + i)
#define REPEAT64(i) REPEAT32(i) REPEAT32(32 + i)
#define REPEAT128(i) REPEAT64(i) REPEAT64(64 + i)
#define REPEAT256(i) REPEAT128(i) REPEAT128(128 + i)

static uint8_t const CLASSIFY[] = {
#define xmacro(c) \
	'\0' == c || \
	'\t' == c || \
	('_' - '@') == c ? CC_FIELD_BREAK : \
	' ' == c || \
	'.' == c || \
	'/' == c ? CC_WORD_BREAK : \
	'_' == c || \
	'-' == c ? CC_SUBWORD_BREAK : \
	':' == c || \
	'$' == c || \
	'(' == c || \
	'[' == c || \
	'#' == c ? CC_SPECIAL : \
	'a' <= c && c <= 'z' ? CC_LOWER : \
	'A' <= c && c <= 'Z' ? CC_UPPER : \
	CC_NONE,
	REPEAT256(0)
#undef xmacro
};

#define CC_ALL(x) \
	[CC_NONE] = (x), \
	[CC_FIELD_BREAK] = (x), \
	[CC_WORD_BREAK] = (x), \
	[CC_SUBWORD_BREAK] = (x), \
	[CC_SPECIAL] = (x), \
	[CC_LOWER] = (x), \
	[CC_UPPER] = (x) \

/* Independent from bonuses, relative to other penalties. */
static uint32_t const GAP_PENALTY = 1;
/* A bit less than subword match. */
static uint32_t const CONT_BONUS = 0;
static uint32_t const REPEAT_BONUS = 10;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Woverride-init"
static uint8_t const BONUS[CC_NB][CC_NB] = {
	/* [previous] { [current] = bonus }. */
	[CC_NONE] = {
		CC_ALL(1),
		[CC_UPPER] = 4,
	},
	[CC_FIELD_BREAK] = {
		CC_ALL(10),
	},
	[CC_WORD_BREAK] = {
		CC_ALL(8),
	},
	[CC_SUBWORD_BREAK] = {
		CC_ALL(5),
	},
	[CC_SPECIAL] = {
		CC_ALL(2),
	},
	[CC_LOWER] = {
		CC_ALL(1),
		/* camelCase */
		[CC_UPPER] = 6,
	},
	[CC_UPPER] = {
		CC_ALL(1),
		[CC_UPPER] = 5, /* SCREAMINGCase */
	},
};
#pragma GCC diagnostic pop

static void
score_record(struct record *record, uint32_t (*positions)[QUERY_SIZE_MAX + 1])
{
	record->score = 0;
	if (positions)
		(*positions)[0] = UINT32_MAX;

	uint32_t n = record->size;
	uint8_t const *const str = record->bytes + BITSET_SIZE(record->size);

	uint8_t in_query[BITSET_SIZE(UINT8_MAX + 1)];
	memset(in_query, 0, sizeof in_query);

	uint32_t m = 0;
	for (uint8_t const *q = (uint8_t *)opt_query,
	     *ptr = str,
	     *end = ptr + n;
	     *q;
	     ++q, ++m)
	{
		BITSET_SET(in_query, *q);
		if ('a' <= *q && *q <= 'z')
			BITSET_SET(in_query, *q - 'a' + 'A');

		for (uint32_t i;;) {
			uint8_t const *p = memchr(ptr, *q, end - ptr);

			if ('a' <= *q && *q <= 'z') {
				ptr = memchr(ptr, *q ^ ' ', (p ? p : end) - ptr);
				if (!ptr)
					ptr = p;
			} else
				ptr = p;
			if (!ptr) {
				return;
			}

			i = ptr - str;
			++ptr;

			if (!BITSET_TEST(record->bytes, i))
				break;
		}
	}

	if (!m) {
		record->score = 1;
		return;
	}

	__builtin_prefetch(record->bytes, 1, 1);
	__builtin_prefetch(str, 1, 1);

	/*
	 *  subject string
	 * Q j i -> n
	 * U ^
	 * E |
	 * R k
	 * Y m
	 */

	uint32_t max_paths[QUERY_SIZE_MAX][QUERY_SIZE_MAX];
	uint32_t max_scores[QUERY_SIZE_MAX];
	uint64_t matched = 0;

	memset(max_scores, 0, sizeof max_scores);

	uint32_t max_score = 0;
	uint32_t k = 1;
	uint32_t jumps = 0;

	enum char_class cc_prev = CC_FIELD_BREAK;
	for (uint32_t i = 0; i < n; ++i) {
		if (BITSET_TEST(record->bytes, i))
			continue;

		uint8_t c = str[i];
		enum char_class cc_cur = CLASSIFY[c];
		uint32_t bonus = BONUS[cc_prev][cc_cur];
		cc_prev = cc_cur;

		uint32_t const bonus_mult = 32 * GAP_PENALTY;
		bonus *= bonus_mult;

		/* Speed of light squared. */
		uint8_t c2 = 'A' <= c && c <= 'Z' ? c - 'A' + 'a' : c;

		++jumps;

		uint64_t prev_matched = matched;
		matched = 0;

		if (!(BITSET_TEST(in_query, c) ||
		      BITSET_TEST(in_query, c2)))
			continue;

		/* Scores fade away in the distance. */
		for (uint32_t j = 0; j < k; ++j)
			max_scores[j] = jumps * GAP_PENALTY < max_scores[j]
				? max_scores[j] - jumps * GAP_PENALTY
				: 0;
		jumps = 0;

		/* Go backwards so we will see the previous state of an upper
		 * cell. */
		for (uint32_t j = k; j > 0;) {
			uint8_t q = opt_query[--j];

			if (!(q == c || q == c2))
				continue;

			uint32_t score = 0;
			/* Best score up to the prefix string. */
			score += max_scores[j];
			/* Bonus for matching this particular position. */
			score += bonus;
			/* Bonus for continuous match. */
			if (0 < j && (prev_matched & (1 << (j - 1))))
				score += CONT_BONUS;

			if (j + 1 == k)
				++k;

			matched |= 1 << j;

			if (max_scores[j + 1] < score) {
				max_scores[j + 1] = score;
				/* Give higher score to reoccurrances. */
				if (j + 1 == m) {
#if 0
					/* Too much noize because random letters match. */
					max_scores[0] += score;
#else
					max_scores[0] += REPEAT_BONUS * bonus_mult;
#endif
					max_score = score;
				}

				/* Only the first `j * sizeof(uint32_t)` bytes
				 * are needed but it's faster with known size. */
				if (0 < j)
					memcpy(max_paths[j], max_paths[j - 1], sizeof *max_paths);
				max_paths[j][j] = i;
			}
		}
	}

	if (positions) {
		memcpy(*positions, max_paths[m - 1], sizeof *max_paths);
		(*positions)[m] = UINT32_MAX;
	}

	record->score = max_score;
	assert(0 < record->score);
}

static void
score_all(void)
{
	static char cur_query[QUERY_SIZE_MAX + 1 /* NUL */];

	bool subquery = strstr(opt_query, cur_query);

	uint32_t n = subquery ? nb_matches : nb_records;

	memcpy(cur_query, opt_query, sizeof cur_query);

	/* Thread number can be controlled by setting OMP_NUM_THREADS=2
	 * environment variable. */
#pragma omp parallel for schedule(dynamic)
	for (uint32_t i = 0; i < n; ++i) {
		struct record *record = records[i];
		score_record(record, NULL);
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
}

#define COMPARE(a, b) (((a) > (b)) - ((a) < (b)))

static int
compare_index(void const *px, void const *py)
{
	struct record const *x = *(struct record **)px;
	struct record const *y = *(struct record **)py;

	return COMPARE(x->index, y->index);
}

static int
compare_score(void const *px, void const *py)
{
	struct record const *x = *(struct record **)px;
	struct record const *y = *(struct record **)py;

	int cmp = COMPARE(x->score, y->score);
	if (cmp)
		return -cmp;

	return compare_index(px, py);
}

static void
sort_all(void)
{
	if (!opt_sort)
		return;
	qsort(records, nb_matches, sizeof *records, compare_score);
}

static char const *
gen_word(uint32_t i, char a, char z)
{
	static char buf[100];

	char *p = (&buf)[1];
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
		char pre[100];
		int presz = 0;
		if (opt_prefix_alpha) {
			char const *word = gen_word(nb_total_records, 'A', 'Z');
			presz = sprintf(pre, "%s\t", word);
		}
		add_record(pre, presz, line, linelen - 1 /* CR */);
	}
	free(line);
}

static void
print_records(int nlines)
{
	if (nlines < 0)
		return;

	for (uint32_t i = 0; i < nb_matches && i < (uint32_t)nlines; ++i) {
		fputs("\n\x1b[m", tty);

		struct record *record = records[i];
		uint32_t positions[QUERY_SIZE_MAX + 1];
		score_record(record, &positions);

#if 0
		fprintf(tty, "(%5d) ", record->score);
#endif

		uint8_t const *str = record->bytes + BITSET_SIZE(record->size);
		uint32_t start = 0;
		for (uint32_t k = 0;; ++k) {
			uint32_t end = positions[k];
			if (UINT32_MAX == end)
				break;

			fwrite(str + start, 1, end - start, tty);

			while ((start = positions[k] + 1) == positions[k + 1])
				++k;

			fputs("\x1b[7m", tty);
			fwrite(str + end, 1, start - end, tty);
			fputs("\x1b[27m", tty);
		}

		fwrite(str + start, 1, record->size - start, tty);
	}
}

static void
emit_record(struct record const *record)
{
	if (opt_print_indices)
		printf("%"PRIu32, record->index);
	else
		fwrite(record->bytes + BITSET_SIZE(record->size), 1, record->size, stdout);
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
submit_line(char *line)
{
	(void)line;
	accept_one();
}

static int
filter_matches(int count, int c)
{
	(void)count, (void)c;
	nb_records = nb_matches;
	rl_replace_line("", true);

	if (1 == nb_records)
		accept_one();

	return 1;
}

static void
run_tui(void)
{
	tty = fopen(ctermid(NULL), "w+");
	if (!tty) {
		perror("Cannot open terminal");
		exit(EXIT_FAILURE);
	}
	setvbuf(tty, NULL, _IOFBF, BUFSIZ);

	rl_readline_name = "fizzy";
	rl_instream = tty;
	rl_outstream = tty;

	rl_callback_handler_install(opt_prompt, submit_line);

	fputs("\x1b[?7l", tty);

	rl_insert_text(opt_query);

	rl_resize_terminal();
	/* rl_bind_key(' ', filter_matches); */
	rl_bind_key('\t', filter_matches);

	for (;;) {
		fputs("\x1b[H\x1b[2J\n\x1b[m", tty);
		int rows, cols;
		rl_get_screen_size(&rows, &cols);

		score_all();
		sort_all();

		if (nb_records == nb_total_records)
			fprintf(tty, "[%"PRIu32"/%"PRIu32"] %s", nb_matches, nb_records, opt_header);
		else
			fprintf(tty, "[%"PRIu32"/%"PRIu32" (%"PRIu32")] %s", nb_matches, nb_records, nb_total_records, opt_header);

		print_records(rows - 2);

		fputs("\x1b[H\x1b[;1m", tty);

		fflush(tty);

		if (opt_print_changes)
			emit_one();

		rl_forced_update_display();
		rl_callback_read_char();

		snprintf(opt_query, sizeof opt_query, "%s", rl_line_buffer);
	}
}

int
main(int argc, char *argv[])
{
	for (int opt; -1 != (opt = getopt(argc, argv, "0acfh:jip:q:s"));)
		switch (opt) {
		case '0':
			opt_delim = '\0';
			break;

		case 'a':
			opt_delim = '^' - '@';
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

		case 'j':
			opt_prefix_alpha = true;
			break;

		case 'i':
			opt_print_indices = true;
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

		case '?':
		default:
			fprintf(stderr, "unknown option: '%c'\n", opt);
			return EXIT_FAILURE;
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

	read_records(input);
	nb_matches = nb_total_records;
	nb_records = nb_total_records;

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

	if (opt_interactive) {
		run_tui();
	} else {
		score_all();
		sort_all();
		emit_all();
	}
}
