#define _POSIX_C_SOURCE 200809

#include <stdio.h>

#include <readline/readline.h>

#include <ctype.h>
#include <curses.h>
#include <getopt.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <term.h>
#include <unistd.h>

enum {
	QUERY_SIZE_MAX = 32,
	MATCH_RANGE_MAX = UINT8_MAX,
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

static char opt_delim = '\n';
static char const *opt_prefix_format = NULL;
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
	size_t index;
	size_t len;
	uint8_t bytes[];
};

#if 0
# define D(...) printf(__VA_ARGS__)
#else
# define D(...) ((void)0)
#endif

static size_t nrecords, nmatches;
static struct record **records;

#define BITSET_SIZE(n) (((n) + (CHAR_BIT - 1)) / CHAR_BIT)

static void
add_record(char const *buf, size_t bufsz, char const *prefix, size_t prefixsz)
{
	size_t len = prefixsz + bufsz;
	size_t sz = offsetof(struct record, bytes[BITSET_SIZE(len) + len]);
	struct record *record = malloc(sz);
	if (!record)
		abort();

	record->score = 0;
	record->index = nrecords;
	record->len = len;
	memset(record->bytes, 0, BITSET_SIZE(len));
	uint8_t *str = record->bytes + BITSET_SIZE(len);
	memcpy(str, prefix, prefixsz);
	memcpy(record->bytes + BITSET_SIZE(len) + prefixsz, buf, bufsz);

	bool escape = false;
	for (size_t i = 0; i < len; ++i) {
		uint8_t c = str[i];

		escape |= ('[' - '@') == c;

		bool control = c < ' ';
		bool ignore = control || escape;
		record->bytes[i / CHAR_BIT] |= ignore << (i % CHAR_BIT);

		/* End of SGR sequence. */
		escape &= 'm' != c;
	}

	/* Allocate 2^x sizes. */
	if (!(nrecords & (nrecords - 1))) {
		records = realloc(records, (2 * nrecords + !nrecords) * sizeof *records);
		if (!records)
			abort();
	}
	records[nrecords++] = record;
}

static uint8_t const BONUS[] = {
#define xmacro(c) \
	  '\0' == c ? 4 /* start of line */ \
	: '\t' == c ? 4 /* field separator */ \
	: '/' == c ? 3 /* file paths */ \
	: ' ' == c ? 3 /* word separator */ \
	: 'A' <= c && c <= 'Z' ? 2 /* camelCase */ \
	: '_' == c ? 2 /* snake_case */ \
	: '-' == c ? 2 /* snake-case */ \
	: '.' == c ? 2 /* file extension */ \
	: ':' == c ? 2 /* file:line:col */ \
	: '$' == c ? 1 /* $var */ \
	: '(' == c ? 1 /* (stuff) */ \
	: '[' == c ? 1 /* [tag] */ \
	: '#' == c ? 1 /* #ticket, */ \
	: 0,
	REPEAT256(0)
#undef xmacro
};

uint32_t const GAP_PENALTY = 50;
uint32_t const TRAILING_GAP_PENALTY = 1;

static void
score_record(struct record *record, size_t positions[static QUERY_SIZE_MAX])
{
	uint32_t scores[QUERY_SIZE_MAX][MATCH_RANGE_MAX];
	uint8_t shifts[QUERY_SIZE_MAX][MATCH_RANGE_MAX];

	record->score = 0;

	size_t n = record->len;
	uint8_t const *str = record->bytes + BITSET_SIZE(record->len);

	uint8_t const *ptr = str;
	uint8_t const *end = ptr + n;

	size_t row = 0;
	for (char const *q = opt_query; *q; ++q, ++row) {
		size_t i;
		for (;;) {
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

			if (!(record->bytes[i / CHAR_BIT] & (1 << i % CHAR_BIT)))
				break;
		}

		positions[row] = i;
	}

	record->score = 1024;

	if (!row) {
		positions[0] = SIZE_MAX;
		return;
	}

	D("%.*s\n", (int)n, str);

	row = 0;
	D("  ");
	for (size_t x = 0; x < n; ++x)
		D("          %c", isprint(str[x]) ? str[x] : '.');
	D("\n");

	for (char const *q = opt_query; *q; ++q, ++row) {
		size_t skip = positions[row];
		D("%c:", *q);

		/* for (size_t x = 0; x < skip - positions[0]; ++x)
			printf("     "); */

		uint32_t max = 0;
		uint8_t max_col = 0;
		for (size_t col = 0; col < n; ++col) {
			if (!row || !col)
				;
			else if (max <= scores[row - 1][col - 1]) {
				max = scores[row - 1][col - 1];
				max_col = col - 1;
			}

			int B = 50 * GAP_PENALTY;
			/proded
			/camelCase
			uint32_t bonus = BONUS[0 < col ? str[col - 1] : '\0'] * B;

			/* No double bonus. Bonus is only for otherwise low quality matches. */
#if 0
			CAPITAL_LETTERS
			if (bonus <= BONUS[str[col]])
				bonus = 0;
#endif

			bool z = 'a' <= *q && *q <= 'z' && (*q ^ ' ') == str[col];
			uint32_t self = *q == str[col] || z
				? (
					max +
					bonus +
					((z && 'A' <= str[col] && str[col] <= 'Z') ? 1 + 1 : 1) * B +
					(0 < row && 0 < col ? scores[row - 1][col - 1] / 2 /* Continous. */ : 0)
				)
				: 0;

			if (col < skip) {
				self = 0;
			}

			bool ignore = record->bytes[col / CHAR_BIT] & (1 << (col % CHAR_BIT));

			if (ignore)
				self = 0;

			shifts[row][col] = max_col;

			scores[row][col] = self;
			D("%c%6d(%2d)", bonus ? '+' : ' ', self, max_col);

			if (ignore)
				continue;
			if (GAP_PENALTY < max)
				max -= GAP_PENALTY;
		}
		D("\n");
	}

	uint32_t last_max = 0;
	uint8_t last_max_col;
	for (size_t col = 0; col < n; ++col) {
		uint32_t score = scores[row - 1][col];
		if (!score)
			continue;
		uint32_t penalty = (n - col - 1) * TRAILING_GAP_PENALTY;
		if (score <= penalty)
			continue;
		score -= penalty;
		if (last_max < score) {
			last_max = score;
			last_max_col = col;
		}
	}

	record->score = last_max;

	positions[row] = 0;
	positions[row - 1] = last_max_col;
	D("o[%d]=%d\n", row - 1, last_max_col);
	while (row > 1) {
		last_max_col = shifts[--row][last_max_col];
		positions[row - 1] = last_max_col;
		D("[%d]=%d\n", row - 1, last_max_col);
	}
	D("\n");
}

static void
score_records(void)
{
	nmatches = 0;
	for (size_t i = 0; i < nrecords; ++i) {
		struct record *record = records[i];
		size_t positions[QUERY_SIZE_MAX];
		score_record(record, positions);
		if (record->score) {
			struct record *t = records[nmatches];
			records[nmatches] = record;
			records[i] = t;
			++nmatches;
		}
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
sort_records(void)
{
	if (!opt_sort)
		return;
	qsort(records, nmatches, sizeof *records, compare_score);
}

static char const *
generate_word(size_t i, char a, char z)
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
		char prefix[100];
		int prefixlen = 0;
		if (opt_prefix_alpha) {
			char const *word = generate_word(nrecords, 'A', 'Z');
			prefixlen = sprintf(prefix, opt_prefix_format, word);
		}
		add_record(line, linelen - 1 /* CR */, prefix, prefixlen);
	}
	free(line);
}

static void
print_records(size_t nlines)
{
	for (size_t i = 0; i < nmatches && i < nlines; ++i) {
		fputs("\n\x1b[m", tty);

		struct record *record = records[i];
		size_t positions[QUERY_SIZE_MAX];
		score_record(record, positions);
		/* fprintf(tty, "(%5d) ", record->score); */
		size_t k = 0;
		bool hi = false;
		for (size_t j = 0; j < record->len; ++j) {
			bool matched = j == positions[k];
			if (matched)
				++k;
			if (hi != matched) {
				hi = matched;
				fputs(hi ? "\x1b[7m" : "\x1b[27m", tty);
			}
			fputc(((uint8_t*)(record->bytes + BITSET_SIZE(record->len)))[j], tty);
		}
	}
}

static void
print_record(struct record const *record)
{
	if (opt_print_indices)
		printf("%zu", record->index);
	else
		fwrite(record->bytes + BITSET_SIZE(record->len), 1, record->len, stdout);
	fputc(opt_delim, stdout);
}

static bool
print_one(void)
{
	if (!nmatches)
		return false;
	print_record(records[0]);
	fflush(stdout);
	return true;
}

static bool
print_all(void)
{
	if (!nmatches)
		return false;
	for (size_t i = 0; i < nmatches; ++i) {
		print_record(records[i]);
	}
	fflush(stdout);
	return true;
}

static void
accept_one(char *line)
{
	(void)line;
	exit(print_one() ? EXIT_SUCCESS : EXIT_FAILURE);
}

static void
run_tui()
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

	rl_callback_handler_install(opt_prompt, &accept_one);

	fputs("\x1b[?7l", tty);

	rl_insert_text(opt_query);

	rl_resize_terminal();
	rl_bind_key('\t', rl_insert);

	for (;;) {
		fputs("\x1b[H\x1b[2J\n\x1b[m", tty);
		int rows, cols;
		rl_get_screen_size(&rows, &cols);

		score_records();
		sort_records();

		fprintf(tty, "[%zu/%zu] %s", nmatches, nrecords, opt_header);

		print_records(rows - 2);

		fputs("\x1b[H\x1b[;1m", tty);

		fflush(tty);

		if (opt_print_changes)
			print_one();

		rl_forced_update_display();
		rl_callback_read_char();

		snprintf(opt_query, sizeof opt_query, "%s", rl_line_buffer);
	}
}

int
main(int argc, char *argv[])
{
	for (int opt; -1 != (opt = getopt(argc, argv, "0acfh:ilp:q:"));)
		switch (opt) {
		case '0':
			opt_delim = '\0';
			break;

		case 'a':
			opt_prefix_format = "%s\t";
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

	if (opt_interactive) {
		run_tui();
	} else {
		score_records();
		sort_records();
		print_all();
	}
}
