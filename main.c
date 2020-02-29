#include <avr/io.h>
#include <avr/power.h>
#include <avr/sleep.h>
#include <avr/pgmspace.h>
#include <avr/interrupt.h>
#include <util/delay.h>
#include <math.h>
#include <ctype.h>
#include <stdint.h>
#include <stdlib.h>
#include "lcd.c"

#define PIN_SHIFT               4

#define MSG_START_LEN           6
#define MSG_STEP_LEN            5
#define MSG_ERROR_LEN           5
#define FIELD_START_WIDTH      16
#define FIELD_STEP_WIDTH       16
#define FIELD_NUMBER_WIDTH     16
#define NUMBER_STACK_SIZE      32
#define OPERATOR_STACK_SIZE    32
#define TOKEN_LIST_SIZE        32
#define OUTPUT_PRECISION        4
#define MODE_TABLE_STEP_BIG    10
#define TERM_MAX_LEN          256

#define UNSHIFT(key)             (key & ~(1 << 4))
#define RAD_TO_DEG(rad)          ((rad) * (180.0 / M_PI))
#define DEG_TO_RAD(deg)          ((deg) * M_PI / 180.0)
#define SIND(x)                  (sin(DEG_TO_RAD((float)(x))))
#define COSD(x)                  (cos(DEG_TO_RAD((float)(x))))
#define TAND(x)                  (tan(DEG_TO_RAD((float)(x))))
#define ASIND(x)                 (RAD_TO_DEG(asin((float)(x))))
#define ACOSD(x)                 (RAD_TO_DEG(acos((float)(x))))
#define ATAND(x)                 (RAD_TO_DEG(atan((float)(x))))
#define FORMAT_NUMBER(v, s, n) \
	(uint8_t *)dtostrf(v, n, OUTPUT_PRECISION, (char *)s)

enum KEY
{
	KEY_NULL = -1,

	KEY_3_3,
	KEY_2_3,
	KEY_1_3,
	KEY_0_3,

	KEY_3_2,
	KEY_2_2,
	KEY_1_2,
	KEY_0_2,

	KEY_3_1,
	KEY_2_1,
	KEY_1_1,
	KEY_0_1,

	KEY_3_0,
	KEY_2_0,
	KEY_1_0,
	KEY_0_0,

	KEY_SHIFT_3_3,
	KEY_SHIFT_2_3,
	KEY_SHIFT_1_3,
	KEY_SHIFT_0_3,

	KEY_SHIFT_3_2,
	KEY_SHIFT_2_2,
	KEY_SHIFT_1_2,
	KEY_SHIFT_0_2,

	KEY_SHIFT_3_1,
	KEY_SHIFT_2_1,
	KEY_SHIFT_1_1,
	KEY_SHIFT_0_1,

	KEY_SHIFT_3_0,
	KEY_SHIFT_2_0,
	KEY_SHIFT_1_0,
	KEY_SHIFT_0_0
};

enum PGM_STRING
{
	STR_PRESS_ANY_KEY,
	ERROR_SYNTAX,
	ERROR_MATH,
	ERROR_NOMEM,
	ERROR_RANGE,
	STR_SIN,
	STR_COS,
	STR_TAN,
	STR_ASIN,
	STR_ACOS,
	STR_ATAN,
	STR_START,
	STR_STEP,
	STR_ERROR,
	STR_NO_UNKNOWNS,
};

/* Character values for pi and div are taken
from the Hitachi HD44780 LCD controller datasheet */
enum CHAR
{
	CHAR_X = 'x',
	CHAR_DP = '.',
	CHAR_LP = '(',
	CHAR_RP = ')',
	CHAR_PI = 0xF7, /* 0b11110111 */
	CHAR_ADD = '+',
	CHAR_SUB = '-',
	CHAR_MUL = '*',
	CHAR_DIV = 0xFD, /* 0b11111101 */
	CHAR_POW = '^',
};

enum TOKEN_TYPE
{
	/* Infix */
	TT_NULL,
	TT_NUMBER,
	TT_X,
	TT_LP,
	TT_RP,

	/* Postfix */
	/* Unary */
	TT_UNARY_MINUS,
	TT_LOG,
	TT_SIN,
	TT_COS,
	TT_TAN,
	TT_ASIN,
	TT_ACOS,
	TT_ATAN,

	/* Binary */
	TT_ADD,
	TT_SUB,
	TT_MUL,
	TT_DIV,
	TT_POW,
};

typedef struct FIELD
{
	uint8_t row, col, width;
	uint8_t *buf;
	int16_t pos, len, max;
} Field;

/* Constants in Flash Memory */
static const uint8_t _str_sin[] PROGMEM = "sin";
static const uint8_t _str_cos[] PROGMEM = "cos";
static const uint8_t _str_tan[] PROGMEM = "tan";
static const uint8_t _str_asin[] PROGMEM = "asin";
static const uint8_t _str_acos[] PROGMEM = "acos";
static const uint8_t _str_atan[] PROGMEM = "atan";
static const uint8_t _str_log[] PROGMEM = "log";
static const uint8_t _str_start[] PROGMEM = "START=";
static const uint8_t _str_step[] PROGMEM = "STEP=";
static const uint8_t _str_error[] PROGMEM = "ERROR";
static const uint8_t _str_press_any_key[] PROGMEM = "Press any key";
static const uint8_t _str_syntax_error[] PROGMEM = "Syntax Error";
static const uint8_t _str_math_error[] PROGMEM = "Math. Error";
static const uint8_t _str_not_enough_mem[] PROGMEM = "Not enough mem.";
static const uint8_t _str_range_error[] PROGMEM = "Range Error";

static const uint8_t *const _err_msg[] PROGMEM =
{
	_str_syntax_error,
	_str_math_error,
	_str_not_enough_mem,
	_str_range_error
};

static Field fld_term;
static uint8_t buf_term[TERM_MAX_LEN];
static uint8_t x_cnt;

static Field fld_start;
static uint8_t buf_start[FIELD_START_WIDTH];

static Field fld_step;
static uint8_t buf_step[FIELD_STEP_WIDTH];

static Field *tbl_cur_fld;
static float tbl_pos, tbl_start, tbl_step;

static uint8_t tok_cnt;
static uint8_t op_stack[OPERATOR_STACK_SIZE];
static float num_stack[NUMBER_STACK_SIZE];
static uint8_t tok_type_list[TOKEN_LIST_SIZE];
static float tok_num_list[TOKEN_LIST_SIZE];


static uint8_t _buf_conv[LCD_WIDTH + 1];

static const Field _fld_term_P PROGMEM =
{
	0, 0, LCD_WIDTH,
	buf_term,
	0, 0, TERM_MAX_LEN
};

static const Field _fld_start_P PROGMEM =
{
	0, MSG_START_LEN, LCD_WIDTH - MSG_START_LEN,
	buf_start,
	0, 0, FIELD_START_WIDTH
};

static const Field _fld_step_P PROGMEM =
{
	1, MSG_STEP_LEN, LCD_WIDTH - MSG_STEP_LEN,
	buf_step,
	0, 0, FIELD_STEP_WIDTH
};

static void (*_event)(uint8_t);
static void (*_mode)(void);

/* Field */
static void field_grow(Field *f, uint8_t n);
static void field_shrink(Field *f, uint8_t n);
static void field_ins_chr(Field *f, uint8_t c);
static void field_ins_str_P(Field *f, const uint8_t *s, uint8_t n);
static void field_clear(Field *f);
static void field_delete(Field *f);
static void field_mv_left(Field *f);
static void field_mv_right(Field *f);
static void field_update(Field *f);

/* Term Field */
static void field_term_delete(Field *f);
static void field_term_mv_left(Field *f);
static void field_term_mv_right(Field *f);

/* Number Field */
static void field_number_event(Field *f, uint8_t key);

/* Input Mode */
static void mode_input(void);
static void mode_input_event(uint8_t key);

/* Result Mode */
static void mode_result(float y);
static void mode_result_event(uint8_t key);

/* Table Mode */
static void mode_table(void);
static void mode_table_event(uint8_t key);
static void mode_table_update(void);

/* Settings Mode */
static void mode_settings(void);
static void mode_settings_event(uint8_t key);

/* Error Mode */
static void mode_error(uint8_t err);
static void mode_error_event(uint8_t key);

/* Calculation */
static uint8_t calc_prepare(uint8_t *term);
static uint8_t calc_solve(float x, float *y);
static uint8_t asin_acos_range(float n);
static uint8_t get_precedence(uint8_t tt);

int main(void)
{
	lcd_init();

	/* CTC Mode */
	TCCR2A = (1 << WGM21);

	/* Prescaler 1024 */
	TCCR2B = (1 << CS22) | (1 << CS20);

	/* Enable compare match interrupt */
	TIMSK2 = (1 << OCIE2A);

	/* 100 Hz / 10 ms at F_OSC = 8 MHz */
	OCR2A = 78;

	/* Internal pullups on shift and mode button
	pins and on all other unused pins */
	PORTB |= (1 << PIN_SHIFT) | (1 << 5) | (1 << 6) | (1 << 7);
	PORTC |= (1 << 4) | (1 << 5);
	PORTD |= (1 << 0) | (1 << 1);

	memcpy_P(&fld_term, &_fld_term_P, sizeof(Field));
	memcpy_P(&fld_start, &_fld_start_P, sizeof(Field));
	memcpy_P(&fld_step, &_fld_step_P, sizeof(Field));
	mode_input();

	sei();

	/* Reduce power usage by disabling unused modules
	and enabling sleep modes*/
	power_adc_disable();
	power_spi_disable();
	power_twi_disable();
	power_timer0_disable();
	power_timer1_disable();
	power_usart0_disable();
	sleep_enable();
	set_sleep_mode(SLEEP_MODE_PWR_SAVE);
	for(;;) { sleep_cpu(); }
	return 0;
}

/* Field */
static void field_grow(Field *f, uint8_t n)
{
	if(f->buf[f->pos])
	{
		int16_t i;
		for(i = f->len - 1; i >= f->pos; --i)
		{
			f->buf[i + n] = f->buf[i];
		}
	}

	f->len += n;
	f->buf[f->len] = '\0';
}

static void field_shrink(Field *f, uint8_t n)
{
	if(f->buf[f->pos])
	{
		int16_t i = f->pos;
		for(; f->buf[i]; ++i)
		{
			f->buf[i - n] = f->buf[i];
		}
	}
}

static void field_ins_chr(Field *f, uint8_t c)
{
	if(f->len + 1 < f->max)
	{
		field_grow(f, 1);
		f->buf [f->pos++] = c;
		field_update(f);
	}
}

static void field_ins_str_P(Field *f, const uint8_t *s, uint8_t n)
{
	if(f->len + n + 1 < f->max)
	{
		field_grow(f, n + 1);
		while(n--)
		{
			f->buf[f->pos++] = pgm_read_byte(s++);
		}

		f->buf[f->pos++] = '(';
		field_update(f);
	}
}

static void field_clear(Field *f)
{
	f->len = 0;
	f->pos = 0;
	f->buf[0] = '\0';
	field_update(f);
}

static void field_delete(Field *f)
{
	if(f->pos > 0)
	{
		field_shrink(f, 1);
		--(f->pos);
		--(f->len);
		f->buf[f->len] = '\0';
		field_update(f);
	}
}

static void field_mv_left(Field *f)
{
	if(f->pos > 0)
	{
		--(f->pos);
	}
	else
	{
		f->pos = f->len;
	}

	field_update(f);
}

static void field_mv_right(Field *f)
{
	if(f->pos < f->len)
	{
		++(f->pos);
	}
	else
	{
		f->pos = 0;
	}

	field_update(f);
}

static void field_update(Field *f)
{
	int8_t i;
	if(f->pos < f->width - 1)
	{
		lcd_cursor(f->col, f->row);
		for(i = 0; f->buf[i]; ++i)
		{
			lcd_data(f->buf[i]);
		}

		for(; i < f->width; ++i)
		{
			lcd_data(' ');
		}

		lcd_cursor(f->col + f->pos, f->row);
	}
	else
	{
		lcd_cursor(f->col + f->width - 1, f->row);
		lcd_data(' ');

		lcd_cursor(f->col, f->row);
		for(i = f->pos - (f->width - 1);
			i < f->pos + 1 && f->buf[i]; ++i)
		{
			lcd_data(f->buf[i]);
		}

		lcd_cursor(f->col + f->width - 1, f->row);
	}
}

/* Term Field */
static void field_term_delete(Field *f)
{
	if(f->pos > 0)
	{
		uint8_t n = 1, a;
		a = f->buf[f->pos - 1];
		if(a == CHAR_X)
		{
			--x_cnt;
		}
		else if(a == CHAR_LP)
		{
			for(++n; islower(f->buf[f->pos - n]); ++n) ;
			--n;
		}

		field_shrink(f, n);
		f->pos -= n;
		f->len -= n;
		f->buf[f->len] = '\0';
		field_update(f);
	}
}

static void field_term_mv_left(Field *f)
{
	if(f->pos > 0)
	{
		--(f->pos);
		if(f->buf[f->pos] == CHAR_LP)
		{
			--(f->pos);
			for(; islower(f->buf[f->pos]); --(f->pos)) ;
			++(f->pos);
		}
	}
	else
	{
		f->pos = f->len;
	}

	field_update(f);
}

static void field_term_mv_right(Field *f)
{
	if(f->pos < f->len)
	{
		if(f->buf[f->pos] != CHAR_X)
		{
			while(islower(f->buf[f->pos]))
			{
				++(f->pos);
			}
		}

		++(f->pos);
	}
	else
	{
		f->pos = 0;
	}

	field_update(f);
}

/* Number Field */
static void field_number_event(Field *f, uint8_t key)
{
	switch(key)
	{
	case KEY_0_0:
		field_ins_chr(f, '1');
		break;

	case KEY_0_1:
		field_ins_chr(f, '4');
		break;

	case KEY_0_2:
		field_ins_chr(f, '7');
		break;

	case KEY_1_0:
		field_ins_chr(f, '2');
		break;

	case KEY_1_1:
		field_ins_chr(f, '5');
		break;

	case KEY_1_2:
		field_ins_chr(f, '8');
		break;

	case KEY_1_3:
		field_ins_chr(f, '0');
		break;

	case KEY_2_0:
		field_ins_chr(f, '3');
		break;

	case KEY_2_1:
		field_ins_chr(f, '6');
		break;

	case KEY_2_2:
		field_ins_chr(f, '9');
		break;

	case KEY_3_0:
		field_clear(f);
		break;

	case KEY_3_1:
		field_delete(f);
		break;

	case KEY_3_2:
		field_ins_chr(f, CHAR_DP);
		break;

	case KEY_SHIFT_0_1:
		/* left */
		field_mv_left(f);
		break;

	case KEY_SHIFT_2_1:
		/* right */
		field_mv_right(f);
		break;
	}
}

/* Input Mode */
static void mode_input(void)
{
	_mode = mode_input;
	_event = mode_input_event;
	lcd_clear();
	lcd_command(LCD_SET_DISPLAY | LCD_DISPLAY_ON |
		LCD_CURSOR_ON | LCD_BLINKING_OFF);
	field_update(&fld_term);
}

static void mode_input_event(uint8_t key)
{
	switch(key)
	{
	case KEY_0_0:
		field_ins_chr(&fld_term, '1');
		break;

	case KEY_0_1:
		field_ins_chr(&fld_term, '4');
		break;

	case KEY_0_2:
		field_ins_chr(&fld_term, '7');
		break;

	case KEY_0_3:
		field_ins_chr(&fld_term, CHAR_LP);
		break;

	case KEY_1_0:
		field_ins_chr(&fld_term, '2');
		break;

	case KEY_1_1:
		field_ins_chr(&fld_term, '5');
		break;

	case KEY_1_2:
		field_ins_chr(&fld_term, '8');
		break;

	case KEY_1_3:
		field_ins_chr(&fld_term, '0');
		break;

	case KEY_2_0:
		field_ins_chr(&fld_term, '3');
		break;

	case KEY_2_1:
		field_ins_chr(&fld_term, '6');
		break;

	case KEY_2_2:
		field_ins_chr(&fld_term, '9');
		break;

	case KEY_2_3:
		field_ins_chr(&fld_term, CHAR_RP);
		break;

	case KEY_3_0:
		field_clear(&fld_term);
		x_cnt = 0;
		break;

	case KEY_3_1:
		field_term_delete(&fld_term);
		break;

	case KEY_3_2:
		field_ins_chr(&fld_term, CHAR_DP);
		break;

	case KEY_3_3:
	{
		/* enter */
		uint8_t err;
		float y = 0;
		if((err = calc_prepare(buf_term)))
		{
			mode_error(err);
			break;
		}

		err = calc_solve(0, &y);
		if(x_cnt)
		{
			if(err && err != ERROR_MATH)
			{
				mode_error(err);
				break;
			}

			mode_settings();
		}
		else
		{
			if(err)
			{
				mode_error(err);
				break;
			}

			mode_result(y);
		}
		break;
	}

	case KEY_SHIFT_0_0:
		field_ins_str_P(&fld_term, _str_sin, 3);
		break;

	case KEY_SHIFT_0_1:
		field_term_mv_left(&fld_term);
		break;

	case KEY_SHIFT_0_2:
		field_ins_chr(&fld_term, CHAR_X);
		++x_cnt;
		break;

	case KEY_SHIFT_0_3:
		field_ins_str_P(&fld_term, _str_asin, 4);
		break;

	case KEY_SHIFT_1_0:
		field_ins_str_P(&fld_term, _str_cos, 3);
		break;

	case KEY_SHIFT_1_1:
		field_ins_chr(&fld_term, CHAR_PI);
		break;

	case KEY_SHIFT_1_2:
		field_ins_chr(&fld_term, CHAR_POW);
		break;

	case KEY_SHIFT_1_3:
		field_ins_str_P(&fld_term, _str_acos, 4);
		break;

	case KEY_SHIFT_2_0:
		field_ins_str_P(&fld_term, _str_tan, 3);
		break;

	case KEY_SHIFT_2_1:
		field_term_mv_right(&fld_term);
		break;

	case KEY_SHIFT_2_2:
		field_ins_str_P(&fld_term, _str_log, 3);
		break;

	case KEY_SHIFT_2_3:
		field_ins_str_P(&fld_term, _str_atan, 4);
		break;

	case KEY_SHIFT_3_0:
		field_ins_chr(&fld_term, CHAR_ADD);
		break;

	case KEY_SHIFT_3_1:
		field_ins_chr(&fld_term, CHAR_SUB);
		break;

	case KEY_SHIFT_3_2:
		field_ins_chr(&fld_term, CHAR_MUL);
		break;

	case KEY_SHIFT_3_3:
		field_ins_chr(&fld_term, CHAR_DIV);
		break;

	default:
		break;
	}
}

/* Result Mode */
static void mode_result(float y)
{
	_event = mode_result_event;
	lcd_cursor(0, 1);
	lcd_string(FORMAT_NUMBER(y, _buf_conv, sizeof(_buf_conv) - 1));
	lcd_cursor(fld_term.pos < LCD_WIDTH - 1 ?
		fld_term.pos : LCD_WIDTH - 1, 0);
}

static void mode_result_event(uint8_t key)
{
	mode_input();
	mode_input_event(key);
}

/* Table Mode */
static void mode_table(void)
{
	tbl_pos = 0;
	_event = mode_table_event;
	lcd_command(LCD_SET_DISPLAY | LCD_DISPLAY_ON |
		LCD_CURSOR_OFF | LCD_BLINKING_OFF);
	lcd_cursor(0, 0);
	lcd_data('X');
	lcd_data('=');
	lcd_cursor(0, 1);
	lcd_data('Y');
	lcd_data('=');
	mode_table_update();
}

static void mode_table_event(uint8_t key)
{
	switch(UNSHIFT(key))
	{
	case KEY_0_0:
		mode_input();
		break;

	case KEY_0_1:
		/* left arrow */
		tbl_pos -= MODE_TABLE_STEP_BIG;
		mode_table_update();
		break;

	case KEY_1_0:
		/* up arrow */
		--tbl_pos;
		mode_table_update();
		break;

	case KEY_1_1:
		/* reset */
		tbl_pos = 0;
		mode_table_update();
		break;

	case KEY_1_2:
		/* down arrow */
		++tbl_pos;
		mode_table_update();
		break;

	case KEY_2_1:
		/* right arrow */
		tbl_pos += MODE_TABLE_STEP_BIG;
		mode_table_update();
		break;

	default:
		break;
	}
}

static void mode_table_update(void)
{
	float x, y;
	x = tbl_start + tbl_pos * tbl_step;
	y = 0;

	/* Print X */
	lcd_cursor(2, 0);
	lcd_string(FORMAT_NUMBER(x, _buf_conv, 14));

	if(calc_solve(x, &y))
	{
		/* Do not go into error mode when in table mode, because
		often functions are undefined for some x values. e.g.
		f(0) = 1 / x = NaN
		Print "ERROR" for y instead. */
		uint8_t i;
		lcd_cursor(2, 1);
		for(i = 2; i < LCD_WIDTH - MSG_ERROR_LEN; ++i)
		{
			lcd_data(' ');
		}

		lcd_string_P(_str_error);
	}
	else
	{
		/* Print Y */
		lcd_cursor(2, 1);
		lcd_string(FORMAT_NUMBER(y, _buf_conv, 14));
	}
}

/* Settings Mode */
static void mode_settings(void)
{
	_mode = mode_settings;
	_event = mode_settings_event;
	tbl_cur_fld = &fld_start;

	lcd_clear();
	lcd_command(LCD_SET_DISPLAY | LCD_DISPLAY_ON |
		LCD_CURSOR_ON | LCD_BLINKING_OFF);

	lcd_string_P(_str_start);
	lcd_string(buf_start);

	lcd_cursor(0, 1);
	lcd_string_P(_str_step);
	lcd_string(buf_step);
	field_update(tbl_cur_fld);
}

static void mode_settings_event(uint8_t key)
{
	field_number_event(tbl_cur_fld, key);
	switch(key)
	{
	case KEY_3_3:
		/* enter */
		/* if the start value is invalid, ignore it and just use 0.0 instead */
		tbl_start = atof((char *)buf_start);

		/* step has to be greater than zero */
		if((tbl_step = atof((char *)buf_step)) == 0.0)
		{
			mode_error(ERROR_RANGE);
			break;
		}

		mode_table();
		break;

	case KEY_SHIFT_0_0:
		/* escape */
		mode_input();
		break;

	case KEY_SHIFT_3_1:
		/* minus */
		if(tbl_cur_fld == &fld_start)
		{
			field_ins_chr(tbl_cur_fld, '-');
		}
		break;

	case KEY_SHIFT_1_0:
		/* up */
		tbl_cur_fld = &fld_start;
		field_update(tbl_cur_fld);
		break;

	case KEY_SHIFT_1_2:
		/* down */
		tbl_cur_fld = &fld_step;
		field_update(tbl_cur_fld);
		break;
	}
}

/* Error Mode */
static void mode_error(uint8_t err)
{
	lcd_clear();
	lcd_command(LCD_SET_DISPLAY | LCD_DISPLAY_ON |
		LCD_CURSOR_OFF | LCD_BLINKING_OFF);
	lcd_string_P((uint8_t *)pgm_read_word(_err_msg + err - 1));
	_event = mode_error_event;
	lcd_cursor(0, 1);
	lcd_string_P(_str_press_any_key);
}

static void mode_error_event(uint8_t key)
{
	_mode();
}

/* Calculation */
static uint8_t calc_prepare(uint8_t *term)
{
	uint8_t c, cur_type, isop, top_stack, top_num;
	cur_type = TT_NULL;
	tok_cnt = 0;
	top_num = 0;
	top_stack = 0;
	while((c = *term))
	{
		isop = 1;

		/* Tokenizer */
		if(isdigit(c))
		{
			/* Numbers */
			uint8_t *begin, dps;
			float n, power;

			/* Find the end of the float */
			for(dps = 0, begin = term; (c = *term); ++term)
			{
				if(c == CHAR_DP)
				{
					if(++dps > 1)
					{
						/* Return a syntax error if there
						is more than one decimal point */
						return ERROR_SYNTAX;
					}
				}
				else if(!isdigit(c))
				{
					/* Break when the end of the number
					(non digit character) is reached */
					break;
				}
			}

			/* Digits before the decimal point */
			for(n = 0.0; begin < term; ++begin)
			{
				if((c = *begin) == CHAR_DP)
				{
					/* Skip the decimal point, if present */
					++begin;
					break;
				}

				n = n * 10.0 + c - '0';
			}

			/* Digits after the decimal point */
			for(power = 1.0; begin < term; ++begin)
			{
				n = n * 10.0 + *begin - '0';
				power *= 10.0;
			}

			if(tok_cnt >= TOKEN_LIST_SIZE - 1)
			{
				return ERROR_NOMEM;
			}

			tok_type_list[tok_cnt++] = cur_type = TT_NUMBER;
			tok_num_list[top_num++] = n / power;
			isop = 0;
		}
		else
		{
			/* Translate characters to tokens */
			switch(c)
			{
			case CHAR_SUB:
				switch(cur_type)
				{
				case TT_NULL:
				case TT_ADD:
				case TT_SUB:
				case TT_MUL:
				case TT_DIV:
				case TT_POW:
				case TT_LP:
					cur_type = TT_UNARY_MINUS;
					break;

				case TT_NUMBER:
				case TT_X:
				case TT_RP:
					cur_type = TT_SUB;
					break;
				}
				break;

			case CHAR_PI:
				if(tok_cnt >= TOKEN_LIST_SIZE - 1)
				{
					return ERROR_NOMEM;
				}

				tok_type_list[tok_cnt++] =
					cur_type = TT_NUMBER;
				tok_num_list[top_num++] = M_PI;
				isop = 0;
				break;

			case CHAR_X:
				if(tok_cnt >= TOKEN_LIST_SIZE - 1)
				{
					return ERROR_NOMEM;
				}

				tok_type_list[tok_cnt++] =
					cur_type = TT_X;
				isop = 0;
				break;

			/* Parenthesis */
			case CHAR_LP:
				/* Push onto the operator stack */
				if(top_stack >= OPERATOR_STACK_SIZE - 1)
				{
					return ERROR_NOMEM;
				}

				op_stack[top_stack++] = cur_type = TT_LP;
				isop = 0;
				break;

			case CHAR_RP:
			{
				/* Pop all operators from the stack
				until the opening bracket is found */
				uint8_t t, i;
				cur_type = TT_RP;
				i = 1;
				while(i)
				{
					if(top_stack == 0)
					{
						/* Missing opening bracket */
						return ERROR_SYNTAX;
					}

					if((t = op_stack[top_stack - 1]) == TT_LP)
					{
						i = 0;
					}
					else
					{
						if(tok_cnt >= TOKEN_LIST_SIZE - 1)
						{
							return ERROR_NOMEM;
						}

						tok_type_list[tok_cnt++] = t;
					}

					--top_stack;
				}

				isop = 0;
				break;
			}

			/* Operators */
			case CHAR_ADD:
				cur_type = TT_ADD;
				break;

			case CHAR_MUL:
				cur_type = TT_MUL;
				break;

			case CHAR_DIV:
				cur_type = TT_DIV;
				break;

			case CHAR_POW:
				cur_type = TT_POW;
				break;

			/* Logarithm */
			case 'l':
				cur_type = TT_LOG;
				goto add2;

			/* Trigonometric functions */
			case 'a':
				switch(*(++term))
				{
				case 's':
					cur_type = TT_ASIN;
					break;

				case 'c':
					cur_type = TT_ACOS;
					break;

				case 't':
					cur_type = TT_ATAN;
					break;
				}

				goto add2;

			case 's':
				cur_type = TT_SIN;
				goto add2;

			case 'c':
				cur_type = TT_COS;
				goto add2;

			case 't':
				cur_type = TT_TAN;

			add2:
				term += 2;
			}

			++term;
		}

		/* RPN converter using the
		shunting yard algorithm */
		if(isop)
		{
			/* Any operator: pop all operators from
			the stack that have a lower precedence */
			uint8_t precedence, tmp;
			precedence = get_precedence(cur_type);
			while(top_stack > 0)
			{
				tmp = op_stack[top_stack - 1];
				if((get_precedence(tmp) > precedence) ||
					(tmp == TT_LP))
				{
					break;
				}

				--top_stack;
				if(tok_cnt >= TOKEN_LIST_SIZE - 1)
				{
					return ERROR_NOMEM;
				}

				tok_type_list[tok_cnt++] = tmp;
			}

			if(top_stack >= OPERATOR_STACK_SIZE - 1)
			{
				return ERROR_NOMEM;
			}

			op_stack[top_stack++] = cur_type;
		}
	}

	/* Pop all remaining operators from the stack */
	while(top_stack > 0)
	{
		if(tok_cnt >= TOKEN_LIST_SIZE - 1)
		{
			return ERROR_NOMEM;
		}

		tok_type_list[tok_cnt++] =
			op_stack[--top_stack];
	}

	return 0;
}

static uint8_t calc_solve(float x, float *y)
{
	float op_left, op_right;
	uint8_t tok_type_i, tok_num_i, top_num;
	tok_type_i = 0;
	tok_num_i = 0;
	top_num = 0;
	for(; tok_type_i < tok_cnt; ++tok_type_i)
	{
		switch(tok_type_list[tok_type_i])
		{
		case TT_NUMBER:
			if(top_num >= NUMBER_STACK_SIZE - 1)
			{
				return ERROR_NOMEM;
			}

			num_stack[top_num++] =
				tok_num_list[tok_num_i++];
			break;

		case TT_X:
			if(top_num >= NUMBER_STACK_SIZE - 1)
			{
				return ERROR_NOMEM;
			}

			num_stack[top_num++] = x;
			break;

		default:
			op_right = 0;
			if(tok_type_list[tok_type_i] < TT_ADD)
			{
				if(top_num == 0)
				{
					/* Buffer underflow */
					return ERROR_SYNTAX;
				}
			}
			else
			{
				if(top_num <= 1)
				{
					/* Buffer underflow */
					return ERROR_SYNTAX;
				}

				op_right = num_stack[--top_num];
			}

			op_left = num_stack[--top_num];
			switch(tok_type_list[tok_type_i])
			{
			case TT_UNARY_MINUS:
				op_left = -op_left;
				break;

			case TT_ADD:
				op_left += op_right;
				break;

			case TT_SUB:
				op_left -= op_right;
				break;

			case TT_MUL:
				op_left *= op_right;
				break;

			case TT_DIV:
				if(op_right == 0.0)
				{
					/* Division by zero */
					return ERROR_MATH;
				}

				op_left /= op_right;
				break;

			case TT_LOG:
				op_left = log(op_left);
				break;

			case TT_SIN:
				op_left = SIND(op_left);
				break;

			case TT_COS:
				op_left = COSD(op_left);
				break;

			case TT_TAN:
				op_left = TAND(op_left);
				break;

			case TT_ASIN:
				if(!asin_acos_range(op_left))
				{
					return ERROR_MATH;
				}
				op_left = ASIND(op_left);
				break;

			case TT_ACOS:
				if(!asin_acos_range(op_left))
				{
					return ERROR_MATH;
				}
				op_left = ACOSD(op_left);
				break;

			case TT_ATAN:
				op_left = ATAND(op_left);
				break;

			case TT_POW:
				op_left = pow(op_left, op_right);
				break;

			default:
				continue;
			}

			if(top_num >= NUMBER_STACK_SIZE - 1)
			{
				return ERROR_NOMEM;
			}

			num_stack[top_num++] = op_left;
			break;
		}
	}

	if(top_num != 1)
	{
		return ERROR_SYNTAX;
	}

	*y = num_stack[--top_num];
	return 0;
}

static uint8_t asin_acos_range(float n)
{
	return n >= -1 && n <= 1;
}

static uint8_t get_precedence(uint8_t tt)
{
	switch(tt)
	{
	case TT_ADD:
	case TT_SUB:
		return 3;

	case TT_MUL:
	case TT_DIV:
		return 2;

	case TT_POW:
		return 1;
	}

	return 0;
}

/* Key Scanning Interrupt */
ISR(TIMER2_COMPA_vect)
{
	static int8_t last_key = KEY_NULL;
	static uint8_t t = 0, lt = 3;
	static uint16_t key_states = 0;

	key_states |= (PINC & 0x0F) << (4 * lt);
	DDRB &= ~(1 << lt);
	PORTB &= ~(1 << lt);

	if(++lt == 4)
	{
		lt = 0;
	}

	DDRB |= (1 << t);
	PORTB |= (1 << t);

	if(++t == 4)
	{
		int8_t key = KEY_NULL;
		for(t = 0; t < 16; ++t)
		{
			/* pressed */
			if((key_states >> t) & 1)
			{
				key = t;

				/* shift */
				if(!((PINB >> PIN_SHIFT) & 1))
				{
					key += 16;
				}
				break;
			}
		}

		key_states = 0;
		t = 0;
		if(key != last_key && last_key == KEY_NULL)
		{
			_event((uint8_t)key);
		}

		last_key = key;
	}
}

