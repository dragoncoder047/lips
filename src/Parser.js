/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol */
import { LNumber, LComplex, LRational, LFloat, nan } from './Numbers.js';
import { nil, Pair } from './Pair.js';
import { eof } from './Ports.js';
import { LSymbol } from './LSymbol.js';
import Stack from './Stack.js';
import LCharacter from './LCharacter.js';
import LString from './LString.js';
import { read_only } from './utils.js';
import { is_plain_object } from './typechecking.js';
import { global_env, user_env } from './CoreLibrary.js';
import { evaluate } from './eval.js';
import { Macro } from './Macro.js';

/* eslint-disable max-len */
// functions generate regexes to match number rational, integer, complex, complex+ratioanl
function num_mnemicic_re(mnemonic) {
    return mnemonic ? `(?:#${mnemonic}(?:#[ie])?|#[ie]#${mnemonic})` : '(?:#[ie])?';
}
function gen_rational_re(mnemonic, range) {
    return `${num_mnemicic_re(mnemonic)}[+-]?${range}+/${range}+`;
}
// TODO: float complex
function gen_complex_re(mnemonic, range) {
    // [+-]i have (?=..) so it don't match +i from +inf.0
    return `${num_mnemicic_re(mnemonic)}(?:[+-]?(?:${range}+/${range}+|nan.0|inf.0|${range}+))?(?:[+-]i|[+-]?(?:${range}+/${range}+|${range}+|nan.0|inf.0)i)(?=[()[\\]\\s]|$)`;
}
function gen_integer_re(mnemonic, range) {
    return `${num_mnemicic_re(mnemonic)}[+-]?${range}+`;
}
var re_re = /^#\/((?:\\\/|[^/]|\[[^\]]*\/[^\]]*\])+)\/([gimyus]*)$/;
var float_stre = '(?:[-+]?(?:[0-9]+(?:[eE][-+]?[0-9]+)|(?:\\.[0-9]+|[0-9]+\\.[0-9]+)(?:[eE][-+]?[0-9]+)?)|[0-9]+\\.)';
// TODO: extend to ([+-]1/2|float)([+-]1/2|float)
var complex_float_stre = `(?:#[ie])?(?:[+-]?(?:[0-9]+/[0-9]+|nan.0|inf.0|${float_stre}|[+-]?[0-9]+))?(?:${float_stre}|[+-](?:[0-9]+/[0-9]+|[0-9]+|nan.0|inf.0))i`;
var float_re = new RegExp(`^(#[ie])?${float_stre}$`, 'i');
function make_complex_match_re(mnemonic, range) {
    // complex need special treatment of 10e+1i when it's hex or decimal
    var neg = mnemonic === 'x' ? `(?!\\+|${range})` : `(?!\\.|${range})`;
    var fl = '';
    if (mnemonic === '') {
        fl = '(?:[-+]?(?:[0-9]+(?:[eE][-+]?[0-9]+)|(?:\\.[0-9]+|[0-9]+\\.[0-9]+(?![0-9]))(?:[eE][-+]?[0-9]+)?))';
    }
    return new RegExp(`^((?:(?:${fl}|[-+]?inf.0|[-+]?nan.0|[+-]?${range}+/${range}+(?!${range})|[+-]?${range}+)${neg})?)(${fl}|[-+]?inf.0|[-+]?nan.0|[+-]?${range}+/${range}+|[+-]?${range}+|[+-])i$`, 'i');
}
var complex_list_re = (function() {
    var result = {};
    [
        [10, '', '[0-9]'],
        [16, 'x', '[0-9a-fA-F]'],
        [8, 'o', '[0-7]'],
        [2, 'b', '[01]']
    ].forEach(([radix, mnemonic, range]) => {
        result[radix] = make_complex_match_re(mnemonic, range);
    });
    return result;
})();
const characters = {
    'alarm': '\x07',
    'backspace': '\x08',
    'delete': '\x7F',
    'escape': '\x1B',
    'newline': '\n',
    'null': '\x00',
    'return': '\r',
    'space': ' ',
    'tab': '\t',
    // new symbols from ASCII table in SRFI-175
    'dle': '\x10',
    'soh': '\x01',
    'dc1': '\x11',
    'stx': '\x02',
    'dc2': '\x12',
    'etx': '\x03',
    'dc3': '\x13',
    'eot': '\x04',
    'dc4': '\x14',
    'enq': '\x05',
    'nak': '\x15',
    'ack': '\x06',
    'syn': '\x16',
    'bel': '\x07',
    'etb': '\x17',
    'bs': '\x08',
    'can': '\x18',
    'ht': '\x09',
    'em': '\x19',
    'lf': '\x0a',
    'sub': '\x1a',
    'vt': '\x0b',
    'esc': '\x1b',
    'ff': '\x0c',
    'fs': '\x1c',
    'cr': '\x0d',
    'gs': '\x1d',
    'so': '\x0e',
    'rs': '\x1e',
    'si': '\x0f',
    'us': '\x1f',
    'del': '\x7f'
};
// -------------------------------------------------------------------------
const constants = {
    'true': true,
    'false': false,
    '#true': true,
    '#false': false,
    '#t': true,
    '#f': false,
    nil,
    'undefined': undefined,
    'null': null,
    'NaN': nan,
    '+nan.0': nan,
    '-nan.0': nan
};
// -------------------------------------------------------------------------
// :: ref: https://github.com/bestiejs/punycode.js/blob/master/punycode.js
// -------------------------------------------------------------------------
function ucs2decode(string) {
    const output = [];
    let counter = 0;
    const length = string.length;
    while (counter < length) {
        const value = string.charCodeAt(counter++);
        if (value >= 0xD800 && value <= 0xDBFF && counter < length) {
            // It's a high surrogate, and there is a next character.
            const extra = string.charCodeAt(counter++);
            if ((extra & 0xFC00) === 0xDC00) { // Low surrogate.
                output.push(((value & 0x3FF) << 10) + (extra & 0x3FF) + 0x10000);
            } else {
                // It's an unmatched surrogate; only append this code unit, in case the
                // next code unit is the high surrogate of a surrogate pair.
                output.push(value);
                counter--;
            }
        } else {
            output.push(value);
        }
    }
    return output;
}
// -------------------------------------------------------------------------
const character_symbols = Object.keys(characters).join('|');
const char_sre_re = `#\\\\(?:x[0-9a-f]+|${character_symbols}|[\\s\\S])`;
const char_re = new RegExp(`^${char_sre_re}$`, 'i');
// complex with (int) (float) (rational)
function make_num_stre(fn) {
    const ranges = [
        ['o', '[0-7]'],
        ['x', '[0-9a-fA-F]'],
        ['b', '[01]'],
        ['d', '[0-9]'],
        ['', '[0-9]']
    ];
    // float exception that don't accept mnemonics
    let result = ranges.map(([m, range]) => fn(m, range)).join('|');
    if (fn === gen_complex_re) {
        result = complex_float_stre + '|' + result;
    }
    return result;
}
function make_type_re(fn) {
    return new RegExp('^(?:' + make_num_stre(fn) + ')$', 'i');
}
const complex_re = make_type_re(gen_complex_re);
const rational_re = make_type_re(gen_rational_re);
const int_re = make_type_re(gen_integer_re);

// regexes with full range but without mnemonics for string->number
const int_bare_re = new RegExp('^(?:' + gen_integer_re('', '[0-9a-f]') + ')$', 'i');
const rational_bare_re = new RegExp('^(?:' + gen_rational_re('', '[0-9a-f]') + ')$', 'i');
const complex_bare_re = new RegExp('^(?:' + gen_complex_re('', '[0-9a-f]') + ')$', 'i');

const complex_bare_match_re = make_complex_match_re('', '[0-9a-fA-F]');

const pre_num_parse_re = /((?:#[xodbie]){0,2})(.*)/i;
/* eslint-enable */
function num_pre_parse(arg) {
    var parts = arg.match(pre_num_parse_re);
    var options = {};
    if (parts[1]) {
        var type = parts[1].replace(/#/g, '').toLowerCase().split('');
        if (type.includes('x')) {
            options.radix = 16;
        } else if (type.includes('o')) {
            options.radix = 8;
        } else if (type.includes('b')) {
            options.radix = 2;
        } else if (type.includes('d')) {
            options.radix = 10;
        }
        if (type.includes('i')) {
            options.inexact = true;
        }
        if (type.includes('e')) {
            options.exact = true;
        }
    }
    options.number = parts[2];
    return options;
}
// ----------------------------------------------------------------------
function parse_rational(arg, radix = 10) {
    var parse = num_pre_parse(arg);
    var parts = parse.number.split('/');
    var num = LRational({
        num: LNumber([parts[0], parse.radix || radix]),
        denom: LNumber([parts[1], parse.radix || radix])
    });
    if (parse.inexact) {
        return num.valueOf();
    } else {
        return num;
    }
}
// ----------------------------------------------------------------------
function parse_integer(arg, radix = 10) {
    var parse = num_pre_parse(arg);
    if (parse.inexact) {
        return LFloat(parseInt(parse.number, parse.radix || radix), true);
    }
    return LNumber([parse.number, parse.radix || radix]);
}
// ----------------------------------------------------------------------
function parse_character(arg) {
    var m = arg.match(/#\\x([0-9a-f]+)$/i);
    var char;
    if (m) {
        var ord = parseInt(m[1], 16);
        char = String.fromCodePoint(ord);
    } else {
        m = arg.match(/#\\(.+)$/);
        if (m) {
            char = m[1];
        }
    }
    if (char) {
        return LCharacter(char);
    }
    throw new Error('Parse: invalid character');
}
// ----------------------------------------------------------------------
function parse_complex(arg, radix = 10) {
    function parse_num(n) {
        var value;
        if (n === '+') {
            value = LNumber(1);
        } else if (n === '-') {
            value = LNumber(-1);
        } else if (n.match(int_bare_re)) {
            value = LNumber([n, radix]);
        } else if (n.match(rational_bare_re)) {
            var parts = n.split('/');
            value = LRational({
                num: LNumber([parts[0], radix]),
                denom: LNumber([parts[1], radix])
            });
        } else if (n.match(float_re)) {
            var float = parse_float(n);
            if (parse.exact) {
                return float.toRational();
            }
            return float;
        } else if (n.match(/nan.0$/)) {
            return LNumber(NaN);
        } else if (n.match(/inf.0$/)) {
            if (n[0] === '-') {
                return LNumber(Number.NEGATIVE_INFINITY);
            }
            return LNumber(Number.POSITIVE_INFINITY);
        } else {
            throw new Error('Internal Parser Error');
        }
        if (parse.inexact) {
            return LFloat(value.valueOf(), true);
        }
        return value;
    }
    var parse = num_pre_parse(arg);
    radix = parse.radix || radix;
    var parts;
    var bare_match = parse.number.match(complex_bare_match_re);
    if (radix !== 10 && bare_match) {
        parts = bare_match;
    } else {
        parts = parse.number.match(complex_list_re[radix]);
    }
    var re, im;
    im = parse_num(parts[2]);
    if (parts[1]) {
        re = parse_num(parts[1]);
    } else {
        re = LNumber(0);
    }
    if (im.cmp(0) === 0 && im.__type__ === 'bigint') {
        return re;
    }
    return LComplex({ im, re });
}
// ----------------------------------------------------------------------
function is_int(value) {
    return parseInt(value.toString(), 10) === value;
}
// ----------------------------------------------------------------------
function parse_big_int(str) {
    var num_match = str.match(/^(([-+]?[0-9]*)(?:\.([0-9]+))?)e([-+]?[0-9]+)/i);
    if (num_match) {
        var exponent = parseInt(num_match[4], 10);
        var mantisa;// = parseFloat(num_match[1]);
        var digits = num_match[1].replace(/[-+]?([0-9]*)\..+$/, '$1').length;
        var decimal_points = num_match[3] && num_match[3].length;
        if (digits < Math.abs(exponent)) {
            mantisa = LNumber([num_match[1].replace(/\./, ''), 10]);
            if (decimal_points) {
                exponent -= decimal_points;
            }
        }
    }
    return { exponent, mantisa };
}
// ----------------------------------------------------------------------
function parse_float(arg) {
    var parse = num_pre_parse(arg);
    var value = parseFloat(parse.number);
    var simple_number = (parse.number.match(/\.0$/) ||
                         !parse.number.match(/\./)) && !parse.number.match(/e/i);
    if (!parse.inexact) {
        if (parse.exact && simple_number) {
            return LNumber(value);
        }
        // positive big num that eval to int e.g.: 1.2e+20
        if (is_int(value) && parse.number.match(/e\+?[0-9]/i)) {
            return LNumber(value);
        }
        // calculate big int and big fration by hand - it don't fit into JS float
        var { mantisa, exponent } = parse_big_int(parse.number);
        if (mantisa !== undefined && exponent !== undefined) {
            var factor = LNumber(10).pow(LNumber(Math.abs(exponent)));
            if (parse.exact && exponent < 0) {
                return LRational({ num: mantisa, denom: factor });
            } else if (exponent > 0) {
                return LNumber(mantisa).mul(factor);
            }
        }
    }
    value = LFloat(value, true);
    if (parse.exact) {
        return value.toRational();
    }
    return value;
}
// ----------------------------------------------------------------------
function parse_string(string) {
    // handle non JSON escapes and skip unicode escape \u (even partial)
    string = string.replace(/\\x([0-9a-f]+);/ig, function(_, hex) {
        return "\\u" + hex.padStart(4, '0');
    }).replace(/\n/g, '\\n'); // in LIPS strings can be multiline
    var m = string.match(/(\\*)(\\x[0-9A-F])/i);
    if (m && m[1].length % 2 === 0) {
        throw new Error(`Invalid string literal, unclosed ${m[2]}`);
    }
    try {
        return LString(JSON.parse(string));
    } catch (e) {
        throw new Error('Invalid string literal');
    }
}
// ----------------------------------------------------------------------
function parse_symbol(arg) {
    if (arg.match(/^\|.*\|$/)) {
        arg = arg.replace(/(^\|)|(\|$)/g, '');
        var chars = {
            t: '\t',
            r: '\r',
            n: '\n'
        };
        arg = arg.replace(/\\(x[^;]+);/g, function(_, chr) {
            return String.fromCharCode(parseInt('0' + chr, 16));
        }).replace(/\\(.)/g, function(_, chr) {
            return chars[chr] || chr;
        });
    }
    return new LSymbol(arg);
}
// ----------------------------------------------------------------------
function parse_argument(arg) {
    if (constants.hasOwnProperty(arg)) {
        return constants[arg];
    }
    if (arg.match(/^"[\s\S]*"$/)) {
        return parse_string(arg);
    } else if (arg[0] === '#') {
        var regex = arg.match(re_re);
        if (regex) {
            return new RegExp(regex[1], regex[2]);
        } else if (arg.match(char_re)) {
            return parse_character(arg);
        }
        // characters with more than one codepoint
        var m = arg.match(/#\\(.+)/);
        if (m && ucs2decode(m[1]).length === 1) {
            return parse_character(arg);
        }
    }
    if (arg.match(/[0-9a-f]|[+-]i/i)) {
        if (arg.match(int_re)) {
            return parse_integer(arg);
        } else if (arg.match(float_re)) {
            return parse_float(arg);
        } else if (arg.match(rational_re)) {
            return parse_rational(arg);
        } else if (arg.match(complex_re)) {
            return parse_complex(arg);
        }
    }
    if (arg.match(/^#[iexobd]/)) {
        throw new Error('Invalid numeric constant: ' + arg);
    }
    return parse_symbol(arg);
}

// ----------------------------------------------------------------------
function is_symbol_string(str) {
    return is_atom_string(str) &&
        !(str.match(re_re) ||
          str.match(/^"[\s\S]*"$/) || str.match(int_re) ||
          str.match(float_re) || str.match(complex_re) ||
          str.match(rational_re) || str.match(char_re) ||
          ['#t', '#f', 'nil', 'true', 'false'].includes(str));
}

// ----------------------------------------------------------------------
function is_atom_string(str) {
    return !(['(', ')', '[', ']'].includes(str) ||
             specials.names().includes(str));
}

// ----------------------------------------------------------------------

const string_re = /"(?:\\[\S\s]|[^"])*"?/g;
// ----------------------------------------------------------------------
function tokens(str) {
    if (str instanceof LString) {
        str = str.valueOf();
    }
    var lexer = new Lexer(str, { whitespace: true });
    var result = [];
    while (true) {
        const token = lexer.peek(true);
        if (token === eof) {
            break;
        }
        result.push(token);
        lexer.skip();
    }
    return result;
}

// ----------------------------------------------------------------------
function tokenize(str, meta = false) {
    if (str instanceof LString) {
        str = str.toString();
    }
    if (meta) {
        return tokens(str);
    } else {
        var result = tokens(str).map(function(token) {
            // we don't want literal space character to be trimmed
            if (token.token === '#\\ ') {
                return token.token;
            }
            return token.token.trim();
        }).filter(function(token) {
            return token && !token.match(/^;/) && !token.match(/^#\|[\s\S]*\|#$/);
        });
        return strip_s_comments(result);
    }
}

// ----------------------------------------------------------------------
function strip_s_comments(tokens) {
    var s_count = 0;
    var s_start = null;
    var remove_list = [];
    for (let i = 0; i < tokens.length; ++i) {
        const token = tokens[i];
        if (token === '#;') {
            if (['(', '['].includes(tokens[i + 1])) {
                s_count = 1;
                s_start = i;
            } else {
                remove_list.push([i, i + 2]);
            }
            i += 1;
            continue;
        }
        if (s_start !== null) {
            if ([')', ']'].includes(token)) {
                s_count--;
            } else if (['(', '['].includes(token)) {
                s_count++;
            }
            if (s_count === 0) {
                remove_list.push([s_start, i + 1]);
                s_start = null;
            }
        }
    }
    tokens = tokens.slice();
    remove_list.reverse();
    for (const [begin, end] of remove_list) {
        tokens.splice(begin, end - begin);
    }
    return tokens;
}

// ----------------------------------------------------------------------
function match_or_null(re, char) {
    return re === null || char.match(re);
}

// ----------------------------------------------------------------------
// :: Parser macros transformers
// ----------------------------------------------------------------------
var specials = {
    LITERAL: Symbol.for('literal'),
    SPLICE: Symbol.for('splice'),
    SYMBOL: Symbol.for('symbol'),
    names: function() {
        return Object.keys(this._specials);
    },
    type: function(name) {
        return this.get(name).type;
    },
    get: function(name) {
        return this._specials[name];
    },
    // events are used in Lexer dynamic rules
    off: function(name, fn = null) {
        if (Array.isArray(name)) {
            name.forEach(name => this.off(name, fn));
        } else if (fn === null) {
            delete this._events[name];
        } else {
            this._events = this._events.filter(test => test !== fn);
        }
    },
    on: function(name, fn) {
        if (Array.isArray(name)) {
            name.forEach(name => this.on(name, fn));
        } else if (!this._events[name]) {
            this._events[name] = [fn];
        } else {
            this._events[name].push(fn);
        }
    },
    trigger: function(name, ...args) {
        if (this._events[name]) {
            this._events[name].forEach(fn => fn(...args));
        }
    },
    remove: function(name) {
        this.trigger('remove');
        delete this._specials[name];
    },
    append: function(name, value, type) {
        this.trigger('append');
        this._specials[name] = {
            seq: name,
            symbol: value,
            type
        };
    },
    _events: {},
    _specials: {}
};

// ----------------------------------------------------------------------
function is_special(token) {
    return specials.names().includes(token);
}

// ----------------------------------------------------------------------
function is_builtin(token) {
    return specials.builtin.includes(token);
}

// ----------------------------------------------------------------------
function is_literal(special) {
    return specials.type(special) === specials.LITERAL;
}

// ----------------------------------------------------------------------
var defined_specials = [
    ["'", new LSymbol('quote'), specials.LITERAL],
    ['`', new LSymbol('quasiquote'), specials.LITERAL],
    [',@', new LSymbol('unquote-splicing'), specials.LITERAL],
    [',', new LSymbol('unquote'), specials.LITERAL],
    ["'>", new LSymbol('quote-promise'), specials.LITERAL]
];

// ----------------------------------------------------------------------
Object.defineProperty(specials, 'builtin', {
    writable: false,
    value: defined_specials.map(arr => arr[0])
});

// ----------------------------------------------------------------------
defined_specials.forEach(([seq, symbol, type]) => {
    specials.append(seq, symbol, type);
});

// ----------------------------------------------------------------------
// :: Finite State Machine based incremental Lexer
// ----------------------------------------------------------------------
/* Lexer debugger
   var DEBUG = false;
   function log(...args) {
   if (DEBUG) {
   console.log(...args);
   }
   }
*/
class Lexer {
    constructor(input, { whitespace = false } = {}) {
        read_only(this, '__input__', input.replace(/\r/g, ''));
        var internals = {};
        // hide internals from introspection
        [
            '_i', '_whitespace', '_col', '_newline', '_line',
            '_state', '_next', '_token', '_prev_char'
        ].forEach(name => {
            Object.defineProperty(this, name, {
                configurable: false,
                enumerable: false,
                get() {
                    return internals[name];
                },
                set(value) {
                    internals[name] = value;
                }
            });
        });
        this._whitespace = whitespace;
        this._i = this._line = this._col = this._newline = 0;
        this._state = this._next = this._token = null;
        this._prev_char = '';
    }
    get(name) {
        return this.__internal[name];
    }
    set(name, value) {
        this.__internal[name] = value;
    }
    token(meta = false) {
        if (meta) {
            let line = this._line;
            if (this._whitespace && this._token === '\n') {
                --line;
            }
            return {
                token: this._token,
                col: this._col,
                offset: this._i,
                line
            };
        }
        return this._token;
    }
    peek(meta = false) {
        if (this._i >= this.__input__.length) {
            return eof;
        }
        if (this._token) {
            return this.token(meta);
        }
        var found = this.next_token();
        if (found) {
            this._token = this.__input__.substring(this._i, this._next);
            return this.token(meta);
        }
        return eof;
    }
    skip() {
        if (this._next !== null) {
            this._token = null;
            this._i = this._next;
        }
    }
    read_line() {
        var len = this.__input__.length;
        if (this._i >= len) {
            return eof;
        }
        for (let i = this._i; i < len; ++i) {
            var char = this.__input__[i];
            if (char === '\n') {
                const line = this.__input__.substring(this._i, i);
                this._i = i + 1;
                ++this._line;
                return line;
            }
        }
        return this.read_rest();
    }
    read_rest() {
        const i = this._i;
        this._i = this.__input__.length;
        return this.__input__.substring(i);
    }
    read_string(num) {
        const len = this.__input__.length;
        if (this._i >= len) {
            return eof;
        }
        if (num + this._i >= len) {
            return this.read_rest();
        }
        const end = this._i + num;
        const result = this.__input__.substring(this._i, end);
        const found = result.match(/\n/g);
        if (found) {
            this._line += found.length;
        }
        this._i = end;
        return result;
    }
    peek_char() {
        if (this._i >= this.__input__.length) {
            return eof;
        }
        return LCharacter(this.__input__[this._i]);
    }
    read_char() {
        const char = this.peek_char();
        this.skip_char();
        return char;
    }
    skip_char() {
        if (this._i < this.__input__.length) {
            ++this._i;
            this._token = null;
        }
    }
    match_rule(rule, { prev_char, char, next_char } = {}) {
        var [ re, prev_re, next_re, state ] = rule;
        if (rule.length !== 5) {
            throw new Error(`Lexer: Invald rule of length ${rule.length}`);
        }
        if (!char.match(re)) {
            return false;
        }
        if (!match_or_null(prev_re, prev_char)) {
            return false;
        }
        if (!match_or_null(next_re, next_char)) {
            return false;
        }
        if (state !== this._state) {
            return false;
        }
        return true;
    }
    next_token() {
        if (this._i >= this.__input__.length) {
            return false;
        }
        var start = true;
        loop:
        for (let i = this._i, len = this.__input__.length; i < len; ++i) {
            var char = this.__input__[i];
            var prev_char = this.__input__[i - 1] || '';
            var next_char = this.__input__[i + 1] || '';
            if (char === '\n') {
                ++this._line;
                const newline = this._newline;
                if (this._state === null) {
                    // keep beging of newline to calculate col
                    // we don't want to check inside the token (e.g. strings)
                    this._newline = i + 1;
                }
                if (this._whitespace && this._state === null) {
                    this._next = i + 1;
                    this._col = this._i - newline;
                    return true;
                }
            }
            // skip leadning spaces
            if (start && this._state === null && char.match(/\s/)) {
                if (this._whitespace) {
                    if (!next_char.match(/\s/)) {
                        this._next = i + 1;
                        this._col = this._i - this._newline;
                        return true;
                    } else {
                        continue;
                    }
                } else {
                    this._i = i + 1;
                    continue;
                }
            }
            start = false;
            for (let rule of Lexer.rules) {
                if (this.match_rule(rule, { prev_char, char, next_char })) {
                    // change state to null is end of the token
                    var next_state = rule[rule.length - 1];
                    this._state = next_state;
                    if (this._state === null) {
                        this._next = i + 1;
                        this._col = this._i - this._newline;
                        return true;
                    }
                    // token is activated
                    continue loop;
                }
            }
            if (this._state !== null) {
                // collect char in token
                continue loop;
            }
            // no rule for token
            var line = this.__input__.split('\n')[this._line];
            throw new Error(`Invalid Syntax at line ${this._line}\n${line}`);
        }
    }
}

// ----------------------------------------------------------------------
Lexer.symbol_rule = function symbol_rule(string, symbol) {
    var rules = Lexer.literal_rule(string, symbol, Lexer.boundary, /\S/);

    return rules.concat([
        [/\S/, /\S/, Lexer.boundary, null, null],
        [/\S/, /\S/, null, null, Lexer.symbol],
        [/\S/, null, Lexer.boundary, Lexer.symbol, null]
    ]);
};
// ----------------------------------------------------------------------
// state rule for literal symbol
// ----------------------------------------------------------------------
Lexer.literal_rule = function literal_rule(string, symbol, p_re = null, n_re = null) {
    if (string.length === 0) {
        throw new Error('Lexer: invalid literal rule');
    }
    if (string.length === 1) {
        return [[string, p_re, n_re, null, null]];
    }
    var rules = [];
    for (let i = 0, len = string.length; i < len; ++i) {
        const rule = [];
        rule.push(string[i]);
        rule.push(string[i - 1] || p_re);
        rule.push(string[i + 1] || n_re);
        if (i === 0) {
            rule.push(null);
            rule.push(symbol);
        } else if (i === len - 1) {
            rule.push(symbol);
            rule.push(null);
        } else {
            rule.push(symbol);
            rule.push(symbol);
        }
        rules.push(rule);
    }
    return rules;
};
// ----------------------------------------------------------------------
Lexer.string = Symbol.for('string');
Lexer.symbol = Symbol.for('symbol');
Lexer.comment = Symbol.for('comment');
Lexer.regex = Symbol.for('regex');
Lexer.regex_class = Symbol.for('regex_class');
Lexer.character = Symbol.for('character');
Lexer.bracket = Symbol.for('bracket');
Lexer.b_symbol = Symbol.for('b_symbol');
Lexer.b_comment = Symbol.for('b_comment');
Lexer.i_comment = Symbol.for('i_comment');
Lexer.l_datum = Symbol.for('l_datum');
Lexer.dot = Symbol.for('dot');
// ----------------------------------------------------------------------
Lexer.boundary = /^$|[\s()[\]']/;
// ----------------------------------------------------------------------
Lexer._rules = [
    // char_re prev_re next_re from_state to_state
    // null as to_state mean that is single char token
    // string
    [/"/, /^$|[^\\]/, null, null, Lexer.string],
    [/"/, /^$|[^\\]/, null, Lexer.string, null],

    // hash special symbols, lexer don't need to distingiush those
    // we only care if it's not pick up by vectors literals
    [/#/, null, /[bdxoeitf]/i, null, Lexer.symbol],

    // characters
    [/#/, null, /\\/, null, Lexer.character],
    [/\\/, /#/, /\s/, Lexer.character, Lexer.character],
    [/\\/, /#/, /[()[\]]/, Lexer.character, Lexer.character],
    [/\s/, /\\/, null, Lexer.character, null],
    [/\S/, null, Lexer.boundary, Lexer.character, null],

    // regex
    [/#/, Lexer.boundary, /\//, null, Lexer.regex],
    [/[ \t]/, null, null, Lexer.regex, Lexer.regex],
    [/\[/, null, null, Lexer.regex, Lexer.regex_class],
    [/\]/, /[^\\]/, null, Lexer.regex_class, Lexer.regex],
    [/[()[\]]/, null, null, Lexer.regex, Lexer.regex],
    [/\//, /\\/, null, Lexer.regex, Lexer.regex],
    [/\//, /[^#]/, Lexer.boundary, Lexer.regex, null],
    [/[gimyus]/, /\//, Lexer.boundary, Lexer.regex, null],
    [/[gimyus]/, /\//, /[gimyus]/, Lexer.regex, Lexer.regex],
    [/[gimyus]/, /[gimyus]/, Lexer.boundary, Lexer.regex, null],

    // comment
    [/;/, /^$|[^#]/, null, null, Lexer.comment],
    [/[\s\S]/, null, /\n/, Lexer.comment, null],
    [/\s/, null, null, Lexer.comment, Lexer.comment],

    // block comment
    [/#/, null, /\|/, null, Lexer.b_comment],
    [/\s/, null, null, Lexer.b_comment, Lexer.b_comment],
    [/#/, /\|/, null, Lexer.b_comment, null],

    // inline commentss
    [/#/, null, /;/, null, Lexer.i_comment],
    [/;/, /#/, null, Lexer.i_comment, null],

    // datum label
    [/#/, null, /[0-9]/, null, Lexer.l_datum],
    [/=/, /[0-9]/, null, Lexer.l_datum, null],
    [/#/, /[0-9]/, null, Lexer.l_datum, null],

    // for dot comma `(a .,b)
    [/\./, Lexer.boundary, /,/, null, null],

    // block symbols
    [/\|/, null, null, null, Lexer.b_symbol],
    [/\s/, null, null, Lexer.b_symbol, Lexer.b_symbol],
    [/\|/, null, Lexer.boundary, Lexer.b_symbol, null]
];
// ----------------------------------------------------------------------
Lexer._brackets = [
    [/[()[\]]/, null, null, null, null]
];
// ----------------------------------------------------------------------
// :: symbols should be matched last
// ----------------------------------------------------------------------
Lexer._symbol_rules = [
    [/\S/, Lexer.boundary, Lexer.boundary, null, null],
    [/\S/, Lexer.boundary, null, null, Lexer.symbol],
    [/\S/, null, Lexer.boundary, null, null],
    [/\S/, null, null, null, Lexer.symbol],
    [/\S/, null, Lexer.boundary, Lexer.symbol, null]
];
// ----------------------------------------------------------------------
// :: dynamic getter or Lexer state rules, parser use this
// :: so in fact user code can modify lexer using syntax extensions
// ----------------------------------------------------------------------
Lexer._cache = {
    valid: false,
    rules: null
};

// ----------------------------------------------------------------------
specials.on(['remove', 'append'], function() {
    Lexer._cache.valid = false;
    Lexer._cache.rules = null;
});

// ----------------------------------------------------------------------
Object.defineProperty(Lexer, 'rules', {
    get() {
        if (Lexer._cache.valid) {
            return Lexer._cache.rules;
        }
        var tokens = specials.names().sort((a, b) => {
            return b.length - a.length || a.localeCompare(b);
        });

        var special_rules = tokens.reduce((acc, token) => {
            const { type, symbol: special_symbol } = specials.get(token);
            let rules;
            let symbol;
            // we need distinct symbols_ for syntax extensions
            if (token[0] === '#') {
                if (token.length === 1) {
                    symbol = Symbol.for(token);
                } else {
                    symbol = Symbol.for(token[1]);
                }
            } else {
                symbol = special_symbol;
            }
            if (type === specials.SYMBOL) {
                rules = Lexer.symbol_rule(token, symbol);
            } else {
                rules = Lexer.literal_rule(token, symbol);
            }
            return acc.concat(rules);
        }, []);

        Lexer._cache.rules = Lexer._rules.concat(
            Lexer._brackets,
            special_rules,
            Lexer._symbol_rules
        );

        Lexer._cache.valid = true;
        return Lexer._cache.rules;
    }
});

// ----------------------------------------------------------------------
// :: Parser inspired by BiwaScheme
// :: ref: https://github.com/biwascheme/biwascheme/blob/master/src/system/parser.js
// ----------------------------------------------------------------------
class Parser {
    constructor(arg, { env, meta = false, formatter = multiline_formatter } = {}) {
        if (arg instanceof LString) {
            arg = arg.toString();
        }

        read_only(this, '_formatter', formatter, { hidden: true });
        read_only(this, '__lexer__', new Lexer(arg));
        read_only(this, '__env__', env);

        read_only(this, '_meta', meta, { hidden: true });
        // datum labels
        read_only(this, '_refs', [], { hidden: true });
    }
    resolve(name) {
        return this.__env__ && this.__env__.get(name, { throwError: false });
    }
    async peek() {
        let token;
        while (true) {
            token = this.__lexer__.peek(true);
            if (token === eof) {
                return eof;
            }
            if (this.is_comment(token.token)) {
                this.skip();
                continue;
            }
            if (token.token === '#;') {
                this.skip();
                if (this.__lexer__.peek() === eof) {
                    throw new Error('Lexer: syntax error eof found after comment');
                }
                await this._read_object();
                continue;
            }
            break;
        }
        token = this._formatter(token);
        if (this._meta) {
            return token;
        }
        return token.token;
    }
    reset() {
        this._refs.length = 0;
    }
    skip() {
        this.__lexer__.skip();
    }
    async read() {
        const token = await this.peek();
        this.skip();
        return token;
    }
    match_datum_label(token) {
        var m = token.match(/^#([0-9]+)=$/);
        return m && m[1];
    }
    match_datum_ref(token) {
        var m = token.match(/^#([0-9]+)#$/);
        return m && m[1];
    }
    is_open(token) {
        return ['(', '['].includes(token);
    }
    is_close(token) {
        return [')', ']'].includes(token);
    }
    async read_list() {
        let head = nil, prev = head;
        while (true) {
            const token = await this.peek();
            if (token === eof) {
                break;
            }
            if (this.is_close(token)) {
                this.skip();
                break;
            }
            if (token === '.' && head !== nil) {
                this.skip();
                prev.cdr = await this._read_object();
            } else {
                const cur = new Pair(await this._read_object(), nil);
                if (head === nil) {
                    head = cur;
                } else {
                    prev.cdr = cur;
                }
                prev = cur;
            }
        }
        return head;
    }
    async read_value() {
        var token = await this.read();
        if (token === eof) {
            throw new Error('Parser: Expected token eof found');
        }
        return parse_argument(token);
    }
    is_comment(token) {
        return token.match(/^;/) || (token.match(/^#\|/) && token.match(/\|#$/));
    }
    evaluate(code) {
        return evaluate(code, { env: this.__env__, error: (e) => {
            throw e;
        } });
    }
    // public API that handle R7RS datum labels
    async read_object() {
        this.reset();
        var object = await this._read_object();
        if (object instanceof DatumReference) {
            object = object.valueOf();
        }
        if (this._refs.length) {
            return this._resolve_object(object);
        }
        return object;
    }
    async _resolve_object(object) {
        if (Array.isArray(object)) {
            return object.map(item => this._resolve_object(item));
        }
        if (is_plain_object(object)) {
            var result = {};
            Object.keys(object).forEach(key => {
                result[key] = this._resolve_object(object[key]);
            });
            return result;
        }
        if (object instanceof Pair) {
            return this._resolve_pair(object);
        }
        return object;
    }
    async _resolve_pair(pair) {
        if (pair instanceof Pair) {
            if (pair.car instanceof DatumReference) {
                pair.car = await pair.car.valueOf();
            } else {
                this._resolve_pair(pair.car);
            }
            if (pair.cdr instanceof DatumReference) {
                pair.cdr = await pair.cdr.valueOf();
            } else {
                this._resolve_pair(pair.cdr);
            }
        }
        return pair;
    }
    async _read_object() {
        const token = await this.peek();
        if (token === eof) {
            return token;
        }
        if (is_special(token)) {
            // bultin parser extensions are mapping short symbol to longer symbol
            // that can be function or macro, parser don't care
            // if it's not bultin then the extension can be macro or function
            // FUNCTION: when it's used it get arguments like FEXPR and
            // result is returned by parser as is
            // MACRO: if macros are used they are evaluated in place and
            // result is returned by parser but they are quoted
            const special = specials.get(token);
            const bultin = is_builtin(token);
            this.skip();
            let expr;
            const object = await this._read_object();
            if (!bultin) {
                var extension = this.__env__.get(special.symbol);
                if (typeof extension === 'function') {
                    if (is_literal(token)) {
                        return extension.call(this.__env__, object);
                    } else if (object instanceof Pair) {
                        return extension.apply(this.__env__, object.to_array(false));
                    }
                    throw new Error('Parse Error: Invalid parser extension ' +
                                    `invocation ${special.symbol}`);
                }
            }
            if (is_literal(token)) {
                expr = new Pair(
                    special.symbol,
                    new Pair(
                        object,
                        nil
                    )
                );
            } else {
                expr = new Pair(
                    special.symbol,
                    object
                );
            }
            // builtin parser extensions just expand into lists like 'x ==> (quote x)
            if (bultin) {
                return expr;
            }
            // evaluate parser extension at parse time
            if (extension instanceof Macro) {
                var result = await this.evaluate(expr);
                // we need literal quote to make macro that return pair works
                // because after parser return the value it will be evaluated again
                // by the interpreter, so we create quoted expression
                if (result instanceof Pair || result instanceof LSymbol) {
                    return Pair.fromArray([LSymbol('quote'), result]);
                }
                return result;
            } else {
                throw new Error('Parse Error: invlid parser extension: ' +
                                special.symbol);
            }
        }
        var ref = this.match_datum_ref(token);
        if (ref !== null) {
            this.skip();
            if (this._refs[ref]) {
                return new DatumReference(ref, this._refs[ref]);
            }
            throw new Error(`Parse Error: invalid datum label #${ref}#`);
        }
        var ref_label = this.match_datum_label(token);
        if (ref_label !== null) {
            this.skip();
            this._refs[ref_label] = this._read_object();
            return this._refs[ref_label];
        } else if (this.is_open(token)) {
            this.skip();
            return this.read_list();
        } else {
            return this.read_value();
        }
    }
}

// ----------------------------------------------------------------------
// :: parser helper that allow to handle circular list structures
// :: using datum labels
// ----------------------------------------------------------------------
class DatumReference {
    constructor(name, data) {
        this.name = name;
        this.data = data;
    }
    valueOf() {
        return this.data;
    }
}
// ----------------------------------------------------------------------
// :: tokens are the array of strings from tokenizer
// :: the return value is array of lisp code created out of Pair class
// :: env is needed for parser extensions that will invoke the function
// :: or macro assigned to symbol, this function is async because
// :: it evaluate the code, from parser extensions, that may return promise
// ----------------------------------------------------------------------
async function* parse(arg, env) {
    if (!env) {
        if (global_env) {
            env = global_env.get('**interaction-environment**', {
                throwError: false
            });
        } else {
            env = user_env;
        }
    }
    const parser = new Parser(arg, { env });
    while (true) {
        const expr = await parser.read_object();
        if (expr === eof) {
            break;
        }
        yield expr;
    }
}

// -------------------------------------------------------------------------
function balanced(code) {
    var maching_pairs = {
        '[': ']',
        '(': ')'
    };
    var tokens;
    if (typeof code === 'string') {
        tokens = tokenize(code);
    } else {
        tokens = code.map(x => x && x.token ? x.token : x);
    }

    var open_tokens = Object.keys(maching_pairs);
    var brackets = Object.values(maching_pairs).concat(open_tokens);
    tokens = tokens.filter(token => brackets.includes(token));

    const stack = new Stack();
    for (const token of tokens) {
        if (open_tokens.includes(token)) {
            stack.push(token);
        } else if (!stack.is_empty()) { // closing token
            var last = stack.top();
            // last on stack need to match
            const closing_token = maching_pairs[last];
            if (token === closing_token) {
                stack.pop();
            } else {
                throw new Error(`Syntax error: missing closing ${closing_token}`);
            }
        } else {
            // closing bracket without opening
            throw new Error(`Syntax error: not matched closing ${token}`);
        }
    }
    return stack.is_empty();
}

// ----------------------------------------------------------------------
function multiline_formatter(meta) {
    var { token, ...rest } = meta;
    if (token.match(/^"[\s\S]*"$/) && token.match(/\n/)) {
        var re = new RegExp('^ {1,' + (meta.col + 1) + '}', 'mg');
        token = token.replace(re, '');
    }
    return {
        token,
        ...rest
    };
}

export {
    tokenize,
    parse,
    Lexer,
    Parser,
    is_symbol_string,
    is_atom_string,
    complex_bare_re,
    balanced,
    specials,
    characters,
    is_special,
    string_re,
    re_re
};
