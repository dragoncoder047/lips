/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
import { string_re, re_re, is_atom_string, is_symbol_string } from './Parser.js';

// ----------------------------------------------------------------------
// :: token based pattern matching (used by formatter)
// ----------------------------------------------------------------------
function match(pattern, input) {
    return inner_match(pattern, input) === input.length;
    function inner_match(pattern, input) {
        function get_first_match(patterns, input) {
            for (let p of patterns) {
                const m = inner_match(p, input);
                if (m !== -1) {
                    return m;
                }
            }
            return -1;
        }
        function not_symbol_match() {
            return pattern[p] === Symbol.for('symbol') && !is_symbol_string(input[i]);
        }
        function match_next() {
            var next_pattern = pattern[p + 1];
            var next_input = input[i + 1];
            if (next_pattern !== undefined && next_input !== undefined) {
                return inner_match([next_pattern], [next_input]);
            }
        }
        var p = 0;
        var glob = {};
        for (var i = 0; i < input.length; ++i) {
            if (typeof pattern[p] === 'undefined') {
                return i;
            }
            if (pattern[p] instanceof Pattern) {
                var m;
                if (['+', '*'].includes(pattern[p].flag)) {
                    while (i < input.length) {
                        m = get_first_match(pattern[p].patterns, input.slice(i));
                        if (m === -1) {
                            break;
                        }
                        i += m;
                    }
                    i -= 1;
                    p++;
                    continue;
                } else if (pattern[p].flag === '?') {
                    m = get_first_match(pattern[p].patterns, input.slice(i));
                    if (m === -1) {
                        i -= 2; // if not found use same test on same input again
                    } else {
                        p++;
                    }
                    continue;
                }
            } else if (pattern[p] instanceof RegExp) {
                if (!input[i].match(pattern[p])) {
                    return -1;
                }
            } else if (lips.LString.isString(pattern[p])) {
                if (pattern[p].valueOf() !== input[i]) {
                    return -1;
                }
            } else if (typeof pattern[p] === 'symbol') {
                if (pattern[p] === Symbol.for('*')) {
                    // ignore S-expressions inside for case when next pattern is )
                    glob[p] = glob[p] || 0;
                    //var zero_match = empty_match();
                    if (['(', '['].includes(input[i])) {
                        glob[p]++;
                    } else if ([')', ']'].includes(input[i])) {
                        glob[p]--;
                    }
                    if ((typeof pattern[p + 1] !== 'undefined' &&
                         glob[p] === 0 && match_next() === -1) ||
                        glob[p] > 0) {
                        continue;
                    }
                } else if (not_symbol_match()) {
                    return -1;
                }
            } else if (pattern[p] instanceof Array) {
                var inc = inner_match(pattern[p], input.slice(i));
                if (inc === -1 || inc + i > input.length) {
                    // if no more input it's not match
                    return -1;
                }
                i += inc - 1;
                p++;
                continue;
            } else {
                return -1;
            }
            p++;
        }
        if (pattern.length !== p) {
            // if there are still patterns it's not match
            return -1;
        }
        return input.length;
    }
}
// ----------------------------------------------------------------------
// :: Code formatter class
// :: based on http://community.schemewiki.org/?scheme-style
// :: and GNU Emacs scheme mode
// :: it rely on meta data from tokenizer function
// ----------------------------------------------------------------------
function Formatter(code) {
    this.__code__ = code.replace(/\r/g, '');
}
// ----------------------------------------------------------------------
/* eslint-disable max-len */
Formatter.defaults = {
    offset: 0,
    indent: 2,
    exceptions: {
        specials: [
            /* eslint-disable max-len */
            /^(?:#:)?(?:define(?:-values|-syntax|-macro|-class|-record-type)?|(?:call-with-(?:input-file|output-file|port))|lambda|let-env|try|catch|when|unless|while|syntax-rules|(let|letrec)(-syntax|\*)?)$/
            /* eslint-enable */
        ],
        shift: {
            1: ['&', '#']
        }
    }
};
/* eslint-enable */
Formatter.match = match;

// ----------------------------------------------------------------------
// :: return indent for next line
// ----------------------------------------------------------------------
Formatter.prototype._options = function _options(options) {
    var defaults = Formatter.defaults;
    if (typeof options === 'undefined') {
        return Object.assign({}, defaults);
    }
    var exeptions = options && options.exceptions || {};
    var specials = exeptions.specials || [];
    var shift = exeptions.shift || { 1: [] };
    return {
        ...defaults,
        ...options,
        exceptions: {
            specials: [...defaults.exceptions.specials, ...specials],
            shift: {
                ...shift,
                1: [...defaults.exceptions.shift[1], ...shift[1]]
            }
        }
    };
};

// ----------------------------------------------------------------------
Formatter.prototype.indent = function indent(options) {
    var tokens = tokenize(this.__code__, true);
    return this._indent(tokens, options);
};

// ----------------------------------------------------------------------
Formatter.exception_shift = function(token, settings) {
    function match(list) {
        if (!list.length) {
            return false;
        }
        if (list.indexOf(token) !== -1) {
            return true;
        } else {
            var regexes = list.filter(s => s instanceof RegExp);
            if (!regexes.length) {
                return false;
            }
            for (let re of regexes) {
                if (token.match(re)) {
                    return true;
                }
            }
        }
        return false;
    }
    if (match(settings.exceptions.specials)) {
        return settings.indent;
    }
    var shift = settings.exceptions.shift;
    for (var [indent, tokens] of Object.entries(shift)) {
        if (match(tokens)) {
            return +indent;
        }
    }
    return -1;
};

// ----------------------------------------------------------------------
Formatter.prototype._indent = function _indent(tokens, options) {
    var settings = this._options(options);
    var spaces = lineIndent(tokens);
    var sexp = previousSexp(tokens);
    // one character before S-Expression
    var before_sexpr = tokens[tokens.length - sexp.length - 1];
    var last = tokens[tokens.length - 1];
    if (last.token.match(/^"[\S\s]+[^"]$/)) {
        return spaces + settings.indent;
    }
    if (sexp && sexp.length) {
        if (sexp[0].line > 0) {
            settings.offset = 0;
        }
        if (sexp.toString() === tokens.toString() && balanced(sexp)) {
            return settings.offset + sexp[0].col;
        } else if (sexp.length === 1) {
            return settings.offset + sexp[0].col + 1;
        } else {
            // search for token before S-Expression for case like #(10 or &(:x
            var exeption = -1;
            if (before_sexpr) {
                var shift = Formatter.exception_shift(before_sexpr.token, settings);
                if (shift !== -1) {
                    exeption = shift;
                }
            }
            if (exeption === -1) {
                exeption = Formatter.exception_shift(sexp[1].token, settings);
            }
            if (exeption !== -1) {
                return settings.offset + sexp[0].col + exeption;
            } else if (sexp[0].line < sexp[1].line) {
                return settings.offset + sexp[0].col + 1;
            } else if (sexp.length > 3 && sexp[1].line === sexp[3].line) {
                if (sexp[1].token === '(' || sexp[1].token === '[') {
                    return settings.offset + sexp[1].col;
                }
                return settings.offset + sexp[3].col;
            } else if (sexp[0].line === sexp[1].line) {
                return settings.offset + settings.indent + sexp[0].col;
            } else {
                var next_tokens = sexp.slice(2);
                for (var i = 0; i < next_tokens.length; ++i) {
                    var token = next_tokens[i];
                    if (token.token.trim()) {
                        return token.col;
                    }
                }
            }
        }
    } else {
        return 0;
    }
    return spaces + settings.indent;
};

// ----------------------------------------------------------------------
function Ahead(pattern) {
    this.pattern = pattern;
}

// ----------------------------------------------------------------------
// TODO: make it print
Ahead.prototype.toString = function() {
    return `#<pattern(${this.pattern})>`;
};

// ----------------------------------------------------------------------
Ahead.prototype.match = function(string) {
    return string.match(this.pattern);
};

// ----------------------------------------------------------------------
// Pattern have any number of patterns that is match using OR operator
// pattern is in form of array with regular expressions
// ----------------------------------------------------------------------
function Pattern(...args) {
    var flag = args.pop();
    this.patterns = args;
    this.flag = flag;
}

// ----------------------------------------------------------------------
Pattern.prototype.toString = function() {
    var patterns = this.patterns.map(x => toString(x)).join('|');
    return `#<pattern(${patterns} ${this.flag})>`;
};

// ----------------------------------------------------------------------
Formatter.Pattern = Pattern;
Formatter.Ahead = Ahead;
var p_o = /^[[(]$/;
var p_e = /^[\])]$/;
var not_p = /[^()[\]]/;
const not_close = new Ahead(/[^)\]]/);
//const open = new Ahead(/[([]/);
const glob = Symbol.for('*');
const sexp_or_atom = new Pattern([p_o, glob, p_e], [not_p], '+');
const sexp = new Pattern([p_o, glob, p_e], '+');
const symbol = new Pattern([Symbol.for('symbol')], '?');
const symbols = new Pattern([Symbol.for('symbol')], '*');
const identifiers = [p_o, symbols, p_e];
const let_value = new Pattern([p_o, Symbol.for('symbol'), glob, p_e], '+');
// rules for breaking S-Expressions into lines
var def_lambda_re = keywords_re('define', 'lambda', 'define-macro', 'syntax-rules');
/* eslint-disable max-len */
var non_def = /^(?!.*\b(?:[()[\]]|define(?:-macro)?|let(?:\*|rec|-env|-syntax|)?|lambda|syntax-rules)\b).*$/;
/* eslint-enable */
var let_re = /^(?:#:)?(let(?:\*|rec|-env|-syntax)?)$/;
// match keyword if it's normal token or gensym (prefixed with #:)
function keywords_re(...args) {
    return new RegExp(`^(?:#:)?(?:${args.join('|')})$`);
}
// line breaking rules
Formatter.rules = [
    [[sexp], 0, not_close],
    [[p_o, keywords_re('begin', 'cond-expand')], 1],
    [[p_o, let_re, symbol, p_o, let_value, p_e], 1],
    [[p_o, let_re, symbol, sexp_or_atom], 1, not_close],
    [[p_o, let_re, p_o, let_value], 1, not_close],
    //--[[p_o, keywords_re('define-syntax'), /.+/], 1],
    [[p_o, non_def, new Pattern([/[^()[\]]/], '+'), sexp], 1, not_close],
    [[p_o, sexp], 1, not_close],
    [[p_o, not_p, sexp], 1, not_close],
    [[p_o, keywords_re('lambda', 'if'), not_p], 1, not_close],
    [[p_o, keywords_re('while'), not_p, sexp], 1, not_close],
    [[p_o, keywords_re('if'), not_p, glob], 1],
    [[p_o, def_lambda_re, identifiers], 0, not_close],
    [[p_o, def_lambda_re, identifiers, string_re], 0, not_close],
    [[p_o, def_lambda_re, identifiers, string_re, sexp], 0, not_close],
    [[p_o, def_lambda_re, identifiers, sexp], 0, not_close]
];

// ----------------------------------------------------------------------
Formatter.prototype.break = function() {
    var code = this.__code__.replace(/\n[ \t]*/g, '\n ').replace(/^\s+/, '');
    // function that work when calling tokenize with meta data or not
    const token = t => {
        if (t.token.match(string_re) || t.token.match(re_re)) {
            return t.token;
        } else {
            return t.token.replace(/\s+/, ' ');
        }
    };
    const first_token_index = tokens => {
        for (let i = tokens.length; i--;) {
            const token = tokens[i];
            if (token.trim() && !is_special(token)) {
                return tokens.length - i - 1;
            }
        }
    };
    // tokenize is part of the parser/lexer that split code into tokens and inclue
    // meta data like number of column or line
    var tokens = tokenize(code, true).map(token).filter(t => t !== '\n');
    const { rules } = Formatter;
    outer: for (let i = 1; i < tokens.length; ++i) {
        if (!tokens[i].trim()) {
            continue;
        }
        var sub = tokens.slice(0, i);
        var sexp = {};
        rules.map(b => b[1]).forEach(count => {
            count = count.valueOf();
            // some patterns require to check what was before like
            // if inside let binding
            if (count > 0 && !sexp[count]) {
                sexp[count] = previousSexp(sub, count);
            }
        });
        for (let [pattern, count, ext] of rules) {
            count = count.valueOf();
            // 0 count mean ignore the previous S-Expression
            var test_sexp = count > 0 ? sexp[count] : sub;
            const input = test_sexp.filter(t => t.trim() && !is_special(t));
            const inc = first_token_index(test_sexp);
            var m = match(pattern, input);
            var next = tokens.slice(i).find(t => t.trim() && !is_special(t));
            if (m && (ext instanceof Ahead && ext.match(next) || !ext)) {
                const index = i - inc;
                if (tokens[index] !== '\n') {
                    if (!tokens[index].trim()) {
                        tokens[index] = '\n';
                    } else {
                        tokens.splice(index, 0, '\n');
                        i++;
                    }
                }
                i += inc;
                continue outer;
            }
        }
    }
    this.__code__ = tokens.join('');
    return this;
};

// ----------------------------------------------------------------------
Formatter.prototype._spaces = function(i) {
    return new Array(i + 1).join(' ');
};

// ----------------------------------------------------------------------
// :: auto formatting of code, it require to have newlines
// ----------------------------------------------------------------------
Formatter.prototype.format = function format(options) {
    // prepare code with single space after newline
    // so we have space token to align
    var code = this.__code__.replace(/[ \t]*\n[ \t]*/g, '\n ');
    var tokens = tokenize(code, true);
    var settings = this._options(options);
    var indent = 0;
    var offset = 0;
    for (var i = 0; i < tokens.length; ++i) {
        var token = tokens[i];
        if (token.token === '\n') {
            indent = this._indent(tokens.slice(0, i), settings);
            offset += indent;
            if (tokens[i + 1]) {
                tokens[i + 1].token = this._spaces(indent);
                // because we have single space as initial indent
                indent--;
                offset--;
                for (var j = i + 2; j < tokens.length; ++j) {
                    tokens[j].offset += offset;
                    tokens[j].col += indent;
                    if (tokens[j].token === '\n') {
                        // ++i is called after the loop
                        i = j - 1;
                        break;
                    }
                }
            }
        }
    }
    return tokens.map(token => {
        if (token.token.match(string_re)) {
            if (token.token.match(/\n/)) {
                var spaces = new Array(token.col + 1).join(' ');
                var lines = token.token.split('\n');
                token.token = [lines[0]].concat(lines.slice(1).map(line => {
                    return spaces + line;
                })).join('\n');
            }
        }
        return token.token;
    }).join('');
};

export { Formatter, Ahead, Pattern };
