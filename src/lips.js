/*
 * TODO: consider using exec in env.eval or use different maybe_async code
 */
/* global jQuery, BigInt, Map, Set, Symbol, importScripts, Uint8Array */
"use strict";



import { addExtension, Encoder } from 'cbor-x';
import { pack, unpack } from 'lzjb-pack';
import unfetch from 'unfetch';

import root from './root.js';

import { Nil, nil, Pair, markCycles } from './Pair.js';
import {
    to_array,
    escape_regex,
    read_only,
    uniterate_async,
    noop,
    box,
    unbind,
    bind,
    hidden_prop,
    set_fn_length,
    get_props,
    equal,
    same_atom,
    doc,
    trim_lines
} from './utils.js';
import {
    typecheck_args,
    typeErrorMessage,
    typecheck,
    type,
    __fn__,
    typecheck_text_port,
    is_null,
    is_continuation,
    is_callable,
    is_function,
    is_undef,
    is_plain_object,
    is_atom,
    is_port,
    is_port_method,
    is_lambda,
    is_method,
    is_raw_lambda,
    is_native_function,
    is_native,
    is_iterator,
    is_object_bound,
    is_bound,
    has_own_symbol,
    has_own_function
} from './typechecking.js';
import { gensym, symbol_to_string, LSymbol } from './LSymbol.js';
import { LNumber, LComplex, LRational, LFloat, LBigInteger, nan } from './Numbers.js';
import { Formatter, Ahead, Pattern } from './Formatter.js';
import { Macro, macro_expand, Syntax, syntax_rules, define_macro } from './Macro.js';
import LString from './LString.js';
import LCharacter from './LCharacter.js';
import Values from './Values.js';
import Continuation from './Continuation.js';
import Value from './Value.js';
import {
    eof,
    __binary_port__,
    InputPort,
    OutputPort,
    BufferedOutputPort,
    OutputStringPort,
    InputStringPort,
    InputByteVectorPort,
    OutputByteVectorPort,
    InputFilePort,
    OutputFilePort,
    InputBinaryFilePort,
    OutputBinaryFilePort
} from './Ports.js';
import {
    QuotedPromise,
    Unquote,
    unpromise,
    quote,
    is_promise,
    escape_quoted_promises,
    unescape_quoted_promises,
    promise_all,
    __data__,
    resolve_promises
} from './Promises.js';

import { global_env, user_env, Interpreter } from './CoreLibrary.js';

import { tokenize, parse, Lexer, Parser, balanced, specials } from './Parser.js';

if (!root.fetch) {
    root.fetch = unfetch;
}

let fs, path, nodeRequire;

const BN = root.BN;

/* eslint-disable */
/* istanbul ignore next */
function contentLoaded(win, fn) {
    var done = false, top = true,

        doc = win.document,
        root = doc.documentElement,
        modern = doc.addEventListener,

        add = modern ? 'addEventListener' : 'attachEvent',
        rem = modern ? 'removeEventListener' : 'detachEvent',
        pre = modern ? '' : 'on',

        init = function(e) {
            if (e.type == 'readystatechange' && doc.readyState != 'complete') return;
            (e.type == 'load' ? win : doc)[rem](pre + e.type, init, false);
            if (!done && (done = true)) fn.call(win, e.type || e);
        },

        poll = function() {
            try { root.doScroll('left'); } catch(e) { setTimeout(poll, 50); return; }
            init('poll');
        };

    if (doc.readyState == 'complete') fn.call(win, 'lazy');
    else {
        if (!modern && root.doScroll) {
            try { top = !win.frameElement; } catch(e) { }
            if (top) poll();
        }
        doc[add](pre + 'DOMContentLoaded', init, false);
        doc[add](pre + 'readystatechange', init, false);
        win[add](pre + 'load', init, false);
    }
}
// -------------------------------------------------------------------------
/* eslint-disable */
/* istanbul ignore next */
function log(x, regex = null) {
    var literal = arguments[1] === true;
    function msg(x) {
        if (!is_debug()) {
            return;
        }
        var value = global_env.get('repr')(x);
        if (regex === null || regex instanceof RegExp && regex.test(value)) {
            console.log(global_env.get('type')(x) + ": " + value);
        }
        if (literal) {
            console.log(x);
        }
    }
    if (is_promise(x)) {
        x.then(msg);
    } else {
        msg(x);
    }
    return x;
}
/* eslint-enable */

// ----------------------------------------------------------------------
/* istanbul ignore next */
function is_debug() {
    return user_env && user_env.get('DEBUG', { throwError: false });
}

// -------------------------------------------------------------------------
function self_evaluated(obj) {
    var type = typeof obj;
    return ['string', 'function'].includes(type) ||
        typeof obj === 'symbol' ||
        obj instanceof QuotedPromise ||
        obj instanceof LSymbol ||
        obj instanceof LNumber ||
        obj instanceof LString ||
        obj instanceof RegExp;
}

// ----------------------------------------------------------------------
function Thunk(fn, cont = () => {}) {
    this.fn = fn;
    this.cont = cont;
}
// ----------------------------------------------------------------------
Thunk.prototype.toString = function() {
    return '#<Thunk>';
};
// ----------------------------------------------------------------------
function trampoline(fn) {
    return function(...args) {
        return unwind(fn.apply(this, args));
    };
}
// ----------------------------------------------------------------------
function unwind(result) {
    while (result instanceof Thunk) {
        const thunk = result;
        result = result.fn();
        if (!(result instanceof Thunk)) {
            thunk.cont();
        }
    }
    return result;
}

// ----------------------------------------------------------------------
// :: function that return mather function that match string against string
// ----------------------------------------------------------------------
function matcher(name, arg) {
    if (arg instanceof RegExp) {
        return x => String(x).match(arg);
    } else if (is_function(arg)) {
        // it will always be function
        return arg;
    }
    throw new Error('Invalid matcher');
}
// ----------------------------------------------------------------------
// return last S-Expression
// @param tokens - array of tokens (objects from tokenizer or strings)
// @param sexp - number of expression to look behind
// ----------------------------------------------------------------------
function previousSexp(tokens, sexp = 1) {
    var i = tokens.length;
    if (sexp <= 0) {
        throw Error(`previousSexp: Invalid argument sexp = ${sexp}`);
    }
    outer: while (sexp-- && i >= 0) {
        var count = 1;
        while (count > 0) {
            var token = tokens[--i];
            if (!token) {
                break outer;
            }
            if (token === '(' || token.token === '(') {
                count--;
            } else if (token === ')' || token.token === ')') {
                count++;
            }
        }
        i--;
    }
    return tokens.slice(i + 1);
}
// ----------------------------------------------------------------------
// :: find number of spaces in line
// ----------------------------------------------------------------------
function lineIndent(tokens) {
    if (!tokens || !tokens.length) {
        return 0;
    }
    var i = tokens.length;
    if (tokens[i - 1].token === '\n') {
        return 0;
    }
    while (--i) {
        if (tokens[i].token === '\n') {
            var token = (tokens[i + 1] || {}).token;
            if (token) {
                return token.length;
            }
        }
    }
    return 0;
}

// ----------------------------------------------------------------------
// :: flatten nested arrays
// :: ref: https://stackoverflow.com/a/27282907/387194
// ----------------------------------------------------------------------
function flatten(array, mutable) {
    var toString = Object.prototype.toString;
    var arrayTypeStr = '[object Array]';

    var result = [];
    var nodes = (mutable && array) || array.slice();
    var node;

    if (!array.length) {
        return result;
    }

    node = nodes.pop();

    do {
        if (toString.call(node) === arrayTypeStr) {
            nodes.push.apply(nodes, node);
        } else {
            result.push(node);
        }
    } while (nodes.length && (node = nodes.pop()) !== undefined);

    result.reverse(); // we reverse result to restore the original order
    return result;
}
var repr = new Map();
// ----------------------------------------------------------------------
var props = Object.getOwnPropertyNames(Array.prototype);
var array_methods = [];
props.forEach(x => {
    array_methods.push(Array[x], Array.prototype[x]);
});
// ----------------------------------------------------------------------
function is_array_method(x) {
    x = unbind(x);
    return array_methods.includes(x);
}
// ----------------------------------------------------------------------
function is_lips_function(x) {
    return is_function(x) && (is_lambda(x) || x.__doc__);
}
// ----------------------------------------------------------------------
function user_repr(obj) {
    var constructor = obj.constructor || Object;
    var plain_object = is_plain_object(obj);
    var iterator = is_function(obj[Symbol.asyncIterator]) ||
        is_function(obj[Symbol.iterator]);
    var fn;
    if (repr.has(constructor)) {
        fn = repr.get(constructor);
    } else {
        repr.forEach(function(value, key) {
            key = unbind(key);
            // if key is Object it should only work for plain_object
            // because otherwise it will match every object
            // we don't use instanceof so it don't work for subclasses
            if (obj.constructor === key &&
                (key === Object && plain_object && !iterator || key !== Object)) {
                fn = value;
            }
        });
    }
    return fn;
}
// ----------------------------------------------------------------------
var str_mapping = new Map();
[
    [true, '#t'],
    [false, '#f'],
    [null, 'null'],
    [undefined, '#<undefined>']
].forEach(([key, value]) => {
    str_mapping.set(key, value);
});
// ----------------------------------------------------------------------
// :: debug function that can be used with JSON.stringify
// :: that will show symbols
// ----------------------------------------------------------------------
/* istanbul ignore next */
function symbolize(obj) {
    if (obj && typeof obj === 'object') {
        var result = {};
        const symbols = Object.getOwnPropertySymbols(obj);
        symbols.forEach((key) => {
            const name = key.toString()
                .replace(/Symbol\(([^)]+)\)/, '$1');
            result[name] = toString(obj[key]);
        });
        const props = Object.getOwnPropertyNames(obj);
        props.forEach(key => {
            const o = obj[key];
            if (o && typeof o === 'object' && o.constructor === Object) {
                result[key] = symbolize(o);
            } else {
                result[key] = toString(o);
            }
        });
        return result;
    }
    return obj;
}

// ----------------------------------------------------------------------
function function_to_string(fn) {
    if (is_native_function(fn)) {
        return '#<procedure(native)>';
    }
    const constructor = fn.prototype && fn.prototype.constructor;
    if (is_function(constructor) && is_lambda(constructor)) {
        if (constructor.hasOwnProperty('__name__')) {
            let name = constructor.__name__;
            if (LString.isString(name)) {
                name = name.toString();
                return `#<class:${name}>`;
            }
            return '#<class>';
        }
    }
    if (fn.hasOwnProperty('__name__')) {
        let name = fn.__name__;
        if (typeof name === 'symbol') {
            name = symbol_to_string(name);
        }
        if (typeof name === 'string') {
            return `#<procedure:${name}>`;
        }
    }
    if (has_own_function(fn, 'toString')) {
        return fn.toString();
    } else if (fn.name && !is_lambda(fn)) {
        return `#<procedure:${fn.name.trim()}>`;
    } else {
        return '#<procedure>';
    }
}
// ----------------------------------------------------------------------
// instances extracted to make cyclomatic complexity of toString smaller
const instances = new Map();
// ----------------------------------------------------------------------
[
    [Error, function(e) {
        return e.message;
    }],
    [Pair, function(pair, { quote, skip_cycles, pair_args }) {
        // make sure that repr directly after update set the cycle ref
        if (!skip_cycles) {
            pair.markCycles();
        }
        return pair.toString(quote, ...pair_args);
    }],
    [LCharacter, function(chr, { quote }) {
        if (quote) {
            return chr.toString();
        }
        return chr.valueOf();
    }],
    [LString, function(str, { quote }) {
        str = str.toString();
        if (quote) {
            return JSON.stringify(str).replace(/\\n/g, '\n');
        }
        return str;
    }],
    [RegExp, function(re) {
        return '#' + re.toString();
    }]
].forEach(([cls, fn]) => {
    instances.set(cls, fn);
});
// ----------------------------------------------------------------------
const native_types = [
    LSymbol,
    LNumber,
    Macro,
    Values,
    InputPort,
    OutputPort,
    Environment,
    QuotedPromise
];
// ----------------------------------------------------------------------
function toString(obj, quote, skip_cycles, ...pair_args) {
    if (typeof jQuery !== 'undefined' &&
        obj instanceof jQuery.fn.init) {
        return '#<jQuery(' + obj.length + ')>';
    }
    if (str_mapping.has(obj)) {
        return str_mapping.get(obj);
    }
    if (is_prototype(obj)) {
        return '#<prototype>';
    }
    if (obj) {
        var cls = obj.constructor;
        if (instances.has(cls)) {
            return instances.get(cls)(obj, { quote, skip_cycles, pair_args });
        }
    }
    // standard objects that have toString
    for (let type of native_types) {
        if (obj instanceof type) {
            return obj.toString(quote);
        }
    }
    // constants
    if ([nil, eof].includes(obj)) {
        return obj.toString();
    }
    if (is_function(obj)) {
        return function_to_string(obj);
    }
    if (obj === root) {
        return '#<js:global>';
    }
    if (obj === null) {
        return 'null';
    }
    if (typeof obj === 'object') {
        var constructor = obj.constructor;
        if (!constructor) {
            // this is case of fs.constants in Node.js that is null constructor object
            // this object can be handled like normal object that have properties
            constructor = Object;
        }
        var name;
        if (typeof constructor.__class__ === 'string') {
            name = constructor.__class__;
        } else {
            var fn = user_repr(obj);
            if (fn) {
                if (is_function(fn)) {
                    return fn(obj, quote);
                } else {
                    throw new Error('toString: Invalid repr value');
                }
            }
            name = constructor.name;
        }
        // user defined representation
        if (is_function(obj.toString) && is_lambda(obj.toString)) {
            return obj.toString().valueOf();
        }
        if (type(obj) === 'instance') {
            if (is_lambda(constructor) && constructor.__name__) {
                name = constructor.__name__.valueOf();
            } else if (!is_native_function(constructor)) {
                name = 'instance';
            }
        }
        if (is_iterator(obj, Symbol.iterator)) {
            if (name) {
                return `#<iterator(${name})>`;
            }
            return '#<iterator>';
        }
        if (is_iterator(obj, Symbol.asyncIterator)) {
            if (name) {
                return `#<asyncIterator(${name})>`;
            }
            return '#<asyncIterator>';
        }
        if (name !== '') {
            return '#<' + name + '>';
        }
        return '#<Object>';
    }
    if (typeof obj !== 'string') {
        return obj.toString();
    }
    return obj;
}
// ----------------------------------------------------------------------------
function is_prototype(obj) {
    return obj &&
        typeof obj === 'object' &&
        obj.hasOwnProperty &&
        obj.hasOwnProperty("constructor") &&
        typeof obj.constructor === "function" &&
        obj.constructor.prototype === obj;
}

// ----------------------------------------------------------------------
// :: abs that work on BigInt
// ----------------------------------------------------------------------
function abs(x) {
    return x < 0 ? -x : x;
}
// ----------------------------------------------------------------------
function seq_compare(fn, args) {
    var [a, ...rest] = args;
    while (rest.length > 0) {
        var [b] = rest;
        if (!fn(a, b)) {
            return false;
        }
        [a, ...rest] = rest;
    }
    return true;
}

// ----------------------------------------------------------------------
var truncate = (function() {
    if (Math.trunc) {
        return Math.trunc;
    } else {
        return function(x) {
            if (x === 0) {
                return 0;
            } else if (x < 0) {
                return Math.ceil(x);
            } else {
                return Math.floor(x);
            }
        };
    }
})();


// ----------------------------------------------------------------------
// :: Function utilities
// ----------------------------------------------------------------------

// ----------------------------------------------------------------------
function map_object(object, fn) {
    const props = Object.getOwnPropertyNames(object);
    const symbols = Object.getOwnPropertySymbols(object);
    props.concat(symbols).forEach(key => {
        const value = fn(object[key]);
        // check if property is read only, happen with webpack
        // and __esModule, it can happen for other properties as well
        const descriptor = Object.getOwnPropertyDescriptor(object, key);
        if (!descriptor || descriptor.writable && object[key] !== value) {
            object[key] = value;
        }
    });
    return object;
}

// ----------------------------------------------------------------------
// :: function that return macro for let, let* and letrec
// ----------------------------------------------------------------------
function let_macro(symbol) {
    var name;
    switch (symbol) {
        case Symbol.for('letrec'):
            name = 'letrec';
            break;
        case Symbol.for('let'):
            name = 'let';
            break;
        case Symbol.for('let*'):
            name = 'let*';
            break;
        default:
            throw new Error('Invalid let_macro value');
    }
    return Macro.defmacro(name, function(code, options) {
        var { dynamic_scope, error, macro_expand } = options;
        var args;
        // named let:
        // (let iter ((x 10)) (iter (- x 1))) -> (let* ((iter (lambda (x) ...
        if (code.car instanceof LSymbol) {
            if (!(code.cdr.car instanceof Pair || code.cdr.car === nil)) {
                throw new Error('let require list of pairs');
            }
            var params;
            if (code.cdr.car === nil) {
                args = nil;
                params = nil;
            } else {
                params = code.cdr.car.map(pair => pair.car);
                args = code.cdr.car.map(pair => pair.cdr.car);
            }
            return Pair.fromArray([
                LSymbol('letrec'),
                [[code.car, Pair(
                    LSymbol('lambda'),
                    Pair(params, code.cdr.cdr))]],
                Pair(code.car, args)
            ]);
        } else if (macro_expand) {
            // Macro.defmacro are special macros that should return lisp code
            // here we use evaluate, so we need to check special flag set by
            // macroexpand to prevent evaluation of code in normal let
            return;
        }
        var self = this;
        args = global_env.get('list->array')(code.car);
        var env = self.inherit(name);
        var values, var_body_env;
        if (name === 'let*') {
            var_body_env = env;
        } else if (name === 'let') {
            values = []; // collect potential promises
        }
        var i = 0;
        function exec() {
            var output = new Pair(new LSymbol('begin'), code.cdr);
            return evaluate(output, {
                env,
                dynamic_scope,
                error
            });
        }
        return (function loop() {
            var pair = args[i++];
            if (dynamic_scope) {
                dynamic_scope = name === 'let*' ? env : self;
            }
            if (!pair) {
                // resolve all promises
                if (values && values.length) {
                    var v = values.map(x => x.value);
                    var promises = v.filter(is_promise);
                    if (promises.length) {
                        return promise_all(v).then((arr) => {
                            for (var i = 0, len = arr.length; i < len; ++i) {
                                env.set(values[i].name, arr[i]);
                            }
                        }).then(exec);
                    } else {
                        for (let { name, value } of values) {
                            env.set(name, value);
                        }
                    }
                }
                return exec();
            } else {
                if (name === 'let') {
                    var_body_env = self;
                } else if (name === 'letrec') {
                    var_body_env = env;
                }
                var value = evaluate(pair.cdr.car, {
                    env: var_body_env,
                    dynamic_scope,
                    error
                });
                if (name === 'let*') {
                    var_body_env = env = var_body_env.inherit('let*[' + i + ']');
                }
                if (values) {
                    values.push({ name: pair.car, value });
                    return loop();
                } else {
                    return unpromise(value, function(value) {
                        env.set(pair.car, value);
                        return loop();
                    });
                }
            }
        })();
    });
}
// -------------------------------------------------------------------------
function pararel(name, fn) {
    return new Macro(name, function(code, { dynamic_scope, error } = {}) {
        var env = this;
        if (dynamic_scope) {
            dynamic_scope = this;
        }
        var node = code;
        var results = [];
        while (node instanceof Pair) {
            results.push(evaluate(node.car, { env, dynamic_scope, error }));
            node = node.cdr;
        }
        var havePromises = results.filter(is_promise).length;
        if (havePromises) {
            return promise_all(results).then(fn.bind(this));
        } else {
            return fn.call(this, results);
        }
    });
}
// -------------------------------------------------------------------------
function guard_math_call(fn, ...args) {
    args.forEach(arg => {
        typecheck('', arg, 'number');
    });
    return fn(...args);
}
// ----------------------------------------------------------------------
function pipe(...fns) {
    fns.forEach((fn, i) => {
        typecheck('pipe', fn, 'function', i + 1);
    });
    return (...args) => {
        return fns.reduce((args, f) => [f.apply(this, args)], args)[0];
    };
}
// -------------------------------------------------------------------------
function compose(...fns) {
    fns.forEach((fn, i) => {
        typecheck('compose', fn, 'function', i + 1);
    });
    return pipe(...fns.reverse());
}
// -------------------------------------------------------------------------
// :: fold functions generator
// -------------------------------------------------------------------------
function fold(name, fold) {
    var self = this;
    return function recur(fn, init, ...lists) {
        typecheck(name, fn, 'function');
        if (lists.some(is_null)) {
            if (typeof init === 'number') {
                return LNumber(init);
            }
            return init;
        } else {
            return fold.call(self, recur, fn, init, ...lists);
        }
    };
}
// -------------------------------------------------------------------------
function limit_math_op(n, fn) {
    // + 1 so it inlcude function in guard_math_call
    return limit(n + 1, curry(guard_math_call, fn));
}
// -------------------------------------------------------------------------
// some functional magic
var single_math_op = curry(limit_math_op, 1);
var binary_math_op = curry(limit_math_op, 2);
// -------------------------------------------------------------------------
function reduce_math_op(fn, init = null) {
    return function(...args) {
        if (init !== null) {
            args = [init, ...args];
        }
        return args.reduce(binary_math_op(fn));
    };
}
// -------------------------------------------------------------------------
function curry(fn, ...init_args) {
    typecheck('curry', fn, 'function');
    var len = fn.length;
    return function() {
        var args = init_args.slice();
        function call(...more_args) {
            args = args.concat(more_args);
            if (args.length >= len) {
                return fn.apply(this, args);
            } else {
                return call;
            }
        }
        return call.apply(this, arguments);
    };
}
// -------------------------------------------------------------------------
// return function with limited number of arguments
function limit(n, fn) {
    typecheck('limit', fn, 'function', 2);
    return function(...args) {
        return fn(...args.slice(0, n));
    };
}

// -------------------------------------------------------------------------
// Lips Exception used in error function
// -------------------------------------------------------------------------
function LipsError(message, args) {
    this.name = 'LipsError';
    this.message = message;
    this.args = args;
    this.stack = (new Error()).stack;
}
LipsError.prototype = new Error();
LipsError.prototype.constructor = LipsError;


// -----------------------------------------------------------------------------
function reversseFind(dir, fn) {
    var parts = dir.split(path.sep).filter(Boolean);
    for (var i = parts.length; i--;) {
        var p = path.join('/', ...parts.slice(0, i + 1));
        if (fn(p)) {
            return p;
        }
    }
}

// -------------------------------------------------------------------------
function evaluate_args(rest, { env, dynamic_scope, error }) {
    var args = [];
    var node = rest;
    markCycles(node);
    function next() {
        return args;
    }
    return (function loop() {
        if (node instanceof Pair) {
            var arg = evaluate(node.car, { env, dynamic_scope, error });
            if (dynamic_scope) {
                arg = unpromise(arg, arg => {
                    if (is_native_function(arg)) {
                        return arg.bind(dynamic_scope);
                    }
                    return arg;
                });
            }
            return unpromise(resolve_promises(arg), function(arg) {
                args.push(arg);
                if (node.haveCycles('cdr')) {
                    return next();
                }
                node = node.cdr;
                return loop();
            });
        } else if (node === nil) {
            return next();
        } else {
            throw new Error('Syntax Error: improper list found in apply');
        }
    })();
}
// -------------------------------------------------------------------------
function evaluate_syntax(macro, code, eval_args) {
    var value = macro.invoke(code, eval_args);
    return unpromise(resolve_promises(value), function(value) {
        if (value instanceof Pair) {
            value.markCycles();
        }
        return quote(value);
    });
}
// -------------------------------------------------------------------------
function evaluate_macro(macro, code, eval_args) {
    function finalize(result) {
        if (result instanceof Pair) {
            result.markCycles();
            return result;
        }
        return quote(result);
    }
    var value = macro.invoke(code, eval_args);
    return unpromise(resolve_promises(value), function ret(value) {
        if (!value || value && value[__data__] || self_evaluated(value)) {
            return value;
        } else {
            return unpromise(evaluate(value, eval_args), finalize);
        }
    });
}

// ----------------------------------------------------------------------
function is_lips_context(obj) {
    if (is_function(obj)) {
        var context = obj[__context__];
        if (context && (context === lips ||
                        (context.constructor &&
                         context.constructor.__class__))) {
            return true;
        }
    }
    return false;
}

// -------------------------------------------------------------------------
function prepare_fn_args(fn, args) {
    if (is_bound(fn) && !is_object_bound(fn) &&
        (!is_lips_context(fn) || is_port_method(fn))) {
        args = args.map(unbox);
    }
    if (!is_raw_lambda(fn) &&
        args.some(is_lips_function) &&
        !is_lips_function(fn) &&
        !is_array_method(fn)) {
        // we unbox values from callback functions #76
        // calling map on array should not unbox the value
        var result = [], i = args.length;
        while (i--) {
            let arg = args[i];
            if (is_lips_function(arg)) {
                var wrapper = function(...args) {
                    return unpromise(arg.apply(this, args), unbox);
                };
                // make wrapper work like output of bind
                hidden_prop(wrapper, '__bound__', true);
                hidden_prop(wrapper, '__fn__', arg);
                // copy prototype from function to wrapper
                // so this work when calling new from JavaScript
                // case of Preact that pass LIPS class as argument
                // to h function
                wrapper.prototype = arg.prototype;
                result[i] = wrapper;
            } else {
                result[i] = arg;
            }
        }
        args = result;
    }
    return args;
}
// -------------------------------------------------------------------------
function apply(fn, args, { env, dynamic_scope, error = () => {} } = {}) {
    args = evaluate_args(args, { env, dynamic_scope, error });
    return unpromise(args, function(args) {
        if (is_raw_lambda(fn)) {
            // lambda need environment as context
            // normal functions are bound to their contexts
            fn = unbind(fn);
        }
        args = prepare_fn_args(fn, args);
        var _args = args.slice();
        var scope = (dynamic_scope || env).newFrame(fn, _args);
        var result = resolve_promises(fn.apply(scope, args));
        return unpromise(result, (result) => {
            if (result instanceof Pair) {
                result.markCycles();
                return quote(result);
            }
            return box(result);
        }, error);
    });
}

// -------------------------------------------------------------------------
function evaluate(code, { env, dynamic_scope, error = noop } = {}) {
    try {
        if (dynamic_scope === true) {
            env = dynamic_scope = env || global_env;
        } else if (env === true) {
            env = dynamic_scope = global_env;
        } else {
            env = env || global_env;
        }
        var eval_args = { env, dynamic_scope, error };
        var value;
        if (is_null(code)) {
            return code;
        }
        if (code instanceof LSymbol) {
            return env.get(code);
        }
        if (!(code instanceof Pair)) {
            return code;
        }
        var first = code.car;
        var rest = code.cdr;
        if (first instanceof Pair) {
            value = resolve_promises(evaluate(first, eval_args));
            if (is_promise(value)) {
                return value.then((value) => {
                    return evaluate(new Pair(value, code.cdr), eval_args);
                });
                // else is later in code
            } else if (!is_callable(value)) {
                throw new Error(
                    type(value) + ' ' + env.get('repr')(value) +
                        ' is not callable while evaluating ' + code.toString()
                );
            }
        }
        if (first instanceof LSymbol) {
            value = env.get(first);
        } else if (is_function(first)) {
            value = first;
        }
        var result;
        if (value instanceof Syntax) {
            result = evaluate_syntax(value, code, eval_args);
        } else if (value instanceof Macro) {
            result = evaluate_macro(value, rest, eval_args);
        } else if (is_function(value)) {
            result = apply(value, rest, eval_args);
        } else if (is_continuation(value)) {
            result = value.invoke();
        } else if (code instanceof Pair) {
            value = first && first.toString();
            throw new Error(`${type(first)} ${value} is not a function`);
        } else {
            return code;
        }
        // escape promise feature #54
        var __promise__ = env.get(Symbol.for('__promise__'), { throwError: false });
        if (__promise__ === true && is_promise(result)) {
            // fix #139 evaluate the code inside the promise that is not data.
            // When promise is not quoted it happen automatically, when returing
            // promise from evaluate.
            result = result.then(result => {
                if (result instanceof Pair && !value[__data__]) {
                    return evaluate(result, eval_args);
                }
                return result;
            });
            return new QuotedPromise(result);
        }
        return result;
    } catch (e) {
        error && error.call(env, e, code);
    }
}
// -------------------------------------------------------------------------
const compile = exec_collect(function(code) {
    return code;
});
// -------------------------------------------------------------------------
const exec = exec_collect(function(code, value) {
    return value;
});
// -------------------------------------------------------------------------
function exec_collect(collect_callback) {
    return async function exec_lambda(arg, env, dynamic_scope) {
        if (dynamic_scope === true) {
            env = dynamic_scope = env || user_env;
        } else if (env === true) {
            env = dynamic_scope = user_env;
        } else {
            env = env || user_env;
        }
        var results = [];
        var input = Array.isArray(arg) ? arg : parse(arg);
        for await (let code of input) {
            const value = evaluate(code, {
                env,
                dynamic_scope,
                error: (e, code) => {
                    if (e && e.message) {
                        if (e.message.match(/^Error:/)) {
                            var re = /^(Error:)\s*([^:]+:\s*)/;
                            // clean duplicated Error: added by JS
                            e.message = e.message.replace(re, '$1 $2');
                        }
                        if (code) {
                            // LIPS stack trace
                            if (!(e.__code__ instanceof Array)) {
                                e.__code__ = [];
                            }
                            e.__code__.push(code.toString(true));
                        }
                    }
                    throw e;
                }
            });
            if (!is_promise(value)) {
                results.push(collect_callback(code, value));
            } else {
                results.push(collect_callback(code, await value));
            }
        }
        return results;
    };
}

// -------------------------------------------------------------------------
function fworker(fn) {
    // ref: https://stackoverflow.com/a/10372280/387194
    var str = '(' + fn.toString() + ')()';
    var URL = window.URL || window.webkitURL;
    var blob;
    try {
        blob = new Blob([str], { type: 'application/javascript' });
    } catch (e) { // Backwards-compatibility
        const BlobBuilder = window.BlobBuilder ||
              window.WebKitBlobBuilder ||
              window.MozBlobBuilder;
        blob = new BlobBuilder();
        blob.append(str);
        blob = blob.getBlob();
    }
    return new root.Worker(URL.createObjectURL(blob));
}
// -------------------------------------------------------------------------
function is_dev() {
    return lips.version.match(/^(\{\{VER\}\}|DEV)$/);
}
// -------------------------------------------------------------------------
function bootstrap(url = '') {
    const std = 'dist/std.xcb';
    if (url === '') {
        if (is_dev()) {
            url = `https://cdn.jsdelivr.net/gh/jcubic/lips@devel/${std}`;
        } else {
            url = `https://cdn.jsdelivr.net/npm/@jcubic/lips@${lips.version}/${std}`;
        }
    }
    var load = global_env.get('load');
    return load.call(user_env, url, global_env);
}
// -------------------------------------------------------------------------
function Worker(url) {
    this.url = url;
    const worker = this.worker = fworker(function() {
        var interpreter;
        var init;
        // string, numbers, booleans
        self.addEventListener('message', function(response) {
            var data = response.data;
            var id = data.id;
            if (data.type !== 'RPC' || id === null) {
                return;
            }
            function send_result(result) {
                self.postMessage({ id: id, type: 'RPC', result: result });
            }
            function send_error(message) {
                self.postMessage({ id: id, type: 'RPC', error: message });
            }
            if (data.method === 'eval') {
                if (!init) {
                    send_error('Worker RPC: LIPS not initilized, call init first');
                    return;
                }
                init.then(function() {
                    // we can use ES6 inside function that's converted to blob
                    var code = data.params[0];
                    var dynamic = data.params[1];
                    interpreter.exec(code, dynamic).then(function(result) {
                        result = result.map(function(value) {
                            return value && value.valueOf();
                        });
                        send_result(result);
                    }).catch(error => {
                        send_error(error);
                    });
                });
            } else if (data.method === 'init') {
                var url = data.params[0];
                if (typeof url !== 'string') {
                    send_error('Worker RPC: url is not a string');
                } else {
                    importScripts(`${url}/dist/lips.min.js`);
                    interpreter = new lips.Interpreter('worker');
                    init = bootstrap(url);
                    init.then(() => {
                        send_result(true);
                    });
                }
            }
        });
    });
    this.rpc = (function() {
        var id = 0;
        return function rpc(method, params) {
            var _id = ++id;
            return new Promise(function(resolve, reject) {
                worker.addEventListener('message', function handler(response) {
                    var data = response.data;
                    if (data && data.type === 'RPC' && data.id === _id) {
                        if (data.error) {
                            reject(data.error);
                        } else {
                            resolve(data.result);
                        }
                        worker.removeEventListener('message', handler);
                    }
                });
                worker.postMessage({
                    type: 'RPC',
                    method: method,
                    id: _id,
                    params: params
                });
            });
        };
    })();
    this.rpc('init', [url]).catch((error) => {
        console.error(error);
    });
    this.exec = function(code, dynamic = false) {
        return this.rpc('eval', [code, dynamic]);
    };
}

// -------------------------------------------------------------------------
// :: Serialization
// -------------------------------------------------------------------------
var serialization_map = {
    'pair': ([car, cdr]) => Pair(car, cdr),
    'number': function(value) {
        if (LString.isString(value)) {
            return LNumber([value, 10]);
        }
        return LNumber(value);
    },
    'regex': function([pattern, flag]) {
        return new RegExp(pattern, flag);
    },
    'nil': function() {
        return nil;
    },
    'symbol': function(value) {
        if (LString.isString(value)) {
            return LSymbol(value);
        } else if (Array.isArray(value)) {
            return LSymbol(Symbol.for(value[0]));
        }
    },
    'string': LString,
    'character': LCharacter
};
// -------------------------------------------------------------------------
// class mapping to create smaller JSON
const available_class = Object.keys(serialization_map);
const class_map = {};
for (let [i, cls] of Object.entries(available_class)) {
    class_map[cls] = +i;
}
function mangle_name(name) {
    return class_map[name];
}
function resolve_name(i) {
    return available_class[i];
}
// -------------------------------------------------------------------------
function serialize(data) {
    return JSON.stringify(data, function(key, value) {
        const v0 = this[key];
        if (v0) {
            if (v0 instanceof RegExp) {
                return {
                    '@': mangle_name('regex'),
                    '#': [v0.source, v0.flags]
                };
            }
            var cls = mangle_name(v0.constructor.__class__);
            if (!is_undef(cls)) {
                return {
                    '@': cls,
                    '#': v0.serialize()
                };
            }
        }
        return value;
    });
}
// -------------------------------------------------------------------------
function unserialize(string) {
    return JSON.parse(string, (_, object) => {
        if (object && typeof object === 'object') {
            if (!is_undef(object['@'])) {
                var cls = resolve_name(object['@']);
                if (serialization_map[cls]) {
                    return serialization_map[cls](object['#']);
                }
            }
        }
        return object;
    });
}

// -------------------------------------------------------------------------
// binary serialization using CBOR binary data format
// -------------------------------------------------------------------------
const cbor = (function() {

    var types = {
        'pair': Pair,
        'symbol': LSymbol,
        'number': LNumber,
        'string': LString,
        'character': LCharacter,
        'nil': nil.constructor,
        'regex': RegExp
    };

    function serializer(Class, fn) {
        return {
            deserialize: fn,
            Class
        };
    }

    var encoder = new Encoder();

    const cbor_serialization_map = {};
    for (const [ name, fn ] of Object.entries(serialization_map)) {
        const Class = types[name];
        cbor_serialization_map[name] = serializer(Class, fn);
    }
    // add CBOR data mapping
    let tag = 43311;
    Object.keys(cbor_serialization_map).forEach(type => {
        const data = cbor_serialization_map[type];
        if (typeof data === 'function') {
            const Class = data;
            addExtension({
                Class,
                tag,
                encode(instance, encode) {
                    encode(instance.serialize());
                },
                decode(data) {
                    return new Class(data);
                }
            });
        } else {
            const { deserialize, Class } = data;
            addExtension({
                Class,
                tag,
                encode(instance, encode) {
                    if (instance instanceof RegExp) {
                        return encode([instance.source, instance.flags]);
                    }
                    encode(instance.serialize());
                },
                decode(data) {
                    return deserialize(data);
                }
            });
        }
        tag++;
    });
    return encoder;
})();

// -------------------------------------------------------------------------
function merge_uint8_array(...args) {
    if (args.length > 1) {
        const len = args.reduce((acc, arr) => acc + arr.length, 0);
        const result = new Uint8Array(len);
        let offset = 0;
        args.forEach(item => {
            result.set(item, offset);
            offset += item.length;
        });
        return result;
    } else if (args.length) {
        return args[0];
    }
}

// -------------------------------------------------------------------------
function encode_magic() {
    const VERSION = 1;
    const encoder = new TextEncoder('utf-8');
    return encoder.encode(`CBRZ${VERSION.toString().padStart(3, ' ')}`);
}

// -------------------------------------------------------------------------
const MAGIC_LENGTH = 7;
// -------------------------------------------------------------------------
function decode_magic(obj) {
    const decoder = new TextDecoder('utf-8');
    const prefix = decoder.decode(obj.slice(0, MAGIC_LENGTH));
    const name = prefix.substring(0, 4);
    if (['CBOR', 'CBRZ'].includes(name)) {
        const m = prefix.match(/^(....).*([0-9]+)$/);
        if (m) {
            return {
                type: m[1],
                version: Number(m[2])
            };
        }
    }
    return {
        type: 'unknown'
    };
}

// -------------------------------------------------------------------------
function serialize_bin(obj) {
    const magic = encode_magic();
    const payload = cbor.encode(obj);
    return merge_uint8_array(magic, pack(payload, { magic: false }));
}

// -------------------------------------------------------------------------
function unserialize_bin(data) {
    const { type, version } = decode_magic(data);
    if (type === 'CBOR' && version === 1) {
        return cbor.decode(data.slice(MAGIC_LENGTH));
    } else if (type === 'CBRZ' && version === 1) {
        const arr = unpack(data.slice(MAGIC_LENGTH), { magic: false });
        return cbor.decode(arr);
    } else {
        throw new Error(`Invalid file format ${type}`);
    }
}

// -------------------------------------------------------------------------
function execError(e) {
    console.error(e.message || e);
    if (e.code) {
        console.error(e.code.map((line, i) => `[${i + 1}]: ${line}`));
    }
}

// -------------------------------------------------------------------------
function init() {
    var lips_mimes = ['text/x-lips', 'text/x-scheme'];
    var bootstraped;
    function load(script) {
        return new Promise(function(resolve) {
            var src = script.getAttribute('src');
            if (src) {
                return fetch(src).then(res => res.text())
                    .then(exec).then(resolve).catch((e) => {
                        execError(e);
                        resolve();
                    });
            } else {
                return exec(script.innerHTML).then(resolve).catch((e) => {
                    execError(e);
                    resolve();
                });
            }
        });
    }

    function loop() {
        return new Promise(function(resolve) {
            var scripts = Array.from(document.querySelectorAll('script'));
            return (function loop() {
                var script = scripts.shift();
                if (!script) {
                    resolve();
                } else {
                    var type = script.getAttribute('type');
                    if (lips_mimes.includes(type)) {
                        var bootstrap_attr = script.getAttribute('bootstrap');
                        if (!bootstraped && typeof bootstrap_attr === 'string') {
                            bootstrap(bootstrap_attr).then(function() {
                                return load(script, function(e) {
                                    console.error(e);
                                });
                            }).then(loop);
                        } else {
                            load(script, function(e) {
                                console.error(e);
                            }).then(loop);
                        }
                    } else if (type && type.match(/lips|lisp/)) {
                        console.warn('Expecting ' + lips_mimes.join(' or ') +
                                     ' found ' + type);
                    }
                    return loop();
                }
            })();
        });
    }
    if (!window.document) {
        return Promise.resolve();
    } else if (currentScript) {
        var script = currentScript;
        var bootstrap_attr = script.getAttribute('bootstrap');
        if (typeof bootstrap_attr === 'string') {
            return bootstrap(bootstrap_attr).then(function() {
                bootstraped = true;
                return loop();
            });
        }
    }
    return loop();
}
// this can't be in init function, because it need to be in script context
const currentScript = typeof window !== 'undefined' &&
      window.document && document.currentScript;
// -------------------------------------------------------------------------
if (typeof window !== 'undefined') {
    contentLoaded(window, init);
}
// -------------------------------------------------------------------------
var banner = (function() {
    // Rollup tree-shaking is removing the variable if it's normal string because
    // obviously '{{DATE}}' == '{{' + 'DATE}}'; can be removed
    // but disablig Tree-shaking is adding lot of not used code so we use this
    // hack instead
    var date = LString('{{DATE}}').valueOf();
    var _date = date === '{{' + 'DATE}}' ? new Date() : new Date(date);
    var _format = x => x.toString().padStart(2, '0');
    var _year = _date.getFullYear();
    var _build = [
        _year,
        _format(_date.getMonth() + 1),
        _format(_date.getDate())
    ].join('-');
    var banner = `
  __ __                          __
 / / \\ \\       _    _  ___  ___  \\ \\
| |   \\ \\     | |  | || . \\/ __>  | |
| |    > \\    | |_ | ||  _/\\__ \\  | |
| |   / ^ \\   |___||_||_|  <___/  | |
 \\_\\ /_/ \\_\\                     /_/

LIPS Interpreter {{VER}} (${_build}) <https://lips.js.org>
Copyright (c) 2018-${_year} Jakub T. Jankiewicz

Type (env) to see environment with functions macros and variables. You can also
use (help name) to display help for specic function or macro, (apropos name)
to display list of matched names in environment and (dir object) to list
properties of an object.
`.replace(/^.*\n/, '');
    return banner;
})();
// -------------------------------------------------------------------------
// to be used with string function when code is minified
// -------------------------------------------------------------------------
read_only(Ahead, '__class__', 'ahead');
read_only(Pair, '__class__', 'pair');
read_only(Nil, '__class__', 'nil');
read_only(Pattern, '__class__', 'pattern');
read_only(Formatter, '__class__', 'formatter');
read_only(Macro, '__class__', 'macro');
read_only(Syntax, '__class__', 'syntax');
read_only(Environment, '__class__', 'environment');
read_only(InputPort, '__class__', 'input-port');
read_only(OutputPort, '__class__', 'output-port');
read_only(BufferedOutputPort, '__class__', 'output-port');
read_only(OutputStringPort, '__class__', 'output-string-port');
read_only(InputStringPort, '__class__', 'input-string-port');
read_only(InputFilePort, '__class__', 'input-file-port');
read_only(OutputFilePort, '__class__', 'output-file-port');
read_only(LipsError, '__class__', 'lips-error');
[LNumber, LComplex, LRational, LFloat, LBigInteger].forEach(cls => {
    read_only(cls, '__class__', 'number');
});
read_only(LCharacter, '__class__', 'character');
read_only(LSymbol, '__class__', 'symbol');
read_only(LString, '__class__', 'string');
read_only(QuotedPromise, '__class__', 'promise');
// -------------------------------------------------------------------------
const lips = {
    version: '{{VER}}',
    banner,
    date: '{{DATE}}',
    exec,
    // unwrap async generator into Promise<Array>
    parse: compose(uniterate_async, parse),
    tokenize,
    evaluate,
    compile,

    serialize,
    unserialize,

    serialize_bin,
    unserialize_bin,

    bootstrap,

    Environment,
    env: user_env,

    Worker,

    Interpreter,
    balanced_parenthesis: balanced,
    balancedParenthesis: balanced,
    balanced,

    Macro,
    Syntax,
    Pair,
    Values,
    QuotedPromise,
    Error: LipsError,

    quote,

    InputPort,
    OutputPort,
    BufferedOutputPort,
    InputFilePort,
    OutputFilePort,
    InputStringPort,
    OutputStringPort,
    InputByteVectorPort,
    OutputByteVectorPort,
    InputBinaryFilePort,
    OutputBinaryFilePort,

    Formatter,
    Parser,
    Lexer,
    specials,
    repr,
    nil,
    eof,

    LSymbol,
    LNumber,
    LFloat,
    LComplex,
    LRational,
    LBigInteger,
    LCharacter,
    LString,
    rationalize
};
// so it work when used with webpack where it will be not global
export default lips;
global_env.set('lips', lips);
