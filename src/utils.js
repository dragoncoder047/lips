/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol */
import {
    typecheck,
    type,
    is_null,
    is_function,
    is_bound,
    is_atom,
    is_lambda,
    is_plain_object,
    is_native_function,
    __fn__,
    __data__
} from './typechecking.js';
import { box } from './boxing.js';
import { nil, Pair } from './Pair.js';
import { LNumber } from './Numbers.js';
import { LSymbol } from './LSymbol.js';
import { is_promise } from './Promises.js';
import LCharacter from './LCharacter.js';
import LString from './LString.js';

function to_array(name, deep) {
    return function recur(list) {
        typecheck(name, list, ['pair', 'nil']);
        if (list === nil) {
            return [];
        }
        var result = [];
        var node = list;
        while (true) {
            if (node instanceof Pair) {
                if (node.haveCycles('cdr')) {
                    break;
                }
                var car = node.car;
                if (deep && car instanceof Pair) {
                    car = this.get(name).call(this, car);
                }
                result.push(car);
                node = node.cdr;
            } else if (node === nil) {
                break;
            } else {
                throw new Error(`${name}: can't convert improper list`);
            }
        }
        return result;
    };
}

// ----------------------------------------------------------------------
function escape_regex(str) {
    if (typeof str === 'string') {
        var special = /([-\\^$[\]()+{}?*.|])/g;
        return str.replace(special, '\\$1');
    }
    return str;
}

// ----------------------------------------------------------------------
function read_only(object, property, value, { hidden = false } = {}) {
    Object.defineProperty(object, property, {
        value,
        configurable: true,
        enumerable: !hidden
    });
}

// ----------------------------------------------------------------------
// :: Function similar to Array.from that work on async iterators
// ----------------------------------------------------------------------
async function uniterate_async(object) {
    const result = [];
    for await (let item of object) {
        result.push(item);
    }
    return result;
}

// ----------------------------------------------------------------------
const noop = () => {};

// ----------------------------------------------------------------------
// :: function get original function that was binded with props
// ----------------------------------------------------------------------
function unbind(obj) {
    if (is_bound(obj)) {
        return obj[__fn__];
    }
    return obj;
}

// ----------------------------------------------------------------------
var exluded_names = ['name', 'length', 'caller', 'callee', 'arguments', 'prototype'];
function filter_fn_names(name) {
    return !exluded_names.includes(name);
}

// ----------------------------------------------------------------------
// :: function bind with contex that can be optionaly unbind
// :: get original function with unbind
// ----------------------------------------------------------------------
function bind(fn, context) {
    if (fn[Symbol.for('__bound__')]) {
        return fn;
    }
    const bound = fn.bind(context);
    const props = Object.getOwnPropertyNames(fn);
    for (var prop of props) {
        if (filter_fn_names(prop)) {
            try {
                bound[prop] = fn[prop];
            } catch (e) {
                // ignore error from express.js while accessing bodyParser
            }
        }
    }
    hidden_prop(bound, '__fn__', fn);
    hidden_prop(bound, '__context__', context);
    hidden_prop(bound, '__bound__', true);
    if (is_native_function(fn)) {
        hidden_prop(bound, '__native__', true);
    }
    if (is_plain_object(context) && is_lambda(fn)) {
        hidden_prop(bound, '__method__', true);
    }
    bound.valueOf = function() {
        return fn;
    };
    return bound;
}

// ----------------------------------------------------------------------
function hidden_prop(obj, name, value) {
    Object.defineProperty(obj, Symbol.for(name), {
        get: () => value,
        set: () => {},
        configurable: false,
        enumerable: false
    });
}

// ----------------------------------------------------------------------
function set_fn_length(fn, length) {
    try {
        Object.defineProperty(fn, 'length', {
            get: function() {
                return length;
            }
        });
        return fn;
    } catch (e) {
        // hack that create function with specific length should work for browsers
        // that don't support Object.defineProperty like old IE
        var args = new Array(length).fill(0).map((_, i) => 'a' + i).join(',');
        var wrapper = new Function(`f`, `return function(${args}) {
                return f.apply(this, arguments);
            };`);
        return wrapper(fn);
    }
}

// ----------------------------------------------------------------------
function get_props(obj) {
    return Object.keys(obj).concat(Object.getOwnPropertySymbols(obj));
}

// ----------------------------------------------------------------------
function equal(x, y) {
    if (is_function(x)) {
        return is_function(y) && unbind(x) === unbind(y);
    } else if (x instanceof LNumber) {
        if (!(y instanceof LNumber)) {
            return false;
        }
        let type;
        if (x.__type__ === y.__type__) {
            if (x.__type__ === 'complex') {
                type = x.__im__.__type__ === y.__im__.__type__ &&
                    x.__re__.__type__ === y.__re__.__type__;
            } else {
                type = true;
            }
            if (type && x.cmp(y) === 0) {
                if (x.valueOf() === 0) {
                    return Object.is(x.valueOf(), y.valueOf());
                }
                return true;
            }
        }
        return false;
    } else if (typeof x === 'number') {
        if (typeof y !== 'number') {
            return false;
        }
        if (Number.isNaN(x)) {
            return Number.isNaN(y);
        }
        if (x === Number.NEGATIVE_INFINITY) {
            return y === Number.NEGATIVE_INFINITY;
        }
        if (x === Number.POSITIVE_INFINITY) {
            return y === Number.POSITIVE_INFINITY;
        }
        return equal(LNumber(x), LNumber(y));
    } else if (x instanceof LCharacter) {
        if (!(y instanceof LCharacter)) {
            return false;
        }
        return x.__char__ === y.__char__;
    } else {
        return x === y;
    }
}

// ----------------------------------------------------------------------
function same_atom(a, b) {
    if (type(a) !== type(b)) {
        return false;
    }
    if (!is_atom(a)) {
        return false;
    }
    if (a instanceof RegExp) {
        return a.source === b.source;
    }
    if (a instanceof LString) {
        return a.valueOf() === b.valueOf();
    }
    return equal(a, b);
}

// ----------------------------------------------------------------------
// :: documentaton decorator to LIPS functions if lines starts with :
// :: they are ignored (not trim) otherwise it trim so
// :: so you can have indent in source code
// ----------------------------------------------------------------------
function doc(name, fn, doc, dump) {
    if (typeof name !== 'string') {
        fn = arguments[0];
        doc = arguments[1];
        dump = arguments[2];
        name = null;
    }
    if (doc) {
        if (dump) {
            fn.__doc__ = doc;
        } else {
            fn.__doc__ = trim_lines(doc);
        }
    }
    if (name) {
        fn.__name__ = name;
    } else if (fn.name && !is_lambda(fn)) {
        fn.__name__ = fn.name;
    }
    return fn;
}
// ----------------------------------------------------------------------
function trim_lines(string) {
    return string.split('\n').map(line => {
        return line.trim();
    }).join('\n');
}

// ----------------------------------------------------------------------
function patch_value(value, context) {
    if (value instanceof Pair) {
        value.markCycles();
        return quote(value);
    }
    if (is_function(value)) {
        // original function can be restored using unbind function
        // only real JS function require to be bound
        if (context) {
            return bind(value, context);
        }
    }
    return box(value);
}

// -------------------------------------------------------------------------
// :: Quote funtion used to pause evaluation from Macro
// -------------------------------------------------------------------------
function quote(value) {
    if (is_promise(value)) {
        return value.then(quote);
    }
    if (value instanceof Pair || value instanceof LSymbol) {
        value[__data__] = true;
    }
    return value;
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
const single_math_op = curry(limit_math_op, 1);
const binary_math_op = curry(limit_math_op, 2);
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
// -------------------------------------------------------------------------
function limit(n, fn) {
    typecheck('limit', fn, 'function', 2);
    return function(...args) {
        return fn(...args.slice(0, n));
    };
}

// -------------------------------------------------------------------------
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

export {
    to_array,
    escape_regex,
    read_only,
    uniterate_async,
    noop,
    unbind,
    bind,
    hidden_prop,
    set_fn_length,
    get_props,
    equal,
    same_atom,
    doc,
    trim_lines,
    patch_value,
    quote,
    pipe,
    compose,
    fold,
    binary_math_op,
    single_math_op,
    reduce_math_op,
    curry,
    limit,
    seq_compare
};
