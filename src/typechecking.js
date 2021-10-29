/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol */
import { Pair, nil } from './Pair.js';
import { LNumber } from './Numbers.js';
import { LSymbol } from './LSymbol.js';
import { InputPort, OutputPort, __binary_port__ } from './Ports.js';
import LString from './LString.js';
import LCharacter from './LCharacter.js';
import Values from './Values.js';
import Continuation from './Continuation.js';
import { Syntax, Macro } from './Macro.js';


// ----------------------------------------------------------------------
// hidden props
// ----------------------------------------------------------------------
const __fn__ = Symbol.for('__fn__');
const __method__ = Symbol.for('__method__');
const __context__ = Symbol.for('__context__');
const __prototype__ = Symbol.for('__prototype__');
const __lambda__ = Symbol.for('__lambda__');
const __data__ = Symbol.for('__data__');

// ----------------------------------------------------------------------
function typecheck(fn, arg, expected, position = null) {
    fn = fn.valueOf();
    const arg_type = type(arg).toLowerCase();
    if (is_function(expected)) {
        if (!expected(arg)) {
            throw new Error(type_error_message(fn, arg_type, expected, position));
        }
        return;
    }
    var match = false;
    if (expected instanceof Pair) {
        expected = expected.to_array();
    }
    if (expected instanceof Array) {
        expected = expected.map(x => x.valueOf());
    }
    if (expected instanceof Array) {
        expected = expected.map(x => x.valueOf().toLowerCase());
        if (expected.includes(arg_type)) {
            match = true;
        }
    } else {
        expected = expected.valueOf().toLowerCase();
    }
    if (!match && arg_type !== expected) {
        throw new Error(type_error_message(fn, arg_type, expected, position));
    }
}

// -------------------------------------------------------------------------
function type_error_message(fn, got, expected, position = null) {
    let postfix = fn ? ` in expression \`${fn}\`` : '';
    if (position !== null) {
        postfix += ` (argument ${position})`;
    }
    if (is_function(expected)) {
        return `Invalid type got ${got}${postfix}`;
    }
    if (expected instanceof Array) {
        if (expected.length === 1) {
            expected = expected[0];
        } else {
            const last = expected[expected.length - 1];
            expected = expected.slice(0, -1).join(', ') + ' or ' + last;
        }
    }
    return `Expecting ${expected}, got ${got}${postfix}`;
}

// -------------------------------------------------------------------------
function typecheck_args(fn, args, expected) {
    args.forEach((arg, i) => {
        typecheck(fn, arg, expected, i + 1);
    });
}

// -------------------------------------------------------------------------
function typecheck_text_port(fn, arg, type) {
    typecheck(fn, arg, type);
    if (arg.__type__ === __binary_port__) {
        throw new Error(type_error_message(
            fn,
            'binary-port',
            'textual-port'
        ));
    }
}

// -------------------------------------------------------------------------
function type(obj) {
    var mapping = {
        'pair': Pair,
        'symbol': LSymbol,
        'character': LCharacter,
        'values': Values,
        'input-port': InputPort,
        'output-port': OutputPort,
        'number': LNumber,
        'regex': RegExp,
        'syntax': Syntax,
        'macro': Macro,
        'string': LString,
        'array': Array,
        'native-symbol': Symbol
    };
    if (Number.isNaN(obj)) {
        return 'NaN';
    }
    if (obj === nil) {
        return 'nil';
    }
    if (obj === null) {
        return 'null';
    }
    for (let [key, value] of Object.entries(mapping)) {
        if (obj instanceof value) {
            return key;
        }
    }
    if (typeof obj === 'object') {
        if (obj.__instance__) {
            obj.__instance__ = false;
            if (obj.__instance__) {
                if (is_function(obj.toType)) {
                    return obj.toType();
                }
                return 'instance';
            }
        }
        if (obj.constructor) {
            if (obj.constructor.__class__) {
                return obj.constructor.__class__;
            }
            if (obj.constructor === Object) {
                if (is_iterator(obj, Symbol.iterator)) {
                    return 'iterator';
                }
                if (is_iterator(obj, Symbol.asyncIterator)) {
                    return 'async-iterator';
                }
            }
            return obj.constructor.name.toLowerCase();
        }
    }
    return typeof obj;
}

// ----------------------------------------------------------------------
// :: check for nullish values
// ----------------------------------------------------------------------
function is_null(value) {
    return is_undef(value) || value === nil || value === null;
}

// ----------------------------------------------------------------------
function is_continuation(o) {
    return o instanceof Continuation;
}

// ----------------------------------------------------------------------
function is_callable(o) {
    return is_function(o) || is_continuation(o);
}

// ----------------------------------------------------------------------
function is_function(o) {
    return typeof o === 'function' && typeof o.bind === 'function';
}

// ----------------------------------------------------------------------
function is_undef(value) {
    return typeof value === 'undefined';
}

// ----------------------------------------------------------------------
function is_plain_object(object) {
    return object && typeof object === 'object' && object.constructor === Object;
}

// ----------------------------------------------------------------------
function is_atom(obj) {
    return obj instanceof LSymbol ||
        LString.isString(obj) ||
        obj === nil ||
        obj === null ||
        obj instanceof LCharacter ||
        obj instanceof LNumber ||
        obj === true ||
        obj === false;
}

// ----------------------------------------------------------------------
function is_port(obj) {
    return obj instanceof InputPort || obj instanceof OutputPort;
}

// ----------------------------------------------------------------------
function is_port_method(obj) {
    if (is_function(obj)) {
        if (is_port(obj[__context__])) {
            return true;
        }
    }
    return false;
}

// ----------------------------------------------------------------------
function is_lambda(obj) {
    return obj && obj[__lambda__];
}

// ----------------------------------------------------------------------
function is_method(obj) {
    return obj && obj[__method__];
}

// ----------------------------------------------------------------------
function is_raw_lambda(fn) {
    return is_lambda(fn) && !fn[__prototype__] &&
        !is_method(fn) && !is_port_method(fn);
}

// ----------------------------------------------------------------------
function is_native_function(fn) {
    var native = Symbol.for('__native__');
    return is_function(fn) &&
        fn.toString().match(/\{\s*\[native code\]\s*\}/) &&
        ((fn.name.match(/^bound /) && fn[native] === true) ||
         (!fn.name.match(/^bound /) && !fn[native]));
}

// -------------------------------------------------------------------------
function is_native(obj) {
    return obj instanceof LNumber ||
        obj instanceof LString ||
        obj instanceof LCharacter;
}
// -------------------------------------------------------------------------
function is_iterator(obj, symbol) {
    if (has_own_symbol(obj, symbol) || has_own_symbol(obj.__proto__, symbol)) {
        return is_function(obj[symbol]);
    }
}

// ----------------------------------------------------------------------
// function used to check if function should not get unboxed arguments,
// so you can call Object.getPrototypeOf for lips data types
// this is case, see dir function and #73
// ----------------------------------------------------------------------
function is_object_bound(obj) {
    return is_bound(obj) && obj[Symbol.for('__context__')] === Object;
}

// ----------------------------------------------------------------------
function is_bound(obj) {
    return !!(is_function(obj) && obj[__fn__]);
}

// -------------------------------------------------------------------------
function has_own_symbol(obj, symbol) {
    if (obj === null) {
        return false;
    }
    return typeof obj === 'object' &&
        symbol in Object.getOwnPropertySymbols(obj);
}

// ----------------------------------------------------------------------
function has_own_function(obj, name) {
    return obj.hasOwnProperty(name) && is_function(obj.toString);
}

export {
    typecheck_args,
    type_error_message,
    typecheck,
    type,
    __fn__,
    __data__,
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
};
