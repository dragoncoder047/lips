/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Map */
import { parse, tokenize } from './Parser.js';
import { is_plain_object, is_function, typecheck } from './typechecking.js';
import { QuotedPromise } from './Promises.js';
import { LNumber } from './Numbers.js';
import { nil } from './Pair.js';
import { LSymbol } from './LSymbol.js';
import { doc, trim_lines, get_props, unbind, patch_value } from './utils.js';
import { global_env } from './CoreLibrary.js';
import { unbox } from './boxing.js';
import LString from './LString.js';
import Value from './Value.js';
import root from './root.js';
// -------------------------------------------------------------------------
// :: Environment constructor (parent and name arguments are optional)
// -------------------------------------------------------------------------
function Environment(obj, parent, name) {
    if (arguments.length === 1) {
        if (typeof arguments[0] === 'object') {
            obj = arguments[0];
            parent = null;
        } else if (typeof arguments[0] === 'string') {
            obj = {};
            parent = null;
            name = arguments[0];
        }
    }
    this.__docs__ = new Map();
    this.__env__ = obj;
    this.__parent__ = parent;
    this.__name__ = name || 'anonymous';
}
// -------------------------------------------------------------------------
Environment.prototype.list = function() {
    return get_props(this.__env__);
};
// -------------------------------------------------------------------------
Environment.prototype.fs = function() {
    return this.get('**fs**');
};
// -------------------------------------------------------------------------
Environment.prototype.unset = function(name) {
    if (name instanceof LSymbol) {
        name = name.valueOf();
    }
    if (name instanceof LString) {
        name = name.valueOf();
    }
    delete this.__env__[name];
};
// -------------------------------------------------------------------------
Environment.prototype.inherit = function(name, obj = {}) {
    if (typeof name === "object") {
        obj = name;
    }
    if (!name || typeof name === "object") {
        name = 'child of ' + (this.__name__ || 'unknown');
    }
    return new Environment(obj || {}, this, name);
};
// -------------------------------------------------------------------------
// :: lookup function for variable doc strings
// -------------------------------------------------------------------------
Environment.prototype.doc = function(name, value = null, dump = false) {
    if (name instanceof LSymbol) {
        name = name.__name__;
    }
    if (name instanceof LString) {
        name = name.valueOf();
    }
    if (value) {
        if (!dump) {
            value = trim_lines(value);
        }
        this.__docs__.set(name, value);
        return this;
    }
    if (this.__docs__.has(name)) {
        return this.__docs__.get(name);
    }
    if (this.__parent__) {
        return this.__parent__.doc(name);
    }
};
// -------------------------------------------------------------------------
// :: function create frame environment for usage in functions
// :: frames are used to it's easier to find environments of the functions
// :: in scope chain, they are dummy environments just for lookup
// -------------------------------------------------------------------------
Environment.prototype.newFrame = function(fn, args) {
    var frame = this.inherit('__frame__');
    frame.set('parent.frame', doc('parent.frame', function(n = 1) {
        n = n.valueOf();
        var scope = frame.__parent__;
        if (!(scope instanceof Environment)) {
            return nil;
        }
        if (n <= 0) {
            return scope;
        }
        var parent_frame = scope.get('parent.frame');
        return parent_frame(n - 1);
    }, global_env.__env__['parent.frame'].__doc__));
    args.callee = fn;
    frame.set('arguments', args);
    return frame;
};
// -------------------------------------------------------------------------
Environment.prototype._lookup = function(symbol) {
    if (symbol instanceof LSymbol) {
        symbol = symbol.__name__;
    }
    if (symbol instanceof LString) {
        symbol = symbol.valueOf();
    }
    if (this.__env__.hasOwnProperty(symbol)) {
        return Value(this.__env__[symbol]);
    }
    if (this.__parent__) {
        return this.__parent__._lookup(symbol);
    }
};
// -------------------------------------------------------------------------
Environment.prototype.toString = function() {
    return '#<environment:' + this.__name__ + '>';
};
// -------------------------------------------------------------------------
Environment.prototype.clone = function() {
    // duplicate refs
    var env = {};
    // TODO: duplicated Symbols
    Object.keys(this.__env__).forEach(key => {
        env[key] = this.__env__[key];
    });
    return new Environment(env, this.__parent__, this.__name__);
};
// -------------------------------------------------------------------------
Environment.prototype.merge = function(env, name = 'merge') {
    typecheck('Environment::merge', env, 'environment');
    return this.inherit(name, env.__env__);
};
// -------------------------------------------------------------------------
Environment.prototype.get = function(symbol, options = {}) {
    // we keep original environment as context for bind
    // so print will get user stdout
    typecheck('Environment::get', symbol, ['symbol', 'string']);
    const { throwError = true } = options;
    var name = symbol;
    if (name instanceof LSymbol || name instanceof LString) {
        name = name.valueOf();
    }
    var value = this._lookup(name);
    if (value instanceof Value) {
        if (Value.isUndefined(value)) {
            return undefined;
        }
        return patch_value(value.valueOf());
    }
    var parts;
    if (symbol instanceof LSymbol && symbol[LSymbol.object]) {
        // dot notation symbols from syntax-rules that are gensyms
        parts = symbol[LSymbol.object];
    } else if (typeof name === 'string') {
        parts = name.split('.').filter(Boolean);
    }
    if (parts && parts.length > 0) {
        var [first, ...rest] = parts;
        value = this._lookup(first);
        if (rest.length) {
            try {
                if (value instanceof Value) {
                    value = value.valueOf();
                } else {
                    value = get(root, first);
                    if (is_function(value)) {
                        value = unbind(value);
                    }
                }
                if (typeof value !== 'undefined') {
                    // object accessor
                    return get(value, ...rest);
                }
            } catch (e) {
                throw e;
            }
        } else if (value instanceof Value) {
            return patch_value(value.valueOf());
        }
        value = get(root, name);
    }
    if (typeof value !== 'undefined') {
        return value;
    }
    if (throwError) {
        throw new Error("Unbound variable `" + name.toString() + "'");
    }
};
// -------------------------------------------------------------------------
Environment.prototype.set = function(name, value, doc = null) {
    typecheck('Environment::set', name, ['string', 'symbol']);
    if (LNumber.isNumber(value)) {
        value = LNumber(value);
    }
    if (name instanceof LSymbol) {
        name = name.__name__;
    }
    if (name instanceof LString) {
        name = name.valueOf();
    }
    this.__env__[name] = value;
    if (doc) {
        this.doc(name, doc, true);
    }
    return this;
};
// -------------------------------------------------------------------------
// for internal use only
// -------------------------------------------------------------------------
Environment.prototype.constant = function(name, value) {
    if (this.__env__.hasOwnProperty(name)) {
        throw new Error(`Environment::constant: ${name} already exists`);
    }
    if (arguments.length === 1 && is_plain_object(arguments[0])) {
        var obj = arguments[0];
        Object.keys(obj).forEach(key => {
            this.constant(name, obj[key]);
        });
    } else {
        Object.defineProperty(this.__env__, name, {
            value,
            enumerable: true
        });
    }
    return this;
};
// -------------------------------------------------------------------------
Environment.prototype.has = function(name) {
    return this.__env__.hasOwnProperty(name);
};
// -------------------------------------------------------------------------
Environment.prototype.ref = function(name) {
    var env = this;
    while (true) {
        if (!env) {
            break;
        }
        if (env.has(name)) {
            return env;
        }
        env = env.__parent__;
    }
};
// -------------------------------------------------------------------------
Environment.prototype.parents = function() {
    var env = this;
    var result = [];
    while (env) {
        result.unshift(env);
        env = env.__parent__;
    }
    return result;
};
// -------------------------------------------------------------------------------
var native_lambda = parse(tokenize(`(lambda ()
                                      "[native code]"
                                      (throw "Invalid Invocation"))`))[0];
// -------------------------------------------------------------------------------
var get = doc('get', function get(object, ...args) {
    var value;
    var len = args.length;
    while (args.length) {
        // if arg is symbol someone probably want to get __fn__ from binded function
        if (is_function(object) && typeof args[0] !== 'symbol') {
            object = unbind(object);
        }
        var arg = args.shift();
        var name = unbox(arg);
        // the value was set to false to prevent resolving
        // by Real Promises #153
        if (name === 'then' && object instanceof QuotedPromise) {
            value = QuotedPromise.prototype.then;
        } else if (name === '__code__' && is_function(object) &&
                   typeof object.__code__ === 'undefined') {
            value = native_lambda;
        } else {
            value = object[name];
        }
        if (typeof value === 'undefined') {
            if (args.length) {
                throw new Error(`Try to get ${args[0]} from undefined`);
            }
            return value;
        } else {
            var context;
            if (args.length - 1 < len) {
                context = object;
            }
            value = patch_value(value, context);
        }
        object = value;
    }
    return value;
}, `(. obj . args)
    (get obj . args)

    Function use object as base and keep using arguments to get the
    property of JavaScript object. Arguments need to be a strings.
    e.g. \`(. console "log")\` if you use any function inside LIPS is
    will be weakly bind (can be rebind), so you can call this log function
    without problem unlike in JavaScript when you use
    \`var log = console.log\`.
    \`get\` is an alias because . don't work in every place, e.g. you can't
    pass it as argument.`);

export { Environment, get };
