/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol */
import LString from './LString.js';
import { hidden_prop } from './utils.js';

// ----------------------------------------------------------------------
function LSymbol(name) {
    if (typeof this !== 'undefined' && this.constructor !== LSymbol ||
        typeof this === 'undefined') {
        return new LSymbol(name);
    }
    if (name instanceof LString) {
        name = name.valueOf();
    }
    if (LSymbol.list[name] instanceof LSymbol) {
        return LSymbol.list[name];
    }
    this.__name__ = name;
    if (typeof name === 'string') {
        LSymbol.list[name] = this;
    }
}
LSymbol.list = {};
LSymbol.literal = Symbol.for('__literal__');
LSymbol.object = Symbol.for('__object__');
// ----------------------------------------------------------------------
LSymbol.is = function(symbol, name) {
    return symbol instanceof LSymbol &&
        ((name instanceof LSymbol && symbol.__name__ === name.__name__) ||
         (typeof name === 'string' && symbol.__name__ === name) ||
         (name instanceof RegExp && name.test(symbol.__name__)));
};
// ----------------------------------------------------------------------
LSymbol.prototype.toString = function(quote) {
    //return '#<symbol \'' + this.name + '\'>';
    if (is_symbol(this.__name__)) {
        return symbol_to_string(this.__name__);
    }
    var str = this.valueOf();
    // those special characters can be normal symbol when printed
    if (quote && str.match(/(^;|[\s()[\]'])/)) {
        return `|${str}|`;
    }
    return str;
};
LSymbol.prototype.literal = function() {
    if (this.is_gensym()) {
        return this[LSymbol.literal];
    }
    return this.valueOf();
};
LSymbol.prototype.serialize = function() {
    if (LString.isString(this.__name__)) {
        return this.__name__;
    }
    return [symbol_to_string(this.__name__)];
};
LSymbol.prototype.valueOf = function() {
    return this.__name__.valueOf();
};
// -------------------------------------------------------------------------
LSymbol.prototype.is_gensym = function() {
    return is_gensym(this.__name__);
};
// -------------------------------------------------------------------------
function symbol_to_string(obj) {
    return obj.toString().replace(/^Symbol\(([^)]+)\)/, '$1');
}
// -------------------------------------------------------------------------
function is_gensym(symbol) {
    if (typeof symbol === 'symbol') {
        return !!symbol.toString().match(/^Symbol\(#:/);
    }
    return false;
}
// -------------------------------------------------------------------------
var gensym = (function() {
    var count = 0;
    function with_props(name, sym) {
        var symbol = new LSymbol(sym);
        hidden_prop(symbol, '__literal__', name);
        return symbol;
    }
    return function(name = null) {
        if (name instanceof LSymbol) {
            if (name.is_gensym()) {
                return name;
            }
            name = name.valueOf();
        }
        if (is_gensym(name)) {
            // don't do double gynsyms in nested syntax-rules
            return LSymbol(name);
        }
        // use ES6 symbol as name for lips symbol (they are unique)
        if (name !== null) {
            return with_props(name, Symbol(`#:${name}`));
        }
        count++;
        return with_props(count, Symbol(`#:g${count}`));
    };
})();
// ----------------------------------------------------------------------
// detect if object is ES6 Symbol that work with polyfills
// ----------------------------------------------------------------------
function is_symbol(x) {
    return typeof x === 'symbol' ||
        typeof x === 'object' &&
        Object.prototype.toString.call(x) === '[object Symbol]';
}

export { gensym, symbol_to_string, LSymbol, is_symbol };
