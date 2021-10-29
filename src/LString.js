/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
import { typecheck } from './typechecking.js';
import LCharacter from './LCharacter.js';
// -----------------------------------------------------------------------------
// :: String wrapper that handle copy and in place change
// -----------------------------------------------------------------------------
function LString(string) {
    if (typeof this !== 'undefined' && !(this instanceof LString) ||
        typeof this === 'undefined') {
        return new LString(string);
    }
    if (string instanceof Array) {
        this.__string__ = string.map((x, i) => {
            typecheck('LString', x, 'character', i + 1);
            return x.toString();
        }).join('');
    } else {
        this.__string__ = string.valueOf();
    }
}

// -----------------------------------------------------------------------------
{
    const ignore = ['length', 'constructor'];
    const _keys = Object.getOwnPropertyNames(String.prototype).filter(name => {
        return !ignore.includes(name);
    });
    const wrap = (fn) => function(...args) {
        return fn.apply(this.__string__, args);
    };
    for (let key of _keys) {
        LString.prototype[key] = wrap(String.prototype[key]);
    }
}

// -----------------------------------------------------------------------------
LString.prototype.serialize = function() {
    return this.valueOf();
};

// -----------------------------------------------------------------------------
LString.isString = function(x) {
    return x instanceof LString || typeof x === 'string';
};

// -----------------------------------------------------------------------------
LString.prototype.get = function(n) {
    typecheck('LString::get', n, 'number');
    return Array.from(this.__string__)[n.valueOf()];
};

// -----------------------------------------------------------------------------
LString.prototype.cmp = function(string) {
    typecheck('LString::cmp', string, 'string');
    var a = this.valueOf();
    var b = string.valueOf();
    if (a < b) {
        return -1;
    } else if (a === b) {
        return 0;
    } else {
        return 1;
    }
};

// -----------------------------------------------------------------------------
LString.prototype.lower = function() {
    return LString(this.__string__.toLowerCase());
};

// -----------------------------------------------------------------------------
LString.prototype.upper = function() {
    return LString(this.__string__.toUpperCase());
};

// -----------------------------------------------------------------------------
LString.prototype.set = function(n, char) {
    typecheck('LString::set', n, 'number');
    typecheck('LString::set', char, ['string', 'character']);
    n = n.valueOf();
    if (char instanceof LCharacter) {
        char = char.__char__;
    }
    var string = [];
    if (n > 0) {
        string.push(this.__string__.substring(0, n));
    }
    string.push(char);
    if (n < this.__string__.length - 1) {
        string.push(this.__string__.substring(n + 1));
    }
    this.__string__ = string.join('');
};

// -----------------------------------------------------------------------------
Object.defineProperty(LString.prototype, "length", {
    get: function() {
        return this.__string__.length;
    }
});

// -----------------------------------------------------------------------------
LString.prototype.clone = function() {
    return LString(this.valueOf());
};

// -----------------------------------------------------------------------------
LString.prototype.fill = function(char) {
    typecheck('LString::fill', char, ['string', 'character']);
    if (char instanceof LCharacter) {
        char = char.toString();
    }
    var len = this.__string__.length;
    this.__string__ = new Array(len + 1).join(char);
};

export default LString;
