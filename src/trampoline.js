/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */

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

export { trampoline, Thunk };
