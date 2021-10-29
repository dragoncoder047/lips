/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
// -------------------------------------------------------------------------
// value returned in lookup if found value in env and in promise_all
// -------------------------------------------------------------------------
function Value(value) {
    if (typeof this !== 'undefined' && !(this instanceof Value) ||
        typeof this === 'undefined') {
        return new Value(value);
    }
    this.value = value;
}
// -------------------------------------------------------------------------
Value.isUndefined = function(x) {
    return x instanceof Value && typeof x.value === 'undefined';
};
// -------------------------------------------------------------------------
Value.prototype.valueOf = function() {
    return this.value;
};

export default Value;
