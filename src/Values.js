/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
// -------------------------------------------------------------------------
// :: different object than value used as object for (values)
// -------------------------------------------------------------------------
function Values(values) {
    if (values.length) {
        if (values.length === 1) {
            return values[0];
        }
    }
    if (typeof this !== 'undefined' && !(this instanceof Values) ||
        typeof this === 'undefined') {
        return new Values(values);
    }
    this.__values__ = values;
}
Values.prototype.toString = function() {
    return this.__values__.map(x => toString(x)).join('\n');
};
Values.prototype.valueOf = function() {
    return this.__values__;
};

export default Values;
