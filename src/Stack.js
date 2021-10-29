/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
function Stack() {
    this.data = [];
}
Stack.prototype.push = function(item) {
    this.data.push(item);
};
Stack.prototype.top = function() {
    return this.data[this.data.length - 1];
};
Stack.prototype.pop = function() {
    return this.data.pop();
};
Stack.prototype.is_empty = function() {
    return !this.data.length;
};

export default Stack;
