/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
// -------------------------------------------------------------------------
// :: Continuations object from call/cc
// -------------------------------------------------------------------------
class Continuation {
    constructor(k) {
        this.__value__ = k;
    }
    invoke() {
        if (this.__value__ === null) {
            throw new Error('Continuations are not implemented yet');
        }
    }
    toString() {
        return '#<Continuation>';
    }
}

export default Continuation;
