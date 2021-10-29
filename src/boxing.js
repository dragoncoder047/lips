/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
// ----------------------------------------------------------------------
function unbox(object) {
    var lips_type = [LString, LCharacter, LNumber].some(x => object instanceof x);
    if (lips_type) {
        return object.valueOf();
    }
    if (object instanceof Array) {
        return object.map(unbox);
    }
    if (object instanceof QuotedPromise) {
        delete object.then;
    }
    if (is_plain_object(object)) {
        return map_object(object, unbox);
    }
    return object;
}

// ----------------------------------------------------------------------
function box(object) {
    // we only need to box lips data, arrays and object don't need
    // to be boxed, values from objects will be boxed when accessed
    switch (typeof object) {
        case 'string':
            return LString(object);
        case 'bigint':
            return LNumber(object);
        case 'number':
            if (Number.isNaN(object)) {
                return nan;
            } else {
                return LNumber(object);
            }
    }
    return object;
}


export { box, unbox };
