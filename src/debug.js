/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
import { user_env, global_env } from './CoreLibrary.js';
import { is_promise } from './Promises.js';
// -------------------------------------------------------------------------
/* istanbul ignore next */
function log(x, regex = null) {
    var literal = arguments[1] === true;
    function msg(x) {
        if (!is_debug()) {
            return;
        }
        var value = global_env.get('repr')(x);
        if (regex === null || regex instanceof RegExp && regex.test(value)) {
            console.log(global_env.get('type')(x) + ": " + value);
        }
        if (literal) {
            console.log(x);
        }
    }
    if (is_promise(x)) {
        x.then(msg);
    } else {
        msg(x);
    }
    return x;
}

// ----------------------------------------------------------------------
/* istanbul ignore next */
function is_debug() {
    return user_env && user_env.get('DEBUG', { throwError: false });
}
// ----------------------------------------------------------------------
// :: debug function that can be used with JSON.stringify
// :: that will show symbols
// ----------------------------------------------------------------------
/* istanbul ignore next */
function symbolize(obj) {
    if (obj && typeof obj === 'object') {
        var result = {};
        const symbols = Object.getOwnPropertySymbols(obj);
        symbols.forEach((key) => {
            const name = key.toString()
                .replace(/Symbol\(([^)]+)\)/, '$1');
            result[name] = toString(obj[key]);
        });
        const props = Object.getOwnPropertyNames(obj);
        props.forEach(key => {
            const o = obj[key];
            if (o && typeof o === 'object' && o.constructor === Object) {
                result[key] = symbolize(o);
            } else {
                result[key] = toString(o);
            }
        });
        return result;
    }
    return obj;
}

export { log, is_debug, symbolize };
