/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */

import { __context__, is_function } from './typechecking.js';

const lips = {};

// ----------------------------------------------------------------------
function is_lips_context(obj) {
    if (is_function(obj)) {
        var context = obj[__context__];
        if (context && (context === lips ||
                        (context.constructor &&
                         context.constructor.__class__))) {
            return true;
        }
    }
    return false;
}

export { is_lips_context, lips };
