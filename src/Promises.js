/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
import { is_plain_object, is_function, type, __data__ } from './typechecking.js';
import { read_only } from './utils.js';
import { Pair } from './Pair.js';
import Value from './Value.js';

// ----------------------------------------------------------------------
// class used to escape promises feature #54
// ----------------------------------------------------------------------
function QuotedPromise(promise) {
    var internal = {
        pending: true,
        rejected: false,
        fulfilled: false,
        reason: undefined,
        type: undefined
    };
    // then added to __promise__ is needed otherwise rejection
    // will give UnhandledPromiseRejectionWarning in Node.js
    promise = promise.then(v => {
        internal.type = type(v);
        internal.fulfilled = true;
        internal.pending = false;
        return v;
    });
    // promise without catch, used for valueOf - for rejecting
    // that should throw an error when used with await
    read_only(this, '_promise', promise, { hidden: true });
    if (is_function(promise.catch)) {
        // prevent exception on unhandled rejecting when using
        // '>(Promise.reject (new Error "zonk")) in REPL
        promise = promise.catch((err) => {
            internal.rejected = true;
            internal.pending = false;
            internal.reason = err;
        });
    }
    Object.keys(internal).forEach(name => {
        Object.defineProperty(this, `__${name}__`, {
            enumerable: true,
            get: () => internal[name]
        });
    });
    read_only(this, '__promise__', promise);
    // prevent resolving when returned from real promise #153
    this.then = false;
}
// ----------------------------------------------------------------------
QuotedPromise.prototype.then = function(fn) {
    return new QuotedPromise(this.valueOf().then(fn));
};
// ----------------------------------------------------------------------
QuotedPromise.prototype.catch = function(fn) {
    return new QuotedPromise(this.valueOf().catch(fn));
};
// ----------------------------------------------------------------------
QuotedPromise.prototype.valueOf = function() {
    if (!this._promise) {
        throw new Error('QuotedPromise: invalid promise created');
    }
    return this._promise;
};
// ----------------------------------------------------------------------
QuotedPromise.prototype.toString = function() {
    if (this.__pending__) {
        return QuotedPromise.pending_str;
    }
    if (this.__rejected__) {
        return QuotedPromise.rejected_str;
    }
    return `#<js-promise resolved (${this.__type__})>`;
};
QuotedPromise.pending_str = '#<js-promise (pending)>';
QuotedPromise.rejected_str = '#<js-promise (rejected)>';

// -------------------------------------------------------------------------
// :: Unquote is used for multiple backticks and unquote
// -------------------------------------------------------------------------
function Unquote(value, count, max) {
    this.value = value;
    this.count = count;
    this.max = max;
}
Unquote.prototype.toString = function() {
    return '#<unquote[' + this.count + '] ' + this.value + '>';
};

// ----------------------------------------------------------------------
function is_promise(o) {
    if (o instanceof QuotedPromise) {
        return false;
    }
    if (o instanceof Promise) {
        return true;
    }
    return o && is_function(o.then);
}

// ----------------------------------------------------------------------
function escape_quoted_promises(array) {
    // using loops for performance
    var escaped = new Array(array.length), i = array.length;
    while (i--) {
        const value = array[i];
        if (value instanceof QuotedPromise) {
            escaped[i] = new Value(value);
        } else {
            escaped[i] = value;
        }
    }
    return escaped;
}

// ----------------------------------------------------------------------
function unescape_quoted_promises(array) {
    var unescaped = new Array(array.length), i = array.length;
    while (i--) {
        var value = array[i];
        if (value instanceof Value) {
            unescaped[i] = value.valueOf();
        } else {
            unescaped[i] = value;
        }
    }
    return unescaped;
}


// ----------------------------------------------------------------------
function unpromise(value, fn = x => x, error = null) {
    if (is_promise(value)) {
        var ret = value.then(fn);
        if (error === null) {
            return ret;
        } else {
            return ret.catch(error);
        }
    }
    if (value instanceof Array) {
        return unpromise_array(value, fn, error);
    }
    if (is_plain_object(value)) {
        return unpromise_object(value, fn, error);
    }
    return fn(value);
}

// ----------------------------------------------------------------------
function unpromise_array(array, fn, error) {
    if (array.find(is_promise)) {
        return unpromise(promise_all(array), (arr) => {
            if (Object.isFrozen(array)) {
                Object.freeze(arr);
            }
            return arr;
        }, error);
    }
    return fn(array);
}

// ----------------------------------------------------------------------
function unpromise_object(object, fn, error) {
    const keys = Object.keys(object);
    const values = [], anyPromise = [];
    let i = keys.length;
    while (i--) {
        const key = keys[i];
        const value = object[key];
        values[i] = value;
        if (is_promise(value)) {
            anyPromise.push(value);
        }
    }
    if (anyPromise.length) {
        return unpromise(promise_all(values), (values) => {
            const result = {};
            values.forEach((value, i) => {
                const key = keys[i];
                result[key] = value;
            });
            if (Object.isFrozen(object)) {
                Object.freeze(result);
            }
            return result;
        }, error);
    }
    return fn(object);
}

// ----------------------------------------------------------------------
// wrapper over Promise.all that ignore quoted promises
// ----------------------------------------------------------------------
function promise_all(arg) {
    if (Array.isArray(arg)) {
        return Promise.all(escape_quoted_promises(arg))
            .then(unescape_quoted_promises);
    }
    return arg;
}

// -------------------------------------------------------------------------
// :; wrap tree of Promises with single Promise or return argument as is
// :: if tree have no Promises
// -------------------------------------------------------------------------
function resolve_promises(arg) {
    var promises = [];
    traverse(arg);
    if (promises.length) {
        return resolve(arg);
    }
    return arg;
    function traverse(node) {
        if (is_promise(node)) {
            promises.push(node);
        } else if (node instanceof Pair) {
            if (!node.haveCycles('car')) {
                traverse(node.car);
            }
            if (!node.haveCycles('cdr')) {
                traverse(node.cdr);
            }
        } else if (node instanceof Array) {
            node.forEach(traverse);
        }
    }
    async function promise(node) {
        var pair = new Pair(
            node.haveCycles('car') ? node.car : await resolve(node.car),
            node.haveCycles('cdr') ? node.cdr : await resolve(node.cdr)
        );
        if (node[__data__]) {
            pair[__data__] = true;
        }
        return pair;
    }
    function resolve(node) {
        if (node instanceof Array) {
            return promise_all(node.map(resolve));
        }
        if (node instanceof Pair && promises.length) {
            return promise(node);
        }
        return node;
    }
}

// ----------------------------------------------------------------------
export {
    QuotedPromise,
    Unquote,
    unpromise,
    is_promise,
    escape_quoted_promises,
    unescape_quoted_promises,
    promise_all,
    __data__,
    resolve_promises
};
