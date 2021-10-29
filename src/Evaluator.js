/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol */
import { is_bound, is_object_bound, is_port_method } from './typechecking.js';
import { is_lips_context } from './lips.js';
import {
    __data__,
    type,
    is_null,
    is_native_function,
    is_raw_lambda,
    is_callable,
    is_lips_function,
    is_array_method,
    is_function,
    is_continuation
} from './typechecking.js';
import { unbox, box } from './boxing.js';
import { QuotedPromise, unpromise, resolve_promises, is_promise } from './Promises.js';
import { Pair, nil, markCycles } from './Pair.js';
import { parse } from './Parser.js';
import { noop, quote, unbind, hidden_prop } from './utils.js';
import { global_env, user_env } from './CoreLibrary.js';
import { Macro, Syntax } from './Macro.js';
import { LSymbol } from './LSymbol.js';
import { LNumber } from './Numbers.js';
import LString from './LString.js';

// -------------------------------------------------------------------------
function self_evaluated(obj) {
    var type = typeof obj;
    return ['string', 'function'].includes(type) ||
        typeof obj === 'symbol' ||
        obj instanceof QuotedPromise ||
        obj instanceof LSymbol ||
        obj instanceof LNumber ||
        obj instanceof LString ||
        obj instanceof RegExp;
}

// -----------------------------------------------------------------------------
const compile = exec_collect(function(code) {
    return code;
});

// -----------------------------------------------------------------------------
const exec = exec_collect(function(code, value) {
    return value;
});

// -----------------------------------------------------------------------------
function exec_collect(collect_callback) {
    return async function exec_lambda(arg, env, dynamic_scope) {
        if (dynamic_scope === true) {
            env = dynamic_scope = env || user_env;
        } else if (env === true) {
            env = dynamic_scope = user_env;
        } else {
            env = env || user_env;
        }
        var results = [];
        var input = Array.isArray(arg) ? arg : parse(arg);
        for await (let code of input) {
            const value = evaluate(code, {
                env,
                dynamic_scope,
                error: (e, code) => {
                    if (e && e.message) {
                        if (e.message.match(/^Error:/)) {
                            var re = /^(Error:)\s*([^:]+:\s*)/;
                            // clean duplicated Error: added by JS
                            e.message = e.message.replace(re, '$1 $2');
                        }
                        if (code) {
                            // LIPS stack trace
                            if (!(e.__code__ instanceof Array)) {
                                e.__code__ = [];
                            }
                            e.__code__.push(code.toString(true));
                        }
                    }
                    throw e;
                }
            });
            if (!is_promise(value)) {
                results.push(collect_callback(code, value));
            } else {
                results.push(collect_callback(code, await value));
            }
        }
        return results;
    };
}

// -----------------------------------------------------------------------------
function evaluate(code, { env, dynamic_scope, error = noop } = {}) {
    try {
        if (dynamic_scope === true) {
            env = dynamic_scope = env || global_env;
        } else if (env === true) {
            env = dynamic_scope = global_env;
        } else {
            env = env || global_env;
        }
        var eval_args = { env, dynamic_scope, error };
        var value;
        if (is_null(code)) {
            return code;
        }
        if (code instanceof LSymbol) {
            return env.get(code);
        }
        if (!(code instanceof Pair)) {
            return code;
        }
        var first = code.car;
        var rest = code.cdr;
        if (first instanceof Pair) {
            value = resolve_promises(evaluate(first, eval_args));
            if (is_promise(value)) {
                return value.then((value) => {
                    return evaluate(new Pair(value, code.cdr), eval_args);
                });
                // else is later in code
            } else if (!is_callable(value)) {
                throw new Error(
                    type(value) + ' ' + env.get('repr')(value) +
                        ' is not callable while evaluating ' + code.toString()
                );
            }
        }
        if (first instanceof LSymbol) {
            value = env.get(first);
        } else if (is_function(first)) {
            value = first;
        }
        var result;
        if (value instanceof Syntax) {
            result = evaluate_syntax(value, code, eval_args);
        } else if (value instanceof Macro) {
            result = evaluate_macro(value, rest, eval_args);
        } else if (is_function(value)) {
            result = apply(value, rest, eval_args);
        } else if (is_continuation(value)) {
            result = value.invoke();
        } else if (code instanceof Pair) {
            value = first && first.toString();
            throw new Error(`${type(first)} ${value} is not a function`);
        } else {
            return code;
        }
        // escape promise feature #54
        var __promise__ = env.get(Symbol.for('__promise__'), { throwError: false });
        if (__promise__ === true && is_promise(result)) {
            // fix #139 evaluate the code inside the promise that is not data.
            // When promise is not quoted it happen automatically, when returing
            // promise from evaluate.
            result = result.then(result => {
                if (result instanceof Pair && !value[__data__]) {
                    return evaluate(result, eval_args);
                }
                return result;
            });
            return new QuotedPromise(result);
        }
        return result;
    } catch (e) {
        error && error.call(env, e, code);
    }
}


// -----------------------------------------------------------------------------
function evaluate_syntax(macro, code, eval_args) {
    var value = macro.invoke(code, eval_args);
    return unpromise(resolve_promises(value), function(value) {
        if (value instanceof Pair) {
            value.markCycles();
        }
        return quote(value);
    });
}

// -----------------------------------------------------------------------------
function evaluate_macro(macro, code, eval_args) {
    function finalize(result) {
        if (result instanceof Pair) {
            result.markCycles();
            return result;
        }
        return quote(result);
    }
    var value = macro.invoke(code, eval_args);
    return unpromise(resolve_promises(value), function ret(value) {
        if (!value || value && value[__data__] || self_evaluated(value)) {
            return value;
        } else {
            return unpromise(evaluate(value, eval_args), finalize);
        }
    });
}

// -----------------------------------------------------------------------------
function evaluate_args(rest, { env, dynamic_scope, error }) {
    var args = [];
    var node = rest;
    markCycles(node);
    function next() {
        return args;
    }
    return (function loop() {
        if (node instanceof Pair) {
            var arg = evaluate(node.car, { env, dynamic_scope, error });
            if (dynamic_scope) {
                arg = unpromise(arg, arg => {
                    if (is_native_function(arg)) {
                        return arg.bind(dynamic_scope);
                    }
                    return arg;
                });
            }
            return unpromise(resolve_promises(arg), function(arg) {
                args.push(arg);
                if (node.haveCycles('cdr')) {
                    return next();
                }
                node = node.cdr;
                return loop();
            });
        } else if (node === nil) {
            return next();
        } else {
            throw new Error('Syntax Error: improper list found in apply');
        }
    })();
}

// -----------------------------------------------------------------------------
function prepare_fn_args(fn, args) {
    if (is_bound(fn) && !is_object_bound(fn) &&
        (!is_lips_context(fn) || is_port_method(fn))) {
        args = args.map(unbox);
    }
    if (!is_raw_lambda(fn) &&
        args.some(is_lips_function) &&
        !is_lips_function(fn) &&
        !is_array_method(fn)) {
        // we unbox values from callback functions #76
        // calling map on array should not unbox the value
        var result = [], i = args.length;
        while (i--) {
            let arg = args[i];
            if (is_lips_function(arg)) {
                var wrapper = function(...args) {
                    return unpromise(arg.apply(this, args), unbox);
                };
                // make wrapper work like output of bind
                hidden_prop(wrapper, '__bound__', true);
                hidden_prop(wrapper, '__fn__', arg);
                // copy prototype from function to wrapper
                // so this work when calling new from JavaScript
                // case of Preact that pass LIPS class as argument
                // to h function
                wrapper.prototype = arg.prototype;
                result[i] = wrapper;
            } else {
                result[i] = arg;
            }
        }
        args = result;
    }
    return args;
}


// -----------------------------------------------------------------------------
function apply(fn, args, { env, dynamic_scope, error = () => {} } = {}) {
    args = evaluate_args(args, { env, dynamic_scope, error });
    return unpromise(args, function(args) {
        if (is_raw_lambda(fn)) {
            // lambda need environment as context
            // normal functions are bound to their contexts
            fn = unbind(fn);
        }
        args = prepare_fn_args(fn, args);
        var _args = args.slice();
        var scope = (dynamic_scope || env).newFrame(fn, _args);
        var result = resolve_promises(fn.apply(scope, args));
        return unpromise(result, (result) => {
            if (result instanceof Pair) {
                result.markCycles();
                return quote(result);
            }
            return box(result);
        }, error);
    });
}

export { compile, exec, evaluate, prepare_fn_args };
