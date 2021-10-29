/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol, Set */
import {
    type,
    typecheck,
    is_atom,
    is_plain_object,
    __data__
} from './typechecking.js';
import { Pair, nil } from './Pair.js';
import { LNumber } from './Numbers.js';
import { trim_lines, same_atom, hidden_prop } from './utils.js';
import { evaluate } from './Evaluator.js';
import { unpromise, promise_all, is_promise } from './Promises.js';
import { Environment } from './Environment.js';
import { global_env } from './CoreLibrary.js';
import { LSymbol, gensym } from './LSymbol.js';
import { is_debug, log, symbolize } from './debug.js';
import LString from './LString.js';

// -----------------------------------------------------------------------------
// :: Macro constructor
// -----------------------------------------------------------------------------
function Macro(name, fn, doc, dump) {
    if (typeof this !== 'undefined' && this.constructor !== Macro ||
        typeof this === 'undefined') {
        return new Macro(name, fn);
    }
    typecheck('Macro', name, 'string', 1);
    typecheck('Macro', fn, 'function', 2);
    if (doc) {
        if (dump) {
            this.__doc__ = doc;
        } else {
            this.__doc__ = trim_lines(doc);
        }
    }
    this.__name__ = name;
    this.__fn__ = fn;
}

// -----------------------------------------------------------------------------
Macro.defmacro = function(name, fn, doc, dump) {
    var macro = new Macro(name, fn, doc, dump);
    macro.__defmacro__ = true;
    return macro;
};

// -----------------------------------------------------------------------------
Macro.prototype.invoke = function(code, { env, dynamic_scope, error }, macro_expand) {
    var args = {
        dynamic_scope,
        error,
        macro_expand
    };
    var result = this.__fn__.call(env, code, args, this.__name__);
    return result;
    //return macro_expand ? quote(result) : result;
};

// -----------------------------------------------------------------------------
Macro.prototype.toString = function() {
    return `#<macro:${this.__name__}>`;
};

// -----------------------------------------------------------------------------
const recur_guard = -10000;
function macro_expand(single) {
    return async function(code, args) {
        var env = args['env'] = this;
        var bindings = [];
        var let_macros = ['let', 'let*', 'letrec'];
        var lambda = global_env.get('lambda');
        var define = global_env.get('define');
        function is_let_macro(symbol) {
            var name = symbol.valueOf();
            return let_macros.includes(name);
        }
        function is_procedure(value, node) {
            return value === define && node.cdr.car instanceof Pair;
        }
        function is_lambda(value) {
            return value === lambda;
        }
        function proc_bindings(node) {
            var names = [];
            while (true) {
                if (node !== nil) {
                    if (node instanceof LSymbol) {
                        names.push(node.valueOf());
                        break;
                    }
                    names.push(node.car.valueOf());
                    node = node.cdr;
                } else {
                    break;
                }
            }
            return [...bindings, ...names];
        }
        function let_binding(node) {
            return [...bindings, ...node.to_array(false).map(function(node) {
                if (node instanceof Pair) {
                    return node.car.valueOf();
                }
                throw new Error('macroexpand: Invalid let binding');
            })];
        }
        function is_macro(name, value) {
            return value instanceof Macro &&
                value.__defmacro__ &&
                !bindings.includes(name);
        }
        async function expand_let_binding(node, n) {
            if (node === nil) {
                return nil;
            }
            var pair = node.car;
            return new Pair(
                new Pair(
                    pair.car,
                    await traverse(pair.cdr, n, env)
                ),
                await expand_let_binding(node.cdr)
            );
        }
        async function traverse(node, n, env) {
            if (node instanceof Pair && node.car instanceof LSymbol) {
                if (node[__data__]) {
                    return node;
                }
                var name = node.car.valueOf();
                var value = env.get(node.car, { throwError: false });
                var is_let = is_let_macro(node.car);

                var is_binding = is_let ||
                    is_procedure(value, node) ||
                    is_lambda(value);

                if (is_binding && node.cdr.car instanceof Pair) {
                    var second;
                    if (is_let) {
                        bindings = let_binding(node.cdr.car);
                        second = await expand_let_binding(node.cdr.car, n);
                    } else {
                        bindings = proc_bindings(node.cdr.car);
                        second = node.cdr.car;
                    }
                    return new Pair(
                        node.car,
                        new Pair(
                            second,
                            await traverse(node.cdr.cdr, n, env)
                        )
                    );
                } else if (is_macro(name, value)) {
                    var code = value instanceof Syntax ? node : node.cdr;
                    var result = await value.invoke(code, { ...args, env }, true);
                    if (value instanceof Syntax) {
                        const { expr, scope } = result;
                        if (expr instanceof Pair) {
                            if (n !== -1 && n <= 1 || n < recur_guard) {
                                return expr;
                            }
                            if (n !== -1) {
                                n = n - 1;
                            }
                            return traverse(expr, n, scope);
                        }
                        result = expr;
                    }
                    if (result instanceof LSymbol) {
                        return quote(result);
                    }
                    if (result instanceof Pair) {
                        if (n !== -1 && n <= 1 || n < recur_guard) {
                            return result;
                        }
                        if (n !== -1) {
                            n = n - 1;
                        }
                        return traverse(result, n, env);
                    }
                    if (is_atom(result)) {
                        return result;
                    }
                }
            }
            // TODO: CYCLE DETECT
            var car = node.car;
            if (car instanceof Pair) {
                car = await traverse(car, n, env);
            }
            var cdr = node.cdr;
            if (cdr instanceof Pair) {
                cdr = await traverse(cdr, n, env);
            }
            var pair = new Pair(car, cdr);
            return pair;
        }
        //var this.__code__ = code;
        if (code.cdr instanceof Pair && LNumber.isNumber(code.cdr.car)) {
            return quote((await traverse(code, code.cdr.car.valueOf(), env)).car);
        }
        if (single) {
            return quote((await traverse(code, 1, env)).car);
        }
        return quote((await traverse(code, -1, env)).car);
    };
}

// -----------------------------------------------------------------------------
// TODO: Don't put Syntax as Macro they are not runtime
// -----------------------------------------------------------------------------
function Syntax(fn, env) {
    this.__env__ = env;
    this.__fn__ = fn;
    // allow macroexpand
    this.__defmacro__ = true;
}
Syntax.__merge_env__ = Symbol.for('merge');

// -----------------------------------------------------------------------------
Syntax.prototype = Object.create(Macro.prototype);

// -----------------------------------------------------------------------------
Syntax.prototype.invoke = function(code, { error, env }, macro_expand) {
    var args = {
        error,
        env,
        dynamic_scope: this.__env__,
        macro_expand
    };
    return this.__fn__.call(env, code, args, this.__name__ || 'syntax');
};

// -----------------------------------------------------------------------------
Syntax.prototype.constructor = Syntax;

// -----------------------------------------------------------------------------
Syntax.prototype.toString = function() {
    if (this.__name__) {
        return `#<syntax:${this.__name__}>`;
    }
    return '#<syntax>';
};

// -----------------------------------------------------------------------------
// :: TODO: SRFI-139
// -----------------------------------------------------------------------------
class Parameter extends Syntax {
}
Syntax.Parameter = Parameter;
// -----------------------------------------------------------------------------
// :: for usage in syntax-rule when pattern match it will return
// :: list of bindings from code that match the pattern
// :: TODO detect cycles
// -----------------------------------------------------------------------------
function extract_patterns(pattern, code, symbols, ellipsis_symbol, scope = {}) {
    var bindings = {
        '...': {
            symbols: { }, // symbols ellipsis (x ...)
            lists: [ ]
        },
        symbols: { }
    };
    const { expansion, define } = scope;
    // pattern_names parameter is used to distinguish
    // multiple matches of ((x ...) ...) agains ((1 2 3) (1 2 3))
    // in loop we add x to the list so we know that this is not
    // duplicated ellipsis symbol
    function log(x) {
        /* istanbul ignore next */
        if (is_debug()) {
            console.log(x);
        }
    }
    log(symbols);
    /* eslint-disable complexity */
    function traverse(pattern, code, pattern_names = [], ellipsis = false) {
        log({
            code: code && toString(code, true),
            pattern: pattern && toString(pattern, true)
        });
        if (is_atom(pattern) && !(pattern instanceof LSymbol)) {
            return same_atom(pattern, code);
        }
        if (pattern instanceof LSymbol &&
            symbols.includes(pattern.literal())) {
            const ref = expansion.ref(code);
            // shadowing the indentifier works only with lambda and let
            if (LSymbol.is(code, pattern)) {
                if (typeof ref === 'undefined') {
                    return true;
                }
                return ref === define || ref === global_env;
            }
            return false;
        }
        // pattern (a b (x ...)) and (x ...) match nil
        if (pattern instanceof Pair &&
            pattern.car instanceof Pair &&
            pattern.car.cdr instanceof Pair &&
            LSymbol.is(pattern.car.cdr.car, ellipsis_symbol)) {
            log('>> 0');
            if (code === nil) {
                log({ pattern: pattern.toString() });
                if (pattern.car.car instanceof LSymbol) {
                    if (pattern.car.cdr instanceof Pair &&
                        LSymbol.is(pattern.car.cdr.car, ellipsis_symbol)) {
                        let name = pattern.car.car.valueOf();
                        const last = pattern.last_pair();
                        if (LSymbol.is(last.car, ellipsis_symbol)) {
                            bindings['...'].symbols[name] = null;
                            return true;
                        } else {
                            return false;
                        }
                    }
                    let name = pattern.car.car.valueOf();
                    if (bindings['...'].symbols[name]) {
                        throw new Error('syntax: named ellipsis can only ' +
                                        'appear onces');
                    }
                    bindings['...'].symbols[name] = code;
                }
            }
        }
        if (pattern instanceof Pair &&
            pattern.cdr instanceof Pair &&
            LSymbol.is(pattern.cdr.car, ellipsis_symbol)) {
            // pattern (... ???) - SRFI-46
            if (pattern.cdr.cdr !== nil) {
                if (pattern.cdr.cdr instanceof Pair) {
                    // if we have (x ... a b) we need to remove two from the end
                    const list_len = pattern.cdr.cdr.length();
                    let code_len = code.length();
                    let list = code;
                    while (code_len - 1 > list_len) {
                        list = list.cdr;
                        code_len--;
                    }
                    const rest = list.cdr;
                    list.cdr = nil;
                    if (!traverse(pattern.cdr.cdr, rest, pattern_names, ellipsis)) {
                        return false;
                    }
                }
            }
            if (pattern.car instanceof LSymbol) {
                let name = pattern.car.__name__;
                if (bindings['...'].symbols[name] &&
                    !pattern_names.includes(name) && !ellipsis) {
                    throw new Error('syntax: named ellipsis can only appear onces');
                }
                log('>> 1');
                if (code === nil) {
                    log('>> 2');
                    if (ellipsis) {
                        log('NIL');
                        bindings['...'].symbols[name] = nil;
                    } else {
                        log('NULL');
                        bindings['...'].symbols[name] = null;
                    }
                } else if (code instanceof Pair &&
                           (code.car instanceof Pair || code.car === nil)) {
                    log('>> 3 ' + ellipsis);
                    if (ellipsis) {
                        if (bindings['...'].symbols[name]) {
                            let node = bindings['...'].symbols[name];
                            if (node === nil) {
                                node = new Pair(nil, new Pair(code, nil));
                            } else {
                                node = node.append(new Pair(code, nil));
                            }
                            bindings['...'].symbols[name] = node;
                        } else {
                            bindings['...'].symbols[name] = new Pair(code, nil);
                        }
                    } else {
                        log('>> 4');
                        bindings['...'].symbols[name] = new Pair(code, nil);
                    }
                } else {
                    log('>> 6');
                    if (code instanceof Pair) {
                        log('>> 7 ' + ellipsis);
                        pattern_names.push(name);
                        if (!bindings['...'].symbols[name]) {
                            bindings['...'].symbols[name] = new Pair(
                                code,
                                nil
                            );
                        } else {
                            const node = bindings['...'].symbols[name];
                            bindings['...'].symbols[name] = node.append(
                                new Pair(
                                    code,
                                    nil
                                )
                            );
                        }
                        log({ IIIIII: bindings['...'].symbols[name].toString() });
                    } else {
                        log('>> 8');
                        return false;
                        //bindings['...'].symbols[name] = code;
                    }
                }
                return true;
            } else if (pattern.car instanceof Pair) {
                var names = [...pattern_names];
                if (code === nil) {
                    log('>> 9');
                    bindings['...'].lists.push(nil);
                    return true;
                }
                log('>> 10');
                let node = code;
                while (node instanceof Pair) {
                    if (!traverse(pattern.car, node.car, names, true)) {
                        return false;
                    }
                    node = node.cdr;
                }
                return true;
            }
            return false;
        }
        if (pattern instanceof LSymbol) {
            if (LSymbol.is(pattern, ellipsis_symbol)) {
                throw new Error('syntax: invalid usage of ellipsis');
            }
            log('>> 11');
            const name = pattern.__name__;
            if (symbols.includes(name)) {
                return true;
            }
            log({ name, ellipsis });
            if (ellipsis) {
                bindings['...'].symbols[name] = bindings['...'].symbols[name] || [];
                bindings['...'].symbols[name].push(code);
            }
            bindings.symbols[name] = code;
            if (!bindings.symbols[name]) {
            }
            return true;
        }
        if (pattern instanceof Pair && code instanceof Pair) {
            log('>> 12');
            log({
                a: 12,
                code: code && code.toString(),
                pattern: pattern.toString()
            });
            if (code.cdr === nil) {
                // last item in in call using in recursive calls on
                // last element of the list
                // case of pattern (p . rest) and code (0)
                var rest_pattern = pattern.car instanceof LSymbol &&
                    pattern.cdr instanceof LSymbol;
                if (rest_pattern) {
                    // fix for SRFI-26 in recursive call of (b) ==> (<> . x)
                    // where <> is symbol
                    if (!traverse(pattern.car, code.car, pattern_names, ellipsis)) {
                        return false;
                    }
                    log('>> 12 | 1');
                    let name = pattern.cdr.valueOf();
                    if (!(name in bindings.symbols)) {
                        bindings.symbols[name] = nil;
                    }
                    name = pattern.car.valueOf();
                    if (!(name in bindings.symbols)) {
                        bindings.symbols[name] = code.car;
                    }
                    return true;
                }
            }
            log({
                pattern: pattern.toString(),
                code: code.toString()
            });
            // case (x y) ===> (var0 var1 ... varn) where var1 match nil
            if (pattern.cdr instanceof Pair &&
                pattern.car instanceof LSymbol &&
                pattern.cdr.cdr instanceof Pair &&
                pattern.cdr.car instanceof LSymbol &&
                LSymbol.is(pattern.cdr.cdr.car, ellipsis_symbol) &&
                pattern.cdr.cdr.cdr instanceof Pair &&
                !LSymbol.is(pattern.cdr.cdr.cdr.car, ellipsis_symbol) &&
                traverse(pattern.car, code.car, pattern_names, ellipsis) &&
                traverse(pattern.cdr.cdr.cdr, code.cdr, pattern_names, ellipsis)) {
                const name = pattern.cdr.car.__name__;
                log({
                    pattern: pattern.car.toString(),
                    code: code.car.toString(),
                    name
                });
                if (symbols.includes(name)) {
                    return true;
                }
                bindings['...'].symbols[name] = null;
                return true;
            }
            log('recur');
            if (traverse(pattern.car, code.car, pattern_names, ellipsis) &&
                traverse(pattern.cdr, code.cdr, pattern_names, ellipsis)) {
                return true;
            }
        } else if (pattern === nil && (code === nil || code === undefined)) {
            // undefined is case when you don't have body ...
            // and you do recursive call
            return true;
        } else if (pattern.car instanceof Pair &&
                   LSymbol.is(pattern.car.car, ellipsis_symbol)) {
            // pattern (...)
            throw new Error('syntax: invalid usage of ellipsis');
        } else {
            return false;
        }
    }
    /* eslint-enable complexity */
    if (traverse(pattern, code)) {
        return bindings;
    }
}

// -----------------------------------------------------------------------------
// :: This function is called after syntax-rules macro is evaluated
// :: and if there are any gensyms added by macro they need to restored
// :: to original symbols
// -----------------------------------------------------------------------------
function clear_gensyms(node, gensyms) {
    function traverse(node) {
        if (node instanceof Pair) {
            if (!gensyms.length) {
                return node;
            }
            const car = traverse(node.car);
            const cdr = traverse(node.cdr);
            // TODO: check if it's safe to modify the list
            //       some funky modify of code can happen in macro
            return new Pair(car, cdr);
        } else if (node instanceof LSymbol) {
            var replacement = gensyms.find((gensym) => {
                return gensym.gensym === node;
            });
            if (replacement) {
                return LSymbol(replacement.name);
            }
            return node;
        } else {
            return node;
        }
    }
    return traverse(node);
}

// -----------------------------------------------------------------------------
function transform_syntax(options = {}) {
    const {
        bindings,
        expr,
        scope,
        symbols,
        names,
        ellipsis: ellipsis_symbol } = options;
    var gensyms = {};
    function valid_symbol(symbol) {
        if (symbol instanceof LSymbol) {
            return true;
        }
        return ['string', 'symbol'].includes(typeof symbol);
    }
    function transform(symbol) {
        if (!valid_symbol(symbol)) {
            const t = type(symbol);
            throw new Error(`syntax: internal error, need symbol got ${t}`);
        }
        const name = symbol.valueOf();
        if (name === ellipsis_symbol) {
            throw new Error('syntax: internal error, ellipis not transformed');
        }
        // symbols are gensyms from nested syntax-rules
        var n_type = typeof name;
        if (['string', 'symbol'].includes(n_type)) {
            if (name in bindings.symbols) {
                return bindings.symbols[name];
            } else if (n_type === 'string' && name.match(/\./)) {
                // calling method on pattern symbol #83
                const parts = name.split('.');
                const first = parts[0];
                if (first in bindings.symbols) {
                    return Pair.fromArray([
                        LSymbol('.'),
                        bindings.symbols[first]
                    ].concat(parts.slice(1).map(x => LString(x))));
                }
            }
        }
        if (symbols.includes(name)) {
            return LSymbol(name);
        }
        return rename(name);
    }
    function log(x) {
        /* istanbul ignore next */
        if (is_debug()) {
            console.log(x);
        }
    }
    function rename(name) {
        if (!gensyms[name]) {
            var ref = scope.ref(name);
            const gensym_name = gensym(name);
            if (ref) {
                const value = scope.get(name);
                scope.set(gensym_name, value);
            } else {
                const value = scope.get(name, { throwError: false });
                // value is not in scope, but it's JavaScript object
                if (typeof value !== 'undefined') {
                    scope.set(gensym_name, value);
                }
            }
            // keep names so they can be restored after evaluation
            // if there are free symbols as output
            // kind of hack
            names.push({
                name, gensym: gensym_name
            });
            gensyms[name] = gensym_name;
            // we need to check if name is a string, because it can be
            // gensym from nested syntax-rules
            if (typeof name === 'string' && name.match(/\./)) {
                const [first, ...rest] = name.split('.').filter(Boolean);
                // save JavaScript dot notation for Env::get
                if (gensyms[first]) {
                    hidden_prop(gensym_name, '__object__', [gensyms[first], ...rest]);
                }
            }
        }
        return gensyms[name];
    }
    function transform_ellipsis_expr(expr, bindings, state, next = () => {}) {
        const { nested } = state;
        log(' ==> ' + expr.toString(true));
        log(bindings);
        if (expr instanceof LSymbol) {
            const name = expr.valueOf();
            log('[t 1');
            if (bindings[name]) {
                if (bindings[name] instanceof Pair) {
                    const { car, cdr } = bindings[name];
                    if (nested) {
                        const { car: caar, cdr: cadr } = car;
                        if (cadr !== nil) {
                            next(name, new Pair(cadr, nil));
                        }
                        return caar;
                    }
                    if (cdr !== nil) {
                        next(name, cdr);
                    }
                    return car;
                } else if (bindings[name] instanceof Array) {
                    next(name, bindings[name].slice(1));
                    return bindings[name][0];
                }
            }
            return transform(name);
        }
        if (expr instanceof Pair) {
            if (expr.car instanceof LSymbol &&
                expr.cdr instanceof Pair &&
                LSymbol.is(expr.cdr.car, ellipsis_symbol)) {
                log('[t 2');
                const name = expr.car.valueOf();
                const item = bindings[name];
                log({ expr: expr.toString(true), name, bindings, item });
                if (item === null) {
                    return;
                } else if (item) {
                    log({ b: bindings[name].toString() });
                    if (item instanceof Pair) {
                        log('[t 2 Pair ' + nested);
                        log({ ______: item.toString() });
                        const { car, cdr } = item;
                        if (nested) {
                            if (cdr !== nil) {
                                log('|| next 1');
                                next(name, cdr);
                            }
                            log({ car: car.toString() });
                            return car;
                        } else {
                            if (car.cdr !== nil) {
                                log('|| next 2');
                                next(name, new Pair(car.cdr, cdr));
                            }
                            log({ car: car.car.toString() });
                            return car.car;
                        }
                    } else if (item instanceof Array) {
                        log('[t 2 Array ' + nested);
                        if (nested) {
                            next(name, item.slice(1));
                            return Pair.fromArray(item);
                        } else {
                            const rest = item.slice(1);
                            if (rest.length) {
                                next(name, rest);
                            }
                            return item[0];
                        }
                    } else {
                        return item;
                    }
                }
            }
            log('[t 3 recur ' + expr.toString());
            const head = transform_ellipsis_expr(expr.car, bindings, state, next);
            const rest = transform_ellipsis_expr(expr.cdr, bindings, state, next);
            return new Pair(
                head,
                rest
            );
        }
        return expr;
    }
    function have_binding(biding, skip_nulls) {
        const values = Object.values(biding);
        const symbols = Object.getOwnPropertySymbols(biding);
        if (symbols.length) {
            values.push(...symbols.map(x => biding[x]));
        }
        return values.length && values.every(x => {
            if (x === null) {
                return !skip_nulls;
            }
            return x instanceof Pair || x === nil ||
                (x instanceof Array && x.length);
        });
    }
    function get_names(object) {
        return Object.keys(object).concat(Object.getOwnPropertySymbols(object));
    }
    /* eslint-disable complexity */
    function traverse(expr, { disabled } = {}) {
        log('traverse>> ' + expr.toString());
        if (expr instanceof Pair) {
            // escape ellispsis from R7RS e.g. (... ...)
            if (!disabled && expr.car instanceof Pair &&
                LSymbol.is(expr.car.car, ellipsis_symbol)) {
                return traverse(expr.car.cdr, { disabled: true });
            }
            if (expr.cdr instanceof Pair &&
                LSymbol.is(expr.cdr.car, ellipsis_symbol) && !disabled) {
                log('>> 1');
                const symbols = bindings['...'].symbols;
                // skip expand list of pattern was (x y ... z)
                // and code was (x z) so y == null
                const values = Object.values(symbols);
                if (values.length && values.every(x => x === null)) {
                    return traverse(expr.cdr.cdr, { disabled });
                }
                var keys = get_names(symbols);
                // case of list as first argument ((x . y) ...) or (x ... ...)
                // we need to recursively process the list
                // if we have pattern (_ (x y z ...) ...) and code (foo (1 2) (1 2))
                // x an y will be arrays of [1 1] and [2 2] and z will be array
                // of rest, x will also have it's own mapping to 1 and y to 2
                // in case of usage outside of ellipsis list e.g.: (x y)
                var is_spread = expr.car instanceof LSymbol &&
                    LSymbol.is(expr.cdr.cdr.car, ellipsis_symbol);
                if (expr.car instanceof Pair || is_spread) {
                    // lists is free ellipsis on pairs ((???) ...)
                    // TODO: will this work in every case? Do we need to handle
                    // nesting here?
                    if (bindings['...'].lists[0] === nil) {
                        return nil;
                    }
                    var new_expr = expr.car;
                    if (is_spread) {
                        new_expr = new Pair(
                            expr.car,
                            new Pair(
                                expr.cdr.car,
                                nil));
                    }
                    log('>> 2');
                    let result;
                    if (keys.length) {
                        log('>> 2 (a)');
                        let bind = { ...symbols };
                        result = nil;
                        while (true) {
                            if (!have_binding(bind)) {
                                break;
                            }
                            const new_bind = {};
                            const next = (key, value) => {
                                // ellipsis decide it what should be the next value
                                // there are two cases ((a . b) ...) and (a ...)
                                new_bind[key] = value;
                            };
                            const car = transform_ellipsis_expr(
                                new_expr,
                                bind,
                                { nested: true },
                                next
                            );
                            // undefined can be null caused by null binding
                            // on empty ellipsis
                            if (car !== undefined) {
                                if (is_spread) {
                                    if (result === nil) {
                                        result = car;
                                    } else {
                                        result = result.append(car);
                                    }
                                } else {
                                    result = new Pair(
                                        car,
                                        result
                                    );
                                }
                            }
                            bind = new_bind;
                        }
                        if (result !== nil && !is_spread) {
                            result = result.reverse();
                        }
                        // case of (list) ... (rest code)
                        if (expr.cdr.cdr !== nil &&
                            !LSymbol.is(expr.cdr.cdr.car, ellipsis_symbol)) {
                            const rest = traverse(expr.cdr.cdr, { disabled });
                            return result.append(rest);
                        }
                        return result;
                    } else {
                        log('>> 3');
                        const car = transform_ellipsis_expr(expr.car, symbols, {
                            nested: true
                        });
                        if (car) {
                            return new Pair(
                                car,
                                nil
                            );
                        }
                        return nil;
                    }
                } else if (expr.car instanceof LSymbol) {
                    log('>> 4');
                    if (LSymbol.is(expr.cdr.cdr.car, ellipsis_symbol)) {
                        // case (x ... ...)
                        log('>> 4 (a)');
                    } else {
                        log('>> 4 (b)');
                    }
                    // case: (x ...)
                    let name = expr.car.__name__;
                    let bind = { [name]: symbols[name] };
                    const is_null = symbols[name] === null;
                    let result = nil;
                    while (true) {
                        if (!have_binding(bind, true)) {
                            log({ bind });
                            break;
                        }
                        const new_bind = {};
                        const next = (key, value) => {
                            new_bind[key] = value;
                        };
                        const value = transform_ellipsis_expr(
                            expr,
                            bind,
                            { nested: false },
                            next
                        );
                        log({ value: value.toString() });
                        if (typeof value !== 'undefined') {
                            result = new Pair(
                                value,
                                result
                            );
                        }
                        bind = new_bind;
                    }
                    if (result !== nil) {
                        result = result.reverse();
                    }
                    // case if (x ... y ...) second spread is not processed
                    // and (??? . x) last symbol
                    // by ellipsis transformation
                    if (expr.cdr instanceof Pair) {
                        if (expr.cdr.cdr instanceof Pair ||
                            expr.cdr.cdr instanceof LSymbol) {
                            const node = traverse(expr.cdr.cdr, { disabled });
                            if (is_null) {
                                return node;
                            }
                            log('<<<< 1');
                            result.append(node);
                        }
                    }
                    log('<<<< 2');
                    return result;
                }
            }
            const head = traverse(expr.car, { disabled });
            let rest;
            let is_syntax;
            if ((expr.car instanceof LSymbol)) {
                const value = scope.get(expr.car, { throwError: false });
                is_syntax = value instanceof Macro &&
                    value.__name__ === 'syntax-rules';
            }
            if (is_syntax) {
                if (expr.cdr.car instanceof LSymbol) {
                    rest = new Pair(
                        traverse(expr.cdr.car, { disabled }),
                        new Pair(
                            expr.cdr.cdr.car,
                            traverse(expr.cdr.cdr.cdr, { disabled })
                        )
                    );
                } else {
                    rest = new Pair(
                        expr.cdr.car,
                        traverse(expr.cdr.cdr, { disabled })
                    );
                }
                log('REST >>>> ' + rest.toString());
            } else {
                rest = traverse(expr.cdr, { disabled });
            }
            log({
                a: true,
                car: toString(expr.car),
                cdr: toString(expr.cdr),
                head: toString(head),
                rest: toString(rest)
            });
            return new Pair(
                head,
                rest
            );
        }
        if (expr instanceof LSymbol) {
            if (disabled && LSymbol.is(expr, ellipsis_symbol)) {
                return expr;
            }
            const symbols = Object.keys(bindings['...'].symbols);
            const name = expr.literal();
            if (symbols.includes(name)) {
                const msg = `missing ellipsis symbol next to name \`${name}'`;
                throw new Error(`syntax-rules: ${msg}`);
            }
            const value = transform(expr, { disabled });
            if (typeof value !== 'undefined') {
                return value;
            }
        }
        return expr;
    }
    return traverse(expr, {});
}

// -----------------------------------------------------------------------------
const syntax_rules = new Macro('syntax-rules', function(macro, options) {
    var { dynamic_scope, error } = options;
    var env = this;
    function get_identifiers(node) {
        let symbols = [];
        while (node !== nil) {
            const x = node.car;
            symbols.push(x.valueOf());
            node = node.cdr;
        }
        return symbols;
    }
    function validate_identifiers(node) {
        while (node !== nil) {
            const x = node.car;
            if (!(x instanceof LSymbol)) {
                throw new Error('syntax-rules: wrong identifier');
            }
            node = node.cdr;
        }
    }
    if (macro.car instanceof LSymbol) {
        validate_identifiers(macro.cdr.car);
    } else {
        validate_identifiers(macro.car);
    }
    const syntax = new Syntax(function(code, { macro_expand }) {
        var scope = env.inherit('syntax');
        if (dynamic_scope) {
            dynamic_scope = scope;
        }
        var var_scope = this;
        // for macros that define variables used in macro (2 levels nestting)
        if (var_scope.__name__ === Syntax.__merge_env__) {
            // copy refs for defined gynsyms
            const props = Object.getOwnPropertySymbols(var_scope.__env__);
            props.forEach(symbol => {
                var_scope.__parent__.set(symbol, var_scope.__env__[symbol]);
            });
            var_scope = var_scope.__parent__;
        }
        var eval_args = { env: scope, dynamic_scope, error };
        let ellipsis, rules, symbols;
        if (macro.car instanceof LSymbol) {
            ellipsis = macro.car;
            symbols = get_identifiers(macro.cdr.car);
            rules = macro.cdr.cdr;
        } else {
            ellipsis = '...';
            symbols = get_identifiers(macro.car);
            rules = macro.cdr;
        }
        try {
            while (rules !== nil) {
                var rule = rules.car.car;
                var expr = rules.car.cdr.car;
                log(rule);
                var bindings = extract_patterns(rule, code, symbols, ellipsis, {
                    expansion: this, define: env
                });
                if (bindings) {
                    /* istanbul ignore next */
                    if (is_debug()) {
                        console.log(JSON.stringify(symbolize(bindings), true, 2));
                        console.log('PATTERN: ' + rule.toString(true));
                        console.log('MACRO: ' + code.toString(true));
                    }
                    // name is modified in transform_syntax
                    var names = [];
                    const new_expr = transform_syntax({
                        bindings,
                        expr,
                        symbols,
                        scope,
                        lex_scope: var_scope,
                        names,
                        ellipsis
                    });
                    log('OUPUT>>> ' + new_expr.toString());
                    if (new_expr) {
                        expr = new_expr;
                    }
                    var new_env = var_scope.merge(scope, Syntax.__merge_env__);
                    if (macro_expand) {
                        return { expr, scope: new_env };
                    }
                    var result = evaluate(expr, { ...eval_args, env: new_env });
                    // Hack: update the result if there are generated
                    //       gensyms that should be literal symbols
                    // TODO: maybe not the part move when literal elisps may
                    //       be generated, maybe they will need to be mark somehow
                    return clear_gensyms(result, names);
                }
                rules = rules.cdr;
            }
        } catch (e) {
            e.message += ` in macro: ${macro.toString(true)}`;
            throw e;
        }
        throw new Error(`Invalid Syntax ${code.toString(true)}`);
    }, env);
    syntax.__code__ = macro;
    return syntax;
}, `(syntax-rules () (pattern expression) ...)

    Base of Hygienic macro, it will return new syntax expander
    that works like lisp macros.`);

// -----------------------------------------------------------------------------
const macro = 'define-macro';

// -----------------------------------------------------------------------------
const define_macro = new Macro(macro, function(macro, { dynamic_scope, error }) {
    if (macro.car instanceof Pair && macro.car.car instanceof LSymbol) {
        var name = macro.car.car.__name__;
        var __doc__;
        if (LString.isString(macro.cdr.car) && macro.cdr.cdr instanceof Pair) {
            __doc__ = macro.cdr.car.valueOf();
        }
        var makro_instance = Macro.defmacro(name, function(code) {
            var env = new Environment({}, this, 'defmacro');
            var name = macro.car.cdr;
            var arg = code;
            while (true) {
                if (name === nil) {
                    break;
                }
                if (name instanceof LSymbol) {
                    env.__env__[name.__name__] = arg;
                    break;
                } else if (name.car !== nil) {
                    if (arg === nil) {
                        env.__env__[name.car.__name__] = nil;
                    } else {
                        if (arg.car instanceof Pair) {
                            arg.car[__data__] = true;
                        }
                        env.__env__[name.car.__name__] = arg.car;
                    }
                }
                if (name.cdr === nil) {
                    break;
                }
                if (arg !== nil) {
                    arg = arg.cdr;
                }
                name = name.cdr;
            }
            if (dynamic_scope) {
                dynamic_scope = env;
            }
            var eval_args = {
                env,
                dynamic_scope,
                error
            };
            // evaluate macro
            if (macro.cdr instanceof Pair) {
                // this eval will return lips code
                var rest = __doc__ ? macro.cdr.cdr : macro.cdr;
                var result = rest.reduce(function(result, node) {
                    return evaluate(node, eval_args);
                });
                return unpromise(result, function(result) {
                    if (typeof result === 'object') {
                        delete result[__data__];
                    }
                    return result;
                });
            }
        }, __doc__, true);
        makro_instance.__code__ = new Pair(new LSymbol('define-macro'), macro);
        this.set(name, makro_instance);
    }
}, `(define-macro (name . args) body)

     Meta macro, macro that create new macros, if return value is list structure
     it will be evaluated when macro is invoked. You can use quasiquote \` and
     unquote , and unquote-splicing ,@ inside to create expression that will be
     evaluated on runtime. Macros works like this: if you pass any expression to
     macro the arguments will not be evaluated unless macro itself evaluate it.
     Because of this macro can manipulate expression (arguments) as lists.`);

// -----------------------------------------------------------------------------
// :: function that return macro for let, let* and letrec
// -----------------------------------------------------------------------------
function let_macro(symbol) {
    var name;
    switch (symbol) {
        case Symbol.for('letrec'):
            name = 'letrec';
            break;
        case Symbol.for('let'):
            name = 'let';
            break;
        case Symbol.for('let*'):
            name = 'let*';
            break;
        default:
            throw new Error('Invalid let_macro value');
    }
    return Macro.defmacro(name, function(code, options) {
        var { dynamic_scope, error, macro_expand } = options;
        var args;
        // named let:
        // (let iter ((x 10)) (iter (- x 1))) -> (let* ((iter (lambda (x) ...
        if (code.car instanceof LSymbol) {
            if (!(code.cdr.car instanceof Pair || code.cdr.car === nil)) {
                throw new Error('let require list of pairs');
            }
            var params;
            if (code.cdr.car === nil) {
                args = nil;
                params = nil;
            } else {
                params = code.cdr.car.map(pair => pair.car);
                args = code.cdr.car.map(pair => pair.cdr.car);
            }
            return Pair.fromArray([
                LSymbol('letrec'),
                [[code.car, Pair(
                    LSymbol('lambda'),
                    Pair(params, code.cdr.cdr))]],
                Pair(code.car, args)
            ]);
        } else if (macro_expand) {
            // Macro.defmacro are special macros that should return lisp code
            // here we use evaluate, so we need to check special flag set by
            // macroexpand to prevent evaluation of code in normal let
            return;
        }
        var self = this;
        args = global_env.get('list->array')(code.car);
        var env = self.inherit(name);
        var values, var_body_env;
        if (name === 'let*') {
            var_body_env = env;
        } else if (name === 'let') {
            values = []; // collect potential promises
        }
        var i = 0;
        function exec() {
            var output = new Pair(new LSymbol('begin'), code.cdr);
            return evaluate(output, {
                env,
                dynamic_scope,
                error
            });
        }
        return (function loop() {
            var pair = args[i++];
            if (dynamic_scope) {
                dynamic_scope = name === 'let*' ? env : self;
            }
            if (!pair) {
                // resolve all promises
                if (values && values.length) {
                    var v = values.map(x => x.value);
                    var promises = v.filter(is_promise);
                    if (promises.length) {
                        return promise_all(v).then((arr) => {
                            for (var i = 0, len = arr.length; i < len; ++i) {
                                env.set(values[i].name, arr[i]);
                            }
                        }).then(exec);
                    } else {
                        for (let { name, value } of values) {
                            env.set(name, value);
                        }
                    }
                }
                return exec();
            } else {
                if (name === 'let') {
                    var_body_env = self;
                } else if (name === 'letrec') {
                    var_body_env = env;
                }
                var value = evaluate(pair.cdr.car, {
                    env: var_body_env,
                    dynamic_scope,
                    error
                });
                if (name === 'let*') {
                    var_body_env = env = var_body_env.inherit('let*[' + i + ']');
                }
                if (values) {
                    values.push({ name: pair.car, value });
                    return loop();
                } else {
                    return unpromise(value, function(value) {
                        env.set(pair.car, value);
                        return loop();
                    });
                }
            }
        })();
    });
}

// -----------------------------------------------------------------------------
const quasiquote = Macro.defmacro('quasiquote', function(arg, env) {
    var { dynamic_scope, error } = env;
    var self = this;
    //var max_unquote = 1;
    if (dynamic_scope) {
        dynamic_scope = self;
    }
    // -----------------------------------------------------------------
    function is_struct(value) {
        return value instanceof Pair ||
            is_plain_object(value) ||
            Array.isArray(value);
    }
    // -----------------------------------------------------------------
    function resolve_pair(pair, fn, test = is_struct) {
        if (pair instanceof Pair) {
            var car = pair.car;
            var cdr = pair.cdr;
            if (test(car)) {
                car = fn(car);
            }
            if (test(cdr)) {
                cdr = fn(cdr);
            }
            if (is_promise(car) || is_promise(cdr)) {
                return promise_all([car, cdr]).then(([car, cdr]) => {
                    return new Pair(car, cdr);
                });
            } else {
                return new Pair(car, cdr);
            }
        }
        return pair;
    }
    // -----------------------------------------------------------------
    function join(eval_pair, value) {
        if (eval_pair === nil && value === nil) {
            //return nil;
        }
        if (eval_pair instanceof Pair) {
            if (value !== nil) {
                eval_pair.append(value);
            }
        } else {
            eval_pair = new Pair(
                eval_pair,
                value
            );
        }
        return eval_pair;
    }
    // -----------------------------------------------------------------
    function unquoted_arr(arr) {
        return !!arr.filter(value => {
            return value instanceof Pair &&
                LSymbol.is(value.car, /^(unquote|unquote-splicing)$/);
        }).length;
    }
    // -----------------------------------------------------------------
    function quote_vector(arr, unquote_cnt, max_unq) {
        return arr.reduce((acc, x) => {
            if (!(x instanceof Pair)) {
                acc.push(x);
                return acc;
            }
            if (LSymbol.is(x.car, 'unquote-splicing')) {
                let result;
                if (unquote_cnt + 1 < max_unq) {
                    result = recur(x.cdr, unquote_cnt + 1, max_unq);
                } else {
                    result = evaluate(x.cdr.car, {
                        env: self,
                        dynamic_scope,
                        error
                    });
                }
                if (!(result instanceof Pair)) {
                    throw new Error(`Expecting list ${type(x)} found`);
                }
                return acc.concat(result.to_array());
            }
            acc.push(recur(x, unquote_cnt, max_unq));
            return acc;
        }, []);
    }
    // -----------------------------------------------------------------
    function quote_object(object, unquote_cnt, max_unq) {
        const result = {};
        unquote_cnt++;
        Object.keys(object).forEach(key => {
            const value = object[key];
            if (value instanceof Pair) {
                if (LSymbol.is(value.car, 'unquote-splicing')) {
                    throw new Error("You can't call `unquote-splicing` " +
                                    "inside object");
                }
                let output;
                if (unquote_cnt < max_unq) {
                    output = recur(value.cdr.car, unquote_cnt, max_unq);
                } else {
                    output = evaluate(value.cdr.car, {
                        env: self,
                        dynamic_scope,
                        error
                    });
                }
                result[key] = output;
            } else {
                result[key] = value;
            }
        });
        if (Object.isFrozen(object)) {
            Object.freeze(result);
        }
        return result;
    }
    // -----------------------------------------------------------------
    function unquote_splice(pair, unquote_cnt, max_unq) {
        if (unquote_cnt < max_unq) {
            return new Pair(
                new Pair(
                    pair.car.car,
                    recur(pair.car.cdr, unquote_cnt, max_unq)
                ),
                nil
            );
        }
        var lists = [];
        return (function next(node) {
            var value = evaluate(node.car, {
                env: self,
                dynamic_scope,
                error
            });
            lists.push(value);
            if (node.cdr instanceof Pair) {
                return next(node.cdr);
            }
            return unpromise(lists, function(arr) {
                if (arr.some(x => !(x instanceof Pair))) {
                    if (pair.cdr instanceof Pair &&
                        LSymbol.is(pair.cdr.car, '.') &&
                        pair.cdr.cdr instanceof Pair &&
                        pair.cdr.cdr.cdr === nil) {
                        return pair.cdr.cdr.car;
                    }
                    if (!(pair.cdr === nil || pair.cdr instanceof Pair)) {
                        const msg = "You can't splice atom inside list";
                        throw new Error(msg);
                    }
                    if (arr.length > 1) {
                        const msg = "You can't splice multiple atoms inside list";
                        throw new Error(msg);
                    }
                    if (!(pair.cdr instanceof Pair && arr[0] === nil)) {
                        return arr[0];
                    }
                }
                // don't create Cycles
                arr = arr.map(eval_pair => {
                    if (splices.has(eval_pair)) {
                        return eval_pair.clone();
                    } else {
                        splices.add(eval_pair);
                        return eval_pair;
                    }
                });
                const value = recur(pair.cdr, 0, 1);
                if (value === nil && arr[0] === nil) {
                    return undefined;
                }
                return unpromise(value, value => {
                    if (arr[0] === nil) {
                        return value;
                    }
                    if (arr.length === 1) {
                        return join(arr[0], value);
                    }
                    var result = arr.reduce((result, eval_pair) => {
                        return join(result, eval_pair);
                    });
                    return join(result, value);
                });
            });
        })(pair.car.cdr);
    }
    // -----------------------------------------------------------------
    var splices = new Set();
    function recur(pair, unquote_cnt, max_unq) {
        if (pair instanceof Pair) {
            if (pair.car instanceof Pair) {
                if (LSymbol.is(pair.car.car, 'unquote-splicing')) {
                    return unquote_splice(pair, unquote_cnt + 1, max_unq);
                }
                if (LSymbol.is(pair.car.car, 'unquote')) {
                    // + 2 - one for unquote and one for unquote splicing
                    if (unquote_cnt + 2 === max_unq &&
                        pair.car.cdr instanceof Pair &&
                        pair.car.cdr.car instanceof Pair &&
                        LSymbol.is(pair.car.cdr.car.car, 'unquote-splicing')) {
                        const rest = pair.car.cdr;
                        return new Pair(
                            new Pair(
                                new LSymbol('unquote'),
                                unquote_splice(rest, unquote_cnt + 2, max_unq)
                            ),
                            nil
                        );
                    } else if (pair.car.cdr instanceof Pair &&
                               pair.car.cdr.cdr !== nil) {
                        if (pair.car.cdr.car instanceof Pair) {
                            // values inside unquote are lists
                            const result = [];
                            return (function recur(node) {
                                if (node === nil) {
                                    return Pair.fromArray(result);
                                }
                                return unpromise(evaluate(node.car, {
                                    env: self,
                                    dynamic_scope,
                                    error
                                }), function(next) {
                                    result.push(next);
                                    return recur(node.cdr);
                                });
                            })(pair.car.cdr);
                        } else {
                            // same as in guile if (unquote 1 2 3) it should be
                            // spliced - scheme spec say it's unspecify but it
                            // work like in CL
                            return pair.car.cdr;
                        }
                    }
                }
            }
            if (LSymbol.is(pair.car, 'quasiquote')) {
                var cdr = recur(pair.cdr, unquote_cnt, max_unq + 1);
                return new Pair(pair.car, cdr);
            }
            if (LSymbol.is(pair.car, 'quote')) {
                return new Pair(
                    pair.car,
                    recur(pair.cdr, unquote_cnt, max_unq)
                );
            }
            if (LSymbol.is(pair.car, 'unquote')) {
                unquote_cnt++;
                if (unquote_cnt < max_unq) {
                    return new Pair(
                        new LSymbol('unquote'),
                        recur(pair.cdr, unquote_cnt, max_unq)
                    );
                }
                if (unquote_cnt > max_unq) {
                    throw new Error("You can't call `unquote` outside " +
                                    "of quasiquote");
                }
                if (pair.cdr instanceof Pair) {
                    if (pair.cdr.cdr !== nil) {
                        if (pair.cdr.car instanceof Pair) {
                            // TODO: test if this part is needed
                            // this part was duplicated in previous section
                            // if (LSymbol.is(pair.car.car, 'unquote')) {
                            // so this probably can be removed
                            const result = [];
                            // evaluate all values in unquote
                            return (function recur(node) {
                                if (node === nil) {
                                    return Pair.fromArray(result);
                                }
                                return unpromise(evaluate(node.car, {
                                    env: self,
                                    dynamic_scope,
                                    error
                                }), function(next) {
                                    result.push(next);
                                    return recur(node.cdr);
                                });
                            })(pair.cdr);
                        } else {
                            return pair.cdr;
                        }
                    } else {
                        return evaluate(pair.cdr.car, {
                            env: self,
                            dynamic_scope,
                            error
                        });
                    }
                } else {
                    return pair.cdr;
                }
            }
            return resolve_pair(pair, (pair) => {
                return recur(pair, unquote_cnt, max_unq);
            });
        } else if (is_plain_object(pair)) {
            return quote_object(pair, unquote_cnt, max_unq);
        } else if (pair instanceof Array) {
            return quote_vector(pair, unquote_cnt, max_unq);
        }
        return pair;
    }
    // -----------------------------------------------------------------
    function clear(node) {
        if (node instanceof Pair) {
            delete node[__data__];
            if (!node.haveCycles('car')) {
                clear(node.car);
            }
            if (!node.haveCycles('cdr')) {
                clear(node.cdr);
            }
        }
    }
    // -----------------------------------------------------------------
    if (is_plain_object(arg.car) && !unquoted_arr(Object.values(arg.car))) {
        return quote(arg.car);
    }
    if (Array.isArray(arg.car) && !unquoted_arr(arg.car)) {
        return quote(arg.car);
    }
    if (arg.car instanceof Pair &&
        !arg.car.find('unquote') &&
        !arg.car.find('unquote-splicing') &&
        !arg.car.find('quasiquote')) {
        return quote(arg.car);
    }
    var x = recur(arg.car, 0, 1);
    return unpromise(x, value => {
        // clear nested data for tests
        clear(value);
        return quote(value);
    });
}, `(quasiquote list ,value ,@value)

    Similar macro to \`quote\` but inside it you can use special
    expressions unquote abbreviated to , that will evaluate expresion inside
    and return its value or unquote-splicing abbreviated to ,@ that will
    evaluate expression but return value without parenthesis (it will join)
    the list with its value. Best used with macros but it can be used outside`);

const quote = new Macro('quote', function(arg) {
    return quote(arg.car);
}, `(quote expression)

     Macro that return single lips expression as data (it don't evaluate its
     argument). It will return list of pairs if put in front of lips code.
     And if put in fron of symbol it will return that symbol not value
     associated with that name.`);

export {
    Macro,
    Syntax,
    macro_expand,
    syntax_rules,
    define_macro,
    let_macro,
    quote,
    quasiquote
};
