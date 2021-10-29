/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol, Uint8Array */
import {
    typecheck_args,
    typecheck,
    type,
    typecheck_text_port,
    is_port,
    is_prototype,
    is_native,
    is_lambda,
    is_null,
    type_error_message,
    __lambda__,
    __prototype__
} from './typechecking.js';
import Values from './Values.js';
import {
    doc,
    unbind,
    escape_regex,
    set_fn_length,
    to_array,
    get_props,
    pipe,
    compose,
    fold,
    binary_math_op,
    single_math_op,
    reduce_math_op,
    curry,
    equal,
    patch_value,
    seq_compare
} from './utils.js';
import { unbox } from './boxing.js';
import { BufferedOutputPort, InputPort, eof } from './Ports.js';
import { resolve_promises, unpromise, promise_all, is_promise } from './Promises.js';
import { Formatter } from './Formatter.js';
import {
    Macro,
    Syntax,
    let_macro,
    quote,
    quasiquote,
    define_macro,
    syntax_rules,
    macro_expand
} from './Macro.js';
import { LSymbol, gensym } from './LSymbol.js';
import { Pair, nil } from './Pair.js';
import { LNumber, LFloat, abs, truncate } from './Numbers.js';
import LCharacter from './LCharacter.js';
import { unserialize, unserialize_bin } from './Compiler.js';
import { specials, string_to_number, parse } from './Parser.js';
import { evaluate, exec, prepare_fn_args } from './Evaluator.js';
import { Environment, get } from './Environment.js';
import LString from './LString.js';
import Continuation from './Continuation.js';
import root from './root.js';

let fs, path, node_require;

// -------------------------------------------------------------------------
// function get internal protected data
// -------------------------------------------------------------------------
function internal(env, name) {
    var internal_env = interaction(env, '**internal-env**');
    return internal_env.get(name);
}

// -------------------------------------------------------------------------
function pararel(name, fn) {
    return new Macro(name, function(code, { dynamic_scope, error } = {}) {
        var env = this;
        if (dynamic_scope) {
            dynamic_scope = this;
        }
        var node = code;
        var results = [];
        while (node instanceof Pair) {
            results.push(evaluate(node.car, { env, dynamic_scope, error }));
            node = node.cdr;
        }
        var havePromises = results.filter(is_promise).length;
        if (havePromises) {
            return promise_all(results).then(fn.bind(this));
        } else {
            return fn.call(this, results);
        }
    });
}

// ----------------------------------------------------------------------
// :: function that return mather function that match string against string
// ----------------------------------------------------------------------
function matcher(name, arg) {
    if (arg instanceof RegExp) {
        return x => String(x).match(arg);
    } else if (is_function(arg)) {
        // it will always be function
        return arg;
    }
    throw new Error('Invalid matcher');
}

// -------------------------------------------------------------------------
// get variable from interaction environment
// -------------------------------------------------------------------------
function interaction(env, name) {
    var interaction_env = env.get('**interaction-environment**');
    return interaction_env.get(name);
}

// -------------------------------------------------------------------------
var internal_env = new Environment({
    stdout: new BufferedOutputPort(function(...args) {
        console.log(...args);
    }),
    // ------------------------------------------------------------------
    stderr: new BufferedOutputPort(function(...args) {
        console.error(...args);
    }),
    // ------------------------------------------------------------------
    stdin: InputPort(function() {
        return Promise.resolve(prompt(''));
    }),
    // those will be compiled by babel regex plugin
    'letter-unicode-regex': /\p{L}/u,
    'numeral-unicode-regex': /\p{N}/u,
    'space-unicode-regex': /\s/u
}, undefined, 'internal');

// -------------------------------------------------------------------------
var global_env = new Environment({
    eof,
    undefined, // undefined as parser constant breaks most of the unit tests
    // ---------------------------------------------------------------------
    'peek-char': doc('peek-char', function(port = null) {
        if (port === null) {
            port = internal(this, 'stdin');
        }
        typecheck_text_port('peek-char', port, 'input-port');
        return port.peek_char();
    }, `(peek-char port)

        Function get character from string port or EOF object if no more
        data in string port.`),
    // ------------------------------------------------------------------
    'read-line': doc('read-line', function(port = null) {
        if (port === null) {
            port = internal(this, 'stdin');
        }
        typecheck_text_port('read-line', port, 'input-port');
        return port.read_line();
    }, `(read-char port)

        Function read next character from input port.`),
    // ------------------------------------------------------------------
    'read-char': doc('read-char', function(port = null) {
        if (port === null) {
            port = internal(this, 'stdin');
        }
        typecheck_text_port('read-char', port, 'input-port');
        return port.read_char();
    }, `(read-char port)

        Function read next character from input port.`),
    // ------------------------------------------------------------------
    read: doc('read', async function read(arg = null) {
        if (LString.isString(arg)) {
            for await (let value of parse(arg, this)) {
                return value;
            }
        }
        var port;
        if (arg === null) {
            port = internal(this, 'stdin');
        } else {
            port = arg;
        }
        typecheck_text_port('read', port, 'input-port');
        return port.read.call(this);
    }, `(read [string])

        Function if used with string will parse the string and return
        list structure of LIPS code. If called without an argument it
        will read string from standard input (using browser prompt or
        user defined way) and call itself with that string (parse is)
        function can be used together with eval to evaluate code from
        string`),
    // ------------------------------------------------------------------
    pprint: doc('pprint', function pprint(arg) {
        if (arg instanceof Pair) {
            arg = new Formatter(arg.toString(true)).break().format();
            global_env.get('display').call(global_env, arg);
        } else {
            global_env.get('write').call(global_env, arg);
        }
        global_env.get('newline').call(global_env);
    }, `(pprint expression)

        Pretty print list expression, if called with non-pair it just call
        print function with passed argument.`),
    // ------------------------------------------------------------------
    print: doc('print', function print(...args) {
        const display = global_env.get('display');
        const newline = global_env.get('newline');
        args.forEach(arg => {
            display.call(global_env, arg);
            newline.call(global_env);
        });
    }, `(print . args)

            Function convert each argument to string and print the result to
            standard output (by default it's console but it can be defined
            it user code), the function call newline after printing each arg.`),
    // ------------------------------------------------------------------
    format: doc('format', function format(str, ...args) {
        typecheck('format', str, 'string');
        const re = /(~[as%~])/g;
        let m = str.match(/(~[as])/g);
        if (m && m.length > args.length) {
            throw new Error('Not enough arguments');
        }
        var i = 0;
        var repr = global_env.get('repr');
        str = str.replace(re, (x) => {
            const chr = x[1];
            if (chr === '~') {
                return '~';
            } else if (chr === '%') {
                return '\n';
            } else {
                const arg = args[i++];
                if (chr === 'a') {
                    return repr(arg);
                } else {
                    return repr(arg, true);
                }
            }
        });
        m = str.match(/~([\S])/);
        if (m) {
            throw new Error(`format: Unrecognized escape seqence ${m[1]}`);
        }
        return str;
    }, `(format string n1 n2 ...)

        Function accepts string template and replacing any escape sequences
        by arguments:

        * ~a value as if printed with display
        * ~s value as if printed with write
        * ~% newline character
        * ~~ literal tilde '~' is inserted

        if there missing arguments or other escape character it throw exception.`),
    // ------------------------------------------------------------------
    display: doc('display', function display(arg, port = null) {
        if (port === null) {
            port = internal(this, 'stdout');
        } else {
            typecheck('display', port, 'output-port');
        }
        const value = global_env.get('repr')(arg);
        port.write.call(global_env, value);
    }, `(display arg [port])

        Function send string to standard output or provied port.`),
    // ------------------------------------------------------------------
    'display-error': doc('display-error', function error(...args) {
        const port = internal(this, 'stderr');
        const repr = global_env.get('repr');
        const value = args.map(repr).join(' ');
        port.write.call(global_env, value);
        global_env.get('newline')(port);
    }, `(display-error . args)

        Display error message.`),
    // ------------------------------------------------------------------
    '%same-functions': doc('%same-functions', function(a, b) {
        if (!is_function(a)) {
            return false;
        }
        if (!is_function(b)) {
            return false;
        }
        return unbind(a) === unbind(b);
    }, `(%same-functions a b)

        Helper function that check if two bound functions are the same`),
    // ------------------------------------------------------------------
    help: doc(new Macro('help', function(code, { dynamic_scope, error }) {
        var symbol;
        if (code.car instanceof LSymbol) {
            symbol = code.car;
        } else if (code.car instanceof Pair && code.car.car instanceof LSymbol) {
            symbol = code.car.car;
        } else {
            var env = this;
            if (dynamic_scope) {
                dynamic_scope = this;
            }
            var ret = evaluate(code.car, { env, error, dynamic_scope });
            if (ret && ret.__doc__) {
                return ret.__doc__;
            }
            return;
        }
        var __doc__;
        var value = this.get(symbol);
        __doc__ = value && value.__doc__;
        if (__doc__) {
            return __doc__;
        }
        var ref = this.ref(symbol);
        if (ref) {
            __doc__ = ref.doc(symbol);
            if (__doc__) {
                return __doc__;
            }
        }
    }), `(help object)

         Macro returns documentation for function or macro. You can save the function
         or macro in variable and use it in context. But help for variable require
         to pass the symbol itself.`),
    // ------------------------------------------------------------------
    cons: doc('cons', function cons(car, cdr) {
        return new Pair(car, cdr);
    }, `(cons left right)

        Function return new Pair out of two arguments.`),
    // ------------------------------------------------------------------
    car: doc('car', function car(list) {
        typecheck('car', list, 'pair');
        return list.car;
    }, `(car pair)

        Function returns car (head) of the list/pair.`),
    // ------------------------------------------------------------------
    cdr: doc('cdr', function cdr(list) {
        typecheck('cdr', list, 'pair');
        return list.cdr;
    }, `(cdr pair)

        Function returns cdr (tail) of the list/pair.`),
    // ------------------------------------------------------------------
    'set!': doc(new Macro('set!', function(code, { dynamic_scope, error } = {}) {
        if (dynamic_scope) {
            dynamic_scope = this;
        }
        var env = this;
        var ref;
        var value = evaluate(code.cdr.car, { env: this, dynamic_scope, error });
        value = resolve_promises(value);
        function set(object, key, value) {
            if (is_promise(object)) {
                return object.then(key => set(object, key, value));
            }
            if (is_promise(key)) {
                return key.then(key => set(object, key, value));
            }
            if (is_promise(value)) {
                return value.then(value => set(object, key, value));
            }
            env.get('set-obj!').call(env, object, key, value);
            return value;
        }
        if (code.car instanceof Pair && LSymbol.is(code.car.car, '.')) {
            var second = code.car.cdr.car;
            var thrid = code.car.cdr.cdr.car;
            var object = evaluate(second, { env: this, dynamic_scope, error });
            var key = evaluate(thrid, { env: this, dynamic_scope, error });
            return set(object, key, value);
        }
        if (!(code.car instanceof LSymbol)) {
            throw new Error('set! first argument need to be a symbol or ' +
                            'dot accessor that evaluate to object.');
        }
        var symbol = code.car.valueOf();
        ref = this.ref(code.car.__name__);
        // we don't return value because we only care about sync of set value
        // when value is a promise
        return unpromise(value, value => {
            if (!ref) {
                // case (set! fn.toString (lambda () "xxx"))
                var parts = symbol.split('.');
                if (parts.length > 1) {
                    var key = parts.pop();
                    var name = parts.join('.');
                    var obj = this.get(name, { throwError: false });
                    if (obj) {
                        set(obj, key, value);
                        return;
                    }
                }
                throw new Error('Unbound variable `' + symbol + '\'');
            }
            ref.set(symbol, value);
        });
    }), `(set! name value)

         Macro that can be used to set the value of the variable (mutate)
         it search the scope chain until it finds first non emtpy slot and set it.`),
    // ------------------------------------------------------------------
    'unset!': doc(new Macro('set!', function(code) {
        if (!(code.car instanceof LSymbol)) {
            throw new Error('unset! first argument need to be a symbol or ' +
                            'dot accessor that evaluate to object.');
        }
        const symbol = code.car;
        var ref = this.ref(symbol);
        if (ref) {
            delete ref.__env__[symbol.__name__];
        }
    }), `(unset! name)

         Function delete specified name from environment.`),
    // ------------------------------------------------------------------
    'set-car!': doc('set-car!', function(slot, value) {
        typecheck('set-car!', slot, 'pair');
        slot.car = value;
    }, `(set-car! obj value)

        Function that set car (head) of the list/pair to specified value.
        It can destroy the list. Old value is lost.`),
    // ------------------------------------------------------------------
    'set-cdr!': doc('set-cdr!', function(slot, value) {
        typecheck('set-cdr!', slot, 'pair');
        slot.cdr = value;
    }, `(set-cdr! obj value)

        Function that set cdr (tail) of the list/pair to specified value.
        It can destroy the list. Old value is lost.`),
    // ------------------------------------------------------------------
    'empty?': doc('empty?', function(x) {
        return typeof x === 'undefined' || x === nil;
    }, `(empty? object)

        Function return true if value is undfined empty list.`),
    // ------------------------------------------------------------------
    gensym: doc(
        'gensym',
        gensym,
        `(gensym)

         Function generate unique symbol, to use with macros as meta name.`),
    // ------------------------------------------------------------------
    // TODO: (load filename environment-specifier)
    // ------------------------------------------------------------------
    load: doc('load', function load(file, env) {
        typecheck('load', file, 'string');
        var g_env = this;
        if (g_env.__name__ === '__frame__') {
            g_env = g_env.__parent__;
        }
        if (!(env instanceof Environment)) {
            if (g_env === global_env) {
                // this is used for let-env + load
                // this may be obsolete when there is env arg
                env = g_env;
            } else {
                env = this.get('**interaction-environment**');
            }
        }
        const PATH = '**module-path**';
        var module_path = global_env.get(PATH, { throwError: false });
        file = file.valueOf();
        if (!file.match(/.[^.]+$/)) {
            file += '.scm';
        }
        const IS_BIN = file.match(/\.xcb$/);
        function run(code) {
            if (IS_BIN) {
                code = unserialize_bin(code);
            } else {
                if (type(code) === 'buffer') {
                    code = code.toString();
                }
                code = code.replace(/^#!.*/, '');
                if (code.match(/^\{/)) {
                    code = unserialize(code);
                }
            }
            return exec(code, env);
        }
        function fetch(file) {
            return root.fetch(file)
                .then(res => IS_BIN ? res.arrayBuffer() : res.text())
                .then((code) => {
                    if (IS_BIN) {
                        code = new Uint8Array(code);
                    }
                    return code;
                });
        }
        if (is_node()) {
            return new Promise((resolve, reject) => {
                var path = node_require('path');
                if (module_path) {
                    module_path = module_path.valueOf();
                    file = path.join(module_path, file);
                }
                global_env.set(PATH, path.dirname(file));
                node_require('fs').readFile(file, function(err, data) {
                    if (err) {
                        reject(err);
                        global_env.set(PATH, module_path);
                    } else {
                        try {
                            run(data).then(() => {
                                resolve();
                                global_env.set(PATH, module_path);
                            }).catch(reject);
                        } catch (e) {
                            reject(e);
                        }
                    }
                });
            });
        }
        if (module_path) {
            module_path = module_path.valueOf();
            file = module_path + '/' + file.replace(/^\.?\/?/, '');
        }
        return fetch(file).then(code => {
            global_env.set(PATH, file.replace(/\/[^/]*$/, ''));
            return run(code);
        }).then(() => {}).finally(() => {
            global_env.set(PATH, module_path);
        });
    }, `(load filename)
        (load filename environment)

        Function fetch the file and evaluate its content as LIPS code,
        If second argument is provided and it's environment the evaluation
        will happen in that environment.`),
    // ------------------------------------------------------------------
    'do': doc(new Macro('do', async function(code, { dynamic_scope, error }) {
        var self = this;
        if (dynamic_scope) {
            dynamic_scope = self;
        }
        var scope = self.inherit('do');
        var vars = code.car;
        var test = code.cdr.car;
        var body = code.cdr.cdr;
        if (body !== nil) {
            body = new Pair(LSymbol('begin'), body);
        }
        let eval_args = { env: self, dynamic_scope, error };
        let node = vars;
        while (node !== nil) {
            const item = node.car;
            scope.set(item.car, await evaluate(item.cdr.car, eval_args));
            node = node.cdr;
        }
        eval_args = { env: scope, dynamic_scope, error };
        while ((await evaluate(test.car, eval_args)) === false) {
            if (body !== nil) {
                await evaluate(body, eval_args);
            }
            let node = vars;
            const next = {};
            while (node !== nil) {
                const item = node.car;
                if (item.cdr.cdr !== nil) {
                    const value = await evaluate(item.cdr.cdr.car, eval_args);
                    next[item.car.valueOf()] = value;
                }
                node = node.cdr;
            }
            const symbols = Object.getOwnPropertySymbols(next);
            Object.keys(next).concat(symbols).forEach(key => {
                scope.set(key, next[key]);
            });
        }
        if (test.cdr !== nil) {
            return await evaluate(test.cdr.car, eval_args);
        }
    }), `(do ((<var> <init> <next>)) (test expression) . body)

         Iteration macro that evaluate the expression body in scope of the variables.
         On Eeach loop it increase the variables according to next expression and run
         test to check if the loop should continue. If test is signle call the macro
         will not return anything. If the test is pair of expression and value the
         macro will return that value after finish.`),
    // ------------------------------------------------------------------
    'if': doc(new Macro('if', function(code, { dynamic_scope, error }) {
        if (dynamic_scope) {
            dynamic_scope = this;
        }
        var env = this;
        var resolve = (cond) => {
            if (cond === false) {
                return evaluate(code.cdr.cdr.car, {
                    env,
                    dynamic_scope,
                    error
                });
            } else {
                return evaluate(code.cdr.car, {
                    env,
                    dynamic_scope,
                    error
                });
            }
        };
        if (code === nil) {
            throw new Error('too few expressions for `if`');
        }
        var cond = evaluate(code.car, { env, dynamic_scope, error });
        return unpromise(cond, resolve);
    }), `(if cond true-expr false-expr)

         Macro evaluate condition expression and if the value is true, it
         evaluate and return true expression if not it evaluate and return
         false expression`),
    // ------------------------------------------------------------------
    'let-env': new Macro('let-env', function(code, options = {}) {
        const { dynamic_scope, error } = options;
        typecheck('let-env', code, 'pair');
        var ret = evaluate(code.car, { env: this, dynamic_scope, error });
        return unpromise(ret, function(value) {
            typecheck('let-env', value, 'environment');
            return evaluate(Pair(LSymbol('begin'), code.cdr), {
                env: value, dynamic_scope, error
            });
        });
    }, `(let-env env . body)

        Special macro that evaluate body in context of given environment
        object.`),
    // ------------------------------------------------------------------
    'letrec': doc(
        let_macro(Symbol.for('letrec')),
        `(letrec ((a value-a) (b value-b)) body)

         Macro that creates new environment, then evaluate and assign values to
         names and then evaluate the body in context of that environment.
         Values are evaluated sequentialy and next value can access to
         previous values/names.`),
    // ---------------------------------------------------------------------
    'letrec*': doc(
        let_macro(Symbol.for('letrec')),
        `(letrec* ((a value-a) (b value-b)) body)

         Same as letrec but the order of execution of the binding is guaranteed,
         so use can use recursive code as well as reference previous binding.
         In LIPS both letrec and letrec* behave the same.`),
    // ---------------------------------------------------------------------
    'let*': doc(
        let_macro(Symbol.for('let*')),
        `(let* ((a value-a) (b value-b)) body)

         Macro similar to \`let\` but next argument get environment
         from previous let variable, so they you can define one variable,
         and use in next argument.`),
    // ---------------------------------------------------------------------
    'let': doc(
        let_macro(Symbol.for('let')),
        `(let ((a value-a) (b value-b)) body)

         Macro that creates new environment, then evaluate and assign values to
         names and then evaluate the body in context of that environment.
         Values are evaluated sequentialy but you can't access
         previous values/names when next are evaluated. You can only get them
         from body of let expression.`),
    // ------------------------------------------------------------------
    'begin*': doc(pararel('begin*', function(values) {
        return values.pop();
    }), `(begin* . expr)

         This macro is parallel version of begin. It evaluate each expression and
         if it's a promise it will evaluate it in parallel and return value
         of last expression.`),
    // ------------------------------------------------------------------
    'begin': doc(new Macro('begin', function(code, options) {
        var args = Object.assign({ }, options);
        var arr = global_env.get('list->array')(code);
        if (args.dynamic_scope) {
            args.dynamic_scope = this;
        }
        args.env = this;
        var result;
        return (function loop() {
            if (arr.length) {
                var code = arr.shift();
                var ret = evaluate(code, args);
                return unpromise(ret, value => {
                    result = value;
                    return loop();
                });
            } else {
                return result;
            }
        })();
    }), `(begin . args)

         Macro runs list of expression and return valuate of the list one.
         It can be used in place where you can only have single exression,
         like if expression.`),
    // ------------------------------------------------------------------
    'ignore': new Macro('ignore', function(code, { dynamic_scope, error }) {
        var args = { env: this, error };
        if (dynamic_scope) {
            args.dynamic_scope = this;
        }
        evaluate(new Pair(new LSymbol('begin'), code), args);
    }, `(ignore expression)

        Macro that will evaluate expression and swallow any promises that may
        be created. It wil run and ignore any value that may be returned by
        expression. The code should have side effects and/or when it's promise
        it should resolve to undefined.`),
    // ------------------------------------------------------------------
    'call/cc': doc(Macro.defmacro('call/cc', function(code, eval_args = {}) {
        const args = {
            env: this,
            ...eval_args
        };
        return unpromise(evaluate(code.car, args), (result) => {
            if (is_function(result)) {
                return result(new Continuation(null));
            }
        });
    }), `(call/cc proc)

         Not Yet Implemented.`),
    // ------------------------------------------------------------------
    define: doc(Macro.defmacro('define', function(code, eval_args) {
        var env = this;
        if (code.car instanceof Pair &&
            code.car.car instanceof LSymbol) {
            var new_code = new Pair(
                new LSymbol("define"),
                new Pair(
                    code.car.car,
                    new Pair(
                        new Pair(
                            new LSymbol("lambda"),
                            new Pair(
                                code.car.cdr,
                                code.cdr
                            )
                        )
                    )
                )
            );
            return new_code;
        } else if (eval_args.macro_expand) {
            // prevent evaluation in macroexpand
            return;
        }
        if (eval_args.dynamic_scope) {
            eval_args.dynamic_scope = this;
        }
        eval_args.env = env;
        var value = code.cdr.car;
        let new_expr;
        if (value instanceof Pair) {
            value = evaluate(value, eval_args);
            new_expr = true;
        } else if (value instanceof LSymbol) {
            value = env.get(value);
        }
        typecheck('define', code.car, 'symbol');
        return unpromise(value, value => {
            if (env.__name__ === Syntax.__merge_env__) {
                env = env.__parent__;
            }
            if (new_expr &&
                ((is_function(value) && is_lambda(value)) ||
                 (value instanceof Syntax))) {
                value.__name__ = code.car.valueOf();
                if (value.__name__ instanceof LString) {
                    value.__name__ = value.__name__.valueOf();
                }
            }
            let __doc__;
            if (code.cdr.cdr instanceof Pair &&
                LString.isString(code.cdr.cdr.car)) {
                __doc__ = code.cdr.cdr.car.valueOf();
            }
            env.set(code.car, value, __doc__, true);
        });
    }), `(define name expression)
         (define name expression "doc string")
         (define (function-name . args) body)

         Macro for defining values. It can be used to define variables,
         or function. If first argument is list it will create function
         with name beeing first element of the list. The macro evalute
         code \`(define function (lambda args body))\``),
    // ------------------------------------------------------------------
    'set-obj!': doc('set-obj!', function(obj, key, value) {
        var obj_type = typeof obj;
        if (is_null(obj) || (obj_type !== 'object' && obj_type !== 'function')) {
            var msg = type_error_message('set-obj!', type(obj), ['object', 'function']);
            throw new Error(msg);
        }
        typecheck('set-obj!', key, ['string', 'symbol', 'number']);
        obj = unbind(obj);
        key = key.valueOf();
        if (arguments.length === 2) {
            delete obj[key];
        } else if (is_prototype(obj) && is_function(value)) {
            obj[key] = unbind(value);
            obj[key][__prototype__] = true;
        } else if (is_function(value) || is_native(value) || value === nil) {
            obj[key] = value;
        } else {
            obj[key] = value && !is_prototype(value) ? value.valueOf() : value;
        }
    }, `(set-obj! obj key value)

        Function set property of JavaScript object`),
    // ------------------------------------------------------------------
    'null-environment': doc('null-environment', function() {
        return global_env.inherit('null');
    }, `(null-environment)

        Function return new base environment with std lib.`),
    // ------------------------------------------------------------------
    'values': doc('values', function values(...args) {
        return Values(args);
    }, `(values a1 a2 ...)

            If called with more then one elment it will create special
            Values object that can be used in call-with-values function`),
    // ------------------------------------------------------------------
    'call-with-values': doc('call-with-values', function(producer, consumer) {
        typecheck('call-with-values', producer, 'function', 1);
        typecheck('call-with-values', consumer, 'function', 2);
        var maybe = producer();
        if (maybe instanceof Values) {
            return consumer(...maybe.valueOf());
        }
        return consumer(maybe);
    }, `(call-with-values producer consumer)

        Calls its producer argument with no values and a continuation that,
        when passed some values, calls the consumer procedure with those
        values as arguments.`),
    // ------------------------------------------------------------------
    'current-environment': doc('current-environment', function() {
        if (this.__name__ === '__frame__') {
            return this.__parent__;
        }
        return this;
    }, `(current-environment)

        Function return current environement.`),
    // ------------------------------------------------------------------
    'parent.frame': doc('parent.frame', function() {
        return user_env;
    }, `(parent.frame)

        Return parent environment if called from inside function.
        If no parent frame found it return nil.`),
    // ------------------------------------------------------------------
    'eval': doc('eval', function(code, env) {
        env = env || this.get('current-environment').call(this);
        return evaluate(code, {
            env,
            //dynamic_scope: this,
            error: e => {
                var error = global_env.get('display-error');
                error.call(this, e.message);
                if (e.code) {
                    var stack = e.code.map((line, i) => {
                        return `[${i + 1}]: ${line}`;
                    }).join('\n');
                    error.call(this, stack);
                }
            }
        });
    }, `(eval expr)
        (eval expr environment)

        Function evalute LIPS Scheme code.`),
    // ------------------------------------------------------------------
    lambda: new Macro('lambda', function(code, { dynamic_scope, error } = {}) {
        var self = this;
        var __doc__;
        if (code.cdr instanceof Pair &&
            LString.isString(code.cdr.car) &&
            code.cdr.cdr !== nil) {
            __doc__ = code.cdr.car.valueOf();
        }
        function lambda(...args) {
            var env;
            // this is function calling env
            // self is lexical scope when function was defined
            if (dynamic_scope) {
                if (!(this instanceof Environment)) {
                    env = self;
                } else {
                    env = this;
                }
            } else {
                env = self;
            }
            env = env.inherit('lambda');
            var name = code.car;
            var i = 0;
            var value;
            if (typeof this !== 'undefined' && !(this instanceof Environment)) {
                if (this && !this.__instance__) {
                    Object.defineProperty(this, '__instance__', {
                        enumerable: false,
                        get: () => true,
                        set: () => {},
                        configurable: false
                    });
                }
                env.set('this', this);
            }
            // arguments and arguments.callee inside lambda function
            if (this instanceof Environment) {
                var options = { throwError: false };
                env.set('arguments', this.get('arguments', options));
                env.set('parent.frame', this.get('parent.frame', options));
            } else {
                // this case is for lambda as callback function in JS; e.g. setTimeout
                var _args = args.slice();
                _args.callee = lambda;
                _args.env = env;
                env.set('arguments', _args);
            }
            if (name instanceof LSymbol || name !== nil) {
                while (true) {
                    if (name.car !== nil) {
                        if (name instanceof LSymbol) {
                            // rest argument,  can also be first argument
                            value = quote(Pair.fromArray(args.slice(i), false));
                            env.__env__[name.__name__] = value;
                            break;
                        } else {
                            value = args[i];
                            env.__env__[name.car.__name__] = value;
                        }
                    }
                    if (name.cdr === nil) {
                        break;
                    }
                    i++;
                    name = name.cdr;
                }
            }
            if (dynamic_scope) {
                dynamic_scope = env;
            }
            var rest = __doc__ ? code.cdr.cdr : code.cdr;
            var output = new Pair(new LSymbol('begin'), rest);
            return evaluate(output, { env, dynamic_scope, error });
        }
        var length = code.car instanceof Pair ? code.car.length() : null;
        lambda.__code__ = new Pair(new LSymbol('lambda'), code);
        lambda[__lambda__] = true;
        if (!(code.car instanceof Pair)) {
            return doc(lambda, __doc__, true); // variable arguments
        }
        // wrap and decorate with __doc__
        return doc(set_fn_length(lambda, length), __doc__, true);
    }, `(lambda (a b) body)
        (lambda args body)
        (lambda (a b . rest) body)

        Macro lambda create new anonymous function, if first element of the body
        is string and there is more elements it will be documentation, that can
        be read using (help fn)`),
    'macroexpand': new Macro('macroexpand', macro_expand()),
    'macroexpand-1': new Macro('macroexpand-1', macro_expand(true)),
    // ------------------------------------------------------------------
    'define-macro': define_macro,
    // ------------------------------------------------------------------
    'syntax-rules': syntax_rules,
    // ------------------------------------------------------------------
    quote: quote,
    'unquote-splicing': doc('unquote-splicing', function() {
        throw new Error(`You can't call \`unquote-splicing\` outside of quasiquote`);
    }, `(unquote-splicing code)

        Special form to be used in quasiquote macro, parser is processing special
        characters ,@ and create call to this pseudo function. It can be used
        to evalute expression inside and return the value without parenthesis.
        the value will be joined to the output list structure.`),
    'unquote': doc('unquote', function() {
        throw new Error(`You can't call \`unquote\` outside of quasiquote`);
    }, `(unquote code)

        Special form to be used in quasiquote macro, parser is processing special
        characters , and create call to this pseudo function. It can be used
        to evalute expression inside and return the value, the output is inserted
        into list structure created by queasiquote.`),
    // ------------------------------------------------------------------
    quasiquote: quasiquote,
    // ------------------------------------------------------------------
    clone: doc('clone', function clone(list) {
        typecheck('clone', list, 'pair');
        return list.clone();
    }, `(clone list)

            Function return clone of the list.`),
    // ------------------------------------------------------------------
    append: doc('append', function append(...items) {
        items = items.map(item => {
            if (item instanceof Pair) {
                return item.clone();
            }
            return item;
        });
        return global_env.get('append!').call(this, ...items);
    }, `(append item ...)

        Function will create new list with eac argument appended to the end.
        It will always return new list and not modify it's arguments.`),
    // ------------------------------------------------------------------
    'append!': doc('append!', function(...items) {
        var is_list = global_env.get('list?');
        return items.reduce((acc, item) => {
            typecheck('append!', acc, ['nil', 'pair']);
            if ((item instanceof Pair || item === nil) && !is_list(item)) {
                throw new Error('append!: Invalid argument, value is not a list');
            }
            if (is_null(item)) {
                return acc;
            }
            if (acc === nil) {
                if (item === nil) {
                    return nil;
                }
                return item;
            }
            return acc.append(item);
        }, nil);
    }, `(append! arg1 ...)

        Destructive version of append, it modify the list in place. It return
        new list where each argument is appened to the end. It may modify
        lists added as arguments.`),
    // ------------------------------------------------------------------
    reverse: doc('reverse', function reverse(arg) {
        typecheck('reverse', arg, ['array', 'pair', 'nil']);
        if (arg === nil) {
            return nil;
        }
        if (arg instanceof Pair) {
            var arr = global_env.get('list->array')(arg).reverse();
            return global_env.get('array->list')(arr);
        } else if (!(arg instanceof Array)) {
            throw new Error(type_error_message('reverse', type(arg), 'array or pair'));
        } else {
            return arg.reverse();
        }
    }, `(reverse list)

        Function will reverse the list or array. If value is not a list
        or array it will throw exception.`),
    // ------------------------------------------------------------------
    nth: doc('nth', function nth(index, obj) {
        typecheck('nth', index, 'number');
        typecheck('nth', obj, ['array', 'pair']);
        if (obj instanceof Pair) {
            var node = obj;
            var count = 0;
            while (count < index) {
                if (!node.cdr || node.cdr === nil || node.haveCycles('cdr')) {
                    return nil;
                }
                node = node.cdr;
                count++;
            }
            return node.car;
        } else if (obj instanceof Array) {
            return obj[index];
        } else {
            throw new Error(type_error_message('nth', type(obj), 'array or pair', 2));
        }
    }, `(nth index obj)

        Function return nth element of the list or array. If used with different
        value it will throw exception`),
    // ------------------------------------------------------------------
    list: doc('list', function list(...args) {
        return args.reverse().reduce((list, item) => new Pair(item, list), nil);
    }, `(list . args)

        Function create new list out of its arguments.`),
    // ------------------------------------------------------------------
    substring: doc('substring', function substring(string, start, end) {
        typecheck('substring', string, 'string');
        typecheck('substring', start, 'number');
        typecheck('substring', end, ['number', 'undefined']);
        return string.substring(start.valueOf(), end && end.valueOf());
    }, `(substring string start end)

        Function return part of the string starting at start ending with end.`),
    // ------------------------------------------------------------------
    concat: doc('concat', function concat(...args) {
        args.forEach((arg, i) => typecheck('concat', arg, 'string', i + 1));
        return args.join('');
    }, `(concat . strings)

        Function create new string by joining its arguments`),
    // ------------------------------------------------------------------
    join: doc('join', function join(separator, list) {
        typecheck('join', separator, 'string');
        typecheck('join', list, ['pair', 'nil']);
        return global_env.get('list->array')(list).join(separator);
    }, `(join separator list)

            Function return string by joining elements of the list`),
    // ------------------------------------------------------------------
    split: doc('split', function split(separator, string) {
        typecheck('split', separator, ['regex', 'string']);
        typecheck('split', string, 'string');
        return global_env.get('array->list')(string.split(separator));
    }, `(split separator string)

        Function create list by splitting string by separatar that can
        be a string or regular expression.`),
    // ------------------------------------------------------------------
    replace: doc('replace', function replace(pattern, replacement, string) {
        typecheck('replace', pattern, ['regex', 'string']);
        typecheck('replace', replacement, ['string', 'function']);
        typecheck('replace', string, 'string');
        return string.replace(pattern, replacement);
    }, `(replace pattern replacement string)

        Function change pattern to replacement inside string. Pattern can be string
        or regex and replacement can be function or string.`),
    // ------------------------------------------------------------------
    match: doc('match', function match(pattern, string) {
        typecheck('match', pattern, ['regex', 'string']);
        typecheck('match', string, 'string');
        var m = string.match(pattern);
        return m ? global_env.get('array->list')(m) : false;
    }, `(match pattern string)

        function return match object from JavaScript as list or #f if not match.`),
    // ------------------------------------------------------------------
    search: doc('search', function search(pattern, string) {
        typecheck('search', pattern, ['regex', 'string']);
        typecheck('search', string, 'string');
        return string.search(pattern);
    }, `(search pattern string)

        Function return first found index of the pattern inside a string`),
    // ------------------------------------------------------------------
    repr: doc('repr', function repr(obj, quote) {
        return toString(obj, quote);
    }, `(repr obj)

        Function return string LIPS representation of an object as string.`),
    // ------------------------------------------------------------------
    'escape-regex': doc('escape-regex', function(string) {
        typecheck('escape-regex', string, 'string');
        return escape_regex(string.valueOf());
    }, `(escape-regex string)

        Function return new string where all special operators used in regex,
        are escaped with slash so they can be used in RegExp constructor
        to match literal string`),
    // ------------------------------------------------------------------
    env: doc('env', function env(env) {
        env = env || this;
        var names = Object.keys(env.__env__).map(LSymbol);
        // TODO: get symbols
        var result;
        if (names.length) {
            result = Pair.fromArray(names);
        } else {
            result = nil;
        }
        if (env.__parent__ instanceof Environment) {
            return global_env.get('env')(env.__parent__).append(result);
        }
        return result;
    }, `(env)
        (env obj)

        Function return list of values (functions, macros and variables)
        inside environment and it's parents.`),
    // ------------------------------------------------------------------
    'new': doc('new', function(obj, ...args) {
        var instance = new (unbind(obj))(...args.map(x => unbox(x)));
        return instance;
    }, `(new obj . args)

            Function create new JavaScript instance of an object.`),
    // ------------------------------------------------------------------
    'typecheck': doc(
        typecheck,
        `(typecheck label value type [position])

         Function check type and throw exception if type don't match.
         Type can be string or list of strings. Position optional argument
         is used to created proper error message.`),
    // ------------------------------------------------------------------
    'unset-special!': doc('unset-special!', function(symbol) {
        typecheck('remove-special!', symbol, 'string');
        delete specials.remove(symbol.valueOf());
    }, `(unset-special! name)

        Function remove special symbol from parser. Added by \`set-special!\`,
        name must be a string.`),
    // ------------------------------------------------------------------
    'set-special!': doc('set-special!', function(seq, name, type = specials.LITERAL) {
        typecheck('set-special!', seq, 'string', 1);
        typecheck('set-special!', name, 'symbol', 2);
        specials.append(seq.valueOf(), name, type);
    }, `(set-special! symbol name [type])

        Add special symbol to the list of transforming operators by the parser.
        e.g.: \`(add-special! "#" 'x)\` will allow to use \`#(1 2 3)\` and it will be
        transformed into (x (1 2 3)) so you can write x macro that will process
        the list. 3rd argument is optional and it can be constant value
        lips.specials.SPLICE if this constant is used it will transform
        \`#(1 2 3)\` into (x 1 2 3) that is required by # that define vectors.`),
    // ------------------------------------------------------------------
    'get': get,
    '.': get,
    // ------------------------------------------------------------------
    'unbind': doc(
        unbind,
        `(unbind fn)

         Function remove bidning from function so you can get props from it.`),
    // ------------------------------------------------------------------
    type: doc(
        type,
        `(type object)

         Function return type of an object as string.`),
    // ------------------------------------------------------------------
    'debugger': doc('debugger', function() {
        /* eslint-disable */
        debugger;
        /* eslint-enable */
    }, `(debugger)

        Function stop JavaScript code in debugger.`),
    // ------------------------------------------------------------------
    'in': doc('in', function(a, b) {
        if (a instanceof LSymbol ||
            a instanceof LString ||
            a instanceof LNumber) {
            a = a.valueOf();
        }
        return a in unbox(b);
    }, `(in key value)

        Function use is in operator to check if value is in object.`),
    // ------------------------------------------------------------------
    'instanceof': doc('instanceof', function(type, obj) {
        return obj instanceof unbind(type);
    }, `(instanceof type obj)

        Function check of object is instance of object.`),
    // ------------------------------------------------------------------
    'prototype?': doc(
        'prototype?',
        is_prototype,
        `(prototype? obj)

         Function check if value is JavaScript Object prototype.`),
    // ------------------------------------------------------------------
    'macro?': doc('macro?', function(obj) {
        return obj instanceof Macro;
    }, `(macro? expression)

        Function check if value is a macro.`),
    // ------------------------------------------------------------------
    'function?': doc(
        'function?',
        is_function,
        `(function? expression)

         Function check if value is a function.`),
    // ------------------------------------------------------------------
    'real?': doc('real?', function(value) {
        if (type(value) !== 'number') {
            return false;
        }
        if (value instanceof LNumber) {
            return value.isFloat();
        }
        return LNumber.isFloat(value);
    }, `(real? number)

        Function check if value is real number.`),
    // ------------------------------------------------------------------
    'number?': doc('number?', function(x) {
        return Number.isNaN(x) || LNumber.isNumber(x);
    }, `(number? expression)

        Function check if value is a number or NaN value.`),
    // ------------------------------------------------------------------
    'string?': doc('string?', function(obj) {
        return LString.isString(obj);
    }, `(string? expression)

        Function check if value is a string.`),
    // ------------------------------------------------------------------
    'pair?': doc('pair?', function(obj) {
        return obj instanceof Pair;
    }, `(pair? expression)

        Function check if value is a pair or list structure.`),
    // ------------------------------------------------------------------
    'regex?': doc('regex?', function(obj) {
        return obj instanceof RegExp;
    }, `(regex? expression)

        Function check if value is regular expression.`),
    // ------------------------------------------------------------------
    'null?': doc('null?', function(obj) {
        return is_null(obj);
    }, `(null? expression)

        Function check if value is nulish.`),
    // ------------------------------------------------------------------
    'boolean?': doc('boolean?', function(obj) {
        return typeof obj === 'boolean';
    }, `(boolean? expression)

        Function check if value is boolean.`),
    // ------------------------------------------------------------------
    'symbol?': doc('symbol?', function(obj) {
        return obj instanceof LSymbol;
    }, `(symbol? expression)

        Function check if value is LIPS symbol`),
    // ------------------------------------------------------------------
    'array?': doc('array?', function(obj) {
        return obj instanceof Array;
    }, `(array? expression)

        Function check if value is an arrray.`),
    // ------------------------------------------------------------------
    'object?': doc('object?', function(obj) {
        return obj !== nil && obj !== null &&
            !(obj instanceof LCharacter) &&
            !(obj instanceof RegExp) &&
            !(obj instanceof LString) &&
            !(obj instanceof Pair) &&
            !(obj instanceof LNumber) &&
            typeof obj === 'object' &&
            !(obj instanceof Array);
    }, `(object? expression)

        Function check if value is an plain object.`),
    // ------------------------------------------------------------------
    flatten: doc('flatten', function flatten(list) {
        typecheck('flatten', list, 'pair');
        return list.flatten();
    }, `(flatten list)

        Return shallow list from tree structure (pairs).`),
    // ------------------------------------------------------------------
    'array->list': doc('array->list', function(array) {
        typecheck('array->list', array, 'array');
        return Pair.fromArray(array);
    }, `(array->list array)

        Function convert JavaScript array to LIPS list.`),
    // ------------------------------------------------------------------
    'tree->array': doc(
        'tree->array',
        to_array('tree->array', true),
        `(tree->array list)

         Function convert LIPS list structure into JavaScript array.`),
    // ------------------------------------------------------------------
    'list->array': doc(
        'list->array',
        to_array('list->array'),
        `(list->array list)

         Function convert LIPS list into JavaScript array.`),
    // ------------------------------------------------------------------
    apply: doc('apply', function apply(fn, ...args) {
        typecheck('apply', fn, 'function', 1);
        var last = args.pop();
        typecheck('apply', last, ['pair', 'nil'], args.length + 2);
        args = args.concat(global_env.get('list->array').call(this, last));
        return fn.apply(this, prepare_fn_args(fn, args));
    }, `(apply fn list)

        Function that call function with list of arguments.`),
    // ------------------------------------------------------------------
    length: doc('length', function length(obj) {
        if (!obj || obj === nil) {
            return 0;
        }
        if (obj instanceof Pair) {
            return obj.length();
        }
        if ("length" in obj) {
            return obj.length;
        }
    }, `(length expression)

        Function return length of the object, the object can be list
        or any object that have length property.`),
    // ------------------------------------------------------------------
    'string->number': doc(
        'string->number',
        string_to_number,
        `(string->number number [radix])

         Function convert string to number.`),
    // ------------------------------------------------------------------
    'try': doc(new Macro('try', function(code, { dynamic_scope, error }) {
        return new Promise((resolve, reject) => {
            var catch_clause, finally_clause;
            if (LSymbol.is(code.cdr.car.car, 'catch')) {
                catch_clause = code.cdr.car;
                if (code.cdr.cdr instanceof Pair &&
                    LSymbol.is(code.cdr.cdr.car.car, 'finally')) {
                    finally_clause = code.cdr.cdr.car;
                }
            } else if (LSymbol.is(code.cdr.car.car, 'finally')) {
                finally_clause = code.cdr.car;
            }
            if (!(finally_clause || catch_clause)) {
                throw new Error('try: invalid syntax');
            }
            var next = resolve;
            if (finally_clause) {
                next = function(result, cont) {
                    // prevent infinite loop when finally throw exception
                    next = reject;
                    unpromise(evaluate(new Pair(
                        new LSymbol('begin'),
                        finally_clause.cdr
                    ), args), function() {
                        cont(result);
                    });
                };
            }
            var args = {
                env: this,
                error: (e) => {
                    var env = this.inherit('try');
                    if (catch_clause) {
                        env.set(catch_clause.cdr.car.car, e);
                        var args = {
                            env,
                            error
                        };
                        if (dynamic_scope) {
                            args.dynamic_scope = this;
                        }
                        unpromise(evaluate(new Pair(
                            new LSymbol('begin'),
                            catch_clause.cdr.cdr
                        ), args), function(result) {
                            next(result, resolve);
                        });
                    } else {
                        next(e, error);
                    }
                }
            };
            if (dynamic_scope) {
                args.dynamic_scope = this;
            }
            var result = evaluate(code.car, args);
            if (is_promise(result)) {
                result.then(result => {
                    next(result, resolve);
                }).catch(args.error);
            } else {
                next(result, resolve);
            }
        });
    }), `(try expr (catch (e) code))
         (try expr (catch (e) code) (finally code))
         (try expr (finally code))

         Macro execute user code and catch exception. If catch is provided
         it's executed when expression expr throw error. If finally is provide
         it's always executed at the end.`),
    // ------------------------------------------------------------------
    'raise': doc('raise', function(obj) {
        throw obj;
    }, `(raise obj)

        Throws new exception with given object.`),
    'throw': doc('throw', function(message) {
        throw new Error(message);
    }, `(throw string)

        Throws new expection.`),
    // ------------------------------------------------------------------
    find: doc('find', function find(arg, list) {
        typecheck('find', arg, ['regex', 'function']);
        typecheck('find', list, ['pair', 'nil']);
        if (is_null(list)) {
            return nil;
        }
        var fn = matcher('find', arg);
        return unpromise(fn(list.car), function(value) {
            if (value && value !== nil) {
                return list.car;
            }
            return find(arg, list.cdr);
        });
    }, `(find fn list)
        (find regex list)

        Higher order Function find first value for which function return true.
        If called with regex it will create matcher function.`),
    // ------------------------------------------------------------------
    'for-each': doc('for-each', function(fn, ...lists) {
        typecheck('for-each', fn, 'function');
        lists.forEach((arg, i) => {
            typecheck('for-each', arg, ['pair', 'nil'], i + 1);
        });
        // we need to use call(this because babel transpile this code into:
        // var ret = map.apply(void 0, [fn].concat(lists));
        // it don't work with weakBind
        var ret = global_env.get('map').call(this, fn, ...lists);
        if (is_promise(ret)) {
            return ret.then(() => {});
        }
    }, `(for-each fn . lists)

        Higher order function that call function \`fn\` by for each
        value of the argument. If you provide more then one list as argument
        it will take each value from each list and call \`fn\` function
        with that many argument as number of list arguments.`),
    // ------------------------------------------------------------------
    map: doc('map', function map(fn, ...lists) {
        typecheck('map', fn, 'function');
        var is_list = global_env.get('list?');
        lists.forEach((arg, i) => {
            typecheck('map', arg, ['pair', 'nil'], i + 1);
            // detect cycles
            if (arg instanceof Pair && !is_list.call(this, arg)) {
                throw new Error(`map: argument ${i + 1} is not a list`);
            }
        });
        if (lists.length === 0) {
            return nil;
        }
        if (lists.some(x => x === nil)) {
            return nil;
        }
        var args = lists.map(l => l.car);
        var parent_frame = this.get('parent.frame');
        var env = this.newFrame(fn, args);
        env.set('parent.frame', parent_frame);
        return unpromise(fn.call(env, ...args), (head) => {
            return unpromise(map.call(this, fn, ...lists.map(l => l.cdr)), (rest) => {
                return new Pair(head, rest);
            });
        });
    }, `(map fn . lists)

        Higher order function that call function \`fn\` by for each
        value of the argument. If you provide more then one list as argument
        it will take each value from each list and call \`fn\` function
        with that many argument as number of list arguments. The return
        values of the function call is acumulated in result list and
        returned by the call to map.`),
    // ------------------------------------------------------------------
    'list?': doc('list?', function(obj) {
        var node = obj;
        while (true) {
            if (node === nil) {
                return true;
            }
            if (!(node instanceof Pair)) {
                return false;
            }
            if (node.haveCycles('cdr')) {
                return false;
            }
            node = node.cdr;
        }
    }, `(list? obj)

        Function test if value is proper linked list structure.
        The car of each pair can be any value. It return false on cycles."`),
    // ------------------------------------------------------------------
    some: doc('some', function some(fn, list) {
        typecheck('some', fn, 'function');
        typecheck('some', list, ['pair', 'nil']);
        if (is_null(list)) {
            return false;
        } else {
            return unpromise(fn(list.car), (value) => {
                return value || some(fn, list.cdr);
            });
        }
    }, `(some fn list)

        Higher order function that call argument on each element of the list.
        It stops when function fn return true for a value if so it will
        return true. If none of the values give true, the function return false`),
    // ------------------------------------------------------------------
    fold: doc('fold', fold('fold', function(fold, fn, init, ...lists) {
        typecheck('fold', fn, 'function');
        lists.forEach((arg, i) => {
            typecheck('fold', arg, ['pair', 'nil'], i + 1);
        });
        if (lists.some(x => x === nil)) {
            return init;
        }
        const value = fold.call(this, fn, init, ...lists.map(l => l.cdr));
        return unpromise(value, value => {
            return fn(...lists.map(l => l.car), value);
        });
    }), `(fold fn init . lists)

         Function fold is reverse of the reduce. it call function \`fn\`
         on each elements of the list and return single value.
         e.g. it call (fn a1 b1 (fn a2 b2 (fn a3 b3 '())))
         for: (fold fn '() alist blist)`),
    // ------------------------------------------------------------------
    pluck: doc('pluck', function pluck(...keys) {
        return function(obj) {
            keys = keys.map(x => x instanceof LSymbol ? x.__name__ : x);
            if (keys.length === 0) {
                return nil;
            } else if (keys.length === 1) {
                const [key] = keys;
                return obj[key];
            }
            var result = {};
            keys.forEach((key) => {
                result[key] = obj[key];
            });
            return result;
        };
    }, `(pluck . string)

        If called with single string it will return function that will return
        key from object. If called with more then one argument function will
        return new object by taking all properties from given object.`),
    // ------------------------------------------------------------------
    reduce: doc('reduce', fold('reduce', function(reduce, fn, init, ...lists) {
        typecheck('reduce', fn, 'function');
        lists.forEach((arg, i) => {
            typecheck('reduce', arg, ['pair', 'nil'], i + 1);
        });
        if (lists.some(x => x === nil)) {
            return init;
        }
        return unpromise(fn(...lists.map(l => l.car), init), (value) => {
            return reduce.call(this, fn, value, ...lists.map(l => l.cdr));
        });
    }), `(reduce fn init list . lists)

         Higher order function take each element of the list and call
         the function with result of previous call or init and next element
         on the list until each element is processed and return single value
         as result of last call to \`fn\` function.
         e.g. it call (fn a3 b3 (fn a2 b2 (fn a1 b1 init)))
         for (reduce fn init alist blist)`),
    // ------------------------------------------------------------------
    filter: doc('filter', function filter(arg, list) {
        typecheck('filter', arg, ['regex', 'function']);
        typecheck('filter', list, ['pair', 'nil']);
        var array = global_env.get('list->array')(list);
        var result = [];
        var fn = matcher('filter', arg);
        return (function loop(i) {
            function next(value) {
                if (value && value !== nil) {
                    result.push(item);
                }
                return loop(++i);
            }
            if (i === array.length) {
                return Pair.fromArray(result);
            }
            var item = array[i];
            return unpromise(fn(item), next);
        })(0);
    }, `(filter fn list)
        (filter regex list)

        Higher order function that call \`fn\` for each element of the list
        and return list for only those elements for which funtion return
        true value. If called with regex it will create matcher function.`),
    // ------------------------------------------------------------------
    compose: doc(
        compose,
        `(compose . fns)

         Higher order function and create new function that apply all functions
         From right to left and return it's value. Reverse of compose.
         e.g.:
         ((compose (curry + 2) (curry * 3)) 3)
         11
        `),
    pipe: doc(
        pipe,
        `(pipe . fns)

         Higher order function and create new function that apply all functions
         From left to right and return it's value. Reverse of compose.
         e.g.:
         ((pipe (curry + 2) (curry * 3)) 3)
         15`),
    curry: doc(
        curry,
        `(curry fn . args)

         Higher order function that create curried version of the function.
         The result function will have parially applied arguments and it
         will keep returning functions until all arguments are added

         e.g.:
         (define (add a b c d) (+ a b c d))
         (define add1 (curry add 1))
         (define add12 (add 2))
         (display (add12 3 4))`),
    // ------------------------------------------------------------------
    // Numbers
    // ------------------------------------------------------------------
    gcd: doc('gcd', function gcd(...args) {
        typecheck_args('lcm', args, 'number');
        return args.reduce(function(result, item) {
            return result.gcd(item);
        });
    }, `(gcd n1 n2 ...)

        Function return the greatest common divisor of their arguments.`),
    // ------------------------------------------------------------------
    lcm: doc('lcm', function lcm(...args) {
        typecheck_args('lcm', args, 'number');
        // ref: https://rosettacode.org/wiki/Least_common_multiple#JavaScript
        var n = args.length, a = abs(args[0]);
        for (var i = 1; i < n; i++) {
            var b = abs(args[i]), c = a;
            while (a && b) {
                a > b ? a %= b : b %= a;
            }
            a = abs(c * args[i]) / (a + b);
        }
        return LNumber(a);
    }, `(lcm n1 n2 ...)

        Function return the least common multiple of their arguments.`),
    // ------------------------------------------------------------------
    'odd?': doc('odd?', single_math_op(function(num) {
        return LNumber(num).isOdd();
    }), `(odd? number)

         Function check if number os odd.`),
    // ------------------------------------------------------------------
    'even?': doc('even?', single_math_op(function(num) {
        return LNumber(num).isEven();
    }), `(even? number)

         Function check if number is even.`),
    // ------------------------------------------------------------------
    // math functions
    '*': doc('*', reduce_math_op(function(a, b) {
        return LNumber(a).mul(b);
    }, LNumber(1)), `(* . numbers)

        Multiplicate all numbers passed as arguments. If single value is passed
        it will return that value.`),
    // ------------------------------------------------------------------
    '+': doc('+', reduce_math_op(function(a, b) {
        return LNumber(a).add(b);
    }, LNumber(0)), `(+ . numbers)

        Sum all numbers passed as arguments. If single value is passed it will
        return that value.`),
    // ------------------------------------------------------------------
    '-': doc('-', function(...args) {
        if (args.length === 0) {
            throw new Error('-: procedure require at least one argument');
        }
        typecheck_args('-', args, 'number');
        if (args.length === 1) {
            return LNumber(args[0]).sub();
        }
        if (args.length) {
            return args.reduce(binary_math_op(function(a, b) {
                return LNumber(a).sub(b);
            }));
        }
    }, `(- n1 n2 ...)
        (- n)

        Substract number passed as argument. If only one argument is passed
        it will negate the value.`),
    // ------------------------------------------------------------------
    '/': doc('/', function(...args) {
        if (args.length === 0) {
            throw new Error('/: procedure require at least one argument');
        }
        typecheck_args('/', args, 'number');
        if (args.length === 1) {
            return LNumber(1).div(args[0]);
        }
        return args.reduce(binary_math_op(function(a, b) {
            return LNumber(a).div(b);
        }));
    }, `(/ n1 n2 ...)
        (/ n)

        Divide number passed as arguments one by one. If single argument
        is passed it will calculate (/ 1 n1).`),
    // ------------------------------------------------------------------
    abs: doc('abs', single_math_op(function(n) {
        return LNumber(n).abs();
    }), `(abs number)

         Function create absolute value from number.`),
    // ------------------------------------------------------------------
    truncate: doc('truncate', function(n) {
        typecheck('truncate', n, 'number');
        if (LNumber.isFloat(n)) {
            if (n instanceof LNumber) {
                n = n.valueOf();
            }
            return LFloat(truncate(n));
        }
        return n;
    }, `(truncate n)

        Function return integer value from real number.`),
    // ------------------------------------------------------------------
    sqrt: doc('sqrt', single_math_op(function(n) {
        return LNumber(n).sqrt();
    }), `(sqrt number)

         Function return square root of the number.`),
    // ------------------------------------------------------------------
    '**': doc('**', binary_math_op(function(a, b) {
        a = LNumber(a);
        b = LNumber(b);
        if (b.cmp(0) === -1) {
            return LFloat(1).div(a).pow(b.sub());
        }
        return a.pow(b);
    }), `(** a b)

         Function calculate number a to to the power of b.`),
    // ------------------------------------------------------------------
    '1+': doc('1+', single_math_op(function(number) {
        return LNumber(number).add(1);
    }), `(1+ number)

         Function add 1 to the number and return result.`),
    // ------------------------------------------------------------------
    '1-': doc(single_math_op(function(number) {
        return LNumber(number).sub(1);
    }), `(1- number)

         Function substract 1 from the number and return result.`),
    // ------------------------------------------------------------------
    '%': doc('%', function(a, b) {
        typecheck_args('%', [a, b], 'number');
        return LNumber(a).rem(b);
    }, `(% n1 n2)

        Function get reminder of it's arguments.`),
    // ------------------------------------------------------------------
    // Booleans
    '==': doc('==', function(...args) {
        typecheck_args('==', args, 'number');
        return seq_compare((a, b) => LNumber(a).cmp(b) === 0, args);
    }, `(== x1 x2 ...)

        Function compare its numerical arguments and check if they are equal`),
    // ------------------------------------------------------------------
    '>': doc('>', function(...args) {
        typecheck_args('>', args, 'number');
        return seq_compare((a, b) => LNumber(a).cmp(b) === 1, args);
    }, `(> x1 x2 ...)

        Function compare its numerical arguments and check if they are
        monotonically increasing`),
    // ------------------------------------------------------------------
    '<': doc('<', function(...args) {
        typecheck_args('<', args, 'number');
        return seq_compare((a, b) => LNumber(a).cmp(b) === -1, args);
    }, `(< x1 x2 ...)

        Function compare its numerical arguments and check if they are
        monotonically decreasing`),
    // ------------------------------------------------------------------
    '<=': doc('<=', function(...args) {
        typecheck_args('<=', args, 'number');
        return seq_compare((a, b) => [0, -1].includes(LNumber(a).cmp(b)), args);
    }, `(<= x1 x2 ...)

        Function compare its numerical arguments and check if they are
        monotonically nonincreasing`),
    // ------------------------------------------------------------------
    '>=': doc('>=', function(...args) {
        typecheck_args('>=', args, 'number');
        return seq_compare((a, b) => [0, 1].includes(LNumber(a).cmp(b)), args);
    }, `(>= x1 x2 ...)

        Function compare its numerical arguments and check if they are
        monotonically nondecreasing`),
    // ------------------------------------------------------------------
    'eq?': doc(
        'eq?',
        equal,
        `(eq? a b)

         Function compare two values if they are identical.`),
    // ------------------------------------------------------------------
    or: doc(new Macro('or', function(code, { dynamic_scope, error }) {
        var args = global_env.get('list->array')(code);
        var self = this;
        if (dynamic_scope) {
            dynamic_scope = self;
        }
        if (!args.length) {
            return false;
        }
        var result;
        return (function loop() {
            function next(value) {
                result = value;
                if (result !== false) {
                    return result;
                } else {
                    return loop();
                }
            }
            if (!args.length) {
                if (result !== false) {
                    return result;
                } else {
                    return false;
                }
            } else {
                var arg = args.shift();
                var value = evaluate(arg, { env: self, dynamic_scope, error });
                return unpromise(value, next);
            }
        })();
    }), `(or . expressions)

         Macro execute the values one by one and return the one that is truthy value.
         If there are no expression that evaluate to true it return false.`),
    // ------------------------------------------------------------------
    and: doc(new Macro('and', function(code, { dynamic_scope, error } = {}) {
        var args = global_env.get('list->array')(code);
        var self = this;
        if (dynamic_scope) {
            dynamic_scope = self;
        }
        if (!args.length) {
            return true;
        }
        var result;
        return (function loop() {
            function next(value) {
                result = value;
                if (result === false) {
                    return false;
                } else {
                    return loop();
                }
            }
            if (!args.length) {
                if (result !== false) {
                    return result;
                } else {
                    return false;
                }
            } else {
                var arg = args.shift();
                var value = evaluate(arg, { env: self, dynamic_scope, error });
                return unpromise(value, next);
            }
        })();
    }), `(and . expressions)

         Macro evalute each expression in sequence if any value return false it will
         return false. If each value return true it will return the last value.
         If it's called without arguments it will return true.`),
    // bit operations
    '|': doc('|', function(a, b) {
        return LNumber(a).or(b);
    }, `(| a b)

        Function calculate or bit operation.`),
    '&': doc('&', function(a, b) {
        return LNumber(a).and(b);
    }, `(& a b)

        Function calculate and bit operation.`),
    '~': doc('~', function(a) {
        return LNumber(a).neg();
    }, `(~ number)

        Function negate the value.`),
    '>>': doc('>>', function(a, b) {
        return LNumber(a).shr(b);
    }, `(>> a b)

        Function right shit the value a by value b.`),
    '<<': doc('<<', function(a, b) {
        return LNumber(a).shl(b);
    }, `(<< a b)

        Function left shit the value a by value b.`),
    not: doc('not', function not(value) {
        if (is_null(value)) {
            return true;
        }
        return !value;
    }, `(not object)

        Function return negation of the argument.`)
}, undefined, 'global');

var user_env = global_env.inherit('user-env');
// -------------------------------------------------------------------------
function set_interaction_env(interaction, internal) {
    interaction.constant('**internal-env**', internal);
    interaction.doc(
        '**internal-env**',
        `**internal-env**

         Constant used to hide stdin, stdout and stderr so they don't interfere
         with variables with the same name. Constants are internal type
         of variables that can't be redefined, defining variable with same name
         will throw an error.`
    );
    global_env.set('**interaction-environment**', interaction);
}
// -------------------------------------------------------------------------
set_interaction_env(user_env, internal_env);
global_env.doc(
    '**interaction-environment**',
    `**interaction-environment**

     Internal dynamic, global variable used to find interpreter environment.
     It's used so the read and write functions can locate **internal-env**
     that contain references to stdin, stdout and stderr.`
);


// -------------------------------------------------------------------------
// ref: https://stackoverflow.com/a/4331218/387194
function allPossibleCases(arr) {
    if (arr.length === 1) {
        return arr[0];
    } else {
        var result = [];
        // recur with the rest of array
        var allCasesOfRest = allPossibleCases(arr.slice(1));
        for (var i = 0; i < allCasesOfRest.length; i++) {
            for (var j = 0; j < arr[0].length; j++) {
                result.push(arr[0][j] + allCasesOfRest[i]);
            }
        }
        return result;
    }
}

// -------------------------------------------------------------------------
function combinations(input, start, end) {
    var result = [];
    for (var i = start; i <= end; ++i) {
        var input_arr = [];
        for (var j = 0; j < i; ++j) {
            input_arr.push(input);
        }
        result = result.concat(allPossibleCases(input_arr));
    }
    return result;
}

// -------------------------------------------------------------------------
// cadr caddr cadadr etc.
combinations(['d', 'a'], 2, 5).forEach(spec => {
    const s = spec.split('');
    const chars = s.slice().reverse();
    const code = s.map(c => `(c${c}r`).join(' ') + ' arg' + ')'.repeat(s.length);
    const name = 'c' + spec + 'r';
    global_env.set(name, doc(name, function(arg) {
        return chars.reduce(function(list, type) {
            typecheck(name, list, 'pair');
            if (type === 'a') {
                return list.car;
            } else {
                return list.cdr;
            }
        }, arg);
    }, `(${name} arg)

        Function calculate ${code}`));
});

// -------------------------------------------------------------------------
(function() {
    var map = { ceil: 'ceiling' };
    ['floor', 'round', 'ceil'].forEach(fn => {
        var name = map[fn] ? map[fn] : fn;
        global_env.set(name, doc(name, function(value) {
            typecheck(name, value, 'number');
            if (value instanceof LNumber) {
                return value[fn]();
            }
        }, `(${name} number)

            Function calculate ${name} of a number.`));
    });
})();

// -----------------------------------------------------------------------------
function node_module_find(dir) {
    return reverse_find(dir, function(dir) {
        return fs.existsSync(path.join(dir, 'node_modules'));
    });
}

// -------------------------------------------------------------------------
function is_node() {
    return typeof global !== 'undefined' && global.global === global;
}

// -----------------------------------------------------------------------------
function reverse_find(dir, fn) {
    var parts = dir.split(path.sep).filter(Boolean);
    for (var i = parts.length; i--;) {
        var p = path.join('/', ...parts.slice(0, i + 1));
        if (fn(p)) {
            return p;
        }
    }
}

// -------------------------------------------------------------------------
async function node_specific() {
    const { createRequire } = await import('module');
    node_require = createRequire(import.meta.url);
    fs = await import('fs');
    path = await import('path');
    global_env.set('global', global);
    global_env.set('self', global);
    global_env.set('window', undefined);
    const moduleURL = new URL(import.meta.url);
    const __dirname = path.dirname(moduleURL.pathname);
    const __filename = path.basename(moduleURL.pathname);
    global_env.set('__dirname', __dirname);
    global_env.set('__filename', __filename);
    // ---------------------------------------------------------------------
    global_env.set('require.resolve', doc('require.resolve', function(path) {
        typecheck('require.resolve', path, 'string');
        var name = path.valueOf();
        return node_require.resolve(name);
    }, `(require.resolve path)

           Return path relative the current module.`));
    // ---------------------------------------------------------------------
    global_env.set('require', doc('require', function(module) {
        typecheck('require', module, 'string');
        module = module.valueOf();
        var root = process.cwd();
        var value;
        try {
            if (module.match(/^\s*\./)) {
                value = node_require(path.join(root, module));
            } else {
                var dir = node_module_find(root);
                if (dir) {
                    value = node_require(path.join(dir, 'node_modules', module));
                } else {
                    value = node_require(module);
                }
            }
        } catch (e) {
            value = node_require(module);
        }
        return patch_value(value, global);
    }, `(require module)

            Function to be used inside Node.js to import the module.`));
}

// -------------------------------------------------------------------------
if (is_node()) {
    node_specific();
} else if (typeof window !== 'undefined' && window === root) {
    global_env.set('window', window);
    global_env.set('global', undefined);
    global_env.set('self', window);
} else if (typeof self !== 'undefined' && typeof WorkerGlobalScope !== 'undefined') {
    global_env.set('self', self);
    global_env.set('window', undefined);
    global_env.set('global', undefined);
}

// -------------------------------------------------------------------------
// simpler way to create interpreter with interaction-environment
// -------------------------------------------------------------------------
function Interpreter(name, { stderr, stdin, stdout, ...obj } = {}) {
    if (typeof this !== 'undefined' && !(this instanceof Interpreter) ||
        typeof this === 'undefined') {
        return new Interpreter(name, { stdin, stdout, stderr, ...obj });
    }
    if (typeof name === 'undefined') {
        name = 'anonymous';
    }
    this.__env__ = user_env.inherit(name, obj);
    this.__env__.set('parent.frame', doc('parent.frame', () => {
        return this.__env__;
    }, global_env.__env__['parent.frame'].__doc__));
    const defaults_name = '**interaction-environment-defaults**';
    this.set(defaults_name, get_props(obj).concat(defaults_name));
    var inter = internal_env.inherit(`internal-${name}`);
    if (is_port(stdin)) {
        inter.set('stdin', stdin);
    }
    if (is_port(stderr)) {
        inter.set('stderr', stderr);
    }
    if (is_port(stdout)) {
        inter.set('stdout', stdout);
    }
    set_interaction_env(this.__env__, inter);
}

// -------------------------------------------------------------------------
Interpreter.prototype.exec = function(code, dynamic = false, env = null) {
    typecheck('Interpreter::exec', code, ['string', 'array'], 1);
    typecheck('Interpreter::exec', dynamic, 'boolean', 2);
    // simple solution to overwrite this variable in each interpreter
    // before evaluation of user code
    global_env.set('**interaction-environment**', this.__env__);
    if (env === null) {
        env = this.__env__;
    }
    return exec(code, env, dynamic ? env : false);
};

// -------------------------------------------------------------------------
Interpreter.prototype.get = function(value) {
    const result = this.__env__.get(value);
    if (is_function(result)) {
        return result.bind(this.__env__);
    }
    return result;
};

// -------------------------------------------------------------------------
Interpreter.prototype.set = function(name, value) {
    return this.__env__.set(name, value);
};

// -------------------------------------------------------------------------
Interpreter.prototype.constant = function(name, value) {
    return this.__env__.constant(name, value);
};

export { global_env, user_env, Interpreter };
