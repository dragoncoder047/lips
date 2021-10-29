/*
 * TODO: consider using exec in env.eval or use different maybe_async code
 */
/* global jQuery, Map, Symbol, importScripts */
"use strict";

import unfetch from 'unfetch';

import root from './root.js';
import { lips } from './lips.js';

import { Nil, nil, Pair } from './Pair.js';
import {
    read_only,
    uniterate_async,
    unbind,
    quote
} from './utils.js';
import {
    type,
    has_own_function
} from './typechecking.js';
import { symbol_to_string, LSymbol } from './LSymbol.js';
import { LNumber, LComplex, LRational, LFloat, LBigInteger } from './Numbers.js';
import { Formatter, Ahead, Pattern } from './Formatter.js';
import { Macro, Syntax } from './Macro.js';
import LString from './LString.js';
import LCharacter from './LCharacter.js';
import Values from './Values.js';
import {
    eof,
    InputPort,
    OutputPort,
    BufferedOutputPort,
    OutputStringPort,
    InputStringPort,
    InputByteVectorPort,
    OutputByteVectorPort,
    InputFilePort,
    OutputFilePort,
    InputBinaryFilePort,
    OutputBinaryFilePort
} from './Ports.js';
import {
    QuotedPromise
} from './Promises.js';

import { global_env, user_env, Interpreter } from './CoreLibrary.js';

import { tokenize, parse, Lexer, Parser, balanced, specials } from './Parser.js';

if (!root.fetch) {
    root.fetch = unfetch;
}

/* eslint-disable */
/* istanbul ignore next */
function contentLoaded(win, fn) {
    var done = false, top = true,

        doc = win.document,
        root = doc.documentElement,
        modern = doc.addEventListener,

        add = modern ? 'addEventListener' : 'attachEvent',
        rem = modern ? 'removeEventListener' : 'detachEvent',
        pre = modern ? '' : 'on',

        init = function(e) {
            if (e.type == 'readystatechange' && doc.readyState != 'complete') return;
            (e.type == 'load' ? win : doc)[rem](pre + e.type, init, false);
            if (!done && (done = true)) fn.call(win, e.type || e);
        },

        poll = function() {
            try { root.doScroll('left'); } catch(e) { setTimeout(poll, 50); return; }
            init('poll');
        };

    if (doc.readyState == 'complete') fn.call(win, 'lazy');
    else {
        if (!modern && root.doScroll) {
            try { top = !win.frameElement; } catch(e) { }
            if (top) poll();
        }
        doc[add](pre + 'DOMContentLoaded', init, false);
        doc[add](pre + 'readystatechange', init, false);
        win[add](pre + 'load', init, false);
    }
}



var repr = new Map();

// ----------------------------------------------------------------------
function user_repr(obj) {
    var constructor = obj.constructor || Object;
    var plain_object = is_plain_object(obj);
    var iterator = is_function(obj[Symbol.asyncIterator]) ||
        is_function(obj[Symbol.iterator]);
    var fn;
    if (repr.has(constructor)) {
        fn = repr.get(constructor);
    } else {
        repr.forEach(function(value, key) {
            key = unbind(key);
            // if key is Object it should only work for plain_object
            // because otherwise it will match every object
            // we don't use instanceof so it don't work for subclasses
            if (obj.constructor === key &&
                (key === Object && plain_object && !iterator || key !== Object)) {
                fn = value;
            }
        });
    }
    return fn;
}
// ----------------------------------------------------------------------
var str_mapping = new Map();
[
    [true, '#t'],
    [false, '#f'],
    [null, 'null'],
    [undefined, '#<undefined>']
].forEach(([key, value]) => {
    str_mapping.set(key, value);
});

// ----------------------------------------------------------------------
function function_to_string(fn) {
    if (is_native_function(fn)) {
        return '#<procedure(native)>';
    }
    const constructor = fn.prototype && fn.prototype.constructor;
    if (is_function(constructor) && is_lambda(constructor)) {
        if (constructor.hasOwnProperty('__name__')) {
            let name = constructor.__name__;
            if (LString.isString(name)) {
                name = name.toString();
                return `#<class:${name}>`;
            }
            return '#<class>';
        }
    }
    if (fn.hasOwnProperty('__name__')) {
        let name = fn.__name__;
        if (typeof name === 'symbol') {
            name = symbol_to_string(name);
        }
        if (typeof name === 'string') {
            return `#<procedure:${name}>`;
        }
    }
    if (has_own_function(fn, 'toString')) {
        return fn.toString();
    } else if (fn.name && !is_lambda(fn)) {
        return `#<procedure:${fn.name.trim()}>`;
    } else {
        return '#<procedure>';
    }
}
// ----------------------------------------------------------------------
// instances extracted to make cyclomatic complexity of toString smaller
const instances = new Map();
// ----------------------------------------------------------------------
[
    [Error, function(e) {
        return e.message;
    }],
    [Pair, function(pair, { quote, skip_cycles, pair_args }) {
        // make sure that repr directly after update set the cycle ref
        if (!skip_cycles) {
            pair.markCycles();
        }
        return pair.toString(quote, ...pair_args);
    }],
    [LCharacter, function(chr, { quote }) {
        if (quote) {
            return chr.toString();
        }
        return chr.valueOf();
    }],
    [LString, function(str, { quote }) {
        str = str.toString();
        if (quote) {
            return JSON.stringify(str).replace(/\\n/g, '\n');
        }
        return str;
    }],
    [RegExp, function(re) {
        return '#' + re.toString();
    }]
].forEach(([cls, fn]) => {
    instances.set(cls, fn);
});
// ----------------------------------------------------------------------
const native_types = [
    LSymbol,
    LNumber,
    Macro,
    Values,
    InputPort,
    OutputPort,
    Environment,
    QuotedPromise
];
// ----------------------------------------------------------------------
function toString(obj, quote, skip_cycles, ...pair_args) {
    if (typeof jQuery !== 'undefined' &&
        obj instanceof jQuery.fn.init) {
        return '#<jQuery(' + obj.length + ')>';
    }
    if (str_mapping.has(obj)) {
        return str_mapping.get(obj);
    }
    if (is_prototype(obj)) {
        return '#<prototype>';
    }
    if (obj) {
        var cls = obj.constructor;
        if (instances.has(cls)) {
            return instances.get(cls)(obj, { quote, skip_cycles, pair_args });
        }
    }
    // standard objects that have toString
    for (let type of native_types) {
        if (obj instanceof type) {
            return obj.toString(quote);
        }
    }
    // constants
    if ([nil, eof].includes(obj)) {
        return obj.toString();
    }
    if (is_function(obj)) {
        return function_to_string(obj);
    }
    if (obj === root) {
        return '#<js:global>';
    }
    if (obj === null) {
        return 'null';
    }
    if (typeof obj === 'object') {
        var constructor = obj.constructor;
        if (!constructor) {
            // this is case of fs.constants in Node.js that is null constructor object
            // this object can be handled like normal object that have properties
            constructor = Object;
        }
        var name;
        if (typeof constructor.__class__ === 'string') {
            name = constructor.__class__;
        } else {
            var fn = user_repr(obj);
            if (fn) {
                if (is_function(fn)) {
                    return fn(obj, quote);
                } else {
                    throw new Error('toString: Invalid repr value');
                }
            }
            name = constructor.name;
        }
        // user defined representation
        if (is_function(obj.toString) && is_lambda(obj.toString)) {
            return obj.toString().valueOf();
        }
        if (type(obj) === 'instance') {
            if (is_lambda(constructor) && constructor.__name__) {
                name = constructor.__name__.valueOf();
            } else if (!is_native_function(constructor)) {
                name = 'instance';
            }
        }
        if (is_iterator(obj, Symbol.iterator)) {
            if (name) {
                return `#<iterator(${name})>`;
            }
            return '#<iterator>';
        }
        if (is_iterator(obj, Symbol.asyncIterator)) {
            if (name) {
                return `#<asyncIterator(${name})>`;
            }
            return '#<asyncIterator>';
        }
        if (name !== '') {
            return '#<' + name + '>';
        }
        return '#<Object>';
    }
    if (typeof obj !== 'string') {
        return obj.toString();
    }
    return obj;
}

// ----------------------------------------------------------------------
// :: Function utilities
// ----------------------------------------------------------------------


// -------------------------------------------------------------------------
// Lips Exception used in error function
// -------------------------------------------------------------------------
function LipsError(message, args) {
    this.name = 'LipsError';
    this.message = message;
    this.args = args;
    this.stack = (new Error()).stack;
}
LipsError.prototype = new Error();
LipsError.prototype.constructor = LipsError;

// -------------------------------------------------------------------------
function fworker(fn) {
    // ref: https://stackoverflow.com/a/10372280/387194
    var str = '(' + fn.toString() + ')()';
    var URL = window.URL || window.webkitURL;
    var blob;
    try {
        blob = new Blob([str], { type: 'application/javascript' });
    } catch (e) { // Backwards-compatibility
        const BlobBuilder = window.BlobBuilder ||
              window.WebKitBlobBuilder ||
              window.MozBlobBuilder;
        blob = new BlobBuilder();
        blob.append(str);
        blob = blob.getBlob();
    }
    return new root.Worker(URL.createObjectURL(blob));
}
// -------------------------------------------------------------------------
function is_dev() {
    return lips.version.match(/^(\{\{VER\}\}|DEV)$/);
}
// -------------------------------------------------------------------------
function bootstrap(url = '') {
    const std = 'dist/std.xcb';
    if (url === '') {
        if (is_dev()) {
            url = `https://cdn.jsdelivr.net/gh/jcubic/lips@devel/${std}`;
        } else {
            url = `https://cdn.jsdelivr.net/npm/@jcubic/lips@${lips.version}/${std}`;
        }
    }
    var load = global_env.get('load');
    return load.call(user_env, url, global_env);
}
// -------------------------------------------------------------------------
function Worker(url) {
    this.url = url;
    const worker = this.worker = fworker(function() {
        var interpreter;
        var init;
        // string, numbers, booleans
        self.addEventListener('message', function(response) {
            var data = response.data;
            var id = data.id;
            if (data.type !== 'RPC' || id === null) {
                return;
            }
            function send_result(result) {
                self.postMessage({ id: id, type: 'RPC', result: result });
            }
            function send_error(message) {
                self.postMessage({ id: id, type: 'RPC', error: message });
            }
            if (data.method === 'eval') {
                if (!init) {
                    send_error('Worker RPC: LIPS not initilized, call init first');
                    return;
                }
                init.then(function() {
                    // we can use ES6 inside function that's converted to blob
                    var code = data.params[0];
                    var dynamic = data.params[1];
                    interpreter.exec(code, dynamic).then(function(result) {
                        result = result.map(function(value) {
                            return value && value.valueOf();
                        });
                        send_result(result);
                    }).catch(error => {
                        send_error(error);
                    });
                });
            } else if (data.method === 'init') {
                var url = data.params[0];
                if (typeof url !== 'string') {
                    send_error('Worker RPC: url is not a string');
                } else {
                    importScripts(`${url}/dist/lips.min.js`);
                    interpreter = new lips.Interpreter('worker');
                    init = bootstrap(url);
                    init.then(() => {
                        send_result(true);
                    });
                }
            }
        });
    });
    this.rpc = (function() {
        var id = 0;
        return function rpc(method, params) {
            var _id = ++id;
            return new Promise(function(resolve, reject) {
                worker.addEventListener('message', function handler(response) {
                    var data = response.data;
                    if (data && data.type === 'RPC' && data.id === _id) {
                        if (data.error) {
                            reject(data.error);
                        } else {
                            resolve(data.result);
                        }
                        worker.removeEventListener('message', handler);
                    }
                });
                worker.postMessage({
                    type: 'RPC',
                    method: method,
                    id: _id,
                    params: params
                });
            });
        };
    })();
    this.rpc('init', [url]).catch((error) => {
        console.error(error);
    });
    this.exec = function(code, dynamic = false) {
        return this.rpc('eval', [code, dynamic]);
    };
}


// -------------------------------------------------------------------------
function execError(e) {
    console.error(e.message || e);
    if (e.code) {
        console.error(e.code.map((line, i) => `[${i + 1}]: ${line}`));
    }
}

// -------------------------------------------------------------------------
function init() {
    var lips_mimes = ['text/x-lips', 'text/x-scheme'];
    var bootstraped;
    function load(script) {
        return new Promise(function(resolve) {
            var src = script.getAttribute('src');
            if (src) {
                return fetch(src).then(res => res.text())
                    .then(exec).then(resolve).catch((e) => {
                        execError(e);
                        resolve();
                    });
            } else {
                return exec(script.innerHTML).then(resolve).catch((e) => {
                    execError(e);
                    resolve();
                });
            }
        });
    }

    function loop() {
        return new Promise(function(resolve) {
            var scripts = Array.from(document.querySelectorAll('script'));
            return (function loop() {
                var script = scripts.shift();
                if (!script) {
                    resolve();
                } else {
                    var type = script.getAttribute('type');
                    if (lips_mimes.includes(type)) {
                        var bootstrap_attr = script.getAttribute('bootstrap');
                        if (!bootstraped && typeof bootstrap_attr === 'string') {
                            bootstrap(bootstrap_attr).then(function() {
                                return load(script, function(e) {
                                    console.error(e);
                                });
                            }).then(loop);
                        } else {
                            load(script, function(e) {
                                console.error(e);
                            }).then(loop);
                        }
                    } else if (type && type.match(/lips|lisp/)) {
                        console.warn('Expecting ' + lips_mimes.join(' or ') +
                                     ' found ' + type);
                    }
                    return loop();
                }
            })();
        });
    }
    if (!window.document) {
        return Promise.resolve();
    } else if (currentScript) {
        var script = currentScript;
        var bootstrap_attr = script.getAttribute('bootstrap');
        if (typeof bootstrap_attr === 'string') {
            return bootstrap(bootstrap_attr).then(function() {
                bootstraped = true;
                return loop();
            });
        }
    }
    return loop();
}
// this can't be in init function, because it need to be in script context
const currentScript = typeof window !== 'undefined' &&
      window.document && document.currentScript;
// -------------------------------------------------------------------------
if (typeof window !== 'undefined') {
    contentLoaded(window, init);
}
// -------------------------------------------------------------------------
var banner = (function() {
    // Rollup tree-shaking is removing the variable if it's normal string because
    // obviously '{{DATE}}' == '{{' + 'DATE}}'; can be removed
    // but disablig Tree-shaking is adding lot of not used code so we use this
    // hack instead
    var date = LString('{{DATE}}').valueOf();
    var _date = date === '{{' + 'DATE}}' ? new Date() : new Date(date);
    var _format = x => x.toString().padStart(2, '0');
    var _year = _date.getFullYear();
    var _build = [
        _year,
        _format(_date.getMonth() + 1),
        _format(_date.getDate())
    ].join('-');
    var banner = `
  __ __                          __
 / / \\ \\       _    _  ___  ___  \\ \\
| |   \\ \\     | |  | || . \\/ __>  | |
| |    > \\    | |_ | ||  _/\\__ \\  | |
| |   / ^ \\   |___||_||_|  <___/  | |
 \\_\\ /_/ \\_\\                     /_/

LIPS Interpreter {{VER}} (${_build}) <https://lips.js.org>
Copyright (c) 2018-${_year} Jakub T. Jankiewicz

Type (env) to see environment with functions macros and variables. You can also
use (help name) to display help for specic function or macro, (apropos name)
to display list of matched names in environment and (dir object) to list
properties of an object.
`.replace(/^.*\n/, '');
    return banner;
})();
// -------------------------------------------------------------------------
// to be used with string function when code is minified
// -------------------------------------------------------------------------
read_only(Ahead, '__class__', 'ahead');
read_only(Pair, '__class__', 'pair');
read_only(Nil, '__class__', 'nil');
read_only(Pattern, '__class__', 'pattern');
read_only(Formatter, '__class__', 'formatter');
read_only(Macro, '__class__', 'macro');
read_only(Syntax, '__class__', 'syntax');
read_only(Environment, '__class__', 'environment');
read_only(InputPort, '__class__', 'input-port');
read_only(OutputPort, '__class__', 'output-port');
read_only(BufferedOutputPort, '__class__', 'output-port');
read_only(OutputStringPort, '__class__', 'output-string-port');
read_only(InputStringPort, '__class__', 'input-string-port');
read_only(InputFilePort, '__class__', 'input-file-port');
read_only(OutputFilePort, '__class__', 'output-file-port');
read_only(LipsError, '__class__', 'lips-error');
[LNumber, LComplex, LRational, LFloat, LBigInteger].forEach(cls => {
    read_only(cls, '__class__', 'number');
});
read_only(LCharacter, '__class__', 'character');
read_only(LSymbol, '__class__', 'symbol');
read_only(LString, '__class__', 'string');
read_only(QuotedPromise, '__class__', 'promise');
// -------------------------------------------------------------------------
Object.assign(lips, {
    version: '{{VER}}',
    banner,
    date: '{{DATE}}',
    exec,
    // unwrap async generator into Promise<Array>
    parse: compose(uniterate_async, parse),
    tokenize,
    evaluate,
    compile,

    serialize,
    unserialize,

    serialize_bin,
    unserialize_bin,

    bootstrap,

    Environment,
    env: user_env,

    Worker,

    Interpreter,
    balanced_parenthesis: balanced,
    balancedParenthesis: balanced,
    balanced,

    Macro,
    Syntax,
    Pair,
    Values,
    QuotedPromise,
    Error: LipsError,

    quote,

    InputPort,
    OutputPort,
    BufferedOutputPort,
    InputFilePort,
    OutputFilePort,
    InputStringPort,
    OutputStringPort,
    InputByteVectorPort,
    OutputByteVectorPort,
    InputBinaryFilePort,
    OutputBinaryFilePort,

    Formatter,
    Parser,
    Lexer,
    specials,
    repr,
    nil,
    eof,

    LSymbol,
    LNumber,
    LFloat,
    LComplex,
    LRational,
    LBigInteger,
    LCharacter,
    LString,
    rationalize
});

// so it work when used with webpack where it will be not global
export default lips;

global_env.set('lips', lips);
