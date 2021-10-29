/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol, Map */
import { is_plain_object, is_native, __data__ } from './typechecking.js';
import { trampoline, Thunk } from './trampoline.js';
import { LSymbol } from './LSymbol.js';
import { LNumber } from './Numbers.js';
import LString from './LString.js';

const __cycles__ = Symbol.for('__cycles__');
const __ref__ = Symbol.for('__ref__');

// -----------------------------------------------------------------------------
// :: Nil class with only once instance
// -----------------------------------------------------------------------------
class Nil {
    toString() {
        return '()';
    }
    valueOf() {
        return undefined;
    }
    serialize() {
        return 0;
    }
    to_object() {
        return {};
    }
    append(x) {
        return new Pair(x, nil);
    }
    to_array() {
        return [];
    }
}

// -----------------------------------------------------------------------------
const nil = new Nil();

// -----------------------------------------------------------------------------
// :: Pair constructor
// -----------------------------------------------------------------------------
function Pair(car, cdr) {
    if (typeof this !== 'undefined' && this.constructor !== Pair ||
        typeof this === 'undefined') {
        return new Pair(car, cdr);
    }
    this.car = car;
    this.cdr = cdr;
}

// -----------------------------------------------------------------------------
Pair.prototype.flatten = function() {
    return Pair.fromArray(flatten(this.to_array()));
};

// -----------------------------------------------------------------------------
Pair.prototype.length = function() {
    var len = 0;
    var node = this;
    while (true) {
        if (!node || node === nil || !(node instanceof Pair) ||
            node.haveCycles('cdr')) {
            break;
        }
        len++;
        node = node.cdr;
    }
    return len;
};

// -----------------------------------------------------------------------------
Pair.match = function(obj, item) {
    if (obj instanceof LSymbol) {
        return LSymbol.is(obj, item);
    } else if (obj instanceof Pair) {
        return Pair.match(obj.car, item) || Pair.match(obj.cdr, item);
    } else if (Array.isArray(obj)) {
        return obj.some(x => {
            return Pair.match(x, item);
        });
    } else if (is_plain_object(obj)) {
        return Object.values(obj).some(x => {
            return Pair.match(x, item);
        });
    }
    return false;
};

// -----------------------------------------------------------------------------
Pair.prototype.find = function(item) {
    return Pair.match(this, item);
};

// -----------------------------------------------------------------------------
Pair.prototype.clone = function(deep = true) {
    var visited = new Map();
    function clone(node) {
        if (node instanceof Pair) {
            if (visited.has(node)) {
                return visited.get(node);
            }
            var pair = new Pair();
            visited.set(node, pair);
            if (deep) {
                pair.car = clone(node.car);
            } else {
                pair.car = node.car;
            }
            pair.cdr = clone(node.cdr);
            pair[__cycles__] = node[__cycles__];
            return pair;
        }
        return node;
    }
    return clone(this);
};

// -----------------------------------------------------------------------------
Pair.prototype.last_pair = function() {
    let node = this;
    while (true) {
        if (node.cdr === nil) {
            return node;
        }
        node = node.cdr;
    }
};

// -----------------------------------------------------------------------------
Pair.prototype.to_array = function(deep = true) {
    var result = [];
    if (this.car instanceof Pair) {
        if (deep) {
            result.push(this.car.to_array());
        } else {
            result.push(this.car);
        }
    } else {
        result.push(this.car.valueOf());
    }
    if (this.cdr instanceof Pair) {
        result = result.concat(this.cdr.to_array());
    }
    return result;
};

// -----------------------------------------------------------------------------
Pair.fromArray = function(array, deep = true, quote = false) {
    if (array instanceof Pair || quote && array instanceof Array && array[__data__]) {
        return array;
    }
    if (deep === false) {
        var list = nil;
        for (let i = array.length; i--;) {
            list = new Pair(array[i], list);
        }
        return list;
    }
    if (array.length && !(array instanceof Array)) {
        array = [...array];
    }
    var result = nil;
    var i = array.length;
    while (i--) {
        let car = array[i];
        if (car instanceof Array) {
            car = Pair.fromArray(car, deep, quote);
        } else if (typeof car === 'string') {
            car = LString(car);
        } else if (typeof car === 'number' && !Number.isNaN(car)) {
            car = LNumber(car);
        }
        result = new Pair(car, result);
    }
    return result;
};

// -----------------------------------------------------------------------------
// by default to_object was created to create JavaScript objects,
// so it use valueOf to get native values
// literal parameter was a hack to allow create LComplex from LIPS code
// -----------------------------------------------------------------------------
Pair.prototype.to_object = function(literal = false) {
    var node = this;
    var result = {};
    while (true) {
        if (node instanceof Pair && node.car instanceof Pair) {
            var pair = node.car;
            var name = pair.car;
            if (name instanceof LSymbol) {
                name = name.__name__;
            }
            if (name instanceof LString) {
                name = name.valueOf();
            }
            var cdr = pair.cdr;
            if (cdr instanceof Pair) {
                cdr = cdr.to_object(literal);
            }
            if (is_native(cdr)) {
                if (!literal) {
                    cdr = cdr.valueOf();
                }
            }
            result[name] = cdr;
            node = node.cdr;
        } else {
            break;
        }
    }
    return result;
};

// -----------------------------------------------------------------------------
Pair.fromPairs = function(array) {
    return array.reduce((list, pair) => {
        return new Pair(
            new Pair(
                new LSymbol(pair[0]),
                pair[1]
            ),
            list
        );
    }, nil);
};

// -----------------------------------------------------------------------------
Pair.fromObject = function(obj) {
    var array = Object.keys(obj).map((key) => [key, obj[key]]);
    return Pair.fromPairs(array);
};

// -----------------------------------------------------------------------------
Pair.prototype.reduce = function(fn) {
    var node = this;
    var result = nil;
    while (true) {
        if (node !== nil) {
            result = fn(result, node.car);
            node = node.cdr;
        } else {
            break;
        }
    }
    return result;
};

// -----------------------------------------------------------------------------
Pair.prototype.reverse = function() {
    if (this.haveCycles()) {
        throw new Error("You can't reverse list that have cycles");
    }
    var node = this;
    var prev = nil;
    while (node !== nil) {
        var next = node.cdr;
        node.cdr = prev;
        prev = node;
        node = next;
    }
    return prev;
};

// -----------------------------------------------------------------------------
Pair.prototype.transform = function(fn) {
    var visited = [];
    function recur(pair) {
        if (pair instanceof Pair) {
            if (pair.replace) {
                delete pair.replace;
                return pair;
            }
            var car = fn(pair.car);
            if (car instanceof Pair) {
                car = recur(car);
                visited.push(car);
            }
            var cdr = fn(pair.cdr);
            if (cdr instanceof Pair) {
                cdr = recur(cdr);
                visited.push(cdr);
            }
            return new Pair(car, cdr);
        }
        return pair;
    }
    return recur(this);
};

// -----------------------------------------------------------------------------
Pair.prototype.map = function(fn) {
    if (typeof this.car !== 'undefined') {
        return new Pair(fn(this.car), this.cdr === nil ? nil : this.cdr.map(fn));
    } else {
        return nil;
    }
};
// -----------------------------------------------------------------------------
Pair.prototype.markCycles = function() {
    markCycles(this);
    return this;
};

// -----------------------------------------------------------------------------
Pair.prototype.haveCycles = function(name = null) {
    if (!name) {
        return this.haveCycles('car') || this.haveCycles('cdr');
    }
    return !!(this[__cycles__] && this[__cycles__][name]);
};

// -----------------------------------------------------------------------------
function markCycles(pair) {
    var seen_pairs = [];
    var cycles = [];
    var refs = [];
    function visit(pair) {
        if (!seen_pairs.includes(pair)) {
            seen_pairs.push(pair);
        }
    }
    function set(node, type, child, parents) {
        if (child instanceof Pair) {
            if (parents.includes(child)) {
                if (!refs.includes(child)) {
                    refs.push(child);
                }
                if (!node[__cycles__]) {
                    node[__cycles__] = {};
                }
                node[__cycles__][type] = child;
                if (!cycles.includes(node)) {
                    cycles.push(node);
                }
                return true;
            }
        }
    }
    const detect = trampoline(function detect_thunk(pair, parents) {
        if (pair instanceof Pair) {
            delete pair.ref;
            delete pair[__cycles__];
            visit(pair);
            parents.push(pair);
            var car = set(pair, 'car', pair.car, parents);
            var cdr = set(pair, 'cdr', pair.cdr, parents);
            if (!car) {
                detect(pair.car, parents.slice());
            }
            if (!cdr) {
                return new Thunk(() => {
                    return detect_thunk(pair.cdr, parents.slice());
                });
            }
        }
    });
    function mark_node(node, type) {
        if (node[__cycles__][type] instanceof Pair) {
            const count = ref_nodes.indexOf(node[__cycles__][type]);
            node[__cycles__][type] = `#${count}#`;
        }
    }
    detect(pair, []);
    var ref_nodes = seen_pairs.filter(node => refs.includes(node));
    ref_nodes.forEach((node, i) => {
        node[__ref__] = `#${i}=`;
    });
    cycles.forEach(node => {
        mark_node(node, 'car');
        mark_node(node, 'cdr');
    });
}

// -----------------------------------------------------------------------------
// trampoline based recursive pair to string that don't overflow the stack
// -----------------------------------------------------------------------------
/* eslint-disable no-unused-vars */
/* istanbul ignore next */
const pair_to_string = (function() {
    const prefix = (pair, nested) => {
        var result = [];
        if (pair[__ref__]) {
            result.push(pair[__ref__] + '(');
        } else if (!nested) {
            result.push('(');
        }
        return result;
    };
    const postfix = (pair, nested) => {
        if (!nested || pair[__ref__]) {
            return [')'];
        }
        return [];
    };
    return trampoline(function pairToString(pair, quote, extra = {}) {
        const {
            nested = false,
            result = [],
            cont = () => {
                result.push(...postfix(pair, nested));
            }
        } = extra;
        result.push(...prefix(pair, nested));
        let car;
        if (pair[__cycles__] && pair[__cycles__].car) {
            car = pair[__cycles__].car;
        } else {
            car = toString(pair.car, quote, true, { result, cont });
        }
        if (car !== undefined) {
            result.push(car);
        }
        return new Thunk(() => {
            if (pair.cdr instanceof Pair) {
                if (pair[__cycles__] && pair[__cycles__].cdr) {
                    result.push(' . ');
                    result.push(pair[__cycles__].cdr);
                } else {
                    if (pair.cdr[__ref__]) {
                        result.push(' . ');
                    } else {
                        result.push(' ');
                    }
                    return pairToString(pair.cdr, quote, {
                        nested: true,
                        result,
                        cont
                    });
                }
            } else if (pair.cdr !== nil) {
                result.push(' . ');
                result.push(toString(pair.cdr, quote));
            }
        }, cont);
    });
})();

// -----------------------------------------------------------------------------
Pair.prototype.toString = function(quote, { nested = false } = {}) {
    var arr = [];
    if (this[__ref__]) {
        arr.push(this[__ref__] + '(');
    } else if (!nested) {
        arr.push('(');
    }
    var value;
    if (this[__cycles__] && this[__cycles__].car) {
        value = this[__cycles__].car;
    } else {
        value = toString(this.car, quote, true);
    }
    if (value !== undefined) {
        arr.push(value);
    }
    if (this.cdr instanceof Pair) {
        if (this[__cycles__] && this[__cycles__].cdr) {
            arr.push(' . ');
            arr.push(this[__cycles__].cdr);
        } else {
            if (this.cdr[__ref__]) {
                arr.push(' . ');
            } else {
                arr.push(' ');
            }
            const cdr = this.cdr.toString(quote, { nested: true });
            arr.push(cdr);
        }
    } else if (this.cdr !== nil) {
        arr = arr.concat([' . ', toString(this.cdr, quote, true)]);
    }
    if (!nested || this[__ref__]) {
        arr.push(')');
    }
    return arr.join('');
};

// -----------------------------------------------------------------------------
Pair.prototype.set = function(prop, value) {
    this[prop] = value;
    if (value instanceof Pair) {
        this.markCycles();
    }
};

// -----------------------------------------------------------------------------
Pair.prototype.append = function(arg) {
    if (arg instanceof Array) {
        return this.append(Pair.fromArray(arg));
    }
    var p = this;
    if (p.car === undefined) {
        if (arg instanceof Pair) {
            this.car = arg.car;
            this.cdr = arg.cdr;
        } else {
            this.car = arg;
        }
    } else if (arg !== nil) {
        while (true) {
            if (p instanceof Pair && p.cdr !== nil) {
                p = p.cdr;
            } else {
                break;
            }
        }
        p.cdr = arg;
    }
    return this;
};

// -----------------------------------------------------------------------------
Pair.prototype.serialize = function() {
    return [
        this.car,
        this.cdr
    ];
};

// -----------------------------------------------------------------------------
// :: List iterator (for do-iterator macro)
// -----------------------------------------------------------------------------
Pair.prototype[Symbol.iterator] = function() {
    var node = this;
    return {
        next: function() {
            var cur = node;
            node = cur.cdr;
            if (cur === nil) {
                return { value: undefined, done: true };
            } else {
                return { value: cur.car, done: false };
            }
        }
    };
};

// -----------------------------------------------------------------------------
// :: flatten nested arrays
// :: ref: https://stackoverflow.com/a/27282907/387194
// -----------------------------------------------------------------------------
function flatten(array, mutable) {
    var toString = Object.prototype.toString;
    var arrayTypeStr = '[object Array]';

    var result = [];
    var nodes = (mutable && array) || array.slice();
    var node;

    if (!array.length) {
        return result;
    }

    node = nodes.pop();

    do {
        if (toString.call(node) === arrayTypeStr) {
            nodes.push.apply(nodes, node);
        } else {
            result.push(node);
        }
    } while (nodes.length && (node = nodes.pop()) !== undefined);

    result.reverse(); // we reverse result to restore the original order
    return result;
}

export { nil, Nil, Pair, markCycles };
