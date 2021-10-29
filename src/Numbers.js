/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global BigInt */
import root from './root.js';
import LString from './LString.js';
import { type } from './typechecking.js';

const BN = root.BN;

// -----------------------------------------------------------------------------
var pow = function(a, b) {
    var e = typeof a === 'bigint' ? BigInt(1) : 1;
    return new Array(Number(b)).fill(0).reduce(x => x * a, e);
};
// -----------------------------------------------------------------------------
// use native exponential operator if possible (it's way faster)
// -----------------------------------------------------------------------------
var exp_op = new Function('a,b', 'return a ** b');
try {
    if (exp_op(2, 2) === 4) {
        pow = exp_op;
    }
} catch (e) {
    // ignore
}

// -----------------------------------------------------------------------------
// :: Number wrapper that handle BigNumbers
// -----------------------------------------------------------------------------
function LNumber(n, force = false) {
    if (n instanceof LNumber) {
        return n;
    }
    if (typeof this !== 'undefined' && !(this instanceof LNumber) ||
        typeof this === 'undefined') {
        return new LNumber(n, force);
    }
    if (typeof n === 'undefined') {
        throw new Error('Invalid LNumber constructor call');
    }
    var _type = LNumber.getType(n);
    if (LNumber.types[_type]) {
        return LNumber.types[_type](n, force);
    }
    var parsable = n instanceof Array && LString.isString(n[0]) &&
        LNumber.isNumber(n[1]);
    if (n instanceof LNumber) {
        return LNumber(n.value);
    }
    if (!LNumber.isNumber(n) && !parsable) {
        throw new Error(`You can't create LNumber from ${type(n)}`);
    }
    // prevent infite loop https://github.com/indutny/bn.js/issues/186
    if (n === null) {
        n = 0;
    }
    var value;
    if (parsable) {
        var [str, radix] = n;
        if (str instanceof LString) {
            str = str.valueOf();
        }
        if (radix instanceof LNumber) {
            radix = radix.valueOf();
        }
        var sign = str.match(/^([+-])/);
        var minus = false;
        if (sign) {
            str = str.replace(/^[+-]/, '');
            if (sign[1] === '-') {
                minus = true;
            }
        }
    }
    if (Number.isNaN(n)) {
        return LFloat(n);
    } else if (typeof BigInt !== 'undefined') {
        if (typeof n !== 'bigint') {
            if (parsable) {
                let prefix;
                // default number base (radix) supported by BigInt constructor
                switch (radix) {
                    case 8:
                        prefix = '0o';
                        break;
                    case 16:
                        prefix = '0x';
                        break;
                    case 2:
                        prefix = '0b';
                        break;
                    case 10:
                        prefix = '';
                        break;
                }
                if (typeof prefix === 'undefined') {
                    // non standard radix we convert by hand
                    var n_radix = BigInt(radix);
                    value = [...str].map((x, i) => {
                        return BigInt(parseInt(x, radix)) * pow(n_radix, BigInt(i));
                    }).reduce((a, b) => a + b);
                } else {
                    value = BigInt(prefix + str);
                }
            } else {
                value = BigInt(n);
            }
            if (minus) {
                value *= BigInt(-1);
            }
        } else {
            value = n;
        }
        return LBigInteger(value, true);
    } else if (typeof BN !== 'undefined' && !(n instanceof BN)) {
        if (n instanceof Array) {
            return LBigInteger(new BN(...n));
        }
        return LBigInteger(new BN(n));
    } else if (parsable) {
        this.constant(parseInt(str, radix), 'integer');
    } else {
        this.constant(n, 'integer');
    }
}
// -----------------------------------------------------------------------------
LNumber.prototype.constant = function(value, type) {
    Object.defineProperty(this, '__value__', {
        value,
        enumerable: true
    });
    Object.defineProperty(this, '__type__', {
        value: type,
        enumerable: true
    });
};
// -----------------------------------------------------------------------------
LNumber.types = {
    float: function(n, force = false) {
        return new LFloat(n, force);
    },
    complex: function(n, force = false) {
        if (!LNumber.isComplex(n)) {
            n = { im: 0, re: n };
        }
        return new LComplex(n, force);
    },
    rational: function(n, force = false) {
        if (!LNumber.isRational(n)) {
            n = { num: n, denom: 1 };
        }
        return new LRational(n, force);
    }
};
// -----------------------------------------------------------------------------
LNumber.prototype.serialize = function() {
    return this.__value__;
};
// -----------------------------------------------------------------------------
LNumber.prototype.isNaN = function() {
    return Number.isNaN(this.__value__);
};
// -----------------------------------------------------------------------------
LNumber.prototype.gcd = function(b) {
    // ref: https://rosettacode.org/wiki/Greatest_common_divisor#JavaScript
    var a = this.abs();
    b = b.abs();
    if (b.cmp(a) === 1) {
        var temp = a;
        a = b;
        b = temp;
    }
    while (true) {
        a = a.rem(b);
        if (a.cmp(0) === 0) {
            return b;
        }
        b = b.rem(a);
        if (b.cmp(0) === 0) {
            return a;
        }
    }
};
// -----------------------------------------------------------------------------
LNumber.isFloat = function isFloat(n) {
    return n instanceof LFloat || (Number(n) === n && n % 1 !== 0);
};
// -----------------------------------------------------------------------------
LNumber.isNumber = function(n) {
    return n instanceof LNumber ||
        (LNumber.isNative(n) || LNumber.isBN(n));
};
// -----------------------------------------------------------------------------
LNumber.isComplex = function(n) {
    if (!n) {
        return false;
    }
    var ret = n instanceof LComplex ||
        ((LNumber.isNumber(n.im) || Number.isNaN(n.im)) &&
         (LNumber.isNumber(n.re) || Number.isNaN(n.re)));
    return ret;
};
// -----------------------------------------------------------------------------
LNumber.isRational = function(n) {
    if (!n) {
        return false;
    }
    return n instanceof LRational ||
        (LNumber.isNumber(n.num) && LNumber.isNumber(n.denom));
};
// -----------------------------------------------------------------------------
LNumber.isInteger = function(n) {
    if (!(LNumber.isNative(n) || n instanceof LNumber)) {
        return false;
    }
    if (LNumber.isFloat(n)) {
        return false;
    }
    if (LNumber.isRational(n)) {
        return false;
    }
    if (LNumber.isComplex(n)) {
        return false;
    }
    return true;
};
// -----------------------------------------------------------------------------
LNumber.isNative = function(n) {
    return typeof n === 'bigint' || typeof n === 'number';
};
// -----------------------------------------------------------------------------
LNumber.isBigInteger = function(n) {
    return n instanceof LBigInteger || typeof n === 'bigint' ||
        LNumber.isBN(n);
};
// -----------------------------------------------------------------------------
LNumber.isBN = function(n) {
    return typeof BN !== 'undefined' && n instanceof BN;
};
// -----------------------------------------------------------------------------
LNumber.getArgsType = function(a, b) {
    if (a instanceof LFloat || b instanceof LFloat) {
        return LFloat;
    }
    if (a instanceof LBigInteger || b instanceof LBigInteger) {
        return LBigInteger;
    }
    return LNumber;
};
// -----------------------------------------------------------------------------
LNumber.prototype.toString = function(radix) {
    if (Number.isNaN(this.__value__)) {
        return '+nan.0';
    }
    if (radix > 2 && radix < 36) {
        return this.__value__.toString(radix);
    }
    return this.__value__.toString();
};
// -----------------------------------------------------------------------------
LNumber.prototype.asType = function(n) {
    var _type = LNumber.getType(this);
    return LNumber.types[_type] ? LNumber.types[_type](n) : LNumber(n);
};
// -----------------------------------------------------------------------------
LNumber.prototype.isBigNumber = function() {
    return typeof this.__value__ === 'bigint' ||
        typeof BN !== 'undefined' && !(this.value instanceof BN);
};
// -----------------------------------------------------------------------------
['floor', 'ceil', 'round'].forEach(fn => {
    LNumber.prototype[fn] = function() {
        if (this.float || LNumber.isFloat(this.__value__)) {
            return LNumber(Math[fn](this.__value__));
        } else {
            return LNumber(Math[fn](this.valueOf()));
        }
    };
});
// -----------------------------------------------------------------------------
LNumber.prototype.valueOf = function() {
    if (LNumber.isNative(this.__value__)) {
        return Number(this.__value__);
    } else if (LNumber.isBN(this.__value__)) {
        return this.__value__.toNumber();
    }
};

// -----------------------------------------------------------------------------
LNumber.prototype.pow = function(n) {
    var value;
    if (LNumber.isBN(this.__value__)) {
        value = this.__value__.pow(n.__value__);
    } else {
        value = pow(this.__value__, n.__value__);
    }
    return LNumber(value);
};
// -----------------------------------------------------------------------------
LNumber.prototype.abs = function() {
    var value = this.__value__;
    if (LNumber.isNative(this.__value__)) {
        if (value < 0) {
            value = -value;
        }
    } else if (LNumber.isBN(value)) {
        value.iabs();
    }
    return new LNumber(value);
};
// -----------------------------------------------------------------------------
LNumber.prototype.isOdd = function() {
    if (LNumber.isNative(this.__value__)) {
        if (this.isBigNumber()) {
            return this.__value__ % BigInt(2) === BigInt(1);
        }
        return this.__value__ % 2 === 1;
    } else if (LNumber.isBN(this.__value__)) {
        return this.__value__.isOdd();
    }
};
// -----------------------------------------------------------------------------
LNumber.prototype.isEven = function() {
    return !this.isOdd();
};
// -----------------------------------------------------------------------------
LNumber.prototype.cmp = function(n) {
    const [a, b] = this.coerce(n);
    function cmp(a, b) {
        if (a.__value__ < b.__value__) {
            return -1;
        } else if (a.__value__ === b.__value__) {
            return 0;
        } else {
            return 1;
        }
    }
    if (a.__type__ === 'bigint') {
        if (LNumber.isNative(a.__value__)) {
            return cmp(a, b);
        } else if (LNumber.isBN(a.__value__)) {
            return this.__value__.cmp(b.__value__);
        }
    } else if (a instanceof LFloat) {
        return cmp(a, b);
    }
};

// -----------------------------------------------------------------------------
LNumber.prototype.isFloat = function() {
    return !!(LNumber.isFloat(this.__value__) || this.float);
};

// -----------------------------------------------------------------------------
LNumber.prototype.coerce = function(n) {
    if (!(typeof n === 'number' || n instanceof LNumber)) {
        throw new Error(`LNumber: you can't coerce ${type(n)}`);
    }
    if (typeof n === 'number') {
        n = LNumber(n);
    }
    return LNumber.coerce(this, n);
};

// -----------------------------------------------------------------------------
LNumber.coerce = function(a, b) {
    const a_type = LNumber.getType(a);
    const b_type = LNumber.getType(b);
    if (!matrix[a_type]) {
        throw new Error(`LNumber::coerce unknown lhs type ${a_type}`);
    } else if (!matrix[a_type][b_type]) {
        throw new Error(`LNumber::coerce unknown rhs type ${b_type}`);
    }
    var tmp = matrix[a_type][b_type](a, b);
    return tmp.map(n => LNumber(n, true));
};

// -----------------------------------------------------------------------------
LNumber.getType = function(n) {
    if (n instanceof LNumber) {
        return n.__type__;
    }
    if (LNumber.isFloat(n)) {
        return 'float';
    }
    if (LNumber.isComplex(n)) {
        return 'complex';
    }
    if (LNumber.isRational(n)) {
        return 'rational';
    }
    if (typeof n === 'number') {
        return 'integer';
    }
    if ((typeof BigInt !== 'undefined' && typeof n !== 'bigint') ||
        (typeof BN !== 'undefined' && !(n instanceof BN))) {
        return 'bigint';
    }
};


// -----------------------------------------------------------------------------
var mapping = {
    'add': '+',
    'sub': '-',
    'mul': '*',
    'div': '/',
    'rem': '%',
    'or': '|',
    'and': '&',
    'neg': '~',
    'shl': '>>',
    'shr': '<<'
};
var rev_mapping = {};
Object.keys(mapping).forEach((key) => {
    rev_mapping[mapping[key]] = key;
    LNumber.prototype[key] = function(n) {
        return this.op(mapping[key], n);
    };
});
// -----------------------------------------------------------------------------
LNumber._ops = {
    '*': function(a, b) {
        return a * b;
    },
    '+': function(a, b) {
        return a + b;
    },
    '-': function(a, b) {
        if (typeof b === 'undefined') {
            return -a;
        }
        return a - b;
    },
    '/': function(a, b) {
        return a / b;
    },
    '%': function(a, b) {
        return a % b;
    },
    '|': function(a, b) {
        return a | b;
    },
    '&': function(a, b) {
        return a & b;
    },
    '~': function(a) {
        return ~a;
    },
    '>>': function(a, b) {
        return a >> b;
    },
    '<<': function(a, b) {
        return a << b;
    }
};
// -----------------------------------------------------------------------------
LNumber.prototype.op = function(op, n) {
    if (typeof n === 'undefined') {
        return LNumber(LNumber._ops[op](this.valueOf()));
    }
    if (typeof n === 'number') {
        n = LNumber(n);
    }
    if (Number.isNaN(this.__value__) && !LNumber.isComplex(n) ||
        !LNumber.isComplex(this) && Number.isNaN(n.__value__)) {
        return LNumber(NaN);
    }
    const [a, b] = this.coerce(n);
    if (a._op) {
        return a._op(op, b);
    }
    return LNumber(LNumber._ops[op](a, b));
};
// -----------------------------------------------------------------------------
LNumber.prototype.sqrt = function() {
    var value = this.valueOf();
    if (this.cmp(0) < 0) {
        var im = Math.sqrt(-value);
        return LComplex({ re: 0, im });
    }
    return LNumber(Math.sqrt(value));
};
// -----------------------------------------------------------------------------
// :: COMPLEX TYPE
// -----------------------------------------------------------------------------
function LComplex(n, force = false) {
    if (typeof this !== 'undefined' && !(this instanceof LComplex) ||
        typeof this === 'undefined') {
        return new LComplex(n, force);
    }
    if (n instanceof LComplex) {
        return LComplex({ im: n.__im__, re: n.__re__ });
    }
    if (LNumber.isNumber(n) && force) {
        if (!force) {
            return Number(n);
        }
    } else if (!LNumber.isComplex(n)) {
        throw new Error('Invalid constructor call for LComplex');
    }
    var im = n.im instanceof LNumber ? n.im : LNumber(n.im);
    var re = n.re instanceof LNumber ? n.re : LNumber(n.re);
    this.constant(im, re);
}
// -----------------------------------------------------------------------------
LComplex.prototype = Object.create(LNumber.prototype);
LComplex.prototype.constructor = LComplex;
// -----------------------------------------------------------------------------
LComplex.prototype.constant = function(im, re) {
    Object.defineProperty(this, '__im__', {
        value: im,
        enumerable: true
    });
    Object.defineProperty(this, '__re__', {
        value: re,
        enumerable: true
    });
    Object.defineProperty(this, '__type__', {
        value: 'complex',
        enumerable: true
    });
};
// -----------------------------------------------------------------------------
LComplex.prototype.serialize = function() {
    return {
        re: this.__re__,
        im: this.__im__
    };
};
// -----------------------------------------------------------------------------
LComplex.prototype.toRational = function(n) {
    if (LNumber.isFloat(this.__im__) && LNumber.isFloat(this.__re__)) {
        const im = LFloat(this.__im__).toRational(n);
        const re = LFloat(this.__re__).toRational(n);
        return LComplex({ im, re });
    }
    return this;
};
// -----------------------------------------------------------------------------
LComplex.prototype.add = function(n) {
    return this.complex_op('add', n, function(a_re, b_re, a_im, b_im) {
        return {
            re: a_re.add(b_re),
            im: a_im.add(b_im)
        };
    });
};
// -----------------------------------------------------------------------------
// :: factor is used in / and modulus
// -----------------------------------------------------------------------------
LComplex.prototype.factor = function() {
    // fix rounding when calculating (/ 1.0 1/10+1/10i)
    if (this.__im__ instanceof LFloat || this.__im__ instanceof LFloat) {
        let { __re__: re, __im__: im } = this;
        let x, y;
        if (re instanceof LFloat) {
            x = re.toRational().mul(re.toRational());
        } else {
            x = re.mul(re);
        }
        if (im instanceof LFloat) {
            y = im.toRational().mul(im.toRational());
        } else {
            y = im.mul(im);
        }
        return x.add(y);
    } else {
        return this.__re__.mul(this.__re__).add(this.__im__.mul(this.__im__));
    }
};
// -----------------------------------------------------------------------------
LComplex.prototype.modulus = function() {
    return this.factor().sqrt();
};
// -----------------------------------------------------------------------------
LComplex.prototype.conjugate = function() {
    return LComplex({ re: this.__re__, im: this.__im__.sub() });
};
// -----------------------------------------------------------------------------
LComplex.prototype.sqrt = function() {
    const r = this.modulus();
    // code based ok Kawa Scheme source code (file DComplex.java)
    // Copyright (c) 1997  Per M.A. Bothner.
    // Released under MIT License
    let re, im;
    if (r.cmp(0) === 0) {
        re = im = r;
    } else if (this.__re__.cmp(0) === 1) {
        re = LFloat(0.5).mul(r.add(this.__re__)).sqrt();
        im = this.__im__.div(re).div(2);
    } else {
        im = LFloat(0.5).mul(r.sub(this.__re__)).sqrt();
        if (this.__im__.cmp(0) === -1) {
            im = im.sub();
        }
        re = this.__im__.div(im).div(2);
    }
    return LComplex({ im, re });
};
// -----------------------------------------------------------------------------
LComplex.prototype.div = function(n) {
    if (LNumber.isNumber(n) && !LNumber.isComplex(n)) {
        if (!(n instanceof LNumber)) {
            n = LNumber(n);
        }
        const re = this.__re__.div(n);
        const im = this.__im__.div(n);
        return LComplex({ re, im });
    } else if (!LNumber.isComplex(n)) {
        throw new Error('[LComplex::div] Invalid value');
    }
    const [ a, b ] = this.coerce(n);
    const denom = b.factor();
    const num = a.mul(b.conjugate());
    const re = num.__re__.op('/', denom);
    const im = num.__im__.op('/', denom);
    return LComplex({ re, im });
};
// -----------------------------------------------------------------------------
LComplex.prototype.sub = function(n) {
    return this.complex_op('sub', n, function(a_re, b_re, a_im, b_im) {
        return {
            re: a_re.sub(b_re),
            im: a_im.sub(b_im)
        };
    });
};
// -----------------------------------------------------------------------------
LComplex.prototype.mul = function(n) {
    return this.complex_op('mul', n, function(a_re, b_re, a_im, b_im) {
        var ret = {
            re: a_re.mul(b_re).sub(a_im.mul(b_im)),
            im: a_re.mul(b_im).add(b_re.mul(a_im))
        };
        return ret;
    });
};
// -----------------------------------------------------------------------------
LComplex.prototype.complex_op = function(name, n, fn) {
    const calc = (re, im) => {
        var result = fn(this.__re__, re, this.__im__, im);
        if ('im' in result && 're' in result) {
            if (result.im.cmp(0) === 0 && !LNumber.isFloat(result.im)) {
                return result.re;
            }
            return LComplex(result, true);
        }
        return result;
    };
    if (typeof n === 'undefined') {
        return calc();
    }
    if (LNumber.isNumber(n) && !LNumber.isComplex(n)) {
        if (!(n instanceof LNumber)) {
            n = LNumber(n);
        }
        const im = n.asType(0);
        n = { __im__: im, __re__: n };
    } else if (!LNumber.isComplex(n)) {
        throw new Error(`[LComplex::${name}] Invalid value`);
    }
    var re = n.__re__ instanceof LNumber ? n.__re__ : this.__re__.asType(n.__re__);
    var im = n.__im__ instanceof LNumber ? n.__im__ : this.__im__.asType(n.__im__);
    return calc(re, im);
};
// -----------------------------------------------------------------------------
LComplex._op = {
    '+': 'add',
    '-': 'sub',
    '*': 'mul',
    '/': 'div'
};
// -----------------------------------------------------------------------------
LComplex.prototype._op = function(op, n) {
    const fn = LComplex._op[op];
    return this[fn](n);
};
// -----------------------------------------------------------------------------
LComplex.prototype.cmp = function(n) {
    const [a, b] = this.coerce(n);
    const [re_a, re_b] = a.__re__.coerce(b.__re__);
    const re_cmp = re_a.cmp(re_b);
    if (re_cmp !== 0) {
        return re_cmp;
    } else {
        const [im_a, im_b] = a.__im__.coerce(b.__im__);
        return im_a.cmp(im_b);
    }
};
// -----------------------------------------------------------------------------
LComplex.prototype.valueOf = function() {
    return [this.__re__, this.__im__].map(x => x.valueOf());
};
// -----------------------------------------------------------------------------
LComplex.prototype.toString = function() {
    var result;
    if (this.__re__.cmp(0) !== 0) {
        result = [toString(this.__re__)];
    } else {
        result = [];
    }
    // NaN and inf already have sign
    var im = this.__im__.valueOf();
    var inf = [Number.NEGATIVE_INFINITY, Number.POSITIVE_INFINITY].includes(im);
    var im_str = toString(this.__im__);
    if (!inf && !Number.isNaN(im)) {
        var zero_check = this.__im__.cmp(0);
        if (zero_check < 0 || (zero_check === 0 && this.__im__._minus)) {
            result.push('-');
        } else {
            result.push('+');
        }
        im_str = im_str.replace(/^-/, '');
    }
    result.push(im_str);
    result.push('i');
    return result.join('');
};
// -----------------------------------------------------------------------------
// :: FLOAT TYPE
// -----------------------------------------------------------------------------
function LFloat(n) {
    if (typeof this !== 'undefined' && !(this instanceof LFloat) ||
        typeof this === 'undefined') {
        return new LFloat(n);
    }
    if (!LNumber.isNumber(n)) {
        throw new Error('Invalid constructor call for LFloat');
    }
    if (n instanceof LNumber) {
        return LFloat(n.valueOf());
    }
    if (typeof n === 'number') {
        if (Object.is(n, -0)) {
            Object.defineProperty(this, '_minus', {
                value: true
            });
        }
        this.constant(n, 'float');
    }
}
// -----------------------------------------------------------------------------
LFloat.prototype = Object.create(LNumber.prototype);
LFloat.prototype.constructor = LFloat;
// -----------------------------------------------------------------------------
LFloat.prototype.toString = function() {
    if (this.__value__ === Number.NEGATIVE_INFINITY) {
        return '-inf.0';
    }
    if (this.__value__ === Number.POSITIVE_INFINITY) {
        return '+inf.0';
    }
    if (Number.isNaN(this.__value__)) {
        return '+nan.0';
    }
    var str = this.__value__.toString();
    if (!LNumber.isFloat(this.__value__) && !str.match(/e/i)) {
        var result = str + '.0';
        return this._minus ? ('-' + result) : result;
    }
    return str.replace(/^([0-9]+)e/, '$1.0e');
};
// -----------------------------------------------------------------------------
LFloat.prototype._op = function(op, n) {
    if (n instanceof LNumber) {
        n = n.__value__;
    }
    const fn = LNumber._ops[op];
    if (op === '/' && this.__value__ === 0 && n === 0) {
        return NaN;
    }
    return LFloat(fn(this.__value__, n), true);
};
// -----------------------------------------------------------------------------
// same aproximation as in guile scheme
LFloat.prototype.toRational = function(n = null) {
    if (n === null) {
        return toRational(this.__value__.valueOf());
    }
    return approxRatio(n.valueOf())(this.__value__.valueOf());
};
// -----------------------------------------------------------------------------
LFloat.prototype.sqrt = function() {
    var value = this.valueOf();
    if (this.cmp(0) < 0) {
        var im = LFloat(Math.sqrt(-value));
        return LComplex({ re: 0, im });
    }
    return LFloat(Math.sqrt(value));
};
// -----------------------------------------------------------------------------
LFloat.prototype.abs = function() {
    var value = this.valueOf();
    if (value < 0) {
        value = -value;
    }
    return LFloat(value);
};
// -----------------------------------------------------------------------------
// ref: https://rosettacode.org/wiki/Convert_decimal_number_to_rational
// -----------------------------------------------------------------------------
var toRational = approxRatio(1e-10);
function approxRatio(eps) {
    return function(n) {
        const gcde = (e, x, y) => {
                const _gcd = (a, b) => (b < e ? a : _gcd(b, a % b));
                if (Number.isNaN(x) || Number.isNaN(y)) {
                    return NaN;
                }
                return _gcd(Math.abs(x), Math.abs(y));
            },
            c = gcde(eps ? eps : (1 / 10000), 1, n);
        return LRational({ num: Math.floor(n / c), denom: Math.floor(1 / c) });
    };
}
// -----------------------------------------------------------------------------
// :: source: Kawa gnu.math.RatNum.java
// :: This algorithm is by Alan Bawden. It has been transcribed
// :: with permission from Kawa copyright M.A. Bothner.
// :: which was transcribed from from C-Gambit, copyright Marc Feeley.
// -----------------------------------------------------------------------------
function rationalize(x, y) {
    var a = x.sub(y);
    var b = x.add(y);
    var result;
    if (a.cmp(b) > 0) {
        result = simplest_rational2(b, a);
    } else if (b.cmp(a) <= 0) {
        result = a;
    } else if (a.cmp(0) > 0) {
        result = simplest_rational2(a, b);
    } else if (y.cmp(0) < 0) {
        result = LNumber(simplest_rational2(b.sub(), a.sub())).sub();
    } else {
        result = LNumber(0);
    }
    if (LNumber.isFloat(y) || LNumber.isFloat(x)) {
        return LFloat(result);
    }
    return result;
}
// -----------------------------------------------------------------------------
function simplest_rational2(x, y) {
    var fx = LNumber(x).floor();
    var fy = LNumber(y).floor();
    if (x.cmp(fx) < 1) {
        return fx;
    } else if (fx.cmp(fy) === 0) {
        var n = LNumber(1).div(y.sub(fy));
        var d = LNumber(1).div(x.sub(fx));
        return fx.add(LNumber(1).div(simplest_rational2(n, d)));
    } else {
        return fx.add(LNumber(1));
    }
}
// -----------------------------------------------------------------------------
function LRational(n, force = false) {
    if (typeof this !== 'undefined' && !(this instanceof LRational) ||
        typeof this === 'undefined') {
        return new LRational(n, force);
    }
    if (!LNumber.isRational(n)) {
        throw new Error('Invalid constructor call for LRational');
    }
    var num, denom;
    if (n instanceof LRational) {
        num = LNumber(n.__num__);
        denom = LNumber(n.__denom__);
    } else {
        num = LNumber(n.num);
        denom = LNumber(n.denom);
    }
    if (!force && denom.cmp(0) !== 0) {
        var is_integer = num.op('%', denom).cmp(0) === 0;
        if (is_integer) {
            return LNumber(num.div(denom));
        }
    }
    this.constant(num, denom);
}
// -----------------------------------------------------------------------------
LRational.prototype = Object.create(LNumber.prototype);
LRational.prototype.constructor = LRational;
// -----------------------------------------------------------------------------
LRational.prototype.constant = function(num, denom) {
    Object.defineProperty(this, '__num__', {
        value: num,
        enumerable: true
    });
    Object.defineProperty(this, '__denom__', {
        value: denom,
        enumerable: true
    });
    Object.defineProperty(this, '__type__', {
        value: 'rational',
        enumerable: true
    });
};
// -----------------------------------------------------------------------------
LRational.prototype.serialize = function() {
    return {
        num: this.__num__,
        denom: this.__denom__
    };
};
// -----------------------------------------------------------------------------
LRational.prototype.pow = function(n) {
    var cmp = n.cmp(0);
    if (cmp === 0) {
        return LNumber(1);
    }
    if (cmp === -1) {
        n = n.sub();
        var num = this.__denom__.pow(n);
        var denom = this.__num__.pow(n);
        return LRational({ num, denom });
    }
    var result = this;
    n = n.valueOf();
    while (n > 1) {
        result = result.mul(this);
        n--;
    }
    return result;
};
// -----------------------------------------------------------------------------
LRational.prototype.sqrt = function() {
    const num = this.__num__.sqrt();
    const denom = this.__denom__.sqrt();
    if (num instanceof LFloat || denom instanceof LFloat) {
        return num.div(denom);
    }
    return LRational({ num, denom });
};
// -----------------------------------------------------------------------------
LRational.prototype.abs = function() {
    var num = this.__num__;
    var denom = this.__denom__;
    if (num.cmp(0) === -1) {
        num = num.sub();
    }
    if (denom.cmp(0) !== 1) {
        denom = denom.sub();
    }
    return LRational({ num, denom });
};
// -----------------------------------------------------------------------------
LRational.prototype.cmp = function(n) {
    return LNumber(this.valueOf(), true).cmp(n);
};
// -----------------------------------------------------------------------------
LRational.prototype.toString = function() {
    var gcd = this.__num__.gcd(this.__denom__);
    var num, denom;
    if (gcd.cmp(1) !== 0) {
        num = this.__num__.div(gcd);
        if (num instanceof LRational) {
            num = LNumber(num.valueOf(true));
        }
        denom = this.__denom__.div(gcd);
        if (denom instanceof LRational) {
            denom = LNumber(denom.valueOf(true));
        }
    } else {
        num = this.__num__;
        denom = this.__denom__;
    }
    const minus = this.cmp(0) < 0;
    if (minus) {
        if (num.abs().cmp(denom.abs()) === 0) {
            return num.toString();
        }
    } else if (num.cmp(denom) === 0) {
        return num.toString();
    }
    return num.toString() + '/' + denom.toString();
};
// -----------------------------------------------------------------------------
LRational.prototype.valueOf = function(exact) {
    if (this.__denom__.cmp(0) === 0) {
        if (this.__num__.cmp(0) < 0) {
            return Number.NEGATIVE_INFINITY;
        }
        return Number.POSITIVE_INFINITY;
    }
    if (exact) {
        return LNumber._ops['/'](this.__num__.value, this.__denom__.value);
    }
    return LFloat(this.__num__.valueOf()).div(this.__denom__.valueOf());
};
// -----------------------------------------------------------------------------
LRational.prototype.mul = function(n) {
    if (!(n instanceof LNumber)) {
        n = LNumber(n); // handle (--> 1/2 (mul 2))
    }
    if (LNumber.isRational(n)) {
        var num = this.__num__.mul(n.__num__);
        var denom = this.__denom__.mul(n.__denom__);
        return LRational({ num, denom });
    }
    const [a, b] = LNumber.coerce(this, n);
    return a.mul(b);
};
// -----------------------------------------------------------------------------
LRational.prototype.div = function(n) {
    if (!(n instanceof LNumber)) {
        n = LNumber(n); // handle (--> 1/2 (div 2))
    }
    if (LNumber.isRational(n)) {
        var num = this.__num__.mul(n.__denom__);
        var denom = this.__denom__.mul(n.__num__);
        return LRational({ num, denom });
    }
    const [a, b] = LNumber.coerce(this, n);
    const ret = a.div(b);
    return ret;
};
// -----------------------------------------------------------------------------
LRational.prototype._op = function(op, n) {
    return this[rev_mapping[op]](n);
};
// -----------------------------------------------------------------------------
LRational.prototype.sub = function(n) {
    if (typeof n === 'undefined') {
        return this.mul(-1);
    }
    if (!(n instanceof LNumber)) {
        n = LNumber(n); // handle (--> 1/2 (sub 1))
    }
    if (LNumber.isRational(n)) {
        var num = n.__num__.sub();
        var denom = n.__denom__;
        return this.add(LRational({ num, denom }));
    }
    if (!(n instanceof LNumber)) {
        n = LNumber(n).sub();
    } else {
        n = n.sub();
    }
    const [a, b] = LNumber.coerce(this, n);
    return a.add(b);
};
// -----------------------------------------------------------------------------
LRational.prototype.add = function(n) {
    if (!(n instanceof LNumber)) {
        n = LNumber(n); // handle (--> 1/2 (add 1))
    }
    if (LNumber.isRational(n)) {
        const a_denom = this.__denom__;
        const b_denom = n.__denom__;
        const a_num = this.__num__;
        const b_num = n.__num__;
        let denom, num;
        if (a_denom !== b_denom) {
            num = b_denom.mul(a_num).add(b_num.mul(a_denom));
            denom = a_denom.mul(b_denom);
        } else {
            num = a_num.add(b_num);
            denom = a_denom;
        }
        return LRational({ num, denom });
    }
    if (LNumber.isFloat(n)) {
        return LFloat(this.valueOf()).add(n);
    }
    const [a, b] = LNumber.coerce(this, n);
    return a.add(b);
};
// -----------------------------------------------------------------------------
function LBigInteger(n, native) {
    if (typeof this !== 'undefined' && !(this instanceof LBigInteger) ||
        typeof this === 'undefined') {
        return new LBigInteger(n, native);
    }
    if (n instanceof LBigInteger) {
        return LBigInteger(n.__value__, n._native);
    }
    if (!LNumber.isBigInteger(n)) {
        throw new Error('Invalid constructor call for LBigInteger');
    }
    this.constant(n, 'bigint');
    Object.defineProperty(this, '_native', {
        value: native
    });
}
// -----------------------------------------------------------------------------
LBigInteger.prototype = Object.create(LNumber.prototype);
LBigInteger.prototype.constructor = LBigInteger;
// -----------------------------------------------------------------------------
LBigInteger.bn_op = {
    '+': 'iadd',
    '-': 'isub',
    '*': 'imul',
    '/': 'idiv',
    '%': 'imod',
    '|': 'ior',
    '&': 'iand',
    '~': 'inot',
    '<<': 'ishrn',
    '>>': 'ishln'
};
LBigInteger.prototype.serialize = function() {
    return this.__value__.toString();
};
// -----------------------------------------------------------------------------
LBigInteger.prototype._op = function(op, n) {
    if (typeof n === 'undefined') {
        if (LNumber.isBN(this.__value__)) {
            op = LBigInteger.bn_op[op];
            return LBigInteger(this.__value__.clone()[op](), false);
        }
        return LBigInteger(LNumber._ops[op](this.__value__), true);
    }
    if (LNumber.isBN(this.__value__) && LNumber.isBN(n.__value__)) {
        op = LBigInteger.bn_op[op];
        return LBigInteger(this.__value__.clone()[op](n), false);
    }
    const ret = LNumber._ops[op](this.__value__, n.__value__);
    if (op === '/') {
        var is_integer = this.op('%', n).cmp(0) === 0;
        if (is_integer) {
            return LNumber(ret);
        }
        return LRational({ num: this, denom: n });
    }
    // use native calucaltion becuase it's real bigint value
    return LBigInteger(ret, true);
};
// -------------------------- -----------------------------------------------
LBigInteger.prototype.sqrt = function() {
    var value;
    var minus = this.cmp(0) < 0;
    if (LNumber.isNative(this.__value__)) {
        value = LNumber(Math.sqrt(minus ? -this.valueOf() : this.valueOf()));
    } else if (LNumber.isBN(this.__value__)) {
        value = minus ? this.__value__.neg().sqrt() : this.__value__.sqrt();
    }
    if (minus) {
        return LComplex({ re: 0, im: value });
    }
    return value;
};
// -----------------------------------------------------------------------------
LNumber.NaN = LNumber(NaN);
// -----------------------------------------------------------------------------
// type coercion matrix
// -----------------------------------------------------------------------------
const matrix = (function() {
    var i = (a, b) => [a, b];
    return {
        bigint: {
            bigint: i,
            float: (a, b) => [LFloat(a.valueOf(), true), b],
            rational: (a, b) => [{ num: a, denom: 1 }, b],
            complex: (a, b) => [{ im: 0, re: a }, b]
        },
        integer: {
            integer: i,
            float: (a, b) => [LFloat(a.valueOf(), true), b],
            rational: (a, b) => [{ num: a, denom: 1 }, b],
            complex: (a, b) => [{ im: 0, re: a }, b]
        },
        float: {
            bigint: (a, b) => [a, b && LFloat(b.valueOf(), true)],
            integer: (a, b) => [a, b && LFloat(b.valueOf(), true)],
            float: i,
            rational: (a, b) => [a, b && LFloat(b.valueOf(), true)],
            complex: (a, b) => [{ re: a, im: LFloat(0, true) }, b]
        },
        complex: {
            bigint: complex('bigint'),
            integer: complex('integer'),
            float: complex('float'),
            rational: complex('rational'),
            complex: (a, b) => {
                const [a_re, b_re] = LNumber.coerce(a.__re__, b.__re__);
                const [a_im, b_im] = LNumber.coerce(a.__im__, b.__im__);
                return [
                    { im: a_im, re: a_re },
                    { im: b_im, re: b_re }
                ];
            }
        },
        rational: {
            bigint: (a, b) => [a, b && { num: b, denom: 1 }],
            integer: (a, b) => [a, b && { num: b, denom: 1 }],
            float: (a, b) => [LFloat(a.valueOf()), b],
            rational: i,
            complex: (a, b) => {
                return [
                    {
                        im: coerce(a.__type__, b.__im__.__type__, 0)[0],
                        re: coerce(a.__type__, b.__re__.__type__, a)[0]
                    },
                    {
                        im: coerce(a.__type__, b.__im__.__type__, b.__im__)[0],
                        re: coerce(a.__type__, b.__re__.__type__, b.__re__)[0]
                    }
                ];
            }
        }
    };
    function complex(type) {
        return (a, b) => {
            return [
                {
                    im: coerce(type, a.__im__.__type__, 0, a.__im__)[1],
                    re: coerce(type, a.__re__.__type__, 0, a.__re__)[1]
                },
                {
                    im: coerce(type, a.__im__.__type__, 0, 0)[1],
                    re: coerce(type, b.__type__, 0, b)[1]
                }
            ];
        };
    }
})();

// -----------------------------------------------------------------------------
function coerce(type_a, type_b, a, b) {
    return matrix[type_a][type_b](a, b);
}

// -----------------------------------------------------------------------------
const nan = LNumber(NaN);

// -----------------------------------------------------------------------------
// :: abs that work on BigInt
// -----------------------------------------------------------------------------
function abs(x) {
    return x < 0 ? -x : x;
}

// -----------------------------------------------------------------------------
const truncate = (function() {
    if (Math.trunc) {
        return Math.trunc;
    } else {
        return function(x) {
            if (x === 0) {
                return 0;
            } else if (x < 0) {
                return Math.ceil(x);
            } else {
                return Math.floor(x);
            }
        };
    }
})();

export {
    LNumber,
    LComplex,
    LFloat,
    LRational,
    LBigInteger,
    nan,
    abs,
    truncate,
    rationalize
};

