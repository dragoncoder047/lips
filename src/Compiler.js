/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol, Uint8Array */
import { addExtension, Encoder } from 'cbor-x';
import { pack, unpack } from 'lzjb-pack';
import { Pair, nil } from './Pair.js';
import { LSymbol } from './LSymbol.js';
import { LNumber } from './Numbers.js';
import { is_undef } from './typechecking.js';
import LCharacter from './LCharacter.js';
import LString from './LString.js';

// -------------------------------------------------------------------------
// :: Serialization
// -------------------------------------------------------------------------
var serialization_map = {
    'pair': ([car, cdr]) => Pair(car, cdr),
    'number': function(value) {
        if (LString.isString(value)) {
            return LNumber([value, 10]);
        }
        return LNumber(value);
    },
    'regex': function([pattern, flag]) {
        return new RegExp(pattern, flag);
    },
    'nil': function() {
        return nil;
    },
    'symbol': function(value) {
        if (LString.isString(value)) {
            return LSymbol(value);
        } else if (Array.isArray(value)) {
            return LSymbol(Symbol.for(value[0]));
        }
    },
    'string': LString,
    'character': LCharacter
};
// -------------------------------------------------------------------------
// class mapping to create smaller JSON
const available_class = Object.keys(serialization_map);
const class_map = {};
for (let [i, cls] of Object.entries(available_class)) {
    class_map[cls] = +i;
}
function mangle_name(name) {
    return class_map[name];
}
function resolve_name(i) {
    return available_class[i];
}
// -------------------------------------------------------------------------
function serialize(data) {
    return JSON.stringify(data, function(key, value) {
        const v0 = this[key];
        if (v0) {
            if (v0 instanceof RegExp) {
                return {
                    '@': mangle_name('regex'),
                    '#': [v0.source, v0.flags]
                };
            }
            var cls = mangle_name(v0.constructor.__class__);
            if (!is_undef(cls)) {
                return {
                    '@': cls,
                    '#': v0.serialize()
                };
            }
        }
        return value;
    });
}
// -------------------------------------------------------------------------
function unserialize(string) {
    return JSON.parse(string, (_, object) => {
        if (object && typeof object === 'object') {
            if (!is_undef(object['@'])) {
                var cls = resolve_name(object['@']);
                if (serialization_map[cls]) {
                    return serialization_map[cls](object['#']);
                }
            }
        }
        return object;
    });
}

// -------------------------------------------------------------------------
// binary serialization using CBOR binary data format
// -------------------------------------------------------------------------
const cbor = (function() {

    var types = {
        'pair': Pair,
        'symbol': LSymbol,
        'number': LNumber,
        'string': LString,
        'character': LCharacter,
        'nil': nil.constructor,
        'regex': RegExp
    };

    function serializer(Class, fn) {
        return {
            deserialize: fn,
            Class
        };
    }

    var encoder = new Encoder();

    const cbor_serialization_map = {};
    for (const [ name, fn ] of Object.entries(serialization_map)) {
        const Class = types[name];
        cbor_serialization_map[name] = serializer(Class, fn);
    }
    // add CBOR data mapping
    let tag = 43311;
    Object.keys(cbor_serialization_map).forEach(type => {
        const data = cbor_serialization_map[type];
        if (typeof data === 'function') {
            const Class = data;
            addExtension({
                Class,
                tag,
                encode(instance, encode) {
                    encode(instance.serialize());
                },
                decode(data) {
                    return new Class(data);
                }
            });
        } else {
            const { deserialize, Class } = data;
            addExtension({
                Class,
                tag,
                encode(instance, encode) {
                    if (instance instanceof RegExp) {
                        return encode([instance.source, instance.flags]);
                    }
                    encode(instance.serialize());
                },
                decode(data) {
                    return deserialize(data);
                }
            });
        }
        tag++;
    });
    return encoder;
})();

// -------------------------------------------------------------------------
function merge_uint8_array(...args) {
    if (args.length > 1) {
        const len = args.reduce((acc, arr) => acc + arr.length, 0);
        const result = new Uint8Array(len);
        let offset = 0;
        args.forEach(item => {
            result.set(item, offset);
            offset += item.length;
        });
        return result;
    } else if (args.length) {
        return args[0];
    }
}

// -------------------------------------------------------------------------
function encode_magic() {
    const VERSION = 1;
    const encoder = new TextEncoder('utf-8');
    return encoder.encode(`CBRZ${VERSION.toString().padStart(3, ' ')}`);
}

// -------------------------------------------------------------------------
const MAGIC_LENGTH = 7;
// -------------------------------------------------------------------------
function decode_magic(obj) {
    const decoder = new TextDecoder('utf-8');
    const prefix = decoder.decode(obj.slice(0, MAGIC_LENGTH));
    const name = prefix.substring(0, 4);
    if (['CBOR', 'CBRZ'].includes(name)) {
        const m = prefix.match(/^(....).*([0-9]+)$/);
        if (m) {
            return {
                type: m[1],
                version: Number(m[2])
            };
        }
    }
    return {
        type: 'unknown'
    };
}

// -------------------------------------------------------------------------
function serialize_bin(obj) {
    const magic = encode_magic();
    const payload = cbor.encode(obj);
    return merge_uint8_array(magic, pack(payload, { magic: false }));
}

// -------------------------------------------------------------------------
function unserialize_bin(data) {
    const { type, version } = decode_magic(data);
    if (type === 'CBOR' && version === 1) {
        return cbor.decode(data.slice(MAGIC_LENGTH));
    } else if (type === 'CBRZ' && version === 1) {
        const arr = unpack(data.slice(MAGIC_LENGTH), { magic: false });
        return cbor.decode(arr);
    } else {
        throw new Error(`Invalid file format ${type}`);
    }
}


export { serialize_bin, unserialize_bin, serialize, unserialize };
