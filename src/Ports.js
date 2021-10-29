/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
/* global Symbol, Uint8Array */
import { typecheck, type_error_message } from './typechecking.js';
import { Parser } from './Parser.js';
import { nil } from './Pair.js';
import { read_only } from './utils.js';
import { LNumber } from './Numbers.js';
import { global_env, user_env } from './CoreLibrary.js';
import LString from './LString.js';

// -------------------------------------------------------------------------
const __binary_port__ = Symbol.for('binary');
const text_port = Symbol.for('text');
var eof = new EOF();
function EOF() {}
EOF.prototype.toString = function() {
    return '#<eof>';
};

// -------------------------------------------------------------------------
// :: Port abstration - read should be a function that return next line
// -------------------------------------------------------------------------
function InputPort(read) {
    if (typeof this !== 'undefined' && !(this instanceof InputPort) ||
        typeof this === 'undefined') {
        return new InputPort(read);
    }
    typecheck('InputPort', read, 'function');
    read_only(this, '__type__', text_port);
    var parser;
    Object.defineProperty(this, '__parser__', {
        enumerable: true,
        get: function() {
            return parser;
        },
        set: function(value) {
            typecheck('InputPort::__parser__', value, 'parser');
            parser = value;
        }
    });
    this._read = read;
    this._with_parser = this._with_init_parser.bind(this, async () => {
        if (!this.char_ready()) {
            const line = await this._read();
            parser = new Parser(line, { env: this });
        }
        return this.__parser__;
    });
    this.char_ready = function() {
        return !!this.__parser__ && this.__parser__.__lexer__.peek() !== eof;
    };
    this._make_defaults();
}
InputPort.prototype._make_defaults = function() {
    this.read = this._with_parser((parser) => {
        return parser.read_object();
    });
    this.read_line = this._with_parser((parser) => {
        return parser.__lexer__.read_line();
    });
    this.read_char = this._with_parser((parser) => {
        return parser.__lexer__.read_char();
    });
    this.read_string = this._with_parser((parser, number) => {
        if (!LNumber.isInteger(number)) {
            const type = LNumber.getType(number);
            type_error_message('read-string', type, 'integer');
        }
        return parser.__lexer__.read_string(number.valueOf());
    });
    this.peek_char = this._with_parser((parser) => {
        return parser.__lexer__.peek_char();
    });
};
InputPort.prototype._with_init_parser = function(make_parser, fn) {
    var self = this;
    return async function(...args) {
        var parser = await make_parser.call(self);
        return fn(parser, ...args);
    };
};
InputPort.prototype.is_open = function() {
    return this._with_parser !== null;
};
InputPort.prototype.close = function() {
    this.__parser__ = null;
    // make content garbage collected, we assign null,
    // because the value is in prototype
    this._with_parser = null;
    ['read', 'close', 'read_char', 'peek-char', 'read_line'].forEach(name => {
        this[name] = function() {
            throw new Error('input-port: port is closed');
        };
    });
    this.char_ready = function() {
        return false;
    };
};
InputPort.prototype.toString = function() {
    return '#<input-port>';
};
// -------------------------------------------------------------------------
function OutputPort(write) {
    if (typeof this !== 'undefined' && !(this instanceof OutputPort) ||
        typeof this === 'undefined') {
        return new OutputPort(write);
    }
    typecheck('OutputPort', write, 'function');
    read_only(this, '__type__', text_port);
    this.write = write;
}
OutputPort.prototype.is_open = function() {
    return this._closed !== true;
};
OutputPort.prototype.close = function() {
    Object.defineProperty(this, '_closed', {
        get: () => true,
        set: () => {},
        configurable: false,
        enumerable: false
    });
    this.write = function() {
        throw new Error('output-port: port is closed');
    };
};
OutputPort.prototype.flush = function() {
    // do nothing
};
OutputPort.prototype.toString = function() {
    return '#<output-port>';
};
// -------------------------------------------------------------------------
class BufferedOutputPort extends OutputPort {
    constructor(fn) {
        super((...args) => this._write(...args));
        typecheck('BufferedOutputPort', fn, 'function');
        read_only(this, '_fn', fn, { hidden: true });
        read_only(this, '_buffer', [], { hidden: true });
    }
    flush() {
        if (this._buffer.length) {
            this._fn(this._buffer.join(''));
            this._buffer.length = 0;
        }
    }
    _write(...args) {
        if (args.length) {
            args.forEach(arg => {
                this._buffer.push(arg);
            });
            const last_value = this._buffer[this._buffer.length - 1];
            if (last_value.match(/\n$/)) {
                this._buffer[this._buffer.length - 1] = last_value.replace(/\n$/, '');
                this.flush();
            }
        }
    }
}
// -------------------------------------------------------------------------
function OutputStringPort(toString) {
    if (typeof this !== 'undefined' && !(this instanceof OutputStringPort) ||
        typeof this === 'undefined') {
        return new OutputStringPort(toString);
    }
    typecheck('OutputStringPort', toString, 'function');
    read_only(this, '__type__', text_port);
    read_only(this, '__buffer__', []);
    this.write = (x) => {
        if (!LString.isString(x)) {
            x = toString(x);
        } else {
            x = x.valueOf();
        }
        this.__buffer__.push(x);
    };
}
OutputStringPort.prototype = Object.create(OutputPort.prototype);
OutputStringPort.prototype.constructor = OutputStringPort;
OutputStringPort.prototype.toString = function() {
    return '#<output-port (string)>';
};
OutputStringPort.prototype.valueOf = function() {
    return this.__buffer__.map(x => x.valueOf()).join('');
};
// -------------------------------------------------------------------------
function InputStringPort(string, env) {
    if (typeof this !== 'undefined' && !(this instanceof InputStringPort) ||
        typeof this === 'undefined') {
        return new InputStringPort(string);
    }
    typecheck('InputStringPort', string, 'string');
    env = env || global_env;
    string = string.valueOf();
    this._with_parser = this._with_init_parser.bind(this, () => {
        if (!this.__parser__) {
            this.__parser__ = new Parser(string, { env });
        }
        return this.__parser__;
    });
    read_only(this, '__type__', text_port);
    this._make_defaults();
}
InputStringPort.prototype.char_ready = function() {
    return true;
};
InputStringPort.prototype = Object.create(InputPort.prototype);
InputStringPort.prototype.constructor = InputStringPort;
InputStringPort.prototype.toString = function() {
    return `#<input-port (string)>`;
};
// -------------------------------------------------------------------------
function InputByteVectorPort(bytevectors) {
    if (typeof this !== 'undefined' && !(this instanceof InputByteVectorPort) ||
        typeof this === 'undefined') {
        return new InputByteVectorPort(bytevectors);
    }
    typecheck('InputByteVectorPort', bytevectors, 'uint8array');
    read_only(this, '__vector__', bytevectors);
    read_only(this, '__type__', __binary_port__);
    var index = 0;
    Object.defineProperty(this, '__index__', {
        enumerable: true,
        get: function() {
            return index;
        },
        set: function(value) {
            typecheck('InputByteVectorPort::__index__', value, 'number');
            if (value instanceof LNumber) {
                value = value.valueOf();
            }
            if (typeof value === 'bigint') {
                value = Number(value);
            }
            if (Math.floor(value) !== value) {
                throw new Error('InputByteVectorPort::__index__ value is ' +
                                'not integer');
            }
            index = value;
        }
    });
}
InputByteVectorPort.prototype = Object.create(InputPort.prototype);
InputByteVectorPort.prototype.constructor = InputByteVectorPort;
InputByteVectorPort.prototype.toString = function() {
    return `#<input-port (bytevector)>`;
};
InputByteVectorPort.prototype.close = function() {
    read_only(this, '__vector__', nil);
    ['read_u8', 'close', 'peek_u8', 'read_u8_vector'].forEach(name => {
        this[name] = function() {
            throw new Error('Input-binary-port: port is closed');
        };
    });
    this.char_ready = function() {
        return false;
    };
};
InputByteVectorPort.prototype.u8_ready = function() {
    return true;
};
InputByteVectorPort.prototype.peek_u8 = function() {
    if (this.__index__ >= this.__vector__.length) {
        return eof;
    }
    return this.__vector__[this.__index__];
};
InputByteVectorPort.prototype.skip = function() {
    if (this.__index__ <= this.__vector__.length) {
        ++this.__index__;
    }
};
InputByteVectorPort.prototype.read_u8 = function() {
    const byte = this.peek_u8();
    this.skip();
    return byte;
};
InputByteVectorPort.prototype.read_u8_vector = function(len) {
    if (typeof len === 'undefined') {
        len = this.__vector__.length;
    } else if (len > this.__index__ + this.__vector__.length) {
        len = this.__index__ + this.__vector__.length;
    }
    if (this.peek_u8() === eof) {
        return eof;
    }
    return this.__vector__.slice(this.__index__, len);
};
// -------------------------------------------------------------------------
function OutputByteVectorPort() {
    if (typeof this !== 'undefined' && !(this instanceof OutputByteVectorPort) ||
        typeof this === 'undefined') {
        return new OutputByteVectorPort();
    }
    read_only(this, '__type__', __binary_port__);
    read_only(this, '_buffer', [], { hidden: true });
    this.write = function(x) {
        typecheck('write', x, ['number', 'uint8array']);
        if (LNumber.isNumber(x)) {
            this._buffer.push(x.valueOf());
        } else {
            this._buffer.push(...Array.from(x));
        }
    };
    Object.defineProperty(this, '__buffer__', {
        enumerable: true,
        get: function() {
            return Uint8Array.from(this._buffer);
        }
    });
}
OutputByteVectorPort.prototype = Object.create(OutputPort.prototype);
OutputByteVectorPort.prototype.constructor = OutputByteVectorPort;
OutputByteVectorPort.prototype.close = function() {
    OutputPort.prototype.close.call(this);
    read_only(this, '_buffer', null, { hidden: true });
};
OutputByteVectorPort.prototype._close_guard = function() {
    if (this._closed) {
        throw new Error('output-port: binary port is closed');
    }
};
OutputByteVectorPort.prototype.write_u8 = function(byte) {
    typecheck('OutputByteVectorPort::write_u8', byte, 'number');
    this.write(byte);
};
OutputByteVectorPort.prototype.write_u8_vector = function(vector) {
    typecheck('OutputByteVectorPort::write_u8_vector', vector, 'uint8array');
    this.write(vector);
};
OutputByteVectorPort.prototype.toString = function() {
    return '#<output-port (bytevector)>';
};
OutputByteVectorPort.prototype.valueOf = function() {
    return this.__buffer__;
};
// -------------------------------------------------------------------------
function OutputFilePort(filename, fd) {
    if (typeof this !== 'undefined' && !(this instanceof OutputFilePort) ||
        typeof this === 'undefined') {
        return new OutputFilePort(filename, fd);
    }
    typecheck('OutputFilePort', filename, 'string');
    read_only(this, '__filename__', filename);
    read_only(this, '_fd', fd.valueOf(), { hidden: true });
    read_only(this, '__type__', text_port);
    this.write = (x) => {
        if (!LString.isString(x)) {
            x = toString(x);
        } else {
            x = x.valueOf();
        }
        this.fs().write(this._fd, x, function(err) {
            if (err) {
                throw err;
            }
        });
    };
}
OutputFilePort.prototype = Object.create(OutputPort.prototype);
OutputFilePort.prototype.constructor = OutputFilePort;
OutputFilePort.prototype.fs = function() {
    if (!this._fs) {
        this._fs = this.internal('fs');
    }
    return this._fs;
};
OutputFilePort.prototype.internal = function(name) {
    return user_env.get('**internal-env**').get(name);
};
OutputFilePort.prototype.close = function() {
    return new Promise((resolve, reject) => {
        this.fs().close(this._fd, (err) => {
            if (err) {
                reject(err);
            } else {
                read_only(this, '_fd', null, { hidden: true });
                OutputPort.prototype.close.call(this);
                resolve();
            }
        });
    });
};
OutputFilePort.prototype.toString = function() {
    return `#<output-port ${this.__filename__}>`;
};
// -------------------------------------------------------------------------
function InputFilePort(content, filename) {
    if (typeof this !== 'undefined' && !(this instanceof InputFilePort) ||
        typeof this === 'undefined') {
        return new InputFilePort(content, filename);
    }
    InputStringPort.call(this, content);
    typecheck('InputFilePort', filename, 'string');
    read_only(this, '__filename__', filename);
}
InputFilePort.prototype = Object.create(InputStringPort.prototype);
InputFilePort.prototype.constructor = InputFilePort;
InputFilePort.prototype.toString = function() {
    return `#<input-port (${this.__filename__})>`;
};
// -------------------------------------------------------------------------
function InputBinaryFilePort(content, filename) {
    if (typeof this !== 'undefined' && !(this instanceof InputBinaryFilePort) ||
        typeof this === 'undefined') {
        return new InputBinaryFilePort(content, filename);
    }
    InputByteVectorPort.call(this, content);
    typecheck('InputBinaryFilePort', filename, 'string');
    read_only(this, '__filename__', filename);
}
InputBinaryFilePort.prototype = Object.create(InputByteVectorPort.prototype);
InputBinaryFilePort.prototype.constructor = InputBinaryFilePort;
InputBinaryFilePort.prototype.toString = function() {
    return `#<input-binary-port (${this.__filename__})>`;
};
// -------------------------------------------------------------------------
function OutputBinaryFilePort(filename, fd) {
    if (typeof this !== 'undefined' && !(this instanceof OutputBinaryFilePort) ||
        typeof this === 'undefined') {
        return new OutputBinaryFilePort(filename, fd);
    }
    typecheck('OutputBinaryFilePort', filename, 'string');
    read_only(this, '__filename__', filename);
    read_only(this, '_fd', fd.valueOf(), { hidden: true });
    read_only(this, '__type__', __binary_port__);
    var fs, Buffer;
    this.write = function(x) {
        typecheck('write', x, ['number', 'uint8array']);
        var buffer;
        if (!fs) {
            fs = this.internal('fs');
        }
        if (!Buffer) {
            Buffer = this.internal('Buffer');
        }
        if (LNumber.isNumber(x)) {
            buffer = Buffer.from([x.valueOf()]);
        } else {
            buffer = Buffer.from(Array.from(x));
        }
        return new Promise((resolve, reject) => {
            fs.write(this._fd, buffer, function(err) {
                if (err) {
                    reject(err);
                } else {
                    resolve();
                }
            });
        });
    };
}
OutputBinaryFilePort.prototype = Object.create(OutputFilePort.prototype);
OutputBinaryFilePort.prototype.constructor = OutputBinaryFilePort;
OutputBinaryFilePort.prototype.write_u8 = function(byte) {
    typecheck('OutputByteVectorPort::write_u8', byte, 'number');
    this.write(byte);
};
OutputBinaryFilePort.prototype.write_u8_vector = function(vector) {
    typecheck('OutputByteVectorPort::write_u8_vector', vector, 'uint8array');
    this.write(vector);
};

export {
    eof,
    __binary_port__,
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
};
