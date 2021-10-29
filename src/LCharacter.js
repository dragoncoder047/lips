/*
 * This file is part of LIPS - Scheme based Powerful LISP in JavaScript
 * Copyright (c) 2018-2021 Jakub T. Jankiewicz <https://jcubic.pl/me>
 * Released under the MIT license
 */
import LString from './LString.js';
import { characters } from './Parser.js';
// -------------------------------------------------------------------------
// :: character object representation
// -------------------------------------------------------------------------
function LCharacter(char) {
    if (typeof this !== 'undefined' && !(this instanceof LCharacter) ||
        typeof this === 'undefined') {
        return new LCharacter(char);
    }
    if (char instanceof LString) {
        char = char.valueOf();
    }
    var name;
    if (Array.from(char).length > 1) {
        // this is name
        char = char.toLowerCase();
        if (LCharacter.__names__[char]) {
            name = char;
            char = LCharacter.__names__[char];
        } else {
            // this should never happen
            // parser don't alow not defined named characters
            throw new Error('Internal: Unknown named character');
        }
    } else {
        name = LCharacter.__rev_names__[char];
    }
    Object.defineProperty(this, '__char__', {
        value: char,
        enumerable: true
    });
    if (name) {
        Object.defineProperty(this, '__name__', {
            value: name,
            enumerable: true
        });
    }
}
LCharacter.__names__ = characters;
LCharacter.__rev_names__ = {};
Object.keys(LCharacter.__names__).forEach(key => {
    var value = LCharacter.__names__[key];
    LCharacter.__rev_names__[value] = key;
});
LCharacter.prototype.toUpperCase = function() {
    return LCharacter(this.__char__.toUpperCase());
};
LCharacter.prototype.toLowerCase = function() {
    return LCharacter(this.__char__.toLowerCase());
};
LCharacter.prototype.toString = function() {
    return '#\\' + (this.__name__ || this.__char__);
};
LCharacter.prototype.valueOf = LCharacter.prototype.serialize = function() {
    return this.__char__;
};

export default LCharacter;
