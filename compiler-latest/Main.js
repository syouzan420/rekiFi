"use strict";
var __haste_prog_id = 'f9fc419619d0c5a90b10cb388ba63db4ace1db57185c138c2271a04b099ba7d8';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8="metaKey",_9="shiftKey",_a="altKey",_b="ctrlKey",_c="keyCode",_d=function(_e,_){var _f=__get(_e,E(_c)),_g=__get(_e,E(_b)),_h=__get(_e,E(_a)),_i=__get(_e,E(_9)),_j=__get(_e,E(_8));return new T(function(){var _k=Number(_f),_l=jsTrunc(_k);return new T5(0,_l,E(_g),E(_h),E(_i),E(_j));});},_m=function(_n,_o,_){return new F(function(){return _d(E(_o),_);});},_p="keydown",_q="keyup",_r="keypress",_s=function(_t){switch(E(_t)){case 0:return E(_r);case 1:return E(_q);default:return E(_p);}},_u=new T2(0,_s,_m),_v="deltaZ",_w="deltaY",_x="deltaX",_y=function(_z,_A){var _B=E(_z);return (_B._==0)?E(_A):new T2(1,_B.a,new T(function(){return B(_y(_B.b,_A));}));},_C=function(_D,_E){var _F=jsShowI(_D);return new F(function(){return _y(fromJSStr(_F),_E);});},_G=41,_H=40,_I=function(_J,_K,_L){if(_K>=0){return new F(function(){return _C(_K,_L);});}else{if(_J<=6){return new F(function(){return _C(_K,_L);});}else{return new T2(1,_H,new T(function(){var _M=jsShowI(_K);return B(_y(fromJSStr(_M),new T2(1,_G,_L)));}));}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_I(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_I(0,_R,_P));}))));});},_S=function(_T,_){return new T(function(){var _U=Number(E(_T)),_V=jsTrunc(_U);if(_V<0){return B(_Q(_V));}else{if(_V>2){return B(_Q(_V));}else{return _V;}}});},_W=0,_X=new T3(0,_W,_W,_W),_Y="button",_Z=new T(function(){return eval("jsGetMouseCoords");}),_10=__Z,_11=function(_12,_){var _13=E(_12);if(!_13._){return _10;}else{var _14=B(_11(_13.b,_));return new T2(1,new T(function(){var _15=Number(E(_13.a));return jsTrunc(_15);}),_14);}},_16=function(_17,_){var _18=__arr2lst(0,_17);return new F(function(){return _11(_18,_);});},_19=function(_1a,_){return new F(function(){return _16(E(_1a),_);});},_1b=function(_1c,_){return new T(function(){var _1d=Number(E(_1c));return jsTrunc(_1d);});},_1e=new T2(0,_1b,_19),_1f=function(_1g,_){var _1h=E(_1g);if(!_1h._){return _10;}else{var _1i=B(_1f(_1h.b,_));return new T2(1,_1h.a,_1i);}},_1j=new T(function(){return B(unCStr("base"));}),_1k=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1l=new T(function(){return B(unCStr("IOException"));}),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1j,_1k,_1l),_1n=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_10,_10),_1o=function(_1p){return E(_1n);},_1q=function(_1r){return E(E(_1r).a);},_1s=function(_1t,_1u,_1v){var _1w=B(A1(_1t,_)),_1x=B(A1(_1u,_)),_1y=hs_eqWord64(_1w.a,_1x.a);if(!_1y){return __Z;}else{var _1z=hs_eqWord64(_1w.b,_1x.b);return (!_1z)?__Z:new T1(1,_1v);}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1s(B(_1q(_1C.a)),_1o,_1C.b);});},_1D=new T(function(){return B(unCStr(": "));}),_1E=new T(function(){return B(unCStr(")"));}),_1F=new T(function(){return B(unCStr(" ("));}),_1G=new T(function(){return B(unCStr("interrupted"));}),_1H=new T(function(){return B(unCStr("system error"));}),_1I=new T(function(){return B(unCStr("unsatisified constraints"));}),_1J=new T(function(){return B(unCStr("user error"));}),_1K=new T(function(){return B(unCStr("permission denied"));}),_1L=new T(function(){return B(unCStr("illegal operation"));}),_1M=new T(function(){return B(unCStr("end of file"));}),_1N=new T(function(){return B(unCStr("resource exhausted"));}),_1O=new T(function(){return B(unCStr("resource busy"));}),_1P=new T(function(){return B(unCStr("does not exist"));}),_1Q=new T(function(){return B(unCStr("already exists"));}),_1R=new T(function(){return B(unCStr("resource vanished"));}),_1S=new T(function(){return B(unCStr("timeout"));}),_1T=new T(function(){return B(unCStr("unsupported operation"));}),_1U=new T(function(){return B(unCStr("hardware fault"));}),_1V=new T(function(){return B(unCStr("inappropriate type"));}),_1W=new T(function(){return B(unCStr("invalid argument"));}),_1X=new T(function(){return B(unCStr("failed"));}),_1Y=new T(function(){return B(unCStr("protocol error"));}),_1Z=function(_20,_21){switch(E(_20)){case 0:return new F(function(){return _y(_1Q,_21);});break;case 1:return new F(function(){return _y(_1P,_21);});break;case 2:return new F(function(){return _y(_1O,_21);});break;case 3:return new F(function(){return _y(_1N,_21);});break;case 4:return new F(function(){return _y(_1M,_21);});break;case 5:return new F(function(){return _y(_1L,_21);});break;case 6:return new F(function(){return _y(_1K,_21);});break;case 7:return new F(function(){return _y(_1J,_21);});break;case 8:return new F(function(){return _y(_1I,_21);});break;case 9:return new F(function(){return _y(_1H,_21);});break;case 10:return new F(function(){return _y(_1Y,_21);});break;case 11:return new F(function(){return _y(_1X,_21);});break;case 12:return new F(function(){return _y(_1W,_21);});break;case 13:return new F(function(){return _y(_1V,_21);});break;case 14:return new F(function(){return _y(_1U,_21);});break;case 15:return new F(function(){return _y(_1T,_21);});break;case 16:return new F(function(){return _y(_1S,_21);});break;case 17:return new F(function(){return _y(_1R,_21);});break;default:return new F(function(){return _y(_1G,_21);});}},_22=new T(function(){return B(unCStr("}"));}),_23=new T(function(){return B(unCStr("{handle: "));}),_24=function(_25,_26,_27,_28,_29,_2a){var _2b=new T(function(){var _2c=new T(function(){var _2d=new T(function(){var _2e=E(_28);if(!_2e._){return E(_2a);}else{var _2f=new T(function(){return B(_y(_2e,new T(function(){return B(_y(_1E,_2a));},1)));},1);return B(_y(_1F,_2f));}},1);return B(_1Z(_26,_2d));}),_2g=E(_27);if(!_2g._){return E(_2c);}else{return B(_y(_2g,new T(function(){return B(_y(_1D,_2c));},1)));}}),_2h=E(_29);if(!_2h._){var _2i=E(_25);if(!_2i._){return E(_2b);}else{var _2j=E(_2i.a);if(!_2j._){var _2k=new T(function(){var _2l=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2l));},1);return new F(function(){return _y(_23,_2k);});}else{var _2m=new T(function(){var _2n=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2n));},1);return new F(function(){return _y(_23,_2m);});}}}else{return new F(function(){return _y(_2h.a,new T(function(){return B(_y(_1D,_2b));},1));});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _24(_2q.a,_2q.b,_2q.c,_2q.d,_2q.f,_10);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _24(_2v.a,_2v.b,_2v.c,_2v.d,_2v.f,_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _24(_2z.a,_2z.b,_2z.c,_2z.d,_2z.f,_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H._){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=new T(function(){var _2J=new T(function(){var _2K=function(_2L){var _2M=E(_2L);if(!_2M._){return E(new T2(1,_2B,_2G));}else{var _2N=new T(function(){return B(A2(_2E,_2M.a,new T(function(){return B(_2K(_2M.b));})));});return new T2(1,_2A,_2N);}};return B(_2K(_2H.b));});return B(A2(_2E,_2H.a,_2J));});return new T2(1,_2C,_2I);}},_2O=function(_2P,_2Q){return new F(function(){return _2D(_2w,_2P,_2Q);});},_2R=new T3(0,_2r,_2o,_2O),_2S=new T(function(){return new T5(0,_1o,_2R,_2T,_1A,_2o);}),_2T=function(_2U){return new T2(0,_2S,_2U);},_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_0,_2V,_10,_2W,_0,_0),_2Y=new T(function(){return B(_2T(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1f(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_3d,_3e,_){if(E(_3d)==7){var _3f=__app1(E(_Z),_3e),_3g=B(_32(_1e,_1e,_3f,_)),_3h=__get(_3e,E(_x)),_3i=__get(_3e,E(_w)),_3j=__get(_3e,E(_v));return new T(function(){return new T3(0,E(_3g),E(_0),E(new T3(0,_3h,_3i,_3j)));});}else{var _3k=__app1(E(_Z),_3e),_3l=B(_32(_1e,_1e,_3k,_)),_3m=__get(_3e,E(_Y)),_3n=__eq(_3m,E(_7));if(!E(_3n)){var _3o=__isUndef(_3m);if(!E(_3o)){var _3p=B(_S(_3m,_));return new T(function(){return new T3(0,E(_3l),E(new T1(1,_3p)),E(_X));});}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}},_3q=function(_3r,_3s,_){return new F(function(){return _3c(_3r,E(_3s),_);});},_3t="mouseout",_3u="mouseover",_3v="mousemove",_3w="mouseup",_3x="mousedown",_3y="dblclick",_3z="click",_3A="wheel",_3B=function(_3C){switch(E(_3C)){case 0:return E(_3z);case 1:return E(_3y);case 2:return E(_3x);case 3:return E(_3w);case 4:return E(_3v);case 5:return E(_3u);case 6:return E(_3t);default:return E(_3A);}},_3D=new T2(0,_3B,_3q),_3E=function(_3F){return E(_3F);},_3G=function(_3H,_3I){return E(_3H)==E(_3I);},_3J=function(_3K,_3L){return E(_3K)!=E(_3L);},_3M=new T2(0,_3G,_3J),_3N="screenY",_3O="screenX",_3P="clientY",_3Q="clientX",_3R="pageY",_3S="pageX",_3T="target",_3U="identifier",_3V=function(_3W,_){var _3X=__get(_3W,E(_3U)),_3Y=__get(_3W,E(_3T)),_3Z=__get(_3W,E(_3S)),_40=__get(_3W,E(_3R)),_41=__get(_3W,E(_3Q)),_42=__get(_3W,E(_3P)),_43=__get(_3W,E(_3O)),_44=__get(_3W,E(_3N));return new T(function(){var _45=Number(_3X),_46=jsTrunc(_45);return new T5(0,_46,_3Y,E(new T2(0,new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}),new T(function(){var _48=Number(_40);return jsTrunc(_48);}))),E(new T2(0,new T(function(){var _49=Number(_41);return jsTrunc(_49);}),new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}))),E(new T2(0,new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}),new T(function(){var _4c=Number(_44);return jsTrunc(_4c);}))));});},_4d=function(_4e,_){var _4f=E(_4e);if(!_4f._){return _10;}else{var _4g=B(_3V(E(_4f.a),_)),_4h=B(_4d(_4f.b,_));return new T2(1,_4g,_4h);}},_4i="touches",_4j=function(_4k){return E(E(_4k).b);},_4l=function(_4m,_4n,_){var _4o=__arr2lst(0,_4n),_4p=new T(function(){return B(_4j(_4m));}),_4q=function(_4r,_){var _4s=E(_4r);if(!_4s._){return _10;}else{var _4t=B(A2(_4p,_4s.a,_)),_4u=B(_4q(_4s.b,_));return new T2(1,_4t,_4u);}};return new F(function(){return _4q(_4o,_);});},_4v=function(_4w,_){return new F(function(){return _4l(_1e,E(_4w),_);});},_4x=new T2(0,_19,_4v),_4y=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4z=function(_4A){return E(E(_4A).a);},_4B=function(_4C,_4D,_4E){while(1){var _4F=E(_4E);if(!_4F._){return false;}else{if(!B(A3(_4z,_4C,_4D,_4F.a))){_4E=_4F.b;continue;}else{return true;}}}},_4G=function(_4H,_4I){while(1){var _4J=B((function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=_4M.b;if(!B(A1(_4K,_4N))){var _4P=_4K;_4H=_4P;_4I=_4O;return __continue;}else{return new T2(1,_4N,new T(function(){return B(_4G(_4K,_4O));}));}}})(_4H,_4I));if(_4J!=__continue){return _4J;}}},_4Q=function(_4R,_){var _4S=__get(_4R,E(_4i)),_4T=__arr2lst(0,_4S),_4U=B(_4d(_4T,_)),_4V=__app1(E(_4y),_4R),_4W=B(_32(_4x,_4x,_4V,_)),_4X=E(_4W),_4Y=new T(function(){var _4Z=function(_50){return new F(function(){return _4B(_3M,new T(function(){return E(_50).a;}),_4X.a);});};return B(_4G(_4Z,_4U));}),_51=new T(function(){var _52=function(_53){return new F(function(){return _4B(_3M,new T(function(){return E(_53).a;}),_4X.b);});};return B(_4G(_52,_4U));});return new T3(0,_4U,_51,_4Y);},_54=function(_55,_56,_){return new F(function(){return _4Q(E(_56),_);});},_57="touchcancel",_58="touchend",_59="touchmove",_5a="touchstart",_5b=function(_5c){switch(E(_5c)){case 0:return E(_5a);case 1:return E(_59);case 2:return E(_58);default:return E(_57);}},_5d=new T2(0,_5b,_54),_5e=function(_5f,_5g,_){var _5h=B(A1(_5f,_)),_5i=B(A1(_5g,_));return _5h;},_5j=function(_5k,_5l,_){var _5m=B(A1(_5k,_)),_5n=B(A1(_5l,_));return new T(function(){return B(A1(_5m,_5n));});},_5o=function(_5p,_5q,_){var _5r=B(A1(_5q,_));return _5p;},_5s=function(_5t,_5u,_){var _5v=B(A1(_5u,_));return new T(function(){return B(A1(_5t,_5v));});},_5w=new T2(0,_5s,_5o),_5x=function(_5y,_){return _5y;},_5z=function(_5A,_5B,_){var _5C=B(A1(_5A,_));return new F(function(){return A1(_5B,_);});},_5D=new T5(0,_5w,_5x,_5j,_5z,_5e),_5E=new T(function(){return E(_2S);}),_5F=function(_5G){return E(E(_5G).c);},_5H=function(_5I){return new T6(0,_0,_2V,_10,_5I,_0,_0);},_5J=function(_5K,_){var _5L=new T(function(){return B(A2(_5F,_5E,new T(function(){return B(A1(_5H,_5K));})));});return new F(function(){return die(_5L);});},_5M=function(_5N,_){return new F(function(){return _5J(_5N,_);});},_5O=function(_5P){return new F(function(){return A1(_5M,_5P);});},_5Q=function(_5R,_5S,_){var _5T=B(A1(_5R,_));return new F(function(){return A2(_5S,_5T,_);});},_5U=new T5(0,_5D,_5Q,_5z,_5x,_5O),_5V=function(_5W){return E(_5W);},_5X=new T2(0,_5U,_5V),_5Y=new T2(0,_5X,_5x),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_60=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_61=new T(function(){return eval("(function(cv){return cv.height})");}),_62=new T(function(){return eval("(function(cv){return cv.width})");}),_63=function(_64,_){var _65=__app1(E(_62),_64),_66=__app1(E(_61),_64),_67=__app1(E(_60),_64),_68=__app1(E(_5Z),_64);return new T2(0,new T2(0,_65,_66),new T2(0,_67,_68));},_69=function(_6a,_6b){while(1){var _6c=E(_6a);if(!_6c._){return (E(_6b)._==0)?true:false;}else{var _6d=E(_6b);if(!_6d._){return false;}else{if(E(_6c.a)!=E(_6d.a)){return false;}else{_6a=_6c.b;_6b=_6d.b;continue;}}}}},_6e=function(_6f,_6g){var _6h=E(_6g);return (_6h._==0)?__Z:new T2(1,new T(function(){return B(A1(_6f,_6h.a));}),new T(function(){return B(_6e(_6f,_6h.b));}));},_6i=function(_6j){return new T1(3,E(B(_6e(_5V,_6j))));},_6k="Tried to deserialie a non-array to a list!",_6l=new T1(0,_6k),_6m=new T1(1,_10),_6n=function(_6o){var _6p=E(_6o);if(!_6p._){return E(_6m);}else{var _6q=B(_6n(_6p.b));return (_6q._==0)?new T1(0,_6q.a):new T1(1,new T2(1,_6p.a,_6q.a));}},_6r=function(_6s){var _6t=E(_6s);if(_6t._==3){return new F(function(){return _6n(_6t.a);});}else{return E(_6l);}},_6u=function(_6v){return new T1(1,_6v);},_6w=new T4(0,_5V,_6i,_6u,_6r),_6x=function(_6y,_6z,_6A){return new F(function(){return A1(_6y,new T2(1,_2A,new T(function(){return B(A1(_6z,_6A));})));});},_6B=function(_6C){return new F(function(){return _I(0,E(_6C),_10);});},_6D=34,_6E=new T2(1,_6D,_10),_6F=new T(function(){return B(unCStr("!!: negative index"));}),_6G=new T(function(){return B(unCStr("Prelude."));}),_6H=new T(function(){return B(_y(_6G,_6F));}),_6I=new T(function(){return B(err(_6H));}),_6J=new T(function(){return B(unCStr("!!: index too large"));}),_6K=new T(function(){return B(_y(_6G,_6J));}),_6L=new T(function(){return B(err(_6K));}),_6M=function(_6N,_6O){while(1){var _6P=E(_6N);if(!_6P._){return E(_6L);}else{var _6Q=E(_6O);if(!_6Q){return E(_6P.a);}else{_6N=_6P.b;_6O=_6Q-1|0;continue;}}}},_6R=function(_6S,_6T){if(_6T>=0){return new F(function(){return _6M(_6S,_6T);});}else{return E(_6I);}},_6U=new T(function(){return B(unCStr("ACK"));}),_6V=new T(function(){return B(unCStr("BEL"));}),_6W=new T(function(){return B(unCStr("BS"));}),_6X=new T(function(){return B(unCStr("SP"));}),_6Y=new T2(1,_6X,_10),_6Z=new T(function(){return B(unCStr("US"));}),_70=new T2(1,_6Z,_6Y),_71=new T(function(){return B(unCStr("RS"));}),_72=new T2(1,_71,_70),_73=new T(function(){return B(unCStr("GS"));}),_74=new T2(1,_73,_72),_75=new T(function(){return B(unCStr("FS"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("ESC"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("SUB"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("EM"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("CAN"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("ETB"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("SYN"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("NAK"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("DC4"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("DC3"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("DC2"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("DC1"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DLE"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("SI"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("SO"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("CR"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("FF"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("VT"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("LF"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("HT"));}),_7I=new T2(1,_7H,_7G),_7J=new T2(1,_6W,_7I),_7K=new T2(1,_6V,_7J),_7L=new T2(1,_6U,_7K),_7M=new T(function(){return B(unCStr("ENQ"));}),_7N=new T2(1,_7M,_7L),_7O=new T(function(){return B(unCStr("EOT"));}),_7P=new T2(1,_7O,_7N),_7Q=new T(function(){return B(unCStr("ETX"));}),_7R=new T2(1,_7Q,_7P),_7S=new T(function(){return B(unCStr("STX"));}),_7T=new T2(1,_7S,_7R),_7U=new T(function(){return B(unCStr("SOH"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("NUL"));}),_7X=new T2(1,_7W,_7V),_7Y=92,_7Z=new T(function(){return B(unCStr("\\DEL"));}),_80=new T(function(){return B(unCStr("\\a"));}),_81=new T(function(){return B(unCStr("\\\\"));}),_82=new T(function(){return B(unCStr("\\SO"));}),_83=new T(function(){return B(unCStr("\\r"));}),_84=new T(function(){return B(unCStr("\\f"));}),_85=new T(function(){return B(unCStr("\\v"));}),_86=new T(function(){return B(unCStr("\\n"));}),_87=new T(function(){return B(unCStr("\\t"));}),_88=new T(function(){return B(unCStr("\\b"));}),_89=function(_8a,_8b){if(_8a<=127){var _8c=E(_8a);switch(_8c){case 92:return new F(function(){return _y(_81,_8b);});break;case 127:return new F(function(){return _y(_7Z,_8b);});break;default:if(_8c<32){var _8d=E(_8c);switch(_8d){case 7:return new F(function(){return _y(_80,_8b);});break;case 8:return new F(function(){return _y(_88,_8b);});break;case 9:return new F(function(){return _y(_87,_8b);});break;case 10:return new F(function(){return _y(_86,_8b);});break;case 11:return new F(function(){return _y(_85,_8b);});break;case 12:return new F(function(){return _y(_84,_8b);});break;case 13:return new F(function(){return _y(_83,_8b);});break;case 14:return new F(function(){return _y(_82,new T(function(){var _8e=E(_8b);if(!_8e._){return __Z;}else{if(E(_8e.a)==72){return B(unAppCStr("\\&",_8e));}else{return E(_8e);}}},1));});break;default:return new F(function(){return _y(new T2(1,_7Y,new T(function(){return B(_6R(_7X,_8d));})),_8b);});}}else{return new T2(1,_8c,_8b);}}}else{var _8f=new T(function(){var _8g=jsShowI(_8a);return B(_y(fromJSStr(_8g),new T(function(){var _8h=E(_8b);if(!_8h._){return __Z;}else{var _8i=E(_8h.a);if(_8i<48){return E(_8h);}else{if(_8i>57){return E(_8h);}else{return B(unAppCStr("\\&",_8h));}}}},1)));});return new T2(1,_7Y,_8f);}},_8j=new T(function(){return B(unCStr("\\\""));}),_8k=function(_8l,_8m){var _8n=E(_8l);if(!_8n._){return E(_8m);}else{var _8o=_8n.b,_8p=E(_8n.a);if(_8p==34){return new F(function(){return _y(_8j,new T(function(){return B(_8k(_8o,_8m));},1));});}else{return new F(function(){return _89(_8p,new T(function(){return B(_8k(_8o,_8m));}));});}}},_8q=function(_8r){return new T2(1,_6D,new T(function(){return B(_8k(_8r,_6E));}));},_8s=function(_8t,_8u){if(_8t<=_8u){var _8v=function(_8w){return new T2(1,_8w,new T(function(){if(_8w!=_8u){return B(_8v(_8w+1|0));}else{return __Z;}}));};return new F(function(){return _8v(_8t);});}else{return __Z;}},_8x=function(_8y){return new F(function(){return _8s(E(_8y),2147483647);});},_8z=function(_8A,_8B,_8C){if(_8C<=_8B){var _8D=new T(function(){var _8E=_8B-_8A|0,_8F=function(_8G){return (_8G>=(_8C-_8E|0))?new T2(1,_8G,new T(function(){return B(_8F(_8G+_8E|0));})):new T2(1,_8G,_10);};return B(_8F(_8B));});return new T2(1,_8A,_8D);}else{return (_8C<=_8A)?new T2(1,_8A,_10):__Z;}},_8H=function(_8I,_8J,_8K){if(_8K>=_8J){var _8L=new T(function(){var _8M=_8J-_8I|0,_8N=function(_8O){return (_8O<=(_8K-_8M|0))?new T2(1,_8O,new T(function(){return B(_8N(_8O+_8M|0));})):new T2(1,_8O,_10);};return B(_8N(_8J));});return new T2(1,_8I,_8L);}else{return (_8K>=_8I)?new T2(1,_8I,_10):__Z;}},_8P=function(_8Q,_8R){if(_8R<_8Q){return new F(function(){return _8z(_8Q,_8R, -2147483648);});}else{return new F(function(){return _8H(_8Q,_8R,2147483647);});}},_8S=function(_8T,_8U){return new F(function(){return _8P(E(_8T),E(_8U));});},_8V=function(_8W,_8X,_8Y){if(_8X<_8W){return new F(function(){return _8z(_8W,_8X,_8Y);});}else{return new F(function(){return _8H(_8W,_8X,_8Y);});}},_8Z=function(_90,_91,_92){return new F(function(){return _8V(E(_90),E(_91),E(_92));});},_93=function(_94,_95){return new F(function(){return _8s(E(_94),E(_95));});},_96=function(_97){return E(_97);},_98=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_99=new T(function(){return B(err(_98));}),_9a=function(_9b){var _9c=E(_9b);return (_9c==( -2147483648))?E(_99):_9c-1|0;},_9d=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9e=new T(function(){return B(err(_9d));}),_9f=function(_9g){var _9h=E(_9g);return (_9h==2147483647)?E(_9e):_9h+1|0;},_9i={_:0,a:_9f,b:_9a,c:_96,d:_96,e:_8x,f:_8S,g:_93,h:_8Z},_9j=function(_9k,_9l){if(_9k<=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{if(_9l>=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{return quot(_9k-1|0,_9l)-1|0;}}},_9m=new T(function(){return B(unCStr("base"));}),_9n=new T(function(){return B(unCStr("GHC.Exception"));}),_9o=new T(function(){return B(unCStr("ArithException"));}),_9p=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9m,_9n,_9o),_9q=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9p,_10,_10),_9r=function(_9s){return E(_9q);},_9t=function(_9u){var _9v=E(_9u);return new F(function(){return _1s(B(_1q(_9v.a)),_9r,_9v.b);});},_9w=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9x=new T(function(){return B(unCStr("denormal"));}),_9y=new T(function(){return B(unCStr("divide by zero"));}),_9z=new T(function(){return B(unCStr("loss of precision"));}),_9A=new T(function(){return B(unCStr("arithmetic underflow"));}),_9B=new T(function(){return B(unCStr("arithmetic overflow"));}),_9C=function(_9D,_9E){switch(E(_9D)){case 0:return new F(function(){return _y(_9B,_9E);});break;case 1:return new F(function(){return _y(_9A,_9E);});break;case 2:return new F(function(){return _y(_9z,_9E);});break;case 3:return new F(function(){return _y(_9y,_9E);});break;case 4:return new F(function(){return _y(_9x,_9E);});break;default:return new F(function(){return _y(_9w,_9E);});}},_9F=function(_9G){return new F(function(){return _9C(_9G,_10);});},_9H=function(_9I,_9J,_9K){return new F(function(){return _9C(_9J,_9K);});},_9L=function(_9M,_9N){return new F(function(){return _2D(_9C,_9M,_9N);});},_9O=new T3(0,_9H,_9F,_9L),_9P=new T(function(){return new T5(0,_9r,_9O,_9Q,_9t,_9F);}),_9Q=function(_9R){return new T2(0,_9P,_9R);},_9S=3,_9T=new T(function(){return B(_9Q(_9S));}),_9U=new T(function(){return die(_9T);}),_9V=0,_9W=new T(function(){return B(_9Q(_9V));}),_9X=new T(function(){return die(_9W);}),_9Y=function(_9Z,_a0){var _a1=E(_a0);switch(_a1){case  -1:var _a2=E(_9Z);if(_a2==( -2147483648)){return E(_9X);}else{return new F(function(){return _9j(_a2, -1);});}break;case 0:return E(_9U);default:return new F(function(){return _9j(_9Z,_a1);});}},_a3=function(_a4,_a5){return new F(function(){return _9Y(E(_a4),E(_a5));});},_a6=0,_a7=new T2(0,_9X,_a6),_a8=function(_a9,_aa){var _ab=E(_a9),_ac=E(_aa);switch(_ac){case  -1:var _ad=E(_ab);if(_ad==( -2147483648)){return E(_a7);}else{if(_ad<=0){if(_ad>=0){var _ae=quotRemI(_ad, -1);return new T2(0,_ae.a,_ae.b);}else{var _af=quotRemI(_ad, -1);return new T2(0,_af.a,_af.b);}}else{var _ag=quotRemI(_ad-1|0, -1);return new T2(0,_ag.a-1|0,(_ag.b+( -1)|0)+1|0);}}break;case 0:return E(_9U);default:if(_ab<=0){if(_ab>=0){var _ah=quotRemI(_ab,_ac);return new T2(0,_ah.a,_ah.b);}else{if(_ac<=0){var _ai=quotRemI(_ab,_ac);return new T2(0,_ai.a,_ai.b);}else{var _aj=quotRemI(_ab+1|0,_ac);return new T2(0,_aj.a-1|0,(_aj.b+_ac|0)-1|0);}}}else{if(_ac>=0){if(_ab>=0){var _ak=quotRemI(_ab,_ac);return new T2(0,_ak.a,_ak.b);}else{if(_ac<=0){var _al=quotRemI(_ab,_ac);return new T2(0,_al.a,_al.b);}else{var _am=quotRemI(_ab+1|0,_ac);return new T2(0,_am.a-1|0,(_am.b+_ac|0)-1|0);}}}else{var _an=quotRemI(_ab-1|0,_ac);return new T2(0,_an.a-1|0,(_an.b+_ac|0)+1|0);}}}},_ao=function(_ap,_aq){var _ar=_ap%_aq;if(_ap<=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _as=E(_ar);return (_as==0)?0:_as+_aq|0;}}}else{if(_aq>=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _at=E(_ar);return (_at==0)?0:_at+_aq|0;}}}else{var _au=E(_ar);return (_au==0)?0:_au+_aq|0;}}},_av=function(_aw,_ax){var _ay=E(_ax);switch(_ay){case  -1:return E(_a6);case 0:return E(_9U);default:return new F(function(){return _ao(E(_aw),_ay);});}},_az=function(_aA,_aB){var _aC=E(_aA),_aD=E(_aB);switch(_aD){case  -1:var _aE=E(_aC);if(_aE==( -2147483648)){return E(_9X);}else{return new F(function(){return quot(_aE, -1);});}break;case 0:return E(_9U);default:return new F(function(){return quot(_aC,_aD);});}},_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=E(_aH);switch(_aJ){case  -1:var _aK=E(_aI);if(_aK==( -2147483648)){return E(_a7);}else{var _aL=quotRemI(_aK, -1);return new T2(0,_aL.a,_aL.b);}break;case 0:return E(_9U);default:var _aM=quotRemI(_aI,_aJ);return new T2(0,_aM.a,_aM.b);}},_aN=function(_aO,_aP){var _aQ=E(_aP);switch(_aQ){case  -1:return E(_a6);case 0:return E(_9U);default:return E(_aO)%_aQ;}},_aR=function(_aS){return new T1(0,_aS);},_aT=function(_aU){return new F(function(){return _aR(E(_aU));});},_aV=new T1(0,1),_aW=function(_aX){return new T2(0,E(B(_aR(E(_aX)))),E(_aV));},_aY=function(_aZ,_b0){return imul(E(_aZ),E(_b0))|0;},_b1=function(_b2,_b3){return E(_b2)+E(_b3)|0;},_b4=function(_b5,_b6){return E(_b5)-E(_b6)|0;},_b7=function(_b8){var _b9=E(_b8);return (_b9<0)? -_b9:E(_b9);},_ba=function(_bb){var _bc=E(_bb);if(!_bc._){return E(_bc.a);}else{return new F(function(){return I_toInt(_bc.a);});}},_bd=function(_be){return new F(function(){return _ba(_be);});},_bf=function(_bg){return  -E(_bg);},_bh= -1,_bi=0,_bj=1,_bk=function(_bl){var _bm=E(_bl);return (_bm>=0)?(E(_bm)==0)?E(_bi):E(_bj):E(_bh);},_bn={_:0,a:_b1,b:_b4,c:_aY,d:_bf,e:_b7,f:_bk,g:_bd},_bo=function(_bp,_bq){var _br=E(_bp),_bs=E(_bq);return (_br>_bs)?E(_br):E(_bs);},_bt=function(_bu,_bv){var _bw=E(_bu),_bx=E(_bv);return (_bw>_bx)?E(_bx):E(_bw);},_by=function(_bz,_bA){return (_bz>=_bA)?(_bz!=_bA)?2:1:0;},_bB=function(_bC,_bD){return new F(function(){return _by(E(_bC),E(_bD));});},_bE=function(_bF,_bG){return E(_bF)>=E(_bG);},_bH=function(_bI,_bJ){return E(_bI)>E(_bJ);},_bK=function(_bL,_bM){return E(_bL)<=E(_bM);},_bN=function(_bO,_bP){return E(_bO)<E(_bP);},_bQ={_:0,a:_3M,b:_bB,c:_bN,d:_bK,e:_bH,f:_bE,g:_bo,h:_bt},_bR=new T3(0,_bn,_bQ,_aW),_bS={_:0,a:_bR,b:_9i,c:_az,d:_aN,e:_a3,f:_av,g:_aF,h:_a8,i:_aT},_bT=function(_bU){var _bV=E(_bU);return new F(function(){return Math.log(_bV+(_bV+1)*Math.sqrt((_bV-1)/(_bV+1)));});},_bW=function(_bX){var _bY=E(_bX);return new F(function(){return Math.log(_bY+Math.sqrt(1+_bY*_bY));});},_bZ=function(_c0){var _c1=E(_c0);return 0.5*Math.log((1+_c1)/(1-_c1));},_c2=function(_c3,_c4){return Math.log(E(_c4))/Math.log(E(_c3));},_c5=3.141592653589793,_c6=new T1(0,1),_c7=function(_c8,_c9){var _ca=E(_c8);if(!_ca._){var _cb=_ca.a,_cc=E(_c9);if(!_cc._){var _cd=_cc.a;return (_cb!=_cd)?(_cb>_cd)?2:0:1;}else{var _ce=I_compareInt(_cc.a,_cb);return (_ce<=0)?(_ce>=0)?1:2:0;}}else{var _cf=_ca.a,_cg=E(_c9);if(!_cg._){var _ch=I_compareInt(_cf,_cg.a);return (_ch>=0)?(_ch<=0)?1:2:0;}else{var _ci=I_compare(_cf,_cg.a);return (_ci>=0)?(_ci<=0)?1:2:0;}}},_cj=function(_ck,_cl){var _cm=E(_ck);return (_cm._==0)?_cm.a*Math.pow(2,_cl):I_toNumber(_cm.a)*Math.pow(2,_cl);},_cn=function(_co,_cp){var _cq=E(_co);if(!_cq._){var _cr=_cq.a,_cs=E(_cp);return (_cs._==0)?_cr==_cs.a:(I_compareInt(_cs.a,_cr)==0)?true:false;}else{var _ct=_cq.a,_cu=E(_cp);return (_cu._==0)?(I_compareInt(_ct,_cu.a)==0)?true:false:(I_compare(_ct,_cu.a)==0)?true:false;}},_cv=function(_cw,_cx){while(1){var _cy=E(_cw);if(!_cy._){var _cz=_cy.a,_cA=E(_cx);if(!_cA._){var _cB=_cA.a,_cC=addC(_cz,_cB);if(!E(_cC.b)){return new T1(0,_cC.a);}else{_cw=new T1(1,I_fromInt(_cz));_cx=new T1(1,I_fromInt(_cB));continue;}}else{_cw=new T1(1,I_fromInt(_cz));_cx=_cA;continue;}}else{var _cD=E(_cx);if(!_cD._){_cw=_cy;_cx=new T1(1,I_fromInt(_cD.a));continue;}else{return new T1(1,I_add(_cy.a,_cD.a));}}}},_cE=function(_cF,_cG){while(1){var _cH=E(_cF);if(!_cH._){var _cI=E(_cH.a);if(_cI==( -2147483648)){_cF=new T1(1,I_fromInt( -2147483648));continue;}else{var _cJ=E(_cG);if(!_cJ._){var _cK=_cJ.a;return new T2(0,new T1(0,quot(_cI,_cK)),new T1(0,_cI%_cK));}else{_cF=new T1(1,I_fromInt(_cI));_cG=_cJ;continue;}}}else{var _cL=E(_cG);if(!_cL._){_cF=_cH;_cG=new T1(1,I_fromInt(_cL.a));continue;}else{var _cM=I_quotRem(_cH.a,_cL.a);return new T2(0,new T1(1,_cM.a),new T1(1,_cM.b));}}}},_cN=new T1(0,0),_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR._){_cP=new T1(1,I_fromInt(_cR.a));continue;}else{return new T1(1,I_shiftLeft(_cR.a,_cQ));}}},_cS=function(_cT,_cU,_cV){if(!B(_cn(_cV,_cN))){var _cW=B(_cE(_cU,_cV)),_cX=_cW.a;switch(B(_c7(B(_cO(_cW.b,1)),_cV))){case 0:return new F(function(){return _cj(_cX,_cT);});break;case 1:if(!(B(_ba(_cX))&1)){return new F(function(){return _cj(_cX,_cT);});}else{return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}break;default:return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}}else{return E(_9U);}},_cY=function(_cZ,_d0){var _d1=E(_cZ);if(!_d1._){var _d2=_d1.a,_d3=E(_d0);return (_d3._==0)?_d2>_d3.a:I_compareInt(_d3.a,_d2)<0;}else{var _d4=_d1.a,_d5=E(_d0);return (_d5._==0)?I_compareInt(_d4,_d5.a)>0:I_compare(_d4,_d5.a)>0;}},_d6=new T1(0,1),_d7=function(_d8,_d9){var _da=E(_d8);if(!_da._){var _db=_da.a,_dc=E(_d9);return (_dc._==0)?_db<_dc.a:I_compareInt(_dc.a,_db)>0;}else{var _dd=_da.a,_de=E(_d9);return (_de._==0)?I_compareInt(_dd,_de.a)<0:I_compare(_dd,_de.a)<0;}},_df=new T(function(){return B(unCStr("base"));}),_dg=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dh=new T(function(){return B(unCStr("PatternMatchFail"));}),_di=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_df,_dg,_dh),_dj=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_di,_10,_10),_dk=function(_dl){return E(_dj);},_dm=function(_dn){var _do=E(_dn);return new F(function(){return _1s(B(_1q(_do.a)),_dk,_do.b);});},_dp=function(_dq){return E(E(_dq).a);},_dr=function(_ds){return new T2(0,_dt,_ds);},_du=function(_dv,_dw){return new F(function(){return _y(E(_dv).a,_dw);});},_dx=function(_dy,_dz){return new F(function(){return _2D(_du,_dy,_dz);});},_dA=function(_dB,_dC,_dD){return new F(function(){return _y(E(_dC).a,_dD);});},_dE=new T3(0,_dA,_dp,_dx),_dt=new T(function(){return new T5(0,_dk,_dE,_dr,_dm,_dp);}),_dF=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dG=function(_dH,_dI){return new F(function(){return die(new T(function(){return B(A2(_5F,_dI,_dH));}));});},_dJ=function(_dK,_9R){return new F(function(){return _dG(_dK,_9R);});},_dL=function(_dM,_dN){var _dO=E(_dN);if(!_dO._){return new T2(0,_10,_10);}else{var _dP=_dO.a;if(!B(A1(_dM,_dP))){return new T2(0,_10,_dO);}else{var _dQ=new T(function(){var _dR=B(_dL(_dM,_dO.b));return new T2(0,_dR.a,_dR.b);});return new T2(0,new T2(1,_dP,new T(function(){return E(E(_dQ).a);})),new T(function(){return E(E(_dQ).b);}));}}},_dS=32,_dT=new T(function(){return B(unCStr("\n"));}),_dU=function(_dV){return (E(_dV)==124)?false:true;},_dW=function(_dX,_dY){var _dZ=B(_dL(_dU,B(unCStr(_dX)))),_e0=_dZ.a,_e1=function(_e2,_e3){var _e4=new T(function(){var _e5=new T(function(){return B(_y(_dY,new T(function(){return B(_y(_e3,_dT));},1)));});return B(unAppCStr(": ",_e5));},1);return new F(function(){return _y(_e2,_e4);});},_e6=E(_dZ.b);if(!_e6._){return new F(function(){return _e1(_e0,_10);});}else{if(E(_e6.a)==124){return new F(function(){return _e1(_e0,new T2(1,_dS,_e6.b));});}else{return new F(function(){return _e1(_e0,_10);});}}},_e7=function(_e8){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_e8,_dF));})),_dt);});},_e9=function(_ea){var _eb=function(_ec,_ed){while(1){if(!B(_d7(_ec,_ea))){if(!B(_cY(_ec,_ea))){if(!B(_cn(_ec,_ea))){return new F(function(){return _e7("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ed);}}else{return _ed-1|0;}}else{var _ee=B(_cO(_ec,1)),_ef=_ed+1|0;_ec=_ee;_ed=_ef;continue;}}};return new F(function(){return _eb(_d6,0);});},_eg=function(_eh){var _ei=E(_eh);if(!_ei._){var _ej=_ei.a>>>0;if(!_ej){return  -1;}else{var _ek=function(_el,_em){while(1){if(_el>=_ej){if(_el<=_ej){if(_el!=_ej){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_em);}}else{return _em-1|0;}}else{var _en=imul(_el,2)>>>0,_eo=_em+1|0;_el=_en;_em=_eo;continue;}}};return new F(function(){return _ek(1,0);});}}else{return new F(function(){return _e9(_ei);});}},_ep=function(_eq){var _er=E(_eq);if(!_er._){var _es=_er.a>>>0;if(!_es){return new T2(0, -1,0);}else{var _et=function(_eu,_ev){while(1){if(_eu>=_es){if(_eu<=_es){if(_eu!=_es){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ev);}}else{return _ev-1|0;}}else{var _ew=imul(_eu,2)>>>0,_ex=_ev+1|0;_eu=_ew;_ev=_ex;continue;}}};return new T2(0,B(_et(1,0)),(_es&_es-1>>>0)>>>0&4294967295);}}else{var _ey=_er.a;return new T2(0,B(_eg(_er)),I_compareInt(I_and(_ey,I_sub(_ey,I_fromInt(1))),0));}},_ez=function(_eA,_eB){var _eC=E(_eA);if(!_eC._){var _eD=_eC.a,_eE=E(_eB);return (_eE._==0)?_eD<=_eE.a:I_compareInt(_eE.a,_eD)>=0;}else{var _eF=_eC.a,_eG=E(_eB);return (_eG._==0)?I_compareInt(_eF,_eG.a)<=0:I_compare(_eF,_eG.a)<=0;}},_eH=function(_eI,_eJ){while(1){var _eK=E(_eI);if(!_eK._){var _eL=_eK.a,_eM=E(_eJ);if(!_eM._){return new T1(0,(_eL>>>0&_eM.a>>>0)>>>0&4294967295);}else{_eI=new T1(1,I_fromInt(_eL));_eJ=_eM;continue;}}else{var _eN=E(_eJ);if(!_eN._){_eI=_eK;_eJ=new T1(1,I_fromInt(_eN.a));continue;}else{return new T1(1,I_and(_eK.a,_eN.a));}}}},_eO=function(_eP,_eQ){while(1){var _eR=E(_eP);if(!_eR._){var _eS=_eR.a,_eT=E(_eQ);if(!_eT._){var _eU=_eT.a,_eV=subC(_eS,_eU);if(!E(_eV.b)){return new T1(0,_eV.a);}else{_eP=new T1(1,I_fromInt(_eS));_eQ=new T1(1,I_fromInt(_eU));continue;}}else{_eP=new T1(1,I_fromInt(_eS));_eQ=_eT;continue;}}else{var _eW=E(_eQ);if(!_eW._){_eP=_eR;_eQ=new T1(1,I_fromInt(_eW.a));continue;}else{return new T1(1,I_sub(_eR.a,_eW.a));}}}},_eX=new T1(0,2),_eY=function(_eZ,_f0){var _f1=E(_eZ);if(!_f1._){var _f2=(_f1.a>>>0&(2<<_f0>>>0)-1>>>0)>>>0,_f3=1<<_f0>>>0;return (_f3<=_f2)?(_f3>=_f2)?1:2:0;}else{var _f4=B(_eH(_f1,B(_eO(B(_cO(_eX,_f0)),_d6)))),_f5=B(_cO(_d6,_f0));return (!B(_cY(_f5,_f4)))?(!B(_d7(_f5,_f4)))?1:2:0;}},_f6=function(_f7,_f8){while(1){var _f9=E(_f7);if(!_f9._){_f7=new T1(1,I_fromInt(_f9.a));continue;}else{return new T1(1,I_shiftRight(_f9.a,_f8));}}},_fa=function(_fb,_fc,_fd,_fe){var _ff=B(_ep(_fe)),_fg=_ff.a;if(!E(_ff.b)){var _fh=B(_eg(_fd));if(_fh<((_fg+_fb|0)-1|0)){var _fi=_fg+(_fb-_fc|0)|0;if(_fi>0){if(_fi>_fh){if(_fi<=(_fh+1|0)){if(!E(B(_ep(_fd)).b)){return 0;}else{return new F(function(){return _cj(_c6,_fb-_fc|0);});}}else{return 0;}}else{var _fj=B(_f6(_fd,_fi));switch(B(_eY(_fd,_fi-1|0))){case 0:return new F(function(){return _cj(_fj,_fb-_fc|0);});break;case 1:if(!(B(_ba(_fj))&1)){return new F(function(){return _cj(_fj,_fb-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}break;default:return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}}}else{return new F(function(){return _cj(_fd,(_fb-_fc|0)-_fi|0);});}}else{if(_fh>=_fc){var _fk=B(_f6(_fd,(_fh+1|0)-_fc|0));switch(B(_eY(_fd,_fh-_fc|0))){case 0:return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});break;case 2:return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});break;default:if(!(B(_ba(_fk))&1)){return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});}}}else{return new F(function(){return _cj(_fd, -_fg);});}}}else{var _fl=B(_eg(_fd))-_fg|0,_fm=function(_fn){var _fo=function(_fp,_fq){if(!B(_ez(B(_cO(_fq,_fc)),_fp))){return new F(function(){return _cS(_fn-_fc|0,_fp,_fq);});}else{return new F(function(){return _cS((_fn-_fc|0)+1|0,_fp,B(_cO(_fq,1)));});}};if(_fn>=_fc){if(_fn!=_fc){return new F(function(){return _fo(_fd,new T(function(){return B(_cO(_fe,_fn-_fc|0));}));});}else{return new F(function(){return _fo(_fd,_fe);});}}else{return new F(function(){return _fo(new T(function(){return B(_cO(_fd,_fc-_fn|0));}),_fe);});}};if(_fb>_fl){return new F(function(){return _fm(_fb);});}else{return new F(function(){return _fm(_fl);});}}},_fr=new T1(0,2147483647),_fs=new T(function(){return B(_cv(_fr,_d6));}),_ft=function(_fu){var _fv=E(_fu);if(!_fv._){var _fw=E(_fv.a);return (_fw==( -2147483648))?E(_fs):new T1(0, -_fw);}else{return new T1(1,I_negate(_fv.a));}},_fx=new T(function(){return 0/0;}),_fy=new T(function(){return  -1/0;}),_fz=new T(function(){return 1/0;}),_fA=0,_fB=function(_fC,_fD){if(!B(_cn(_fD,_cN))){if(!B(_cn(_fC,_cN))){if(!B(_d7(_fC,_cN))){return new F(function(){return _fa( -1021,53,_fC,_fD);});}else{return  -B(_fa( -1021,53,B(_ft(_fC)),_fD));}}else{return E(_fA);}}else{return (!B(_cn(_fC,_cN)))?(!B(_d7(_fC,_cN)))?E(_fz):E(_fy):E(_fx);}},_fE=function(_fF){var _fG=E(_fF);return new F(function(){return _fB(_fG.a,_fG.b);});},_fH=function(_fI){return 1/E(_fI);},_fJ=function(_fK){var _fL=E(_fK);return (_fL!=0)?(_fL<=0)? -_fL:E(_fL):E(_fA);},_fM=function(_fN){var _fO=E(_fN);if(!_fO._){return _fO.a;}else{return new F(function(){return I_toNumber(_fO.a);});}},_fP=function(_fQ){return new F(function(){return _fM(_fQ);});},_fR=1,_fS= -1,_fT=function(_fU){var _fV=E(_fU);return (_fV<=0)?(_fV>=0)?E(_fV):E(_fS):E(_fR);},_fW=function(_fX,_fY){return E(_fX)-E(_fY);},_fZ=function(_g0){return  -E(_g0);},_g1=function(_g2,_g3){return E(_g2)+E(_g3);},_g4=function(_g5,_g6){return E(_g5)*E(_g6);},_g7={_:0,a:_g1,b:_fW,c:_g4,d:_fZ,e:_fJ,f:_fT,g:_fP},_g8=function(_g9,_ga){return E(_g9)/E(_ga);},_gb=new T4(0,_g7,_g8,_fH,_fE),_gc=function(_gd){return new F(function(){return Math.acos(E(_gd));});},_ge=function(_gf){return new F(function(){return Math.asin(E(_gf));});},_gg=function(_gh){return new F(function(){return Math.atan(E(_gh));});},_gi=function(_gj){return new F(function(){return Math.cos(E(_gj));});},_gk=function(_gl){return new F(function(){return cosh(E(_gl));});},_gm=function(_gn){return new F(function(){return Math.exp(E(_gn));});},_go=function(_gp){return new F(function(){return Math.log(E(_gp));});},_gq=function(_gr,_gs){return new F(function(){return Math.pow(E(_gr),E(_gs));});},_gt=function(_gu){return new F(function(){return Math.sin(E(_gu));});},_gv=function(_gw){return new F(function(){return sinh(E(_gw));});},_gx=function(_gy){return new F(function(){return Math.sqrt(E(_gy));});},_gz=function(_gA){return new F(function(){return Math.tan(E(_gA));});},_gB=function(_gC){return new F(function(){return tanh(E(_gC));});},_gD={_:0,a:_gb,b:_c5,c:_gm,d:_go,e:_gx,f:_gq,g:_c2,h:_gt,i:_gi,j:_gz,k:_ge,l:_gc,m:_gg,n:_gv,o:_gk,p:_gB,q:_bW,r:_bT,s:_bZ},_gE=0,_gF=function(_){return _gE;},_gG=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gH=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gI=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gJ=function(_gK,_gL,_gM,_){var _gN=__app1(E(_gH),_gM),_gO=__app2(E(_gI),_gM,E(_gK)),_gP=B(A2(_gL,_gM,_)),_gQ=__app1(E(_gG),_gM);return new F(function(){return _gF(_);});},_gR=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gS=function(_gT,_gU,_gV,_gW,_){var _gX=__app1(E(_gH),_gW),_gY=__app3(E(_gR),_gW,E(_gT),E(_gU)),_gZ=B(A2(_gV,_gW,_)),_h0=__app1(E(_gG),_gW);return new F(function(){return _gF(_);});},_h1=function(_h2,_h3){return E(_h2)!=E(_h3);},_h4=function(_h5,_h6){return E(_h5)==E(_h6);},_h7=new T2(0,_h4,_h1),_h8=function(_h9){return E(E(_h9).a);},_ha=function(_hb){return E(E(_hb).a);},_hc=function(_hd){return E(E(_hd).b);},_he=function(_hf){return E(E(_hf).g);},_hg=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hh=0,_hi=3.3333333333333335,_hj=16.666666666666668,_hk=function(_hl){return E(E(_hl).b);},_hm=new T1(0,0),_hn=new T1(0,2),_ho=function(_hp){return E(E(_hp).i);},_hq=function(_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy){var _hz=new T(function(){var _hA=E(_hy);if(_hA<=31){return B(_4B(_h7,_hA,_hg));}else{if(_hA>=128){return B(_4B(_h7,_hA,_hg));}else{return true;}}}),_hB=new T(function(){if(E(_hu)==8){return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28+20;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20+8*(E(_hv)-1);}));}else{return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20;}));}}),_hC=new T(function(){var _hD=B(_h8(_hr));if(!E(_hz)){return B(A2(_he,B(_ha(_hD)),_hm));}else{return B(A3(_hc,_hD,new T(function(){return B(_hk(_hr));}),new T(function(){return B(A2(_he,B(_ha(_hD)),_hn));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hB).a);}),new T(function(){return E(E(_hB).b);})),new T2(0,new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hi);}}),new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hj);}})),_hC);},_hE=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hF=function(_hG,_hH,_hI){var _hJ=new T(function(){return toJSStr(E(_hI));});return function(_hK,_){var _hL=__app4(E(_hE),E(_hK),E(_hJ),E(_hG),E(_hH));return new F(function(){return _gF(_);});};},_hM=0,_hN=",",_hO="rgba(",_hP=new T(function(){return toJSStr(_10);}),_hQ="rgb(",_hR=")",_hS=new T2(1,_hR,_10),_hT=function(_hU){var _hV=E(_hU);if(!_hV._){var _hW=jsCat(new T2(1,_hQ,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),_hS)))))),E(_hP));return E(_hW);}else{var _hX=jsCat(new T2(1,_hO,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.d);}),_hS)))))))),E(_hP));return E(_hX);}},_hY="strokeStyle",_hZ="fillStyle",_i0=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i1=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i2=function(_i3,_i4){var _i5=new T(function(){return B(_hT(_i3));});return function(_i6,_){var _i7=E(_i6),_i8=E(_hZ),_i9=E(_i0),_ia=__app2(_i9,_i7,_i8),_ib=E(_hY),_ic=__app2(_i9,_i7,_ib),_id=E(_i5),_ie=E(_i1),_if=__app3(_ie,_i7,_i8,_id),_ig=__app3(_ie,_i7,_ib,_id),_ih=B(A2(_i4,_i7,_)),_ii=String(_ia),_ij=__app3(_ie,_i7,_i8,_ii),_ik=String(_ic),_il=__app3(_ie,_i7,_ib,_ik);return new F(function(){return _gF(_);});};},_im="font",_in=function(_io,_ip){var _iq=new T(function(){return toJSStr(E(_io));});return function(_ir,_){var _is=E(_ir),_it=E(_im),_iu=__app2(E(_i0),_is,_it),_iv=E(_i1),_iw=__app3(_iv,_is,_it,E(_iq)),_ix=B(A2(_ip,_is,_)),_iy=String(_iu),_iz=__app3(_iv,_is,_it,_iy);return new F(function(){return _gF(_);});};},_iA=new T(function(){return B(unCStr("px IPAGothic"));}),_iB=function(_iC,_iD,_iE,_iF,_iG,_iH,_iI,_){var _iJ=new T(function(){var _iK=new T(function(){var _iL=B(_hq(_gD,_bS,_bS,_iE,_iF,_iG,_iH,_iI)),_iM=E(_iL.a),_iN=E(_iL.b);return new T5(0,_iM.a,_iM.b,_iN.a,_iN.b,_iL.c);}),_iO=new T(function(){var _iP=E(_iK);return E(_iP.a)+E(_iP.c);}),_iQ=new T(function(){var _iR=E(_iK);return E(_iR.b)-E(_iR.d);}),_iS=new T(function(){return E(E(_iK).e);}),_iT=new T(function(){return B(_hF(_hM,_hM,new T2(1,_iI,_10)));}),_iU=function(_iV,_){return new F(function(){return _gJ(_iS,_iT,E(_iV),_);});};return B(_in(new T(function(){return B(_y(B(_I(0,E(_iE),_10)),_iA));},1),function(_iW,_){return new F(function(){return _gS(_iO,_iQ,_iU,E(_iW),_);});}));});return new F(function(){return A(_i2,[_iD,_iJ,_iC,_]);});},_iX=new T3(0,153,255,255),_iY=new T2(1,_iX,_10),_iZ=new T3(0,255,153,204),_j0=new T2(1,_iZ,_iY),_j1=new T3(0,255,204,153),_j2=new T2(1,_j1,_j0),_j3=new T3(0,200,255,200),_j4=new T2(1,_j3,_j2),_j5=20,_j6=64,_j7=1,_j8=2,_j9=8,_ja=function(_jb,_jc,_jd,_je,_jf,_jg,_jh,_){while(1){var _ji=B((function(_jj,_jk,_jl,_jm,_jn,_jo,_jp,_){var _jq=E(_jp);if(!_jq._){return _gE;}else{var _jr=_jq.b,_js=E(_jq.a),_jt=E(_js);switch(_jt){case 10:var _ju=_jj,_jv=_jk,_jw=_jm,_jx=_jm;_jb=_ju;_jc=_jv;_jd=0;_je=_jw;_jf=new T(function(){return E(_jn)-1|0;});_jg=_jx;_jh=_jr;return __continue;case 123:return new F(function(){return _jy(_jj,_jk,_jl,_jm,_jn,_jo,_jr,_);});break;case 65306:var _jz=new T(function(){return B(_6R(_j4,_jl));}),_jA=function(_jB,_jC,_jD,_jE,_jF,_jG,_){while(1){var _jH=B((function(_jI,_jJ,_jK,_jL,_jM,_jN,_){var _jO=E(_jN);if(!_jO._){return _gE;}else{var _jP=_jO.b,_jQ=E(_jO.a);if(E(_jQ)==65306){var _jR=new T(function(){var _jS=E(_jM);if((_jS+1)*20<=E(_jk)-10){return new T2(0,_jL,_jS+1|0);}else{return new T2(0,new T(function(){return E(_jL)-1|0;}),_jJ);}});return new F(function(){return _ja(_jI,_jk,_jl,_jJ,new T(function(){return E(E(_jR).a);}),new T(function(){return E(E(_jR).b);}),_jP,_);});}else{var _jT=E(_jI),_jU=B(_iB(_jT.a,_jz,_j9,_jK,_jL,_jM,_jQ,_)),_jV=_jJ,_jW=_jK+1,_jX=_jL,_jY=_jM;_jB=_jT;_jC=_jV;_jD=_jW;_jE=_jX;_jF=_jY;_jG=_jP;return __continue;}}})(_jB,_jC,_jD,_jE,_jF,_jG,_));if(_jH!=__continue){return _jH;}}};return new F(function(){return _jA(_jj,_jm,0,new T(function(){if(E(_jm)!=E(_jo)){return E(_jn);}else{return E(_jn)+1|0;}}),new T(function(){var _jZ=E(_jo);if(E(_jm)!=_jZ){return _jZ-1|0;}else{var _k0=(E(_jk)-10)/20,_k1=_k0&4294967295;if(_k0>=_k1){return _k1;}else{return _k1-1|0;}}}),_jr,_);});break;default:var _k2=function(_k3,_k4){var _k5=new T(function(){switch(E(_jt)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _jl;}}),_k6=new T(function(){var _k7=E(_jo);if((_k7+1)*20<=E(_jk)-10){return new T2(0,_jn,_k7+1|0);}else{return new T2(0,new T(function(){return E(_jn)-1|0;}),_jm);}});if(E(_k3)==64){return new F(function(){return _k8(_jj,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}else{var _k9=E(_jj),_ka=B(_iB(_k9.a,new T(function(){return B(_6R(_j4,E(_k5)));},1),_j5,_hM,_jn,_jo,_k4,_));return new F(function(){return _k8(_k9,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}},_kb=E(_jt);switch(_kb){case 42:return new F(function(){return _k2(64,_j6);});break;case 12289:return new F(function(){return _k2(64,_j6);});break;case 12290:return new F(function(){return _k2(64,_j6);});break;default:return new F(function(){return _k2(_kb,_js);});}}}})(_jb,_jc,_jd,_je,_jf,_jg,_jh,_));if(_ji!=__continue){return _ji;}}},_k8=function(_kc,_kd,_ke,_kf,_kg,_kh,_ki,_){var _kj=E(_ki);if(!_kj._){return _gE;}else{var _kk=_kj.b,_kl=E(_kj.a),_km=E(_kl);switch(_km){case 10:return new F(function(){return _ja(_kc,_kd,0,_kf,new T(function(){return E(_kg)-1|0;}),_kf,_kk,_);});break;case 123:return new F(function(){return _jy(_kc,_kd,_ke,_kf,_kg,_kh,_kk,_);});break;case 65306:var _kn=new T(function(){return B(_6R(_j4,E(_ke)));}),_ko=function(_kp,_kq,_kr,_ks,_kt,_ku,_){while(1){var _kv=B((function(_kw,_kx,_ky,_kz,_kA,_kB,_){var _kC=E(_kB);if(!_kC._){return _gE;}else{var _kD=_kC.b,_kE=E(_kC.a);if(E(_kE)==65306){var _kF=new T(function(){var _kG=E(_kA);if((_kG+1)*20<=E(_kd)-10){return new T2(0,_kz,_kG+1|0);}else{return new T2(0,new T(function(){return E(_kz)-1|0;}),_kx);}});return new F(function(){return _k8(_kw,_kd,_ke,_kx,new T(function(){return E(E(_kF).a);}),new T(function(){return E(E(_kF).b);}),_kD,_);});}else{var _kH=E(_kw),_kI=B(_iB(_kH.a,_kn,_j9,_ky,_kz,_kA,_kE,_)),_kJ=_kx,_kK=_ky+1,_kL=_kz,_kM=_kA;_kp=_kH;_kq=_kJ;_kr=_kK;_ks=_kL;_kt=_kM;_ku=_kD;return __continue;}}})(_kp,_kq,_kr,_ks,_kt,_ku,_));if(_kv!=__continue){return _kv;}}};return new F(function(){return _ko(_kc,_kf,0,new T(function(){if(E(_kf)!=E(_kh)){return E(_kg);}else{return E(_kg)+1|0;}}),new T(function(){var _kN=E(_kh);if(E(_kf)!=_kN){return _kN-1|0;}else{var _kO=(E(_kd)-10)/20,_kP=_kO&4294967295;if(_kO>=_kP){return _kP;}else{return _kP-1|0;}}}),_kk,_);});break;default:var _kQ=function(_kR,_kS){var _kT=new T(function(){switch(E(_km)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return E(_ke);}}),_kU=new T(function(){var _kV=E(_kh);if((_kV+1)*20<=E(_kd)-10){return new T2(0,_kg,_kV+1|0);}else{return new T2(0,new T(function(){return E(_kg)-1|0;}),_kf);}});if(E(_kR)==64){return new F(function(){return _k8(_kc,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}else{var _kW=E(_kc),_kX=B(_iB(_kW.a,new T(function(){return B(_6R(_j4,E(_kT)));},1),_j5,_hM,_kg,_kh,_kS,_));return new F(function(){return _k8(_kW,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}},_kY=E(_km);switch(_kY){case 42:return new F(function(){return _kQ(64,_j6);});break;case 12289:return new F(function(){return _kQ(64,_j6);});break;case 12290:return new F(function(){return _kQ(64,_j6);});break;default:return new F(function(){return _kQ(_kY,_kl);});}}}},_jy=function(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_){while(1){var _l6=B((function(_l7,_l8,_l9,_la,_lb,_lc,_ld,_){var _le=E(_ld);if(!_le._){return _gE;}else{var _lf=_le.b;if(E(_le.a)==125){var _lg=new T(function(){var _lh=E(_lc);if((_lh+1)*20<=E(_l8)-10){return new T2(0,_lb,_lh+1|0);}else{return new T2(0,new T(function(){return E(_lb)-1|0;}),_la);}});return new F(function(){return _k8(_l7,_l8,_l9,_la,new T(function(){return E(E(_lg).a);}),new T(function(){return E(E(_lg).b);}),_lf,_);});}else{var _li=_l7,_lj=_l8,_lk=_l9,_ll=_la,_lm=_lb,_ln=_lc;_kZ=_li;_l0=_lj;_l1=_lk;_l2=_ll;_l3=_lm;_l4=_ln;_l5=_lf;return __continue;}}})(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_));if(_l6!=__continue){return _l6;}}},_lo=function(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_){while(1){var _lx=B((function(_ly,_lz,_lA,_lB,_lC,_lD,_lE,_lF,_){var _lG=E(_lF);if(!_lG._){return _gE;}else{var _lH=_lG.b,_lI=E(_lG.a),_lJ=E(_lI);switch(_lJ){case 10:var _lK=_ly,_lL=_lz,_lM=_lA,_lN=_lC,_lO=_lC;_lp=_lK;_lq=_lL;_lr=_lM;_ls=0;_lt=_lN;_lu=new T(function(){return E(_lD)-1|0;});_lv=_lO;_lw=_lH;return __continue;case 123:return new F(function(){return _jy(new T2(0,_ly,_lz),_lA,_lB,_lC,_lD,_lE,_lH,_);});break;case 65306:var _lP=new T(function(){return B(_6R(_j4,_lB));}),_lQ=function(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_){while(1){var _lY=B((function(_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_){var _m6=E(_m5);if(!_m6._){return _gE;}else{var _m7=_m6.b,_m8=E(_m6.a);if(E(_m8)==65306){var _m9=new T(function(){var _ma=E(_m4);if((_ma+1)*20<=E(_lA)-10){return new T2(0,_m3,_ma+1|0);}else{return new T2(0,new T(function(){return E(_m3)-1|0;}),_m1);}});return new F(function(){return _lo(_lZ,_m0,_lA,_lB,_m1,new T(function(){return E(E(_m9).a);}),new T(function(){return E(E(_m9).b);}),_m7,_);});}else{var _mb=B(_iB(_lZ,_lP,_j9,_m2,_m3,_m4,_m8,_)),_mc=_lZ,_md=_m0,_me=_m1,_mf=_m2+1,_mg=_m3,_mh=_m4;_lR=_mc;_lS=_md;_lT=_me;_lU=_mf;_lV=_mg;_lW=_mh;_lX=_m7;return __continue;}}})(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_));if(_lY!=__continue){return _lY;}}};return new F(function(){return _lQ(_ly,_lz,_lC,0,new T(function(){if(E(_lC)!=E(_lE)){return E(_lD);}else{return E(_lD)+1|0;}}),new T(function(){var _mi=E(_lE);if(E(_lC)!=_mi){return _mi-1|0;}else{var _mj=(E(_lA)-10)/20,_mk=_mj&4294967295;if(_mj>=_mk){return _mk;}else{return _mk-1|0;}}}),_lH,_);});break;default:var _ml=function(_mm,_mn){var _mo=new T(function(){switch(E(_lJ)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _lB;}}),_mp=new T(function(){var _mq=E(_lE);if((_mq+1)*20<=E(_lA)-10){return new T2(0,_lD,_mq+1|0);}else{return new T2(0,new T(function(){return E(_lD)-1|0;}),_lC);}});if(E(_mm)==64){return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}else{var _mr=B(_iB(_ly,new T(function(){return B(_6R(_j4,E(_mo)));},1),_j5,_hM,_lD,_lE,_mn,_));return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}},_ms=E(_lJ);switch(_ms){case 42:return new F(function(){return _ml(64,_j6);});break;case 12289:return new F(function(){return _ml(64,_j6);});break;case 12290:return new F(function(){return _ml(64,_j6);});break;default:return new F(function(){return _ml(_ms,_lI);});}}}})(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_));if(_lx!=__continue){return _lx;}}},_mt=function(_mu,_mv){while(1){var _mw=E(_mu);if(!_mw._){return E(_mv);}else{var _mx=_mv+1|0;_mu=_mw.b;_mv=_mx;continue;}}},_my=function(_mz){return E(E(_mz).a);},_mA=function(_mB,_mC){var _mD=E(_mC),_mE=new T(function(){var _mF=B(_ha(_mB)),_mG=B(_mA(_mB,B(A3(_my,_mF,_mD,new T(function(){return B(A2(_he,_mF,_aV));})))));return new T2(1,_mG.a,_mG.b);});return new T2(0,_mD,_mE);},_mH=new T(function(){var _mI=B(_mA(_gb,_hM));return new T2(1,_mI.a,_mI.b);}),_mJ=new T(function(){return B(unCStr("px Courier"));}),_mK=new T(function(){return B(_I(0,20,_10));}),_mL=new T(function(){return B(_y(_mK,_mJ));}),_mM=function(_mN,_){return _gE;},_mO=function(_mP,_mQ,_mR,_mS,_mT){var _mU=new T(function(){return E(_mR)*16;}),_mV=new T(function(){return E(_mS)*20;}),_mW=function(_mX,_mY){var _mZ=E(_mX);if(!_mZ._){return E(_mM);}else{var _n0=E(_mY);if(!_n0._){return E(_mM);}else{var _n1=new T(function(){return B(_mW(_mZ.b,_n0.b));}),_n2=new T(function(){var _n3=new T(function(){var _n4=new T(function(){return B(_hF(new T(function(){return E(_mU)+16*E(_n0.a);}),_mV,new T2(1,_mZ.a,_10)));});return B(_in(_mL,_n4));});return B(_i2(_mQ,_n3));});return function(_n5,_){var _n6=B(A2(_n2,_n5,_));return new F(function(){return A2(_n1,_n5,_);});};}}};return new F(function(){return A3(_mW,_mT,_mH,_mP);});},_n7=45,_n8=new T(function(){return B(unCStr("-"));}),_n9=new T2(1,_n7,_n8),_na=function(_nb){var _nc=E(_nb);return (_nc==1)?E(_n9):new T2(1,_n7,new T(function(){return B(_na(_nc-1|0));}));},_nd=new T(function(){return B(unCStr(": empty list"));}),_ne=function(_nf){return new F(function(){return err(B(_y(_6G,new T(function(){return B(_y(_nf,_nd));},1))));});},_ng=new T(function(){return B(unCStr("head"));}),_nh=new T(function(){return B(_ne(_ng));}),_ni=new T(function(){return eval("(function(e){e.width = e.width;})");}),_nj=new T(function(){return B(_hF(_hM,_hM,_10));}),_nk=32,_nl=new T(function(){return B(unCStr("|"));}),_nm=function(_nn){var _no=E(_nn);return (_no._==0)?E(_nl):new T2(1,new T(function(){var _np=E(_no.a);switch(E(_np.b)){case 7:return E(_nk);break;case 8:return E(_nk);break;default:return E(_np.a);}}),new T(function(){return B(_nm(_no.b));}));},_nq=function(_nr,_ns,_nt,_nu,_nv,_){var _nw=__app1(E(_ni),_ns),_nx=B(A2(_nj,_nr,_)),_ny=B(unAppCStr("-",new T(function(){var _nz=E(_nv);if(!_nz._){return E(_nh);}else{var _nA=B(_mt(_nz.a,0));if(0>=_nA){return E(_n8);}else{return B(_na(_nA));}}}))),_nB=B(A(_mO,[_nr,_j3,_nt,_nu,_ny,_])),_nC=function(_nD,_nE,_nF,_){while(1){var _nG=B((function(_nH,_nI,_nJ,_){var _nK=E(_nJ);if(!_nK._){return new F(function(){return A(_mO,[_nr,_j3,_nH,_nI,_ny,_]);});}else{var _nL=B(A(_mO,[_nr,_j3,_nH,_nI,B(unAppCStr("|",new T(function(){return B(_nm(_nK.a));}))),_])),_nM=_nH;_nD=_nM;_nE=new T(function(){return E(_nI)+1|0;});_nF=_nK.b;return __continue;}})(_nD,_nE,_nF,_));if(_nG!=__continue){return _nG;}}};return new F(function(){return _nC(_nt,new T(function(){return E(_nu)+1|0;}),_nv,_);});},_nN=new T(function(){return B(_6R(_j4,1));}),_nO=new T(function(){return B(_6R(_j4,2));}),_nP=2,_nQ=function(_nR,_nS,_nT,_nU,_){var _nV=__app1(E(_ni),_nS),_nW=B(A2(_nj,_nR,_)),_nX=E(_nU),_nY=E(_nX.b).a,_nZ=E(_nX.a),_o0=_nZ.a;if(!E(E(_nX.n).h)){return _gE;}else{var _o1=B(_nq(_nR,_nS,new T(function(){return E(_nT)-E(_nY)|0;}),_nP,_nZ.b,_));return new F(function(){return A(_mO,[_nR,new T(function(){if(E(_nZ.d)==32){return E(_nN);}else{return E(_nO);}}),new T(function(){return ((E(E(_o0).a)+1|0)+E(_nT)|0)-E(_nY)|0;},1),new T(function(){return (E(E(_o0).b)+2|0)+1|0;},1),new T2(1,_nZ.c,_10),_]);});}},_o2=function(_o3){return E(E(_o3).a);},_o4=function(_o5){return E(E(_o5).a);},_o6=function(_o7,_o8){while(1){var _o9=E(_o7);if(!_o9._){return E(_o8);}else{_o7=_o9.b;_o8=_o9.a;continue;}}},_oa=function(_ob,_oc,_od){return new F(function(){return _o6(_oc,_ob);});},_oe=new T1(0,2),_of=function(_og,_oh){while(1){var _oi=E(_og);if(!_oi._){var _oj=_oi.a,_ok=E(_oh);if(!_ok._){var _ol=_ok.a;if(!(imul(_oj,_ol)|0)){return new T1(0,imul(_oj,_ol)|0);}else{_og=new T1(1,I_fromInt(_oj));_oh=new T1(1,I_fromInt(_ol));continue;}}else{_og=new T1(1,I_fromInt(_oj));_oh=_ok;continue;}}else{var _om=E(_oh);if(!_om._){_og=_oi;_oh=new T1(1,I_fromInt(_om.a));continue;}else{return new T1(1,I_mul(_oi.a,_om.a));}}}},_on=function(_oo,_op,_oq){while(1){if(!(_op%2)){var _or=B(_of(_oo,_oo)),_os=quot(_op,2);_oo=_or;_op=_os;continue;}else{var _ot=E(_op);if(_ot==1){return new F(function(){return _of(_oo,_oq);});}else{var _or=B(_of(_oo,_oo)),_ou=B(_of(_oo,_oq));_oo=_or;_op=quot(_ot-1|0,2);_oq=_ou;continue;}}}},_ov=function(_ow,_ox){while(1){if(!(_ox%2)){var _oy=B(_of(_ow,_ow)),_oz=quot(_ox,2);_ow=_oy;_ox=_oz;continue;}else{var _oA=E(_ox);if(_oA==1){return E(_ow);}else{return new F(function(){return _on(B(_of(_ow,_ow)),quot(_oA-1|0,2),_ow);});}}}},_oB=function(_oC){return E(E(_oC).c);},_oD=function(_oE){return E(E(_oE).a);},_oF=function(_oG){return E(E(_oG).b);},_oH=function(_oI){return E(E(_oI).b);},_oJ=function(_oK){return E(E(_oK).c);},_oL=new T1(0,0),_oM=new T1(0,2),_oN=function(_oO){return E(E(_oO).d);},_oP=function(_oQ,_oR){var _oS=B(_o2(_oQ)),_oT=new T(function(){return B(_o4(_oS));}),_oU=new T(function(){return B(A3(_oN,_oQ,_oR,new T(function(){return B(A2(_he,_oT,_oM));})));});return new F(function(){return A3(_4z,B(_oD(B(_oF(_oS)))),_oU,new T(function(){return B(A2(_he,_oT,_oL));}));});},_oV=new T(function(){return B(unCStr("Negative exponent"));}),_oW=new T(function(){return B(err(_oV));}),_oX=function(_oY){return E(E(_oY).c);},_oZ=function(_p0,_p1,_p2,_p3){var _p4=B(_o2(_p1)),_p5=new T(function(){return B(_o4(_p4));}),_p6=B(_oF(_p4));if(!B(A3(_oJ,_p6,_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){if(!B(A3(_4z,B(_oD(_p6)),_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){var _p7=new T(function(){return B(A2(_he,_p5,_oM));}),_p8=new T(function(){return B(A2(_he,_p5,_aV));}),_p9=B(_oD(_p6)),_pa=function(_pb,_pc,_pd){while(1){var _pe=B((function(_pf,_pg,_ph){if(!B(_oP(_p1,_pg))){if(!B(A3(_4z,_p9,_pg,_p8))){var _pi=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pg,_p8));}),_p7));});_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=_pi;_pd=new T(function(){return B(A3(_oB,_p0,_pf,_ph));});return __continue;}else{return new F(function(){return A3(_oB,_p0,_pf,_ph);});}}else{var _pj=_ph;_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=new T(function(){return B(A3(_oX,_p1,_pg,_p7));});_pd=_pj;return __continue;}})(_pb,_pc,_pd));if(_pe!=__continue){return _pe;}}},_pk=function(_pl,_pm){while(1){var _pn=B((function(_po,_pp){if(!B(_oP(_p1,_pp))){if(!B(A3(_4z,_p9,_pp,_p8))){var _pq=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pp,_p8));}),_p7));});return new F(function(){return _pa(new T(function(){return B(A3(_oB,_p0,_po,_po));}),_pq,_po);});}else{return E(_po);}}else{_pl=new T(function(){return B(A3(_oB,_p0,_po,_po));});_pm=new T(function(){return B(A3(_oX,_p1,_pp,_p7));});return __continue;}})(_pl,_pm));if(_pn!=__continue){return _pn;}}};return new F(function(){return _pk(_p2,_p3);});}else{return new F(function(){return A2(_he,_p0,_aV);});}}else{return E(_oW);}},_pr=new T(function(){return B(err(_oV));}),_ps=function(_pt){var _pu=I_decodeDouble(_pt);return new T2(0,new T1(1,_pu.b),_pu.a);},_pv=function(_pw,_px){var _py=B(_ps(_px)),_pz=_py.a,_pA=_py.b,_pB=new T(function(){return B(_o4(new T(function(){return B(_o2(_pw));})));});if(_pA<0){var _pC= -_pA;if(_pC>=0){var _pD=E(_pC);if(!_pD){var _pE=E(_aV);}else{var _pE=B(_ov(_oe,_pD));}if(!B(_cn(_pE,_cN))){var _pF=B(_cE(_pz,_pE));return new T2(0,new T(function(){return B(A2(_he,_pB,_pF.a));}),new T(function(){return B(_cj(_pF.b,_pA));}));}else{return E(_9U);}}else{return E(_pr);}}else{var _pG=new T(function(){var _pH=new T(function(){return B(_oZ(_pB,_bS,new T(function(){return B(A2(_he,_pB,_oe));}),_pA));});return B(A3(_oB,_pB,new T(function(){return B(A2(_he,_pB,_pz));}),_pH));});return new T2(0,_pG,_fA);}},_pI=function(_pJ,_pK){while(1){var _pL=E(_pK);if(!_pL._){return __Z;}else{var _pM=_pL.b,_pN=E(_pJ);if(_pN==1){return E(_pM);}else{_pJ=_pN-1|0;_pK=_pM;continue;}}}},_pO=function(_pP,_pQ){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.a,_pT=E(_pP);return (_pT==1)?new T2(1,_pS,_10):new T2(1,_pS,new T(function(){return B(_pO(_pT-1|0,_pR.b));}));}},_pU=function(_pV,_pW,_pX,_pY){while(1){if(B(_6R(new T2(1,_pX,_pY),_pW))!=_pV){var _pZ=_pW+1|0;_pW=_pZ;continue;}else{if(0>=_pW){return __Z;}else{return new F(function(){return _pO(_pW,new T2(1,_pX,_pY));});}}}},_q0=function(_q1,_q2,_q3){var _q4=E(_q3);if(!_q4._){return __Z;}else{var _q5=E(_q1);if(B(_6R(_q4,_q2))!=_q5){return new F(function(){return _pU(_q5,_q2+1|0,_q4.a,_q4.b);});}else{if(0>=_q2){return __Z;}else{return new F(function(){return _pO(_q2,_q4);});}}}},_q6=function(_q7,_q8,_q9){var _qa=_q8+1|0;if(_qa>0){return new F(function(){return _pI(_qa,B(_q0(_q7,_qa,_q9)));});}else{return new F(function(){return _q0(_q7,_qa,_q9);});}},_qb=function(_qc,_qd){return (!B(_69(_qc,_qd)))?true:false;},_qe=new T2(0,_69,_qb),_qf=new T(function(){return B(_e7("Event.hs:(63,1)-(64,68)|function addEvent"));}),_qg=0,_qh=function(_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx){while(1){var _qy=E(_qi);if(!_qy._){return {_:0,a:_qj,b:_qk,c:_ql,d:_qm,e:_qn,f:_qo,g:_qp,h:_qq,i:_qr,j:_qs,k:_qt,l:_qu,m:_qv,n:_qw,o:_qx};}else{var _qz=E(_qy.b);if(!_qz._){return E(_qf);}else{var _qA=new T2(1,new T2(0,_qy.a,_qz.a),_qm),_qB=new T2(1,_qg,_qn);_qi=_qz.b;_qm=_qA;_qn=_qB;continue;}}}},_qC=function(_qD,_qE,_qF){var _qG=E(_qF);if(!_qG._){return __Z;}else{var _qH=_qG.a,_qI=_qG.b;return (!B(A2(_qD,_qE,_qH)))?new T2(1,_qH,new T(function(){return B(_qC(_qD,_qE,_qI));})):E(_qI);}},_qJ=function(_qK,_qL){while(1){var _qM=E(_qK);if(!_qM._){return (E(_qL)._==0)?true:false;}else{var _qN=E(_qL);if(!_qN._){return false;}else{if(E(_qM.a)!=E(_qN.a)){return false;}else{_qK=_qM.b;_qL=_qN.b;continue;}}}}},_qO=function(_qP,_qQ){while(1){var _qR=E(_qP);if(!_qR._){return (E(_qQ)._==0)?true:false;}else{var _qS=E(_qQ);if(!_qS._){return false;}else{if(!B(_69(_qR.a,_qS.a))){return false;}else{_qP=_qR.b;_qQ=_qS.b;continue;}}}}},_qT=function(_qU,_qV){switch(E(_qU)){case 0:return (E(_qV)==0)?true:false;case 1:return (E(_qV)==1)?true:false;case 2:return (E(_qV)==2)?true:false;case 3:return (E(_qV)==3)?true:false;case 4:return (E(_qV)==4)?true:false;case 5:return (E(_qV)==5)?true:false;case 6:return (E(_qV)==6)?true:false;case 7:return (E(_qV)==7)?true:false;default:return (E(_qV)==8)?true:false;}},_qW=function(_qX,_qY,_qZ,_r0){if(_qX!=_qZ){return false;}else{return new F(function(){return _qT(_qY,_r0);});}},_r1=function(_r2,_r3){var _r4=E(_r2),_r5=E(_r3);return new F(function(){return _qW(E(_r4.a),_r4.b,E(_r5.a),_r5.b);});},_r6=function(_r7,_r8,_r9,_ra){if(_r7!=_r9){return true;}else{switch(E(_r8)){case 0:return (E(_ra)==0)?false:true;case 1:return (E(_ra)==1)?false:true;case 2:return (E(_ra)==2)?false:true;case 3:return (E(_ra)==3)?false:true;case 4:return (E(_ra)==4)?false:true;case 5:return (E(_ra)==5)?false:true;case 6:return (E(_ra)==6)?false:true;case 7:return (E(_ra)==7)?false:true;default:return (E(_ra)==8)?false:true;}}},_rb=function(_rc,_rd){var _re=E(_rc),_rf=E(_rd);return new F(function(){return _r6(E(_re.a),_re.b,E(_rf.a),_rf.b);});},_rg=new T2(0,_r1,_rb),_rh=0,_ri=function(_rj,_rk){var _rl=E(_rk);if(!_rl._){return 0;}else{var _rm=_rl.b,_rn=E(_rj),_ro=E(_rl.a),_rp=_ro.b;if(E(_rn.a)!=E(_ro.a)){return 1+B(_ri(_rn,_rm))|0;}else{switch(E(_rn.b)){case 0:return (E(_rp)==0)?0:1+B(_ri(_rn,_rm))|0;case 1:return (E(_rp)==1)?0:1+B(_ri(_rn,_rm))|0;case 2:return (E(_rp)==2)?0:1+B(_ri(_rn,_rm))|0;case 3:return (E(_rp)==3)?0:1+B(_ri(_rn,_rm))|0;case 4:return (E(_rp)==4)?0:1+B(_ri(_rn,_rm))|0;case 5:return (E(_rp)==5)?0:1+B(_ri(_rn,_rm))|0;case 6:return (E(_rp)==6)?0:1+B(_ri(_rn,_rm))|0;case 7:return (E(_rp)==7)?0:1+B(_ri(_rn,_rm))|0;default:return (E(_rp)==8)?0:1+B(_ri(_rn,_rm))|0;}}}},_rq=function(_rr,_rs){return new F(function(){return _ri(_rr,_rs);});},_rt=function(_ru,_rv){var _rw=E(_rv);if(!_rw._){return new T2(0,_rh,_rh);}else{var _rx=_rw.a,_ry=_rw.b;return (!B(_4B(_rg,_ru,_rx)))?new T2(0,new T(function(){return E(B(_rt(_ru,_ry)).a);}),new T(function(){return 1+E(B(_rt(_ru,_ry)).b)|0;})):new T2(0,new T(function(){return B(_rq(_ru,_rx));}),_rh);}},_rz=function(_rA,_rB){while(1){var _rC=E(_rB);if(!_rC._){return __Z;}else{var _rD=_rC.b,_rE=E(_rA);if(_rE==1){return E(_rD);}else{_rA=_rE-1|0;_rB=_rD;continue;}}}},_rF=new T(function(){return B(unCStr("getch"));}),_rG=new T(function(){return B(unCStr("=="));}),_rH=new T(function(){return B(unCStr("&&"));}),_rI=new T(function(){return B(unCStr("||"));}),_rJ=new T(function(){return B(unCStr("getpos"));}),_rK=new T(function(){return B(unCStr("ch"));}),_rL=new T(function(){return B(unCStr("tp"));}),_rM=new T2(1,_rL,_10),_rN=new T2(1,_rK,_rM),_rO=new T2(0,_rJ,_rN),_rP=new T(function(){return B(unCStr("a"));}),_rQ=new T(function(){return B(unCStr("b"));}),_rR=new T2(1,_rQ,_10),_rS=new T2(1,_rP,_rR),_rT=new T2(0,_rG,_rS),_rU=new T2(0,_rH,_rS),_rV=new T2(0,_rI,_rS),_rW=new T2(1,_rV,_10),_rX=new T2(1,_rU,_rW),_rY=new T2(1,_rT,_rX),_rZ=new T2(1,_rO,_rY),_s0=new T(function(){return B(unCStr("p"));}),_s1=new T(function(){return B(unCStr("q"));}),_s2=new T2(1,_s1,_10),_s3=new T2(1,_s0,_s2),_s4=new T2(0,_rF,_s3),_s5=new T2(1,_s4,_rZ),_s6=new T(function(){return B(unCStr("foldr1"));}),_s7=new T(function(){return B(_ne(_s6));}),_s8=function(_s9,_sa){var _sb=E(_sa);if(!_sb._){return E(_s7);}else{var _sc=_sb.a,_sd=E(_sb.b);if(!_sd._){return E(_sc);}else{return new F(function(){return A2(_s9,_sc,new T(function(){return B(_s8(_s9,_sd));}));});}}},_se=function(_sf){return E(E(_sf).a);},_sg=function(_sh){var _si=E(_sh);return (_si._==0)?E(_nh):E(_si.a);},_sj=function(_sk,_sl,_sm){while(1){var _sn=E(_sm);if(!_sn._){return __Z;}else{var _so=E(_sn.a);if(!B(A3(_4z,_sk,_sl,_so.a))){_sm=_sn.b;continue;}else{return new T1(1,_so.b);}}}},_sp=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sq=new T(function(){return B(err(_sp));}),_sr=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_ss=new T(function(){return B(err(_sr));}),_st=new T(function(){return B(unCStr("T"));}),_su=new T(function(){return B(unCStr("F"));}),_sv=new T(function(){return B(_e7("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sw=function(_sx,_sy){while(1){var _sz=B((function(_sA,_sB){var _sC=E(_sA);switch(_sC._){case 0:var _sD=E(_sB);if(!_sD._){return __Z;}else{_sx=B(A1(_sC.a,_sD.a));_sy=_sD.b;return __continue;}break;case 1:var _sE=B(A1(_sC.a,_sB)),_sF=_sB;_sx=_sE;_sy=_sF;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sC.a,_sB),new T(function(){return B(_sw(_sC.b,_sB));}));default:return E(_sC.a);}})(_sx,_sy));if(_sz!=__continue){return _sz;}}},_sG=function(_sH,_sI){var _sJ=function(_sK){var _sL=E(_sI);if(_sL._==3){return new T2(3,_sL.a,new T(function(){return B(_sG(_sH,_sL.b));}));}else{var _sM=E(_sH);if(_sM._==2){return E(_sL);}else{var _sN=E(_sL);if(_sN._==2){return E(_sM);}else{var _sO=function(_sP){var _sQ=E(_sN);if(_sQ._==4){var _sR=function(_sS){return new T1(4,new T(function(){return B(_y(B(_sw(_sM,_sS)),_sQ.a));}));};return new T1(1,_sR);}else{var _sT=E(_sM);if(_sT._==1){var _sU=_sT.a,_sV=E(_sQ);if(!_sV._){return new T1(1,function(_sW){return new F(function(){return _sG(B(A1(_sU,_sW)),_sV);});});}else{var _sX=function(_sY){return new F(function(){return _sG(B(A1(_sU,_sY)),new T(function(){return B(A1(_sV.a,_sY));}));});};return new T1(1,_sX);}}else{var _sZ=E(_sQ);if(!_sZ._){return E(_sv);}else{var _t0=function(_t1){return new F(function(){return _sG(_sT,new T(function(){return B(A1(_sZ.a,_t1));}));});};return new T1(1,_t0);}}}},_t2=E(_sM);switch(_t2._){case 1:var _t3=E(_sN);if(_t3._==4){var _t4=function(_t5){return new T1(4,new T(function(){return B(_y(B(_sw(B(A1(_t2.a,_t5)),_t5)),_t3.a));}));};return new T1(1,_t4);}else{return new F(function(){return _sO(_);});}break;case 4:var _t6=_t2.a,_t7=E(_sN);switch(_t7._){case 0:var _t8=function(_t9){var _ta=new T(function(){return B(_y(_t6,new T(function(){return B(_sw(_t7,_t9));},1)));});return new T1(4,_ta);};return new T1(1,_t8);case 1:var _tb=function(_tc){var _td=new T(function(){return B(_y(_t6,new T(function(){return B(_sw(B(A1(_t7.a,_tc)),_tc));},1)));});return new T1(4,_td);};return new T1(1,_tb);default:return new T1(4,new T(function(){return B(_y(_t6,_t7.a));}));}break;default:return new F(function(){return _sO(_);});}}}}},_te=E(_sH);switch(_te._){case 0:var _tf=E(_sI);if(!_tf._){var _tg=function(_th){return new F(function(){return _sG(B(A1(_te.a,_th)),new T(function(){return B(A1(_tf.a,_th));}));});};return new T1(0,_tg);}else{return new F(function(){return _sJ(_);});}break;case 3:return new T2(3,_te.a,new T(function(){return B(_sG(_te.b,_sI));}));default:return new F(function(){return _sJ(_);});}},_ti=new T(function(){return B(unCStr("("));}),_tj=new T(function(){return B(unCStr(")"));}),_tk=function(_tl,_tm){var _tn=E(_tl);switch(_tn._){case 0:return new T1(0,function(_to){return new F(function(){return _tk(B(A1(_tn.a,_to)),_tm);});});case 1:return new T1(1,function(_tp){return new F(function(){return _tk(B(A1(_tn.a,_tp)),_tm);});});case 2:return new T0(2);case 3:return new F(function(){return _sG(B(A1(_tm,_tn.a)),new T(function(){return B(_tk(_tn.b,_tm));}));});break;default:var _tq=function(_tr){var _ts=E(_tr);if(!_ts._){return __Z;}else{var _tt=E(_ts.a);return new F(function(){return _y(B(_sw(B(A1(_tm,_tt.a)),_tt.b)),new T(function(){return B(_tq(_ts.b));},1));});}},_tu=B(_tq(_tn.a));return (_tu._==0)?new T0(2):new T1(4,_tu);}},_tv=new T0(2),_tw=function(_tx){return new T2(3,_tx,_tv);},_ty=function(_tz,_tA){var _tB=E(_tz);if(!_tB){return new F(function(){return A1(_tA,_gE);});}else{var _tC=new T(function(){return B(_ty(_tB-1|0,_tA));});return new T1(0,function(_tD){return E(_tC);});}},_tE=function(_tF,_tG,_tH){var _tI=new T(function(){return B(A1(_tF,_tw));}),_tJ=function(_tK,_tL,_tM,_tN){while(1){var _tO=B((function(_tP,_tQ,_tR,_tS){var _tT=E(_tP);switch(_tT._){case 0:var _tU=E(_tQ);if(!_tU._){return new F(function(){return A1(_tG,_tS);});}else{var _tV=_tR+1|0,_tW=_tS;_tK=B(A1(_tT.a,_tU.a));_tL=_tU.b;_tM=_tV;_tN=_tW;return __continue;}break;case 1:var _tX=B(A1(_tT.a,_tQ)),_tY=_tQ,_tV=_tR,_tW=_tS;_tK=_tX;_tL=_tY;_tM=_tV;_tN=_tW;return __continue;case 2:return new F(function(){return A1(_tG,_tS);});break;case 3:var _tZ=new T(function(){return B(_tk(_tT,_tS));});return new F(function(){return _ty(_tR,function(_u0){return E(_tZ);});});break;default:return new F(function(){return _tk(_tT,_tS);});}})(_tK,_tL,_tM,_tN));if(_tO!=__continue){return _tO;}}};return function(_u1){return new F(function(){return _tJ(_tI,_u1,0,_tH);});};},_u2=function(_u3){return new F(function(){return A1(_u3,_10);});},_u4=function(_u5,_u6){var _u7=function(_u8){var _u9=E(_u8);if(!_u9._){return E(_u2);}else{var _ua=_u9.a;if(!B(A1(_u5,_ua))){return E(_u2);}else{var _ub=new T(function(){return B(_u7(_u9.b));}),_uc=function(_ud){var _ue=new T(function(){return B(A1(_ub,function(_uf){return new F(function(){return A1(_ud,new T2(1,_ua,_uf));});}));});return new T1(0,function(_ug){return E(_ue);});};return E(_uc);}}};return function(_uh){return new F(function(){return A2(_u7,_uh,_u6);});};},_ui=new T0(6),_uj=new T(function(){return B(unCStr("valDig: Bad base"));}),_uk=new T(function(){return B(err(_uj));}),_ul=function(_um,_un){var _uo=function(_up,_uq){var _ur=E(_up);if(!_ur._){var _us=new T(function(){return B(A1(_uq,_10));});return function(_ut){return new F(function(){return A1(_ut,_us);});};}else{var _uu=E(_ur.a),_uv=function(_uw){var _ux=new T(function(){return B(_uo(_ur.b,function(_uy){return new F(function(){return A1(_uq,new T2(1,_uw,_uy));});}));}),_uz=function(_uA){var _uB=new T(function(){return B(A1(_ux,_uA));});return new T1(0,function(_uC){return E(_uB);});};return E(_uz);};switch(E(_um)){case 8:if(48>_uu){var _uD=new T(function(){return B(A1(_uq,_10));});return function(_uE){return new F(function(){return A1(_uE,_uD);});};}else{if(_uu>55){var _uF=new T(function(){return B(A1(_uq,_10));});return function(_uG){return new F(function(){return A1(_uG,_uF);});};}else{return new F(function(){return _uv(_uu-48|0);});}}break;case 10:if(48>_uu){var _uH=new T(function(){return B(A1(_uq,_10));});return function(_uI){return new F(function(){return A1(_uI,_uH);});};}else{if(_uu>57){var _uJ=new T(function(){return B(A1(_uq,_10));});return function(_uK){return new F(function(){return A1(_uK,_uJ);});};}else{return new F(function(){return _uv(_uu-48|0);});}}break;case 16:if(48>_uu){if(97>_uu){if(65>_uu){var _uL=new T(function(){return B(A1(_uq,_10));});return function(_uM){return new F(function(){return A1(_uM,_uL);});};}else{if(_uu>70){var _uN=new T(function(){return B(A1(_uq,_10));});return function(_uO){return new F(function(){return A1(_uO,_uN);});};}else{return new F(function(){return _uv((_uu-65|0)+10|0);});}}}else{if(_uu>102){if(65>_uu){var _uP=new T(function(){return B(A1(_uq,_10));});return function(_uQ){return new F(function(){return A1(_uQ,_uP);});};}else{if(_uu>70){var _uR=new T(function(){return B(A1(_uq,_10));});return function(_uS){return new F(function(){return A1(_uS,_uR);});};}else{return new F(function(){return _uv((_uu-65|0)+10|0);});}}}else{return new F(function(){return _uv((_uu-97|0)+10|0);});}}}else{if(_uu>57){if(97>_uu){if(65>_uu){var _uT=new T(function(){return B(A1(_uq,_10));});return function(_uU){return new F(function(){return A1(_uU,_uT);});};}else{if(_uu>70){var _uV=new T(function(){return B(A1(_uq,_10));});return function(_uW){return new F(function(){return A1(_uW,_uV);});};}else{return new F(function(){return _uv((_uu-65|0)+10|0);});}}}else{if(_uu>102){if(65>_uu){var _uX=new T(function(){return B(A1(_uq,_10));});return function(_uY){return new F(function(){return A1(_uY,_uX);});};}else{if(_uu>70){var _uZ=new T(function(){return B(A1(_uq,_10));});return function(_v0){return new F(function(){return A1(_v0,_uZ);});};}else{return new F(function(){return _uv((_uu-65|0)+10|0);});}}}else{return new F(function(){return _uv((_uu-97|0)+10|0);});}}}else{return new F(function(){return _uv(_uu-48|0);});}}break;default:return E(_uk);}}},_v1=function(_v2){var _v3=E(_v2);if(!_v3._){return new T0(2);}else{return new F(function(){return A1(_un,_v3);});}};return function(_v4){return new F(function(){return A3(_uo,_v4,_5V,_v1);});};},_v5=16,_v6=8,_v7=function(_v8){var _v9=function(_va){return new F(function(){return A1(_v8,new T1(5,new T2(0,_v6,_va)));});},_vb=function(_vc){return new F(function(){return A1(_v8,new T1(5,new T2(0,_v5,_vc)));});},_vd=function(_ve){switch(E(_ve)){case 79:return new T1(1,B(_ul(_v6,_v9)));case 88:return new T1(1,B(_ul(_v5,_vb)));case 111:return new T1(1,B(_ul(_v6,_v9)));case 120:return new T1(1,B(_ul(_v5,_vb)));default:return new T0(2);}};return function(_vf){return (E(_vf)==48)?E(new T1(0,_vd)):new T0(2);};},_vg=function(_vh){return new T1(0,B(_v7(_vh)));},_vi=function(_vj){return new F(function(){return A1(_vj,_0);});},_vk=function(_vl){return new F(function(){return A1(_vl,_0);});},_vm=10,_vn=new T1(0,10),_vo=function(_vp){return new F(function(){return _aR(E(_vp));});},_vq=new T(function(){return B(unCStr("this should not happen"));}),_vr=new T(function(){return B(err(_vq));}),_vs=function(_vt,_vu){var _vv=E(_vu);if(!_vv._){return __Z;}else{var _vw=E(_vv.b);return (_vw._==0)?E(_vr):new T2(1,B(_cv(B(_of(_vv.a,_vt)),_vw.a)),new T(function(){return B(_vs(_vt,_vw.b));}));}},_vx=new T1(0,0),_vy=function(_vz,_vA,_vB){while(1){var _vC=B((function(_vD,_vE,_vF){var _vG=E(_vF);if(!_vG._){return E(_vx);}else{if(!E(_vG.b)._){return E(_vG.a);}else{var _vH=E(_vE);if(_vH<=40){var _vI=function(_vJ,_vK){while(1){var _vL=E(_vK);if(!_vL._){return E(_vJ);}else{var _vM=B(_cv(B(_of(_vJ,_vD)),_vL.a));_vJ=_vM;_vK=_vL.b;continue;}}};return new F(function(){return _vI(_vx,_vG);});}else{var _vN=B(_of(_vD,_vD));if(!(_vH%2)){var _vO=B(_vs(_vD,_vG));_vz=_vN;_vA=quot(_vH+1|0,2);_vB=_vO;return __continue;}else{var _vO=B(_vs(_vD,new T2(1,_vx,_vG)));_vz=_vN;_vA=quot(_vH+1|0,2);_vB=_vO;return __continue;}}}}})(_vz,_vA,_vB));if(_vC!=__continue){return _vC;}}},_vP=function(_vQ,_vR){return new F(function(){return _vy(_vQ,new T(function(){return B(_mt(_vR,0));},1),B(_6e(_vo,_vR)));});},_vS=function(_vT){var _vU=new T(function(){var _vV=new T(function(){var _vW=function(_vX){return new F(function(){return A1(_vT,new T1(1,new T(function(){return B(_vP(_vn,_vX));})));});};return new T1(1,B(_ul(_vm,_vW)));}),_vY=function(_vZ){if(E(_vZ)==43){var _w0=function(_w1){return new F(function(){return A1(_vT,new T1(1,new T(function(){return B(_vP(_vn,_w1));})));});};return new T1(1,B(_ul(_vm,_w0)));}else{return new T0(2);}},_w2=function(_w3){if(E(_w3)==45){var _w4=function(_w5){return new F(function(){return A1(_vT,new T1(1,new T(function(){return B(_ft(B(_vP(_vn,_w5))));})));});};return new T1(1,B(_ul(_vm,_w4)));}else{return new T0(2);}};return B(_sG(B(_sG(new T1(0,_w2),new T1(0,_vY))),_vV));});return new F(function(){return _sG(new T1(0,function(_w6){return (E(_w6)==101)?E(_vU):new T0(2);}),new T1(0,function(_w7){return (E(_w7)==69)?E(_vU):new T0(2);}));});},_w8=function(_w9){var _wa=function(_wb){return new F(function(){return A1(_w9,new T1(1,_wb));});};return function(_wc){return (E(_wc)==46)?new T1(1,B(_ul(_vm,_wa))):new T0(2);};},_wd=function(_we){return new T1(0,B(_w8(_we)));},_wf=function(_wg){var _wh=function(_wi){var _wj=function(_wk){return new T1(1,B(_tE(_vS,_vi,function(_wl){return new F(function(){return A1(_wg,new T1(5,new T3(1,_wi,_wk,_wl)));});})));};return new T1(1,B(_tE(_wd,_vk,_wj)));};return new F(function(){return _ul(_vm,_wh);});},_wm=function(_wn){return new T1(1,B(_wf(_wn)));},_wo=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wp=function(_wq){return new F(function(){return _4B(_h7,_wq,_wo);});},_wr=false,_ws=true,_wt=function(_wu){var _wv=new T(function(){return B(A1(_wu,_v6));}),_ww=new T(function(){return B(A1(_wu,_v5));});return function(_wx){switch(E(_wx)){case 79:return E(_wv);case 88:return E(_ww);case 111:return E(_wv);case 120:return E(_ww);default:return new T0(2);}};},_wy=function(_wz){return new T1(0,B(_wt(_wz)));},_wA=function(_wB){return new F(function(){return A1(_wB,_vm);});},_wC=function(_wD){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_I(9,_wD,_10));}))));});},_wE=function(_wF){return new T0(2);},_wG=function(_wH){var _wI=E(_wH);if(!_wI._){return E(_wE);}else{var _wJ=_wI.a,_wK=E(_wI.b);if(!_wK._){return E(_wJ);}else{var _wL=new T(function(){return B(_wG(_wK));}),_wM=function(_wN){return new F(function(){return _sG(B(A1(_wJ,_wN)),new T(function(){return B(A1(_wL,_wN));}));});};return E(_wM);}}},_wO=function(_wP,_wQ){var _wR=function(_wS,_wT,_wU){var _wV=E(_wS);if(!_wV._){return new F(function(){return A1(_wU,_wP);});}else{var _wW=E(_wT);if(!_wW._){return new T0(2);}else{if(E(_wV.a)!=E(_wW.a)){return new T0(2);}else{var _wX=new T(function(){return B(_wR(_wV.b,_wW.b,_wU));});return new T1(0,function(_wY){return E(_wX);});}}}};return function(_wZ){return new F(function(){return _wR(_wP,_wZ,_wQ);});};},_x0=new T(function(){return B(unCStr("SO"));}),_x1=14,_x2=function(_x3){var _x4=new T(function(){return B(A1(_x3,_x1));});return new T1(1,B(_wO(_x0,function(_x5){return E(_x4);})));},_x6=new T(function(){return B(unCStr("SOH"));}),_x7=1,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_wO(_x6,function(_xb){return E(_xa);})));},_xc=function(_xd){return new T1(1,B(_tE(_x8,_x2,_xd)));},_xe=new T(function(){return B(unCStr("NUL"));}),_xf=0,_xg=function(_xh){var _xi=new T(function(){return B(A1(_xh,_xf));});return new T1(1,B(_wO(_xe,function(_xj){return E(_xi);})));},_xk=new T(function(){return B(unCStr("STX"));}),_xl=2,_xm=function(_xn){var _xo=new T(function(){return B(A1(_xn,_xl));});return new T1(1,B(_wO(_xk,function(_xp){return E(_xo);})));},_xq=new T(function(){return B(unCStr("ETX"));}),_xr=3,_xs=function(_xt){var _xu=new T(function(){return B(A1(_xt,_xr));});return new T1(1,B(_wO(_xq,function(_xv){return E(_xu);})));},_xw=new T(function(){return B(unCStr("EOT"));}),_xx=4,_xy=function(_xz){var _xA=new T(function(){return B(A1(_xz,_xx));});return new T1(1,B(_wO(_xw,function(_xB){return E(_xA);})));},_xC=new T(function(){return B(unCStr("ENQ"));}),_xD=5,_xE=function(_xF){var _xG=new T(function(){return B(A1(_xF,_xD));});return new T1(1,B(_wO(_xC,function(_xH){return E(_xG);})));},_xI=new T(function(){return B(unCStr("ACK"));}),_xJ=6,_xK=function(_xL){var _xM=new T(function(){return B(A1(_xL,_xJ));});return new T1(1,B(_wO(_xI,function(_xN){return E(_xM);})));},_xO=new T(function(){return B(unCStr("BEL"));}),_xP=7,_xQ=function(_xR){var _xS=new T(function(){return B(A1(_xR,_xP));});return new T1(1,B(_wO(_xO,function(_xT){return E(_xS);})));},_xU=new T(function(){return B(unCStr("BS"));}),_xV=8,_xW=function(_xX){var _xY=new T(function(){return B(A1(_xX,_xV));});return new T1(1,B(_wO(_xU,function(_xZ){return E(_xY);})));},_y0=new T(function(){return B(unCStr("HT"));}),_y1=9,_y2=function(_y3){var _y4=new T(function(){return B(A1(_y3,_y1));});return new T1(1,B(_wO(_y0,function(_y5){return E(_y4);})));},_y6=new T(function(){return B(unCStr("LF"));}),_y7=10,_y8=function(_y9){var _ya=new T(function(){return B(A1(_y9,_y7));});return new T1(1,B(_wO(_y6,function(_yb){return E(_ya);})));},_yc=new T(function(){return B(unCStr("VT"));}),_yd=11,_ye=function(_yf){var _yg=new T(function(){return B(A1(_yf,_yd));});return new T1(1,B(_wO(_yc,function(_yh){return E(_yg);})));},_yi=new T(function(){return B(unCStr("FF"));}),_yj=12,_yk=function(_yl){var _ym=new T(function(){return B(A1(_yl,_yj));});return new T1(1,B(_wO(_yi,function(_yn){return E(_ym);})));},_yo=new T(function(){return B(unCStr("CR"));}),_yp=13,_yq=function(_yr){var _ys=new T(function(){return B(A1(_yr,_yp));});return new T1(1,B(_wO(_yo,function(_yt){return E(_ys);})));},_yu=new T(function(){return B(unCStr("SI"));}),_yv=15,_yw=function(_yx){var _yy=new T(function(){return B(A1(_yx,_yv));});return new T1(1,B(_wO(_yu,function(_yz){return E(_yy);})));},_yA=new T(function(){return B(unCStr("DLE"));}),_yB=16,_yC=function(_yD){var _yE=new T(function(){return B(A1(_yD,_yB));});return new T1(1,B(_wO(_yA,function(_yF){return E(_yE);})));},_yG=new T(function(){return B(unCStr("DC1"));}),_yH=17,_yI=function(_yJ){var _yK=new T(function(){return B(A1(_yJ,_yH));});return new T1(1,B(_wO(_yG,function(_yL){return E(_yK);})));},_yM=new T(function(){return B(unCStr("DC2"));}),_yN=18,_yO=function(_yP){var _yQ=new T(function(){return B(A1(_yP,_yN));});return new T1(1,B(_wO(_yM,function(_yR){return E(_yQ);})));},_yS=new T(function(){return B(unCStr("DC3"));}),_yT=19,_yU=function(_yV){var _yW=new T(function(){return B(A1(_yV,_yT));});return new T1(1,B(_wO(_yS,function(_yX){return E(_yW);})));},_yY=new T(function(){return B(unCStr("DC4"));}),_yZ=20,_z0=function(_z1){var _z2=new T(function(){return B(A1(_z1,_yZ));});return new T1(1,B(_wO(_yY,function(_z3){return E(_z2);})));},_z4=new T(function(){return B(unCStr("NAK"));}),_z5=21,_z6=function(_z7){var _z8=new T(function(){return B(A1(_z7,_z5));});return new T1(1,B(_wO(_z4,function(_z9){return E(_z8);})));},_za=new T(function(){return B(unCStr("SYN"));}),_zb=22,_zc=function(_zd){var _ze=new T(function(){return B(A1(_zd,_zb));});return new T1(1,B(_wO(_za,function(_zf){return E(_ze);})));},_zg=new T(function(){return B(unCStr("ETB"));}),_zh=23,_zi=function(_zj){var _zk=new T(function(){return B(A1(_zj,_zh));});return new T1(1,B(_wO(_zg,function(_zl){return E(_zk);})));},_zm=new T(function(){return B(unCStr("CAN"));}),_zn=24,_zo=function(_zp){var _zq=new T(function(){return B(A1(_zp,_zn));});return new T1(1,B(_wO(_zm,function(_zr){return E(_zq);})));},_zs=new T(function(){return B(unCStr("EM"));}),_zt=25,_zu=function(_zv){var _zw=new T(function(){return B(A1(_zv,_zt));});return new T1(1,B(_wO(_zs,function(_zx){return E(_zw);})));},_zy=new T(function(){return B(unCStr("SUB"));}),_zz=26,_zA=function(_zB){var _zC=new T(function(){return B(A1(_zB,_zz));});return new T1(1,B(_wO(_zy,function(_zD){return E(_zC);})));},_zE=new T(function(){return B(unCStr("ESC"));}),_zF=27,_zG=function(_zH){var _zI=new T(function(){return B(A1(_zH,_zF));});return new T1(1,B(_wO(_zE,function(_zJ){return E(_zI);})));},_zK=new T(function(){return B(unCStr("FS"));}),_zL=28,_zM=function(_zN){var _zO=new T(function(){return B(A1(_zN,_zL));});return new T1(1,B(_wO(_zK,function(_zP){return E(_zO);})));},_zQ=new T(function(){return B(unCStr("GS"));}),_zR=29,_zS=function(_zT){var _zU=new T(function(){return B(A1(_zT,_zR));});return new T1(1,B(_wO(_zQ,function(_zV){return E(_zU);})));},_zW=new T(function(){return B(unCStr("RS"));}),_zX=30,_zY=function(_zZ){var _A0=new T(function(){return B(A1(_zZ,_zX));});return new T1(1,B(_wO(_zW,function(_A1){return E(_A0);})));},_A2=new T(function(){return B(unCStr("US"));}),_A3=31,_A4=function(_A5){var _A6=new T(function(){return B(A1(_A5,_A3));});return new T1(1,B(_wO(_A2,function(_A7){return E(_A6);})));},_A8=new T(function(){return B(unCStr("SP"));}),_A9=32,_Aa=function(_Ab){var _Ac=new T(function(){return B(A1(_Ab,_A9));});return new T1(1,B(_wO(_A8,function(_Ad){return E(_Ac);})));},_Ae=new T(function(){return B(unCStr("DEL"));}),_Af=127,_Ag=function(_Ah){var _Ai=new T(function(){return B(A1(_Ah,_Af));});return new T1(1,B(_wO(_Ae,function(_Aj){return E(_Ai);})));},_Ak=new T2(1,_Ag,_10),_Al=new T2(1,_Aa,_Ak),_Am=new T2(1,_A4,_Al),_An=new T2(1,_zY,_Am),_Ao=new T2(1,_zS,_An),_Ap=new T2(1,_zM,_Ao),_Aq=new T2(1,_zG,_Ap),_Ar=new T2(1,_zA,_Aq),_As=new T2(1,_zu,_Ar),_At=new T2(1,_zo,_As),_Au=new T2(1,_zi,_At),_Av=new T2(1,_zc,_Au),_Aw=new T2(1,_z6,_Av),_Ax=new T2(1,_z0,_Aw),_Ay=new T2(1,_yU,_Ax),_Az=new T2(1,_yO,_Ay),_AA=new T2(1,_yI,_Az),_AB=new T2(1,_yC,_AA),_AC=new T2(1,_yw,_AB),_AD=new T2(1,_yq,_AC),_AE=new T2(1,_yk,_AD),_AF=new T2(1,_ye,_AE),_AG=new T2(1,_y8,_AF),_AH=new T2(1,_y2,_AG),_AI=new T2(1,_xW,_AH),_AJ=new T2(1,_xQ,_AI),_AK=new T2(1,_xK,_AJ),_AL=new T2(1,_xE,_AK),_AM=new T2(1,_xy,_AL),_AN=new T2(1,_xs,_AM),_AO=new T2(1,_xm,_AN),_AP=new T2(1,_xg,_AO),_AQ=new T2(1,_xc,_AP),_AR=new T(function(){return B(_wG(_AQ));}),_AS=34,_AT=new T1(0,1114111),_AU=92,_AV=39,_AW=function(_AX){var _AY=new T(function(){return B(A1(_AX,_xP));}),_AZ=new T(function(){return B(A1(_AX,_xV));}),_B0=new T(function(){return B(A1(_AX,_y1));}),_B1=new T(function(){return B(A1(_AX,_y7));}),_B2=new T(function(){return B(A1(_AX,_yd));}),_B3=new T(function(){return B(A1(_AX,_yj));}),_B4=new T(function(){return B(A1(_AX,_yp));}),_B5=new T(function(){return B(A1(_AX,_AU));}),_B6=new T(function(){return B(A1(_AX,_AV));}),_B7=new T(function(){return B(A1(_AX,_AS));}),_B8=new T(function(){var _B9=function(_Ba){var _Bb=new T(function(){return B(_aR(E(_Ba)));}),_Bc=function(_Bd){var _Be=B(_vP(_Bb,_Bd));if(!B(_ez(_Be,_AT))){return new T0(2);}else{return new F(function(){return A1(_AX,new T(function(){var _Bf=B(_ba(_Be));if(_Bf>>>0>1114111){return B(_wC(_Bf));}else{return _Bf;}}));});}};return new T1(1,B(_ul(_Ba,_Bc)));},_Bg=new T(function(){var _Bh=new T(function(){return B(A1(_AX,_A3));}),_Bi=new T(function(){return B(A1(_AX,_zX));}),_Bj=new T(function(){return B(A1(_AX,_zR));}),_Bk=new T(function(){return B(A1(_AX,_zL));}),_Bl=new T(function(){return B(A1(_AX,_zF));}),_Bm=new T(function(){return B(A1(_AX,_zz));}),_Bn=new T(function(){return B(A1(_AX,_zt));}),_Bo=new T(function(){return B(A1(_AX,_zn));}),_Bp=new T(function(){return B(A1(_AX,_zh));}),_Bq=new T(function(){return B(A1(_AX,_zb));}),_Br=new T(function(){return B(A1(_AX,_z5));}),_Bs=new T(function(){return B(A1(_AX,_yZ));}),_Bt=new T(function(){return B(A1(_AX,_yT));}),_Bu=new T(function(){return B(A1(_AX,_yN));}),_Bv=new T(function(){return B(A1(_AX,_yH));}),_Bw=new T(function(){return B(A1(_AX,_yB));}),_Bx=new T(function(){return B(A1(_AX,_yv));}),_By=new T(function(){return B(A1(_AX,_x1));}),_Bz=new T(function(){return B(A1(_AX,_xJ));}),_BA=new T(function(){return B(A1(_AX,_xD));}),_BB=new T(function(){return B(A1(_AX,_xx));}),_BC=new T(function(){return B(A1(_AX,_xr));}),_BD=new T(function(){return B(A1(_AX,_xl));}),_BE=new T(function(){return B(A1(_AX,_x7));}),_BF=new T(function(){return B(A1(_AX,_xf));}),_BG=function(_BH){switch(E(_BH)){case 64:return E(_BF);case 65:return E(_BE);case 66:return E(_BD);case 67:return E(_BC);case 68:return E(_BB);case 69:return E(_BA);case 70:return E(_Bz);case 71:return E(_AY);case 72:return E(_AZ);case 73:return E(_B0);case 74:return E(_B1);case 75:return E(_B2);case 76:return E(_B3);case 77:return E(_B4);case 78:return E(_By);case 79:return E(_Bx);case 80:return E(_Bw);case 81:return E(_Bv);case 82:return E(_Bu);case 83:return E(_Bt);case 84:return E(_Bs);case 85:return E(_Br);case 86:return E(_Bq);case 87:return E(_Bp);case 88:return E(_Bo);case 89:return E(_Bn);case 90:return E(_Bm);case 91:return E(_Bl);case 92:return E(_Bk);case 93:return E(_Bj);case 94:return E(_Bi);case 95:return E(_Bh);default:return new T0(2);}};return B(_sG(new T1(0,function(_BI){return (E(_BI)==94)?E(new T1(0,_BG)):new T0(2);}),new T(function(){return B(A1(_AR,_AX));})));});return B(_sG(new T1(1,B(_tE(_wy,_wA,_B9))),_Bg));});return new F(function(){return _sG(new T1(0,function(_BJ){switch(E(_BJ)){case 34:return E(_B7);case 39:return E(_B6);case 92:return E(_B5);case 97:return E(_AY);case 98:return E(_AZ);case 102:return E(_B3);case 110:return E(_B1);case 114:return E(_B4);case 116:return E(_B0);case 118:return E(_B2);default:return new T0(2);}}),_B8);});},_BK=function(_BL){return new F(function(){return A1(_BL,_gE);});},_BM=function(_BN){var _BO=E(_BN);if(!_BO._){return E(_BK);}else{var _BP=E(_BO.a),_BQ=_BP>>>0,_BR=new T(function(){return B(_BM(_BO.b));});if(_BQ>887){var _BS=u_iswspace(_BP);if(!E(_BS)){return E(_BK);}else{var _BT=function(_BU){var _BV=new T(function(){return B(A1(_BR,_BU));});return new T1(0,function(_BW){return E(_BV);});};return E(_BT);}}else{var _BX=E(_BQ);if(_BX==32){var _BY=function(_BZ){var _C0=new T(function(){return B(A1(_BR,_BZ));});return new T1(0,function(_C1){return E(_C0);});};return E(_BY);}else{if(_BX-9>>>0>4){if(E(_BX)==160){var _C2=function(_C3){var _C4=new T(function(){return B(A1(_BR,_C3));});return new T1(0,function(_C5){return E(_C4);});};return E(_C2);}else{return E(_BK);}}else{var _C6=function(_C7){var _C8=new T(function(){return B(A1(_BR,_C7));});return new T1(0,function(_C9){return E(_C8);});};return E(_C6);}}}}},_Ca=function(_Cb){var _Cc=new T(function(){return B(_Ca(_Cb));}),_Cd=function(_Ce){return (E(_Ce)==92)?E(_Cc):new T0(2);},_Cf=function(_Cg){return E(new T1(0,_Cd));},_Ch=new T1(1,function(_Ci){return new F(function(){return A2(_BM,_Ci,_Cf);});}),_Cj=new T(function(){return B(_AW(function(_Ck){return new F(function(){return A1(_Cb,new T2(0,_Ck,_ws));});}));}),_Cl=function(_Cm){var _Cn=E(_Cm);if(_Cn==38){return E(_Cc);}else{var _Co=_Cn>>>0;if(_Co>887){var _Cp=u_iswspace(_Cn);return (E(_Cp)==0)?new T0(2):E(_Ch);}else{var _Cq=E(_Co);return (_Cq==32)?E(_Ch):(_Cq-9>>>0>4)?(E(_Cq)==160)?E(_Ch):new T0(2):E(_Ch);}}};return new F(function(){return _sG(new T1(0,function(_Cr){return (E(_Cr)==92)?E(new T1(0,_Cl)):new T0(2);}),new T1(0,function(_Cs){var _Ct=E(_Cs);if(E(_Ct)==92){return E(_Cj);}else{return new F(function(){return A1(_Cb,new T2(0,_Ct,_wr));});}}));});},_Cu=function(_Cv,_Cw){var _Cx=new T(function(){return B(A1(_Cw,new T1(1,new T(function(){return B(A1(_Cv,_10));}))));}),_Cy=function(_Cz){var _CA=E(_Cz),_CB=E(_CA.a);if(E(_CB)==34){if(!E(_CA.b)){return E(_Cx);}else{return new F(function(){return _Cu(function(_CC){return new F(function(){return A1(_Cv,new T2(1,_CB,_CC));});},_Cw);});}}else{return new F(function(){return _Cu(function(_CD){return new F(function(){return A1(_Cv,new T2(1,_CB,_CD));});},_Cw);});}};return new F(function(){return _Ca(_Cy);});},_CE=new T(function(){return B(unCStr("_\'"));}),_CF=function(_CG){var _CH=u_iswalnum(_CG);if(!E(_CH)){return new F(function(){return _4B(_h7,_CG,_CE);});}else{return true;}},_CI=function(_CJ){return new F(function(){return _CF(E(_CJ));});},_CK=new T(function(){return B(unCStr(",;()[]{}`"));}),_CL=new T(function(){return B(unCStr("=>"));}),_CM=new T2(1,_CL,_10),_CN=new T(function(){return B(unCStr("~"));}),_CO=new T2(1,_CN,_CM),_CP=new T(function(){return B(unCStr("@"));}),_CQ=new T2(1,_CP,_CO),_CR=new T(function(){return B(unCStr("->"));}),_CS=new T2(1,_CR,_CQ),_CT=new T(function(){return B(unCStr("<-"));}),_CU=new T2(1,_CT,_CS),_CV=new T(function(){return B(unCStr("|"));}),_CW=new T2(1,_CV,_CU),_CX=new T(function(){return B(unCStr("\\"));}),_CY=new T2(1,_CX,_CW),_CZ=new T(function(){return B(unCStr("="));}),_D0=new T2(1,_CZ,_CY),_D1=new T(function(){return B(unCStr("::"));}),_D2=new T2(1,_D1,_D0),_D3=new T(function(){return B(unCStr(".."));}),_D4=new T2(1,_D3,_D2),_D5=function(_D6){var _D7=new T(function(){return B(A1(_D6,_ui));}),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){return B(A1(_D6,new T1(0,_Db)));});return new T1(0,function(_Dd){return (E(_Dd)==39)?E(_Dc):new T0(2);});};return B(_AW(_Da));}),_De=function(_Df){var _Dg=E(_Df);switch(E(_Dg)){case 39:return new T0(2);case 92:return E(_D9);default:var _Dh=new T(function(){return B(A1(_D6,new T1(0,_Dg)));});return new T1(0,function(_Di){return (E(_Di)==39)?E(_Dh):new T0(2);});}},_Dj=new T(function(){var _Dk=new T(function(){return B(_Cu(_5V,_D6));}),_Dl=new T(function(){var _Dm=new T(function(){var _Dn=new T(function(){var _Do=function(_Dp){var _Dq=E(_Dp),_Dr=u_iswalpha(_Dq);return (E(_Dr)==0)?(E(_Dq)==95)?new T1(1,B(_u4(_CI,function(_Ds){return new F(function(){return A1(_D6,new T1(3,new T2(1,_Dq,_Ds)));});}))):new T0(2):new T1(1,B(_u4(_CI,function(_Dt){return new F(function(){return A1(_D6,new T1(3,new T2(1,_Dq,_Dt)));});})));};return B(_sG(new T1(0,_Do),new T(function(){return new T1(1,B(_tE(_vg,_wm,_D6)));})));}),_Du=function(_Dv){return (!B(_4B(_h7,_Dv,_wo)))?new T0(2):new T1(1,B(_u4(_wp,function(_Dw){var _Dx=new T2(1,_Dv,_Dw);if(!B(_4B(_qe,_Dx,_D4))){return new F(function(){return A1(_D6,new T1(4,_Dx));});}else{return new F(function(){return A1(_D6,new T1(2,_Dx));});}})));};return B(_sG(new T1(0,_Du),_Dn));});return B(_sG(new T1(0,function(_Dy){if(!B(_4B(_h7,_Dy,_CK))){return new T0(2);}else{return new F(function(){return A1(_D6,new T1(2,new T2(1,_Dy,_10)));});}}),_Dm));});return B(_sG(new T1(0,function(_Dz){return (E(_Dz)==34)?E(_Dk):new T0(2);}),_Dl));});return B(_sG(new T1(0,function(_DA){return (E(_DA)==39)?E(new T1(0,_De)):new T0(2);}),_Dj));});return new F(function(){return _sG(new T1(1,function(_DB){return (E(_DB)._==0)?E(_D7):new T0(2);}),_D8);});},_DC=0,_DD=function(_DE,_DF){var _DG=new T(function(){var _DH=new T(function(){var _DI=function(_DJ){var _DK=new T(function(){var _DL=new T(function(){return B(A1(_DF,_DJ));});return B(_D5(function(_DM){var _DN=E(_DM);return (_DN._==2)?(!B(_qJ(_DN.a,_tj)))?new T0(2):E(_DL):new T0(2);}));}),_DO=function(_DP){return E(_DK);};return new T1(1,function(_DQ){return new F(function(){return A2(_BM,_DQ,_DO);});});};return B(A2(_DE,_DC,_DI));});return B(_D5(function(_DR){var _DS=E(_DR);return (_DS._==2)?(!B(_qJ(_DS.a,_ti)))?new T0(2):E(_DH):new T0(2);}));}),_DT=function(_DU){return E(_DG);};return function(_DV){return new F(function(){return A2(_BM,_DV,_DT);});};},_DW=function(_DX,_DY){var _DZ=function(_E0){var _E1=new T(function(){return B(A1(_DX,_E0));}),_E2=function(_E3){return new F(function(){return _sG(B(A1(_E1,_E3)),new T(function(){return new T1(1,B(_DD(_DZ,_E3)));}));});};return E(_E2);},_E4=new T(function(){return B(A1(_DX,_DY));}),_E5=function(_E6){return new F(function(){return _sG(B(A1(_E4,_E6)),new T(function(){return new T1(1,B(_DD(_DZ,_E6)));}));});};return E(_E5);},_E7=0,_E8=function(_E9,_Ea){return new F(function(){return A1(_Ea,_E7);});},_Eb=new T(function(){return B(unCStr("Fr"));}),_Ec=new T2(0,_Eb,_E8),_Ed=1,_Ee=function(_Ef,_Eg){return new F(function(){return A1(_Eg,_Ed);});},_Eh=new T(function(){return B(unCStr("Bl"));}),_Ei=new T2(0,_Eh,_Ee),_Ej=2,_Ek=function(_El,_Em){return new F(function(){return A1(_Em,_Ej);});},_En=new T(function(){return B(unCStr("Ex"));}),_Eo=new T2(0,_En,_Ek),_Ep=3,_Eq=function(_Er,_Es){return new F(function(){return A1(_Es,_Ep);});},_Et=new T(function(){return B(unCStr("Mv"));}),_Eu=new T2(0,_Et,_Eq),_Ev=4,_Ew=function(_Ex,_Ey){return new F(function(){return A1(_Ey,_Ev);});},_Ez=new T(function(){return B(unCStr("Pn"));}),_EA=new T2(0,_Ez,_Ew),_EB=8,_EC=function(_ED,_EE){return new F(function(){return A1(_EE,_EB);});},_EF=new T(function(){return B(unCStr("DF"));}),_EG=new T2(0,_EF,_EC),_EH=new T2(1,_EG,_10),_EI=7,_EJ=function(_EK,_EL){return new F(function(){return A1(_EL,_EI);});},_EM=new T(function(){return B(unCStr("DB"));}),_EN=new T2(0,_EM,_EJ),_EO=new T2(1,_EN,_EH),_EP=6,_EQ=function(_ER,_ES){return new F(function(){return A1(_ES,_EP);});},_ET=new T(function(){return B(unCStr("Cm"));}),_EU=new T2(0,_ET,_EQ),_EV=new T2(1,_EU,_EO),_EW=5,_EX=function(_EY,_EZ){return new F(function(){return A1(_EZ,_EW);});},_F0=new T(function(){return B(unCStr("Wn"));}),_F1=new T2(0,_F0,_EX),_F2=new T2(1,_F1,_EV),_F3=new T2(1,_EA,_F2),_F4=new T2(1,_Eu,_F3),_F5=new T2(1,_Eo,_F4),_F6=new T2(1,_Ei,_F5),_F7=new T2(1,_Ec,_F6),_F8=function(_F9,_Fa,_Fb){var _Fc=E(_F9);if(!_Fc._){return new T0(2);}else{var _Fd=E(_Fc.a),_Fe=_Fd.a,_Ff=new T(function(){return B(A2(_Fd.b,_Fa,_Fb));}),_Fg=new T(function(){return B(_D5(function(_Fh){var _Fi=E(_Fh);switch(_Fi._){case 3:return (!B(_qJ(_Fe,_Fi.a)))?new T0(2):E(_Ff);case 4:return (!B(_qJ(_Fe,_Fi.a)))?new T0(2):E(_Ff);default:return new T0(2);}}));}),_Fj=function(_Fk){return E(_Fg);};return new F(function(){return _sG(new T1(1,function(_Fl){return new F(function(){return A2(_BM,_Fl,_Fj);});}),new T(function(){return B(_F8(_Fc.b,_Fa,_Fb));}));});}},_Fm=function(_Fn,_Fo){return new F(function(){return _F8(_F7,_Fn,_Fo);});},_Fp=function(_Fq){var _Fr=function(_Fs){return E(new T2(3,_Fq,_tv));};return new T1(1,function(_Ft){return new F(function(){return A2(_BM,_Ft,_Fr);});});},_Fu=new T(function(){return B(A3(_DW,_Fm,_DC,_Fp));}),_Fv=new T(function(){return B(unCStr("empty"));}),_Fw=new T2(1,_Fv,_10),_Fx=new T(function(){return B(err(_sp));}),_Fy=new T(function(){return B(err(_sr));}),_Fz=function(_FA,_FB){var _FC=function(_FD,_FE){var _FF=function(_FG){return new F(function(){return A1(_FE,new T(function(){return  -E(_FG);}));});},_FH=new T(function(){return B(_D5(function(_FI){return new F(function(){return A3(_FA,_FI,_FD,_FF);});}));}),_FJ=function(_FK){return E(_FH);},_FL=function(_FM){return new F(function(){return A2(_BM,_FM,_FJ);});},_FN=new T(function(){return B(_D5(function(_FO){var _FP=E(_FO);if(_FP._==4){var _FQ=E(_FP.a);if(!_FQ._){return new F(function(){return A3(_FA,_FP,_FD,_FE);});}else{if(E(_FQ.a)==45){if(!E(_FQ.b)._){return E(new T1(1,_FL));}else{return new F(function(){return A3(_FA,_FP,_FD,_FE);});}}else{return new F(function(){return A3(_FA,_FP,_FD,_FE);});}}}else{return new F(function(){return A3(_FA,_FP,_FD,_FE);});}}));}),_FR=function(_FS){return E(_FN);};return new T1(1,function(_FT){return new F(function(){return A2(_BM,_FT,_FR);});});};return new F(function(){return _DW(_FC,_FB);});},_FU=function(_FV){var _FW=E(_FV);if(!_FW._){var _FX=_FW.b,_FY=new T(function(){return B(_vy(new T(function(){return B(_aR(E(_FW.a)));}),new T(function(){return B(_mt(_FX,0));},1),B(_6e(_vo,_FX))));});return new T1(1,_FY);}else{return (E(_FW.b)._==0)?(E(_FW.c)._==0)?new T1(1,new T(function(){return B(_vP(_vn,_FW.a));})):__Z:__Z;}},_FZ=function(_G0,_G1){return new T0(2);},_G2=function(_G3){var _G4=E(_G3);if(_G4._==5){var _G5=B(_FU(_G4.a));if(!_G5._){return E(_FZ);}else{var _G6=new T(function(){return B(_ba(_G5.a));});return function(_G7,_G8){return new F(function(){return A1(_G8,_G6);});};}}else{return E(_FZ);}},_G9=new T(function(){return B(A3(_Fz,_G2,_DC,_Fp));}),_Ga=new T2(1,_G,_10),_Gb=function(_Gc){while(1){var _Gd=B((function(_Ge){var _Gf=E(_Ge);if(!_Gf._){return __Z;}else{var _Gg=_Gf.b,_Gh=E(_Gf.a);if(!E(_Gh.b)._){return new T2(1,_Gh.a,new T(function(){return B(_Gb(_Gg));}));}else{_Gc=_Gg;return __continue;}}})(_Gc));if(_Gd!=__continue){return _Gd;}}},_Gi=function(_Gj,_Gk){while(1){var _Gl=E(_Gj);if(!_Gl._){return E(_Gk);}else{var _Gm=new T2(1,_Gl.a,_Gk);_Gj=_Gl.b;_Gk=_Gm;continue;}}},_Gn=function(_Go,_Gp){var _Gq=E(_Go);if(!_Gq._){return __Z;}else{var _Gr=E(_Gp);return (_Gr._==0)?__Z:new T2(1,new T2(0,_Gq.a,_Gr.a),new T(function(){return B(_Gn(_Gq.b,_Gr.b));}));}},_Gs=function(_Gt,_Gu,_Gv){while(1){var _Gw=B((function(_Gx,_Gy,_Gz){var _GA=E(_Gz);if(!_GA._){return E(_Gy);}else{var _GB=_GA.a,_GC=_GA.b,_GD=B(_sj(_qe,_GB,_s5));if(!_GD._){var _GE=E(_Fw);}else{var _GE=E(_GD.a);}if(!B(_qO(_GE,_Fw))){var _GF=B(_Gi(B(_Gn(B(_Gi(_Gy,_10)),new T(function(){return B(_Gi(_GE,_10));},1))),_10)),_GG=B(_mt(_GF,0)),_GH=new T(function(){var _GI=new T(function(){return B(_6e(_se,_GF));});if(!B(_qJ(_GB,_rH))){if(!B(_qJ(_GB,_rG))){if(!B(_qJ(_GB,_rF))){if(!B(_qJ(_GB,_rJ))){if(!B(_qJ(_GB,_rI))){return __Z;}else{var _GJ=E(_GI);if(!_GJ._){return E(_nh);}else{if(!B(_qJ(_GJ.a,_st))){if(!B(_qJ(B(_6R(_GJ,1)),_st))){return E(_su);}else{return E(_st);}}else{return E(_st);}}}}else{var _GK=new T(function(){var _GL=B(_Gb(B(_sw(_Fu,new T(function(){return B(_6R(_GI,1));})))));if(!_GL._){return E(_sq);}else{if(!E(_GL.b)._){return E(_GL.a);}else{return E(_ss);}}}),_GM=B(_rt(new T2(0,new T(function(){var _GN=E(_GI);if(!_GN._){return E(_nh);}else{var _GO=E(_GN.a);if(!_GO._){return E(_nh);}else{return E(_GO.a);}}}),_GK),E(E(_Gx).a).b)),_GP=new T(function(){return B(A3(_s8,_6x,new T2(1,function(_GQ){return new F(function(){return _I(0,E(_GM.a),_GQ);});},new T2(1,function(_GR){return new F(function(){return _I(0,E(_GM.b),_GR);});},_10)),_Ga));});return new T2(1,_H,_GP);}}else{var _GS=new T(function(){var _GT=B(_Gb(B(_sw(_G9,new T(function(){return B(_sg(_GI));})))));if(!_GT._){return E(_Fx);}else{if(!E(_GT.b)._){var _GU=B(_Gb(B(_sw(_G9,new T(function(){return B(_6R(_GI,1));})))));if(!_GU._){return E(_Fx);}else{if(!E(_GU.b)._){return E(B(_6R(B(_6R(E(E(_Gx).a).b,E(_GU.a))),E(_GT.a))).a);}else{return E(_Fy);}}}else{return E(_Fy);}}});return new T2(1,_GS,_10);}}else{var _GV=E(_GI);if(!_GV._){return E(_nh);}else{if(!B(_qJ(_GV.a,B(_6R(_GV,1))))){return E(_su);}else{return E(_st);}}}}else{var _GW=E(_GI);if(!_GW._){return E(_nh);}else{if(!B(_qJ(_GW.a,_st))){return E(_su);}else{if(!B(_qJ(B(_6R(_GW,1)),_st))){return E(_su);}else{return E(_st);}}}}});if(_GG>0){var _GX=_Gx,_GY=B(_y(B(_Gi(B(_rz(_GG,B(_Gi(_Gy,_10)))),_10)),new T2(1,_GH,_10)));_Gt=_GX;_Gu=_GY;_Gv=_GC;return __continue;}else{var _GX=_Gx,_GY=B(_y(B(_Gi(B(_Gi(_Gy,_10)),_10)),new T2(1,_GH,_10)));_Gt=_GX;_Gu=_GY;_Gv=_GC;return __continue;}}else{var _GX=_Gx,_GY=B(_y(_Gy,new T2(1,_GB,_10)));_Gt=_GX;_Gu=_GY;_Gv=_GC;return __continue;}}})(_Gt,_Gu,_Gv));if(_Gw!=__continue){return _Gw;}}},_GZ=new T(function(){return B(_e7("Event.hs:(84,1)-(88,73)|function addMemory"));}),_H0=function(_H1,_H2){var _H3=E(_H1),_H4=E(_H2);if(!B(_qJ(_H3.a,_H4.a))){return false;}else{return new F(function(){return _qJ(_H3.b,_H4.b);});}},_H5=new T2(1,_10,_10),_H6=function(_H7,_H8,_H9){var _Ha=E(_H9);if(!_Ha._){return new T2(0,new T2(1,_H8,_10),_10);}else{var _Hb=E(_H8),_Hc=new T(function(){var _Hd=B(_H6(_H7,_Ha.a,_Ha.b));return new T2(0,_Hd.a,_Hd.b);});return (_H7!=_Hb)?new T2(0,new T2(1,_Hb,new T(function(){return E(E(_Hc).a);})),new T(function(){return E(E(_Hc).b);})):new T2(0,_10,new T2(1,new T(function(){return E(E(_Hc).a);}),new T(function(){return E(E(_Hc).b);})));}},_He=32,_Hf=function(_Hg){var _Hh=E(_Hg);if(!_Hh._){return __Z;}else{var _Hi=new T(function(){return B(_y(_Hh.a,new T(function(){return B(_Hf(_Hh.b));},1)));});return new T2(1,_He,_Hi);}},_Hj=function(_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz){while(1){var _HA=B((function(_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_HQ){var _HR=E(_HB);if(!_HR._){return {_:0,a:_HC,b:_HD,c:_HE,d:_HF,e:_HG,f:_HH,g:_HI,h:_HJ,i:_HK,j:_HL,k:_HM,l:_HN,m:_HO,n:_HP,o:_HQ};}else{var _HS=_HR.a,_HT=E(_HR.b);if(!_HT._){return E(_GZ);}else{var _HU=new T(function(){var _HV=E(_HT.a);if(!_HV._){var _HW=B(_Gs({_:0,a:E(_HC),b:E(_HD),c:E(_HE),d:E(_HF),e:E(_HG),f:E(_HH),g:E(_HI),h:_HJ,i:_HK,j:_HL,k:_HM,l:E(_HN),m:_HO,n:E(_HP),o:E(_HQ)},_10,_H5));if(!_HW._){return __Z;}else{return B(_y(_HW.a,new T(function(){return B(_Hf(_HW.b));},1)));}}else{var _HX=_HV.a,_HY=E(_HV.b);if(!_HY._){var _HZ=B(_Gs({_:0,a:E(_HC),b:E(_HD),c:E(_HE),d:E(_HF),e:E(_HG),f:E(_HH),g:E(_HI),h:_HJ,i:_HK,j:_HL,k:_HM,l:E(_HN),m:_HO,n:E(_HP),o:E(_HQ)},_10,new T2(1,new T2(1,_HX,_10),_10)));if(!_HZ._){return __Z;}else{return B(_y(_HZ.a,new T(function(){return B(_Hf(_HZ.b));},1)));}}else{var _I0=E(_HX),_I1=new T(function(){var _I2=B(_H6(95,_HY.a,_HY.b));return new T2(0,_I2.a,_I2.b);});if(E(_I0)==95){var _I3=B(_Gs({_:0,a:E(_HC),b:E(_HD),c:E(_HE),d:E(_HF),e:E(_HG),f:E(_HH),g:E(_HI),h:_HJ,i:_HK,j:_HL,k:_HM,l:E(_HN),m:_HO,n:E(_HP),o:E(_HQ)},_10,new T2(1,_10,new T2(1,new T(function(){return E(E(_I1).a);}),new T(function(){return E(E(_I1).b);})))));if(!_I3._){return __Z;}else{return B(_y(_I3.a,new T(function(){return B(_Hf(_I3.b));},1)));}}else{var _I4=B(_Gs({_:0,a:E(_HC),b:E(_HD),c:E(_HE),d:E(_HF),e:E(_HG),f:E(_HH),g:E(_HI),h:_HJ,i:_HK,j:_HL,k:_HM,l:E(_HN),m:_HO,n:E(_HP),o:E(_HQ)},_10,new T2(1,new T2(1,_I0,new T(function(){return E(E(_I1).a);})),new T(function(){return E(E(_I1).b);}))));if(!_I4._){return __Z;}else{return B(_y(_I4.a,new T(function(){return B(_Hf(_I4.b));},1)));}}}}}),_I5=_HC,_I6=_HD,_I7=_HE,_I8=_HF,_I9=_HG,_Ia=_HI,_Ib=_HJ,_Ic=_HK,_Id=_HL,_Ie=_HM,_If=_HN,_Ig=_HO,_Ih=_HP,_Ii=_HQ;_Hk=_HT.b;_Hl=_I5;_Hm=_I6;_Hn=_I7;_Ho=_I8;_Hp=_I9;_Hq=new T2(1,new T2(0,_HS,_HU),new T(function(){var _Ij=B(_sj(_qe,_HS,_HH));if(!_Ij._){var _Ik=__Z;}else{var _Ik=E(_Ij.a);}if(!B(_qJ(_Ik,_10))){return B(_qC(_H0,new T2(0,_HS,_Ik),_HH));}else{return E(_HH);}}));_Hr=_Ia;_Hs=_Ib;_Ht=_Ic;_Hu=_Id;_Hv=_Ie;_Hw=_If;_Hx=_Ig;_Hy=_Ih;_Hz=_Ii;return __continue;}}})(_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz));if(_HA!=__continue){return _HA;}}},_Il=function(_Im){var _In=E(_Im);if(!_In._){return new T2(0,_10,_10);}else{var _Io=E(_In.a),_Ip=new T(function(){var _Iq=B(_Il(_In.b));return new T2(0,_Iq.a,_Iq.b);});return new T2(0,new T2(1,_Io.a,new T(function(){return E(E(_Ip).a);})),new T2(1,_Io.b,new T(function(){return E(E(_Ip).b);})));}},_Ir=function(_Is,_It,_Iu){while(1){var _Iv=B((function(_Iw,_Ix,_Iy){var _Iz=E(_Iy);if(!_Iz._){return __Z;}else{var _IA=_Iz.b;if(_Ix!=E(_Iz.a)){var _IB=_Iw+1|0,_IC=_Ix;_Is=_IB;_It=_IC;_Iu=_IA;return __continue;}else{return new T2(1,_Iw,new T(function(){return B(_Ir(_Iw+1|0,_Ix,_IA));}));}}})(_Is,_It,_Iu));if(_Iv!=__continue){return _Iv;}}},_ID=function(_IE,_IF,_IG){var _IH=E(_IG);if(!_IH._){return __Z;}else{var _II=_IH.b,_IJ=E(_IF);if(_IJ!=E(_IH.a)){return new F(function(){return _Ir(_IE+1|0,_IJ,_II);});}else{return new T2(1,_IE,new T(function(){return B(_Ir(_IE+1|0,_IJ,_II));}));}}},_IK=function(_IL,_IM,_IN,_IO){var _IP=E(_IO);if(!_IP._){return __Z;}else{var _IQ=_IP.b;return (!B(_4B(_3M,_IL,_IN)))?new T2(1,_IP.a,new T(function(){return B(_IK(_IL+1|0,_IM,_IN,_IQ));})):new T2(1,_IM,new T(function(){return B(_IK(_IL+1|0,_IM,_IN,_IQ));}));}},_IR=function(_IS,_IT,_IU){var _IV=E(_IU);if(!_IV._){return __Z;}else{var _IW=new T(function(){var _IX=B(_Il(_IV.a)),_IY=_IX.a,_IZ=new T(function(){return B(_IK(0,_IT,new T(function(){return B(_ID(0,_IS,_IY));}),_IX.b));},1);return B(_Gn(_IY,_IZ));});return new T2(1,_IW,new T(function(){return B(_IR(_IS,_IT,_IV.b));}));}},_J0=new T(function(){return B(_e7("Event.hs:(57,1)-(60,93)|function changeType"));}),_J1=new T(function(){return B(_e7("Event.hs:54:16-116|case"));}),_J2=new T(function(){return B(unCStr("Wn"));}),_J3=new T(function(){return B(unCStr("Pn"));}),_J4=new T(function(){return B(unCStr("Mv"));}),_J5=new T(function(){return B(unCStr("Fr"));}),_J6=new T(function(){return B(unCStr("Ex"));}),_J7=new T(function(){return B(unCStr("DF"));}),_J8=new T(function(){return B(unCStr("DB"));}),_J9=new T(function(){return B(unCStr("Cm"));}),_Ja=new T(function(){return B(unCStr("Bl"));}),_Jb=function(_Jc){return (!B(_qJ(_Jc,_Ja)))?(!B(_qJ(_Jc,_J9)))?(!B(_qJ(_Jc,_J8)))?(!B(_qJ(_Jc,_J7)))?(!B(_qJ(_Jc,_J6)))?(!B(_qJ(_Jc,_J5)))?(!B(_qJ(_Jc,_J4)))?(!B(_qJ(_Jc,_J3)))?(!B(_qJ(_Jc,_J2)))?E(_J1):5:4:3:0:2:8:7:6:1;},_Jd=function(_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt){while(1){var _Ju=B((function(_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK){var _JL=E(_Jv);if(!_JL._){return {_:0,a:_Jw,b:_Jx,c:_Jy,d:_Jz,e:_JA,f:_JB,g:_JC,h:_JD,i:_JE,j:_JF,k:_JG,l:_JH,m:_JI,n:_JJ,o:_JK};}else{var _JM=E(_JL.b);if(!_JM._){return E(_J0);}else{var _JN=E(_Jw),_JO=_Jx,_JP=_Jy,_JQ=_Jz,_JR=_JA,_JS=_JB,_JT=_JC,_JU=_JD,_JV=_JE,_JW=_JF,_JX=_JG,_JY=_JH,_JZ=_JI,_K0=_JJ,_K1=_JK;_Je=_JM.b;_Jf={_:0,a:E(_JN.a),b:E(B(_IR(new T(function(){return B(_sg(_JL.a));}),new T(function(){return B(_Jb(_JM.a));}),_JN.b))),c:_JN.c,d:_JN.d,e:_JN.e,f:_JN.f,g:E(_JN.g),h:E(_JN.h),i:E(_JN.i)};_Jg=_JO;_Jh=_JP;_Ji=_JQ;_Jj=_JR;_Jk=_JS;_Jl=_JT;_Jm=_JU;_Jn=_JV;_Jo=_JW;_Jp=_JX;_Jq=_JY;_Jr=_JZ;_Js=_K0;_Jt=_K1;return __continue;}}})(_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt));if(_Ju!=__continue){return _Ju;}}},_K2=function(_K3,_K4){while(1){var _K5=E(_K4);if(!_K5._){return __Z;}else{var _K6=_K5.b,_K7=E(_K3);if(_K7==1){return E(_K6);}else{_K3=_K7-1|0;_K4=_K6;continue;}}}},_K8=function(_K9,_Ka){while(1){var _Kb=E(_Ka);if(!_Kb._){return __Z;}else{var _Kc=_Kb.b,_Kd=E(_K9);if(_Kd==1){return E(_Kc);}else{_K9=_Kd-1|0;_Ka=_Kc;continue;}}}},_Ke=function(_Kf,_Kg,_Kh,_Ki,_Kj){var _Kk=new T(function(){var _Kl=E(_Kf),_Km=new T(function(){return B(_6R(_Kj,_Kg));}),_Kn=new T2(1,new T2(0,_Kh,_Ki),new T(function(){var _Ko=_Kl+1|0;if(_Ko>0){return B(_K8(_Ko,_Km));}else{return E(_Km);}}));if(0>=_Kl){return E(_Kn);}else{var _Kp=function(_Kq,_Kr){var _Ks=E(_Kq);if(!_Ks._){return E(_Kn);}else{var _Kt=_Ks.a,_Ku=E(_Kr);return (_Ku==1)?new T2(1,_Kt,_Kn):new T2(1,_Kt,new T(function(){return B(_Kp(_Ks.b,_Ku-1|0));}));}};return B(_Kp(_Km,_Kl));}}),_Kv=new T2(1,_Kk,new T(function(){var _Kw=_Kg+1|0;if(_Kw>0){return B(_K2(_Kw,_Kj));}else{return E(_Kj);}}));if(0>=_Kg){return E(_Kv);}else{var _Kx=function(_Ky,_Kz){var _KA=E(_Ky);if(!_KA._){return E(_Kv);}else{var _KB=_KA.a,_KC=E(_Kz);return (_KC==1)?new T2(1,_KB,_Kv):new T2(1,_KB,new T(function(){return B(_Kx(_KA.b,_KC-1|0));}));}};return new F(function(){return _Kx(_Kj,_Kg);});}},_KD=32,_KE=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_KF=function(_KG){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_KG,_KE));})),_dt);});},_KH=function(_KI){return new F(function(){return _KF("Event.hs:40:27-53|(x\' : y\' : _)");});},_KJ=new T(function(){return B(_KH(_));}),_KK=function(_KL,_KM,_KN,_KO,_KP,_KQ,_KR,_KS,_KT,_KU,_KV,_KW,_KX,_KY,_KZ,_L0){while(1){var _L1=B((function(_L2,_L3,_L4,_L5,_L6,_L7,_L8,_L9,_La,_Lb,_Lc,_Ld,_Le,_Lf,_Lg,_Lh){var _Li=E(_L2);if(!_Li._){return {_:0,a:_L3,b:_L4,c:_L5,d:_L6,e:_L7,f:_L8,g:_L9,h:_La,i:_Lb,j:_Lc,k:_Ld,l:_Le,m:_Lf,n:_Lg,o:_Lh};}else{var _Lj=E(_L3),_Lk=new T(function(){var _Ll=E(_Li.a);if(!_Ll._){return E(_KJ);}else{var _Lm=E(_Ll.b);if(!_Lm._){return E(_KJ);}else{var _Ln=_Lm.a,_Lo=_Lm.b,_Lp=E(_Ll.a);if(E(_Lp)==44){return new T2(0,_10,new T(function(){return E(B(_H6(44,_Ln,_Lo)).a);}));}else{var _Lq=B(_H6(44,_Ln,_Lo)),_Lr=E(_Lq.b);if(!_Lr._){return E(_KJ);}else{return new T2(0,new T2(1,_Lp,_Lq.a),_Lr.a);}}}}}),_Ls=B(_Gb(B(_sw(_G9,new T(function(){return E(E(_Lk).b);})))));if(!_Ls._){return E(_Fx);}else{if(!E(_Ls.b)._){var _Lt=new T(function(){var _Lu=B(_Gb(B(_sw(_G9,new T(function(){return E(E(_Lk).a);})))));if(!_Lu._){return E(_Fx);}else{if(!E(_Lu.b)._){return E(_Lu.a);}else{return E(_Fy);}}},1),_Lv=_L4,_Lw=_L5,_Lx=_L6,_Ly=_L7,_Lz=_L8,_LA=_L9,_LB=_La,_LC=_Lb,_LD=_Lc,_LE=_Ld,_LF=_Le,_LG=_Lf,_LH=_Lg,_LI=_Lh;_KL=_Li.b;_KM={_:0,a:E(_Lj.a),b:E(B(_Ke(_Lt,E(_Ls.a),_KD,_E7,_Lj.b))),c:_Lj.c,d:_Lj.d,e:_Lj.e,f:_Lj.f,g:E(_Lj.g),h:E(_Lj.h),i:E(_Lj.i)};_KN=_Lv;_KO=_Lw;_KP=_Lx;_KQ=_Ly;_KR=_Lz;_KS=_LA;_KT=_LB;_KU=_LC;_KV=_LD;_KW=_LE;_KX=_LF;_KY=_LG;_KZ=_LH;_L0=_LI;return __continue;}else{return E(_Fy);}}}})(_KL,_KM,_KN,_KO,_KP,_KQ,_KR,_KS,_KT,_KU,_KV,_KW,_KX,_KY,_KZ,_L0));if(_L1!=__continue){return _L1;}}},_LJ=function(_LK,_LL,_LM){var _LN=E(_LM);return (_LN._==0)?0:(!B(A3(_4z,_LK,_LL,_LN.a)))?1+B(_LJ(_LK,_LL,_LN.b))|0:0;},_LO=function(_LP,_LQ){while(1){var _LR=E(_LQ);if(!_LR._){return __Z;}else{var _LS=_LR.b,_LT=E(_LP);if(_LT==1){return E(_LS);}else{_LP=_LT-1|0;_LQ=_LS;continue;}}}},_LU=function(_LV,_LW){var _LX=new T(function(){var _LY=_LV+1|0;if(_LY>0){return B(_LO(_LY,_LW));}else{return E(_LW);}});if(0>=_LV){return E(_LX);}else{var _LZ=function(_M0,_M1){var _M2=E(_M0);if(!_M2._){return E(_LX);}else{var _M3=_M2.a,_M4=E(_M1);return (_M4==1)?new T2(1,_M3,_LX):new T2(1,_M3,new T(function(){return B(_LZ(_M2.b,_M4-1|0));}));}};return new F(function(){return _LZ(_LW,_LV);});}},_M5=function(_M6,_M7){return new F(function(){return _LU(E(_M6),_M7);});},_M8= -1,_M9=function(_Ma,_Mb,_Mc,_Md,_Me,_Mf,_Mg,_Mh,_Mi,_Mj,_Mk,_Ml,_Mm,_Mn,_Mo,_Mp){while(1){var _Mq=B((function(_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MG){var _MH=E(_Mr);if(!_MH._){return {_:0,a:_Ms,b:_Mt,c:_Mu,d:_Mv,e:_Mw,f:_Mx,g:_My,h:_Mz,i:_MA,j:_MB,k:_MC,l:_MD,m:_ME,n:_MF,o:_MG};}else{var _MI=_MH.a,_MJ=B(_6e(_se,_Mv)),_MK=B(_4B(_qe,_MI,_MJ)),_ML=new T(function(){if(!E(_MK)){return E(_M8);}else{return B(_LJ(_qe,_MI,_MJ));}});if(!E(_MK)){var _MM=E(_Mv);}else{var _MM=B(_M5(_ML,_Mv));}if(!E(_MK)){var _MN=E(_Mw);}else{var _MN=B(_M5(_ML,_Mw));}var _MO=_Ms,_MP=_Mt,_MQ=_Mu,_MR=_Mx,_MS=_My,_MT=_Mz,_MU=_MA,_MV=_MB,_MW=_MC,_MX=_MD,_MY=_ME,_MZ=_MF,_N0=_MG;_Ma=_MH.b;_Mb=_MO;_Mc=_MP;_Md=_MQ;_Me=_MM;_Mf=_MN;_Mg=_MR;_Mh=_MS;_Mi=_MT;_Mj=_MU;_Mk=_MV;_Ml=_MW;_Mm=_MX;_Mn=_MY;_Mo=_MZ;_Mp=_N0;return __continue;}})(_Ma,_Mb,_Mc,_Md,_Me,_Mf,_Mg,_Mh,_Mi,_Mj,_Mk,_Ml,_Mm,_Mn,_Mo,_Mp));if(_Mq!=__continue){return _Mq;}}},_N1=function(_N2){var _N3=E(_N2);if(!_N3._){return new T2(0,_10,_10);}else{var _N4=E(_N3.a),_N5=new T(function(){var _N6=B(_N1(_N3.b));return new T2(0,_N6.a,_N6.b);});return new T2(0,new T2(1,_N4.a,new T(function(){return E(E(_N5).a);})),new T2(1,_N4.b,new T(function(){return E(E(_N5).b);})));}},_N7=function(_N8){return new F(function(){return _KF("Event.hs:101:28-52|(c : d : _)");});},_N9=new T(function(){return B(_N7(_));}),_Na=function(_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx){while(1){var _Ny=B((function(_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV){var _NW=E(_Nz);if(!_NW._){return {_:0,a:E(_NA),b:E(_NB),c:E(_NC),d:E(_ND),e:E(_NE),f:E(_NF),g:E(_NG),h:_NH,i:_NI,j:_NJ,k:_NK,l:E(_NL),m:_NM,n:E({_:0,a:E(_NN),b:E(_NO),c:E(_NP),d:E(_ws),e:E(_NR),f:E(_NS),g:E(_ws),h:E(_NU)}),o:E(_NV)};}else{var _NX=new T(function(){var _NY=E(_NW.a);if(!_NY._){return E(_N9);}else{var _NZ=E(_NY.b);if(!_NZ._){return E(_N9);}else{var _O0=_NZ.a,_O1=_NZ.b,_O2=E(_NY.a);if(E(_O2)==44){return new T2(0,_10,new T(function(){return E(B(_H6(44,_O0,_O1)).a);}));}else{var _O3=B(_H6(44,_O0,_O1)),_O4=E(_O3.b);if(!_O4._){return E(_N9);}else{return new T2(0,new T2(1,_O2,_O3.a),_O4.a);}}}}}),_O5=_NA,_O6=_NB,_O7=_NC,_O8=_ND,_O9=_NE,_Oa=_NF,_Ob=_NG,_Oc=_NH,_Od=_NI,_Oe=_NJ,_Of=_NK,_Og=B(_y(_NL,new T2(1,new T2(0,new T(function(){return E(E(_NX).a);}),new T(function(){return E(E(_NX).b);})),_10))),_Oh=_NM,_Oi=_NN,_Oj=_NO,_Ok=_NP,_Ol=_NQ,_Om=_NR,_On=_NS,_Oo=_NT,_Op=_NU,_Oq=_NV;_Nb=_NW.b;_Nc=_O5;_Nd=_O6;_Ne=_O7;_Nf=_O8;_Ng=_O9;_Nh=_Oa;_Ni=_Ob;_Nj=_Oc;_Nk=_Od;_Nl=_Oe;_Nm=_Of;_Nn=_Og;_No=_Oh;_Np=_Oi;_Nq=_Oj;_Nr=_Ok;_Ns=_Ol;_Nt=_Om;_Nu=_On;_Nv=_Oo;_Nw=_Op;_Nx=_Oq;return __continue;}})(_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx));if(_Ny!=__continue){return _Ny;}}},_Or=function(_Os){return new F(function(){return _KF("Event.hs:47:27-53|(x\' : y\' : _)");});},_Ot=new T(function(){return B(_Or(_));}),_Ou=function(_Ov){return new F(function(){return _KF("Event.hs:48:27-55|(chs : tps : _)");});},_Ow=new T(function(){return B(_Ou(_));}),_Ox=new T(function(){return B(_e7("Event.hs:(45,1)-(51,83)|function putCell"));}),_Oy=function(_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO){while(1){var _OP=B((function(_OQ,_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY,_OZ,_P0,_P1,_P2,_P3,_P4,_P5){var _P6=E(_OQ);if(!_P6._){return {_:0,a:_OR,b:_OS,c:_OT,d:_OU,e:_OV,f:_OW,g:_OX,h:_OY,i:_OZ,j:_P0,k:_P1,l:_P2,m:_P3,n:_P4,o:_P5};}else{var _P7=E(_P6.b);if(!_P7._){return E(_Ox);}else{var _P8=E(_OR),_P9=new T(function(){var _Pa=E(_P6.a);if(!_Pa._){return E(_Ot);}else{var _Pb=E(_Pa.b);if(!_Pb._){return E(_Ot);}else{var _Pc=_Pb.a,_Pd=_Pb.b,_Pe=E(_Pa.a);if(E(_Pe)==44){return new T2(0,_10,new T(function(){return E(B(_H6(44,_Pc,_Pd)).a);}));}else{var _Pf=B(_H6(44,_Pc,_Pd)),_Pg=E(_Pf.b);if(!_Pg._){return E(_Ot);}else{return new T2(0,new T2(1,_Pe,_Pf.a),_Pg.a);}}}}}),_Ph=B(_Gb(B(_sw(_G9,new T(function(){return E(E(_P9).b);})))));if(!_Ph._){return E(_Fx);}else{if(!E(_Ph.b)._){var _Pi=new T(function(){var _Pj=E(_P7.a);if(!_Pj._){return E(_Ow);}else{var _Pk=E(_Pj.b);if(!_Pk._){return E(_Ow);}else{var _Pl=_Pk.a,_Pm=_Pk.b,_Pn=E(_Pj.a);if(E(_Pn)==44){return new T2(0,_10,new T(function(){return E(B(_H6(44,_Pl,_Pm)).a);}));}else{var _Po=B(_H6(44,_Pl,_Pm)),_Pp=E(_Po.b);if(!_Pp._){return E(_Ow);}else{return new T2(0,new T2(1,_Pn,_Po.a),_Pp.a);}}}}}),_Pq=new T(function(){var _Pr=B(_Gb(B(_sw(_G9,new T(function(){return E(E(_P9).a);})))));if(!_Pr._){return E(_Fx);}else{if(!E(_Pr.b)._){return E(_Pr.a);}else{return E(_Fy);}}},1),_Ps=_OS,_Pt=_OT,_Pu=_OU,_Pv=_OV,_Pw=_OW,_Px=_OX,_Py=_OY,_Pz=_OZ,_PA=_P0,_PB=_P1,_PC=_P2,_PD=_P3,_PE=_P4,_PF=_P5;_Oz=_P7.b;_OA={_:0,a:E(_P8.a),b:E(B(_Ke(_Pq,E(_Ph.a),new T(function(){return B(_sg(E(_Pi).a));}),new T(function(){return B(_Jb(E(_Pi).b));}),_P8.b))),c:_P8.c,d:_P8.d,e:_P8.e,f:_P8.f,g:E(_P8.g),h:E(_P8.h),i:E(_P8.i)};_OB=_Ps;_OC=_Pt;_OD=_Pu;_OE=_Pv;_OF=_Pw;_OG=_Px;_OH=_Py;_OI=_Pz;_OJ=_PA;_OK=_PB;_OL=_PC;_OM=_PD;_ON=_PE;_OO=_PF;return __continue;}else{return E(_Fy);}}}}})(_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO));if(_OP!=__continue){return _OP;}}},_PG=function(_PH){var _PI=E(_PH);if(!_PI._){return new T2(0,_10,_10);}else{var _PJ=E(_PI.a),_PK=new T(function(){var _PL=B(_PG(_PI.b));return new T2(0,_PL.a,_PL.b);});return new T2(0,new T2(1,_PJ.a,new T(function(){return E(E(_PK).a);})),new T2(1,_PJ.b,new T(function(){return E(E(_PK).b);})));}},_PM=32,_PN=function(_PO,_PP,_PQ,_PR){var _PS=E(_PR);if(!_PS._){return __Z;}else{var _PT=_PS.b;if(!B(_4B(_3M,_PO,_PQ))){var _PU=new T(function(){return B(_PN(new T(function(){return E(_PO)+1|0;}),_PP,_PQ,_PT));});return new T2(1,_PS.a,_PU);}else{var _PV=new T(function(){return B(_PN(new T(function(){return E(_PO)+1|0;}),_PP,_PQ,_PT));});return new T2(1,_PP,_PV);}}},_PW=function(_PX,_PY){var _PZ=E(_PY);if(!_PZ._){return __Z;}else{var _Q0=new T(function(){var _Q1=B(_PG(_PZ.a)),_Q2=_Q1.a,_Q3=new T(function(){return B(_ID(0,_PX,_Q2));});return B(_Gn(B(_PN(_rh,_PM,_Q3,_Q2)),new T(function(){return B(_IK(0,_E7,_Q3,_Q1.b));},1)));});return new T2(1,_Q0,new T(function(){return B(_PW(_PX,_PZ.b));}));}},_Q4=function(_Q5,_Q6){var _Q7=E(_Q6);return (_Q7._==0)?__Z:new T2(1,_Q5,new T(function(){return B(_Q4(_Q7.a,_Q7.b));}));},_Q8=new T(function(){return B(unCStr("init"));}),_Q9=new T(function(){return B(_ne(_Q8));}),_Qa=function(_Qb,_Qc){var _Qd=function(_Qe){var _Qf=E(_Qe);if(!_Qf._){return __Z;}else{var _Qg=new T(function(){return B(_y(new T2(1,_Qb,_10),new T(function(){return B(_Qd(_Qf.b));},1)));},1);return new F(function(){return _y(_Qf.a,_Qg);});}},_Qh=B(_Qd(_Qc));if(!_Qh._){return E(_Q9);}else{return new F(function(){return _Q4(_Qh.a,_Qh.b);});}},_Qi=61,_Qj=46,_Qk=new T(function(){return B(_e7("Event.hs:(91,1)-(97,61)|function makeDecision"));}),_Ql=new T(function(){return B(unCStr("sm"));}),_Qm=new T(function(){return B(unCStr("if"));}),_Qn=new T(function(){return B(unCStr("hm"));}),_Qo=new T(function(){return B(unCStr("cleq"));}),_Qp=new T(function(){return B(unCStr("da"));}),_Qq=new T(function(){return B(unCStr("ct"));}),_Qr=function(_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH){var _QI=function(_QJ,_QK){var _QL=function(_QM){if(!B(_qJ(_QJ,_Qq))){if(!B(_qJ(_QJ,_Qp))){var _QN=function(_QO){if(!B(_qJ(_QJ,_Qo))){var _QP=function(_QQ){if(!B(_qJ(_QJ,_rK))){if(!B(_qJ(_QJ,_Qn))){if(!B(_qJ(_QJ,_Qm))){if(!B(_qJ(_QJ,_Ql))){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{var _QR=E(_QG);return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E({_:0,a:E(_QR.a),b:E(_QR.b),c:E(_QR.c),d:E(_QR.d),e:E(_QR.e),f:E(_QR.f),g:E(_QR.g),h:E(_ws)}),o:E(_QH)};}}else{var _QS=E(_QK);if(!_QS._){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{var _QT=_QS.a,_QU=E(_QS.b);if(!_QU._){return E(_Qk);}else{var _QV=_QU.a,_QW=B(_N1(_Qy)),_QX=_QW.a,_QY=_QW.b,_QZ=function(_R0){if(!B(_4B(_qe,_QT,_QX))){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{if(!B(_qJ(_QV,B(_6R(_QY,B(_LJ(_qe,_QT,_QX))))))){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{return new F(function(){return _Qr(_R0,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}}},_R1=B(_Qa(_Qj,_QU.b));if(!_R1._){return new F(function(){return _QZ(_10);});}else{var _R2=_R1.a,_R3=E(_R1.b);if(!_R3._){return new F(function(){return _QZ(new T2(1,_R2,_10));});}else{var _R4=_R3.a,_R5=_R3.b,_R6=E(_R2);if(E(_R6)==47){if(!B(_4B(_qe,_QT,_QX))){return new F(function(){return _Qr(B(_H6(47,_R4,_R5)).a,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}else{if(!B(_qJ(_QV,B(_6R(_QY,B(_LJ(_qe,_QT,_QX))))))){return new F(function(){return _Qr(B(_H6(47,_R4,_R5)).a,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}else{return new F(function(){return _Qr(_10,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}}}else{if(!B(_4B(_qe,_QT,_QX))){var _R7=E(B(_H6(47,_R4,_R5)).b);if(!_R7._){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{return new F(function(){return _Qr(_R7.a,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}}else{if(!B(_qJ(_QV,B(_6R(_QY,B(_LJ(_qe,_QT,_QX))))))){var _R8=E(B(_H6(47,_R4,_R5)).b);if(!_R8._){return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}else{return new F(function(){return _Qr(_R8.a,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}}else{return new F(function(){return _Qr(new T2(1,_R6,new T(function(){return E(B(_H6(47,_R4,_R5)).a);})),_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH);});}}}}}}}}}else{var _R9=E(_QG);return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E({_:0,a:E(_R9.a),b:E(_R9.b),c:E(_R9.c),d:E(_R9.d),e:E(_R9.e),f:E(_R9.f),g:E(_R9.g),h:E(_wr)}),o:E(_QH)};}}else{var _Ra=E(_QG);return new F(function(){return _Na(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_10,_QF,_Ra.a,_Ra.b,_Ra.c,_Ra.d,_Ra.e,_Ra.f,_Ra.g,_Ra.h,_QH);});}},_Rb=E(_QJ);if(!_Rb._){return new F(function(){return _QP(_);});}else{if(E(_Rb.a)==109){if(!E(_Rb.b)._){var _Rc=B(_Hj(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Rc.a),b:E(_Rc.b),c:E(_Rc.c),d:E(_Rc.d),e:E(_Rc.e),f:E(_Rc.f),g:E(_Rc.g),h:_Rc.h,i:_Rc.i,j:_Rc.j,k:_Rc.k,l:E(_Rc.l),m:_Rc.m,n:E(_Rc.n),o:E(_Rc.o)};}else{return new F(function(){return _QP(_);});}}else{return new F(function(){return _QP(_);});}}}else{var _Rd=E(_Qt);return {_:0,a:E({_:0,a:E(_Rd.a),b:E(B(_PW(_Qi,_Rd.b))),c:_Rd.c,d:_Rd.d,e:_Rd.e,f:_Rd.f,g:E(_Rd.g),h:E(_Rd.h),i:E(_Rd.i)}),b:E(_Qu),c:E(_Qv),d:E(_Qw),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}},_Re=E(_QJ);if(!_Re._){return new F(function(){return _QN(_);});}else{var _Rf=_Re.b;switch(E(_Re.a)){case 99:if(!E(_Rf)._){var _Rg=B(_KK(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Rg.a),b:E(_Rg.b),c:E(_Rg.c),d:E(_Rg.d),e:E(_Rg.e),f:E(_Rg.f),g:E(_Rg.g),h:_Rg.h,i:_Rg.i,j:_Rg.j,k:_Rg.k,l:E(_Rg.l),m:_Rg.m,n:E(_Rg.n),o:E(_Rg.o)};}else{return new F(function(){return _QN(_);});}break;case 112:if(!E(_Rf)._){var _Rh=B(_Oy(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Rh.a),b:E(_Rh.b),c:E(_Rh.c),d:E(_Rh.d),e:E(_Rh.e),f:E(_Rh.f),g:E(_Rh.g),h:_Rh.h,i:_Rh.i,j:_Rh.j,k:_Rh.k,l:E(_Rh.l),m:_Rh.m,n:E(_Rh.n),o:E(_Rh.o)};}else{return new F(function(){return _QN(_);});}break;default:return new F(function(){return _QN(_);});}}}else{return {_:0,a:E(_Qt),b:E(_Qu),c:E(_Qv),d:E(_10),e:E(_Qx),f:E(_Qy),g:E(_Qz),h:_QA,i:_QB,j:_QC,k:_QD,l:E(_QE),m:_QF,n:E(_QG),o:E(_QH)};}}else{var _Ri=B(_Jd(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Ri.a),b:E(_Ri.b),c:E(_Ri.c),d:E(_Ri.d),e:E(_Ri.e),f:E(_Ri.f),g:E(_Ri.g),h:_Ri.h,i:_Ri.i,j:_Ri.j,k:_Ri.k,l:E(_Ri.l),m:_Ri.m,n:E(_Ri.n),o:E(_Ri.o)};}},_Rj=E(_QJ);if(!_Rj._){return new F(function(){return _QL(_);});}else{var _Rk=_Rj.b;switch(E(_Rj.a)){case 100:if(!E(_Rk)._){var _Rl=B(_M9(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Rl.a),b:E(_Rl.b),c:E(_Rl.c),d:E(_Rl.d),e:E(_Rl.e),f:E(_Rl.f),g:E(_Rl.g),h:_Rl.h,i:_Rl.i,j:_Rl.j,k:_Rl.k,l:E(_Rl.l),m:_Rl.m,n:E(_Rl.n),o:E(_Rl.o)};}else{return new F(function(){return _QL(_);});}break;case 101:if(!E(_Rk)._){var _Rm=B(_qh(_QK,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH));return {_:0,a:E(_Rm.a),b:E(_Rm.b),c:E(_Rm.c),d:E(_Rm.d),e:E(_Rm.e),f:E(_Rm.f),g:E(_Rm.g),h:_Rm.h,i:_Rm.i,j:_Rm.j,k:_Rm.k,l:E(_Rm.l),m:_Rm.m,n:E(_Rm.n),o:E(_Rm.o)};}else{return new F(function(){return _QL(_);});}break;default:return new F(function(){return _QL(_);});}}},_Rn=E(_Qs);if(!_Rn._){return new F(function(){return _QI(_10,_10);});}else{var _Ro=_Rn.a,_Rp=E(_Rn.b);if(!_Rp._){return new F(function(){return _QI(new T2(1,_Ro,_10),_10);});}else{var _Rq=E(_Ro),_Rr=new T(function(){var _Rs=B(_H6(46,_Rp.a,_Rp.b));return new T2(0,_Rs.a,_Rs.b);});if(E(_Rq)==46){return new F(function(){return _QI(_10,new T2(1,new T(function(){return E(E(_Rr).a);}),new T(function(){return E(E(_Rr).b);})));});}else{return new F(function(){return _QI(new T2(1,_Rq,new T(function(){return E(E(_Rr).a);})),new T(function(){return E(E(_Rr).b);}));});}}}},_Rt=new T(function(){return B(unCStr("last"));}),_Ru=new T(function(){return B(_ne(_Rt));}),_Rv=32,_Rw=0,_Rx=65306,_Ry=125,_Rz=new T1(0,1),_RA=function(_RB,_RC,_RD,_RE,_RF){var _RG=new T(function(){return E(_RF).h;}),_RH=new T(function(){return E(E(_RF).c);}),_RI=new T(function(){var _RJ=E(_RG)+1|0;if(0>=_RJ){return E(_Rv);}else{var _RK=B(_pO(_RJ,_RH));if(!_RK._){return E(_Rv);}else{return B(_oa(_RK.a,_RK.b,_Ru));}}}),_RL=new T(function(){var _RM=E(_RI);switch(E(_RM)){case 125:return E(_Rv);break;case 12289:return E(_Rv);break;case 12290:return E(_Rv);break;default:return E(_RM);}}),_RN=new T(function(){if(E(_RL)==10){return true;}else{return false;}}),_RO=new T(function(){if(!E(_RN)){if(E(_RL)==12300){return E(_j7);}else{return E(_RF).i;}}else{return E(_Rw);}}),_RP=new T(function(){var _RQ=E(_RC)/28,_RR=_RQ&4294967295;if(_RQ>=_RR){return _RR-1|0;}else{return (_RR-1|0)-1|0;}}),_RS=new T(function(){if(!E(E(_RE).h)){return E(_j8);}else{return 2+(E(E(E(_RF).b).b)+3|0)|0;}}),_RT=new T(function(){if(!E(_RG)){return new T2(0,_RP,_RS);}else{return E(E(_RF).g);}}),_RU=new T(function(){return E(E(_RT).b);}),_RV=new T(function(){return E(E(_RT).a);}),_RW=new T(function(){if(E(_RL)==65306){return true;}else{return false;}}),_RX=new T(function(){if(!E(_RW)){if(!E(_RN)){var _RY=E(_RU);if((_RY+1)*20<=E(_RD)-10){return new T2(0,_RV,_RY+1|0);}else{return new T2(0,new T(function(){return E(_RV)-1|0;}),_RS);}}else{return new T2(0,new T(function(){return E(_RV)-1|0;}),_RS);}}else{return new T2(0,_RV,_RU);}}),_RZ=new T(function(){if(E(E(_RX).a)==1){if(E(_RV)==1){return false;}else{return true;}}else{return false;}}),_S0=new T(function(){if(!E(_RW)){return __Z;}else{return B(_q6(_Rx,E(_RG),_RH));}}),_S1=new T(function(){if(E(_RL)==123){return true;}else{return false;}}),_S2=new T(function(){if(!E(_S1)){return __Z;}else{return B(_q6(_Ry,E(_RG),_RH));}}),_S3=new T(function(){if(!E(_S1)){var _S4=E(_RF),_S5=E(_RE);if(E(_RI)==12290){var _S6=true;}else{var _S6=false;}return {_:0,a:E(_S4.a),b:E(_S4.b),c:E(_S4.c),d:E(_S4.d),e:E(_S4.e),f:E(_S4.f),g:E(_S4.g),h:_S4.h,i:_S4.i,j:_S4.j,k:_S4.k,l:E(_S4.l),m:_S4.m,n:E({_:0,a:E(_S5.a),b:E(_S5.b),c:E(_S5.c),d:E(_S6),e:E(_S5.e),f:E(_S5.f),g:E(_S5.g),h:E(_S5.h)}),o:E(_S4.o)};}else{var _S7=E(_RF),_S8=E(_RE);if(E(_RI)==12290){var _S9=true;}else{var _S9=false;}return B(_Qr(_S2,_S7.a,_S7.b,_S7.c,_S7.d,_S7.e,_S7.f,_S7.g,_S7.h,_S7.i,_S7.j,_S7.k,_S7.l,_S7.m,{_:0,a:E(_S8.a),b:E(_S8.b),c:E(_S8.c),d:E(_S9),e:E(_S8.e),f:E(_S8.f),g:E(_S8.g),h:E(_S8.h)},_S7.o));}}),_Sa=new T(function(){return E(E(_S3).n);}),_Sb=new T(function(){if(!E(_RG)){return E(_Rw);}else{return E(_S3).j;}}),_Sc=new T(function(){var _Sd=E(_S3),_Se=_Sd.a,_Sf=_Sd.b,_Sg=_Sd.c,_Sh=_Sd.d,_Si=_Sd.e,_Sj=_Sd.f,_Sk=_Sd.k,_Sl=_Sd.l,_Sm=_Sd.m,_Sn=_Sd.o;if(!E(_RZ)){var _So=E(_RX);}else{var _So=new T2(0,_RV,_RS);}var _Sp=E(_RG),_Sq=function(_Sr){var _Ss=B(_mt(_RH,0))-1|0,_St=function(_Su){var _Sv=E(_RO);if(!E(_RZ)){var _Sw=E(_Sa);return {_:0,a:E(_Se),b:E(_Sf),c:E(_Sg),d:E(_Sh),e:E(_Si),f:E(_Sj),g:E(_So),h:_Su,i:_Sv,j:E(_Sb),k:_Sk,l:E(_Sl),m:_Sm,n:E({_:0,a:E(_Sw.a),b:E(_Sw.b),c:(_Sp+_Sr|0)<=_Ss,d:E(_Sw.d),e:E(_Sw.e),f:E(_Sw.f),g:E(_Sw.g),h:E(_Sw.h)}),o:E(_Sn)};}else{var _Sx=E(_Sa);return {_:0,a:E(_Se),b:E(_Sf),c:E(_Sg),d:E(_Sh),e:E(_Si),f:E(_Sj),g:E(_So),h:_Su,i:_Sv,j:E(_Sb)+1|0,k:_Sk,l:E(_Sl),m:_Sm,n:E({_:0,a:E(_Sx.a),b:E(_Sx.b),c:(_Sp+_Sr|0)<=_Ss,d:E(_Sx.d),e:E(_Sx.e),f:E(_Sx.f),g:E(_Sx.g),h:E(_Sx.h)}),o:E(_Sn)};}};if((_Sp+_Sr|0)<=_Ss){return new F(function(){return _St(_Sp+_Sr|0);});}else{return new F(function(){return _St(0);});}};if(!E(_RW)){if(!E(_S1)){return B(_Sq(1));}else{return B(_Sq(B(_mt(_S2,0))+2|0));}}else{return B(_Sq(B(_mt(_S0,0))+2|0));}}),_Sy=new T(function(){var _Sz=B(_o4(B(_o2(_RB)))),_SA=new T(function(){var _SB=B(_pv(_RB,E(_RC)/16)),_SC=_SB.a;if(E(_SB.b)>=0){return E(_SC);}else{return B(A3(_oH,_Sz,_SC,new T(function(){return B(A2(_he,_Sz,_Rz));})));}});return B(A3(_oH,_Sz,_SA,new T(function(){return B(A2(_he,_Sz,_hn));})));});return {_:0,a:_RL,b:_RV,c:_RU,d:new T(function(){if(E(_RS)!=E(_RU)){return E(_RV);}else{return E(_RV)+1|0;}}),e:new T(function(){var _SD=E(_RU);if(E(_RS)!=_SD){return _SD-1|0;}else{var _SE=(E(_RD)-10)/20,_SF=_SE&4294967295;if(_SE>=_SF){return _SF;}else{return _SF-1|0;}}}),f:_RS,g:_RG,h:_RH,i:new T(function(){return B(_6R(_j4,E(_RO)));}),j:_S0,k:_RP,l:_Sy,m:_Sb,n:_j9,o:_RW,p:_S1,q:_RZ,r:_Sa,s:_S3,t:_Sc};},_SG=function(_SH){var _SI=E(_SH);if(!_SI._){return new T2(0,_10,_10);}else{var _SJ=E(_SI.a),_SK=new T(function(){var _SL=B(_SG(_SI.b));return new T2(0,_SL.a,_SL.b);});return new T2(0,new T2(1,_SJ.a,new T(function(){return E(E(_SK).a);})),new T2(1,_SJ.b,new T(function(){return E(E(_SK).b);})));}},_SM=42,_SN=32,_SO=function(_SP,_SQ,_SR){var _SS=E(_SP);if(!_SS._){return __Z;}else{var _ST=_SS.a,_SU=_SS.b;if(_SQ!=_SR){var _SV=E(_ST);return (_SV._==0)?E(_nh):(E(_SV.a)==42)?new T2(1,new T2(1,_SN,_SV.b),new T(function(){return B(_SO(_SU,_SQ,_SR+1|0));})):new T2(1,new T2(1,_SN,_SV),new T(function(){return B(_SO(_SU,_SQ,_SR+1|0));}));}else{var _SW=E(_ST);return (_SW._==0)?E(_nh):(E(_SW.a)==42)?new T2(1,new T2(1,_SN,_SW),new T(function(){return B(_SO(_SU,_SQ,_SR+1|0));})):new T2(1,new T2(1,_SM,_SW),new T(function(){return B(_SO(_SU,_SQ,_SR+1|0));}));}}},_SX=new T(function(){return B(unCStr("\n\n"));}),_SY=function(_SZ){var _T0=E(_SZ);if(!_T0._){return __Z;}else{var _T1=new T(function(){return B(_y(_SX,new T(function(){return B(_SY(_T0.b));},1)));},1);return new F(function(){return _y(_T0.a,_T1);});}},_T2=function(_T3,_T4,_T5){var _T6=new T(function(){var _T7=new T(function(){var _T8=E(_T4);if(!_T8._){return B(_SY(_10));}else{var _T9=_T8.a,_Ta=_T8.b,_Tb=E(_T5);if(!_Tb){var _Tc=E(_T9);if(!_Tc._){return E(_nh);}else{if(E(_Tc.a)==42){return B(_SY(new T2(1,new T2(1,_SN,_Tc),new T(function(){return B(_SO(_Ta,0,1));}))));}else{return B(_SY(new T2(1,new T2(1,_SM,_Tc),new T(function(){return B(_SO(_Ta,0,1));}))));}}}else{var _Td=E(_T9);if(!_Td._){return E(_nh);}else{if(E(_Td.a)==42){return B(_SY(new T2(1,new T2(1,_SN,_Td.b),new T(function(){return B(_SO(_Ta,_Tb,1));}))));}else{return B(_SY(new T2(1,new T2(1,_SN,_Td),new T(function(){return B(_SO(_Ta,_Tb,1));}))));}}}}});return B(unAppCStr("\n\n",_T7));},1);return new F(function(){return _y(_T3,_T6);});},_Te=function(_Tf){return E(E(_Tf).c);},_Tg=function(_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp){var _Tq=new T(function(){if(!E(_Ti)){return E(_Tj);}else{return false;}}),_Tr=new T(function(){if(!E(_Ti)){return false;}else{return E(E(_To).g);}}),_Ts=new T(function(){if(!E(_Tr)){if(!E(_Tq)){return B(A2(_he,_Th,_hm));}else{return B(A3(_my,_Th,new T(function(){return B(A3(_my,_Th,_Tm,_Tn));}),new T(function(){return B(A2(_he,_Th,_Rz));})));}}else{return B(A3(_my,_Th,_Tm,_Tn));}}),_Tt=new T(function(){if(!E(_Tr)){if(!E(_Tq)){return __Z;}else{var _Tu=E(_Tk)+1|0;if(0>=_Tu){return __Z;}else{return B(_pO(_Tu,_Tl));}}}else{return B(_T2(B(_Te(_Tp)),new T(function(){return E(B(_SG(E(_Tp).l)).a);},1),new T(function(){return E(_Tp).m;},1)));}});return new T4(0,_Tr,_Tq,_Tt,_Ts);},_Tv=function(_Tw,_Tx,_Ty){var _Tz=E(_Tx),_TA=E(_Ty),_TB=new T(function(){var _TC=B(_ha(_Tw)),_TD=B(_Tv(_Tw,_TA,B(A3(_oH,_TC,new T(function(){return B(A3(_my,_TC,_TA,_TA));}),_Tz))));return new T2(1,_TD.a,_TD.b);});return new T2(0,_Tz,_TB);},_TE=1,_TF=new T(function(){var _TG=B(_Tv(_gb,_hM,_TE));return new T2(1,_TG.a,_TG.b);}),_TH=function(_TI,_TJ,_TK,_TL,_TM,_TN,_TO,_TP,_TQ,_TR,_TS,_TT,_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U6,_U7,_U8,_U9,_Ua,_Ub,_Uc,_Ud,_Ue,_Uf,_Ug,_){var _Uh={_:0,a:E(_U8),b:E(_U9),c:E(_Ua),d:E(_Ub),e:E(_Uc),f:E(_Ud),g:E(_Ue),h:E(_Uf)};if(!E(_Ua)){return {_:0,a:E({_:0,a:E(_TL),b:E(_TM),c:_TN,d:_TO,e:_TP,f:_TQ,g:E(_TR),h:E(_TS),i:E(_TT)}),b:E(new T2(0,_TU,_TV)),c:E(_TW),d:E(_TX),e:E(_TY),f:E(_TZ),g:E(new T2(0,_U0,_U1)),h:_U2,i:_U3,j:_U4,k:_U5,l:E(_U6),m:_U7,n:E(_Uh),o:E(_Ug)};}else{if(!E(_Ub)){var _Ui=B(_RA(_bS,_TJ,_TK,_Uh,{_:0,a:E({_:0,a:E(_TL),b:E(_TM),c:_TN,d:_TO,e:_TP,f:_TQ,g:E(_TR),h:E(_TS),i:E(_TT)}),b:E(new T2(0,_TU,_TV)),c:E(_TW),d:E(_TX),e:E(_TY),f:E(_TZ),g:E(new T2(0,_U0,_U1)),h:_U2,i:_U3,j:_U4,k:_U5,l:E(_U6),m:_U7,n:E(_Uh),o:E(_Ug)})),_Uj=_Ui.d,_Uk=_Ui.e,_Ul=_Ui.f,_Um=_Ui.i,_Un=_Ui.n,_Uo=_Ui.p,_Up=_Ui.q,_Uq=_Ui.s,_Ur=_Ui.t;if(!E(_Ui.o)){var _Us=B(_Tg(_bn,_Uo,_Up,_Ui.g,_Ui.h,_Ui.k,_Ui.m,_Ui.r,_Uq)),_Ut=function(_){if(!E(_Uo)){if(!E(_Up)){var _Uu=B(_iB(E(_TI).a,_Um,_j5,_hM,_Ui.b,_Ui.c,_Ui.a,_));return _Ur;}else{return _Ur;}}else{return _Ur;}},_Uv=function(_Uw){var _Ux=E(_TI),_Uy=_Ux.a,_Uz=_Ux.b,_UA=B(_nQ(_Uy,_Uz,_Ui.l,_Uq,_)),_UB=B(_lo(_Uy,_Uz,_TK,0,_Ul,_Us.d,_Ul,_Us.c,_));return new F(function(){return _Ut(_);});};if(!E(_Us.a)){if(!E(_Us.b)){return new F(function(){return _Ut(_);});}else{return new F(function(){return _Uv(_);});}}else{return new F(function(){return _Uv(_);});}}else{var _UC=E(_Ui.j);if(!_UC._){return _Ur;}else{var _UD=E(_TF);if(!_UD._){return _Ur;}else{var _UE=E(_TI).a,_UF=B(_iB(_UE,_Um,_Un,_UD.a,_Uj,_Uk,_UC.a,_)),_UG=function(_UH,_UI,_){while(1){var _UJ=E(_UH);if(!_UJ._){return _gE;}else{var _UK=E(_UI);if(!_UK._){return _gE;}else{var _UL=B(_iB(_UE,_Um,_Un,_UK.a,_Uj,_Uk,_UJ.a,_));_UH=_UJ.b;_UI=_UK.b;continue;}}}},_UM=B(_UG(_UC.b,_UD.b,_));return _Ur;}}}}else{return {_:0,a:E({_:0,a:E(_TL),b:E(_TM),c:_TN,d:_TO,e:_TP,f:_TQ,g:E(_TR),h:E(_TS),i:E(_TT)}),b:E(new T2(0,_TU,_TV)),c:E(_TW),d:E(_TX),e:E(_TY),f:E(_TZ),g:E(new T2(0,_U0,_U1)),h:_U2,i:_U3,j:_U4,k:_U5,l:E(_U6),m:_U7,n:E(_Uh),o:E(_Ug)};}}},_UN=function(_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_){while(1){var _Vn=B(_TH(_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_)),_Vo=E(_Vn),_Vp=_Vo.c,_Vq=_Vo.d,_Vr=_Vo.e,_Vs=_Vo.f,_Vt=_Vo.h,_Vu=_Vo.i,_Vv=_Vo.j,_Vw=_Vo.k,_Vx=_Vo.l,_Vy=_Vo.m,_Vz=_Vo.o,_VA=E(_Vo.n),_VB=_VA.a,_VC=_VA.b,_VD=_VA.c,_VE=_VA.e,_VF=_VA.g,_VG=_VA.h,_VH=E(_Vo.a),_VI=E(_Vo.b),_VJ=E(_Vo.g);if(!E(_VA.d)){if(!E(_Vg)){return {_:0,a:E(_VH),b:E(_VI),c:E(_Vp),d:E(_Vq),e:E(_Vr),f:E(_Vs),g:E(_VJ),h:_Vt,i:_Vu,j:_Vv,k:_Vw,l:E(_Vx),m:_Vy,n:E({_:0,a:E(_VB),b:E(_VC),c:E(_VD),d:E(_wr),e:E(_VE),f:E(_wr),g:E(_VF),h:E(_VG)}),o:E(_Vz)};}else{_UR=_VH.a;_US=_VH.b;_UT=_VH.c;_UU=_VH.d;_UV=_VH.e;_UW=_VH.f;_UX=_VH.g;_UY=_VH.h;_UZ=_VH.i;_V0=_VI.a;_V1=_VI.b;_V2=_Vp;_V3=_Vq;_V4=_Vr;_V5=_Vs;_V6=_VJ.a;_V7=_VJ.b;_V8=_Vt;_V9=_Vu;_Va=_Vv;_Vb=_Vw;_Vc=_Vx;_Vd=_Vy;_Ve=_VB;_Vf=_VC;_Vg=_VD;_Vh=_wr;_Vi=_VE;_Vj=_VA.f;_Vk=_VF;_Vl=_VG;_Vm=_Vz;continue;}}else{return {_:0,a:E(_VH),b:E(_VI),c:E(_Vp),d:E(_Vq),e:E(_Vr),f:E(_Vs),g:E(_VJ),h:_Vt,i:_Vu,j:_Vv,k:_Vw,l:E(_Vx),m:_Vy,n:E({_:0,a:E(_VB),b:E(_VC),c:E(_VD),d:E(_ws),e:E(_VE),f:E(_wr),g:E(_VF),h:E(_VG)}),o:E(_Vz)};}}},_VK=function(_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd,_We,_Wf,_Wg,_Wh,_Wi,_){var _Wj=B(_TH(_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_ws,_Wd,_We,_Wf,_Wg,_Wh,_Wi,_)),_Wk=E(_Wj),_Wl=_Wk.c,_Wm=_Wk.d,_Wn=_Wk.e,_Wo=_Wk.f,_Wp=_Wk.h,_Wq=_Wk.i,_Wr=_Wk.j,_Ws=_Wk.k,_Wt=_Wk.l,_Wu=_Wk.m,_Wv=_Wk.o,_Ww=E(_Wk.n),_Wx=_Ww.a,_Wy=_Ww.b,_Wz=_Ww.c,_WA=_Ww.e,_WB=_Ww.g,_WC=_Ww.h,_WD=E(_Wk.a),_WE=E(_Wk.b),_WF=E(_Wk.g);if(!E(_Ww.d)){return new F(function(){return _UN(_VL,_VM,_VN,_WD.a,_WD.b,_WD.c,_WD.d,_WD.e,_WD.f,_WD.g,_WD.h,_WD.i,_WE.a,_WE.b,_Wl,_Wm,_Wn,_Wo,_WF.a,_WF.b,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wx,_Wy,_Wz,_wr,_WA,_Ww.f,_WB,_WC,_Wv,_);});}else{return {_:0,a:E(_WD),b:E(_WE),c:E(_Wl),d:E(_Wm),e:E(_Wn),f:E(_Wo),g:E(_WF),h:_Wp,i:_Wq,j:_Wr,k:_Ws,l:E(_Wt),m:_Wu,n:E({_:0,a:E(_Wx),b:E(_Wy),c:E(_Wz),d:E(_ws),e:E(_WA),f:E(_wr),g:E(_WB),h:E(_WC)}),o:E(_Wv)};}},_WG=function(_WH){var _WI=E(_WH);if(!_WI._){return __Z;}else{var _WJ=E(_WI.b);return (_WJ._==0)?__Z:new T2(1,new T2(0,_WI.a,_WJ.a),new T(function(){return B(_WG(_WJ.b));}));}},_WK=function(_WL,_WM,_WN){return new T2(1,new T2(0,_WL,_WM),new T(function(){return B(_WG(_WN));}));},_WO=function(_WP,_WQ){var _WR=E(_WQ);return (_WR._==0)?__Z:new T2(1,new T2(0,_WP,_WR.a),new T(function(){return B(_WG(_WR.b));}));},_WS="Invalid JSON!",_WT=new T1(0,_WS),_WU="No such value",_WV=new T1(0,_WU),_WW=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_WX=function(_WY){return E(E(_WY).c);},_WZ=function(_X0,_X1,_){var _X2=__app1(E(_WW),_X1),_X3=__eq(_X2,E(_7));if(!E(_X3)){var _X4=__isUndef(_X2);return (E(_X4)==0)?new T(function(){var _X5=String(_X2),_X6=jsParseJSON(_X5);if(!_X6._){return E(_WT);}else{return B(A2(_WX,_X0,_X6.a));}}):_WV;}else{return _WV;}},_X7=new T1(0,0),_X8=function(_X9,_Xa){while(1){var _Xb=E(_X9);if(!_Xb._){var _Xc=_Xb.a,_Xd=E(_Xa);if(!_Xd._){return new T1(0,(_Xc>>>0|_Xd.a>>>0)>>>0&4294967295);}else{_X9=new T1(1,I_fromInt(_Xc));_Xa=_Xd;continue;}}else{var _Xe=E(_Xa);if(!_Xe._){_X9=_Xb;_Xa=new T1(1,I_fromInt(_Xe.a));continue;}else{return new T1(1,I_or(_Xb.a,_Xe.a));}}}},_Xf=function(_Xg){var _Xh=E(_Xg);if(!_Xh._){return E(_X7);}else{return new F(function(){return _X8(new T1(0,E(_Xh.a)),B(_cO(B(_Xf(_Xh.b)),31)));});}},_Xi=function(_Xj,_Xk){if(!E(_Xj)){return new F(function(){return _ft(B(_Xf(_Xk)));});}else{return new F(function(){return _Xf(_Xk);});}},_Xl=1420103680,_Xm=465,_Xn=new T2(1,_Xm,_10),_Xo=new T2(1,_Xl,_Xn),_Xp=new T(function(){return B(_Xi(_ws,_Xo));}),_Xq=function(_Xr){return E(_Xp);},_Xs=new T(function(){return B(unCStr("s"));}),_Xt=function(_Xu,_Xv){while(1){var _Xw=E(_Xu);if(!_Xw._){return E(_Xv);}else{_Xu=_Xw.b;_Xv=_Xw.a;continue;}}},_Xx=function(_Xy,_Xz,_XA){return new F(function(){return _Xt(_Xz,_Xy);});},_XB=new T1(0,1),_XC=function(_XD,_XE){var _XF=E(_XD);return new T2(0,_XF,new T(function(){var _XG=B(_XC(B(_cv(_XF,_XE)),_XE));return new T2(1,_XG.a,_XG.b);}));},_XH=function(_XI){var _XJ=B(_XC(_XI,_XB));return new T2(1,_XJ.a,_XJ.b);},_XK=function(_XL,_XM){var _XN=B(_XC(_XL,new T(function(){return B(_eO(_XM,_XL));})));return new T2(1,_XN.a,_XN.b);},_XO=new T1(0,0),_XP=function(_XQ,_XR){var _XS=E(_XQ);if(!_XS._){var _XT=_XS.a,_XU=E(_XR);return (_XU._==0)?_XT>=_XU.a:I_compareInt(_XU.a,_XT)<=0;}else{var _XV=_XS.a,_XW=E(_XR);return (_XW._==0)?I_compareInt(_XV,_XW.a)>=0:I_compare(_XV,_XW.a)>=0;}},_XX=function(_XY,_XZ,_Y0){if(!B(_XP(_XZ,_XO))){var _Y1=function(_Y2){return (!B(_d7(_Y2,_Y0)))?new T2(1,_Y2,new T(function(){return B(_Y1(B(_cv(_Y2,_XZ))));})):__Z;};return new F(function(){return _Y1(_XY);});}else{var _Y3=function(_Y4){return (!B(_cY(_Y4,_Y0)))?new T2(1,_Y4,new T(function(){return B(_Y3(B(_cv(_Y4,_XZ))));})):__Z;};return new F(function(){return _Y3(_XY);});}},_Y5=function(_Y6,_Y7,_Y8){return new F(function(){return _XX(_Y6,B(_eO(_Y7,_Y6)),_Y8);});},_Y9=function(_Ya,_Yb){return new F(function(){return _XX(_Ya,_XB,_Yb);});},_Yc=function(_Yd){return new F(function(){return _ba(_Yd);});},_Ye=function(_Yf){return new F(function(){return _eO(_Yf,_XB);});},_Yg=function(_Yh){return new F(function(){return _cv(_Yh,_XB);});},_Yi=function(_Yj){return new F(function(){return _aR(E(_Yj));});},_Yk={_:0,a:_Yg,b:_Ye,c:_Yi,d:_Yc,e:_XH,f:_XK,g:_Y9,h:_Y5},_Yl=function(_Ym,_Yn){while(1){var _Yo=E(_Ym);if(!_Yo._){var _Yp=E(_Yo.a);if(_Yp==( -2147483648)){_Ym=new T1(1,I_fromInt( -2147483648));continue;}else{var _Yq=E(_Yn);if(!_Yq._){return new T1(0,B(_9j(_Yp,_Yq.a)));}else{_Ym=new T1(1,I_fromInt(_Yp));_Yn=_Yq;continue;}}}else{var _Yr=_Yo.a,_Ys=E(_Yn);return (_Ys._==0)?new T1(1,I_div(_Yr,I_fromInt(_Ys.a))):new T1(1,I_div(_Yr,_Ys.a));}}},_Yt=function(_Yu,_Yv){if(!B(_cn(_Yv,_oL))){return new F(function(){return _Yl(_Yu,_Yv);});}else{return E(_9U);}},_Yw=function(_Yx,_Yy){while(1){var _Yz=E(_Yx);if(!_Yz._){var _YA=E(_Yz.a);if(_YA==( -2147483648)){_Yx=new T1(1,I_fromInt( -2147483648));continue;}else{var _YB=E(_Yy);if(!_YB._){var _YC=_YB.a;return new T2(0,new T1(0,B(_9j(_YA,_YC))),new T1(0,B(_ao(_YA,_YC))));}else{_Yx=new T1(1,I_fromInt(_YA));_Yy=_YB;continue;}}}else{var _YD=E(_Yy);if(!_YD._){_Yx=_Yz;_Yy=new T1(1,I_fromInt(_YD.a));continue;}else{var _YE=I_divMod(_Yz.a,_YD.a);return new T2(0,new T1(1,_YE.a),new T1(1,_YE.b));}}}},_YF=function(_YG,_YH){if(!B(_cn(_YH,_oL))){var _YI=B(_Yw(_YG,_YH));return new T2(0,_YI.a,_YI.b);}else{return E(_9U);}},_YJ=function(_YK,_YL){while(1){var _YM=E(_YK);if(!_YM._){var _YN=E(_YM.a);if(_YN==( -2147483648)){_YK=new T1(1,I_fromInt( -2147483648));continue;}else{var _YO=E(_YL);if(!_YO._){return new T1(0,B(_ao(_YN,_YO.a)));}else{_YK=new T1(1,I_fromInt(_YN));_YL=_YO;continue;}}}else{var _YP=_YM.a,_YQ=E(_YL);return (_YQ._==0)?new T1(1,I_mod(_YP,I_fromInt(_YQ.a))):new T1(1,I_mod(_YP,_YQ.a));}}},_YR=function(_YS,_YT){if(!B(_cn(_YT,_oL))){return new F(function(){return _YJ(_YS,_YT);});}else{return E(_9U);}},_YU=function(_YV,_YW){while(1){var _YX=E(_YV);if(!_YX._){var _YY=E(_YX.a);if(_YY==( -2147483648)){_YV=new T1(1,I_fromInt( -2147483648));continue;}else{var _YZ=E(_YW);if(!_YZ._){return new T1(0,quot(_YY,_YZ.a));}else{_YV=new T1(1,I_fromInt(_YY));_YW=_YZ;continue;}}}else{var _Z0=_YX.a,_Z1=E(_YW);return (_Z1._==0)?new T1(0,I_toInt(I_quot(_Z0,I_fromInt(_Z1.a)))):new T1(1,I_quot(_Z0,_Z1.a));}}},_Z2=function(_Z3,_Z4){if(!B(_cn(_Z4,_oL))){return new F(function(){return _YU(_Z3,_Z4);});}else{return E(_9U);}},_Z5=function(_Z6,_Z7){if(!B(_cn(_Z7,_oL))){var _Z8=B(_cE(_Z6,_Z7));return new T2(0,_Z8.a,_Z8.b);}else{return E(_9U);}},_Z9=function(_Za,_Zb){while(1){var _Zc=E(_Za);if(!_Zc._){var _Zd=E(_Zc.a);if(_Zd==( -2147483648)){_Za=new T1(1,I_fromInt( -2147483648));continue;}else{var _Ze=E(_Zb);if(!_Ze._){return new T1(0,_Zd%_Ze.a);}else{_Za=new T1(1,I_fromInt(_Zd));_Zb=_Ze;continue;}}}else{var _Zf=_Zc.a,_Zg=E(_Zb);return (_Zg._==0)?new T1(1,I_rem(_Zf,I_fromInt(_Zg.a))):new T1(1,I_rem(_Zf,_Zg.a));}}},_Zh=function(_Zi,_Zj){if(!B(_cn(_Zj,_oL))){return new F(function(){return _Z9(_Zi,_Zj);});}else{return E(_9U);}},_Zk=function(_Zl){return E(_Zl);},_Zm=function(_Zn){return E(_Zn);},_Zo=function(_Zp){var _Zq=E(_Zp);if(!_Zq._){var _Zr=E(_Zq.a);return (_Zr==( -2147483648))?E(_fs):(_Zr<0)?new T1(0, -_Zr):E(_Zq);}else{var _Zs=_Zq.a;return (I_compareInt(_Zs,0)>=0)?E(_Zq):new T1(1,I_negate(_Zs));}},_Zt=new T1(0, -1),_Zu=function(_Zv){var _Zw=E(_Zv);if(!_Zw._){var _Zx=_Zw.a;return (_Zx>=0)?(E(_Zx)==0)?E(_X7):E(_d6):E(_Zt);}else{var _Zy=I_compareInt(_Zw.a,0);return (_Zy<=0)?(E(_Zy)==0)?E(_X7):E(_Zt):E(_d6);}},_Zz={_:0,a:_cv,b:_eO,c:_of,d:_ft,e:_Zo,f:_Zu,g:_Zm},_ZA=function(_ZB,_ZC){var _ZD=E(_ZB);if(!_ZD._){var _ZE=_ZD.a,_ZF=E(_ZC);return (_ZF._==0)?_ZE!=_ZF.a:(I_compareInt(_ZF.a,_ZE)==0)?false:true;}else{var _ZG=_ZD.a,_ZH=E(_ZC);return (_ZH._==0)?(I_compareInt(_ZG,_ZH.a)==0)?false:true:(I_compare(_ZG,_ZH.a)==0)?false:true;}},_ZI=new T2(0,_cn,_ZA),_ZJ=function(_ZK,_ZL){return (!B(_ez(_ZK,_ZL)))?E(_ZK):E(_ZL);},_ZM=function(_ZN,_ZO){return (!B(_ez(_ZN,_ZO)))?E(_ZO):E(_ZN);},_ZP={_:0,a:_ZI,b:_c7,c:_d7,d:_ez,e:_cY,f:_XP,g:_ZJ,h:_ZM},_ZQ=function(_ZR){return new T2(0,E(_ZR),E(_aV));},_ZS=new T3(0,_Zz,_ZP,_ZQ),_ZT={_:0,a:_ZS,b:_Yk,c:_Z2,d:_Zh,e:_Yt,f:_YR,g:_Z5,h:_YF,i:_Zk},_ZU=new T1(0,0),_ZV=function(_ZW,_ZX,_ZY){var _ZZ=B(A1(_ZW,_ZX));if(!B(_cn(_ZZ,_ZU))){return new F(function(){return _Yl(B(_of(_ZX,_ZY)),_ZZ);});}else{return E(_9U);}},_100=function(_101,_102){while(1){if(!B(_cn(_102,_oL))){var _103=_102,_104=B(_Zh(_101,_102));_101=_103;_102=_104;continue;}else{return E(_101);}}},_105=5,_106=new T(function(){return B(_9Q(_105));}),_107=new T(function(){return die(_106);}),_108=function(_109,_10a){if(!B(_cn(_10a,_oL))){var _10b=B(_100(B(_Zo(_109)),B(_Zo(_10a))));return (!B(_cn(_10b,_oL)))?new T2(0,B(_YU(_109,_10b)),B(_YU(_10a,_10b))):E(_9U);}else{return E(_107);}},_10c=function(_10d,_10e,_10f,_10g){var _10h=B(_of(_10e,_10f));return new F(function(){return _108(B(_of(B(_of(_10d,_10g)),B(_Zu(_10h)))),B(_Zo(_10h)));});},_10i=function(_10j,_10k,_10l){var _10m=new T(function(){if(!B(_cn(_10l,_oL))){var _10n=B(_cE(_10k,_10l));return new T2(0,_10n.a,_10n.b);}else{return E(_9U);}}),_10o=new T(function(){return B(A2(_he,B(_o4(B(_o2(_10j)))),new T(function(){return E(E(_10m).a);})));});return new T2(0,_10o,new T(function(){return new T2(0,E(E(_10m).b),E(_10l));}));},_10p=function(_10q,_10r,_10s){var _10t=B(_10i(_10q,_10r,_10s)),_10u=_10t.a,_10v=E(_10t.b);if(!B(_d7(B(_of(_10v.a,_aV)),B(_of(_oL,_10v.b))))){return E(_10u);}else{var _10w=B(_o4(B(_o2(_10q))));return new F(function(){return A3(_oH,_10w,_10u,new T(function(){return B(A2(_he,_10w,_aV));}));});}},_10x=479723520,_10y=40233135,_10z=new T2(1,_10y,_10),_10A=new T2(1,_10x,_10z),_10B=new T(function(){return B(_Xi(_ws,_10A));}),_10C=new T1(0,40587),_10D=function(_10E){var _10F=new T(function(){var _10G=B(_10c(_10E,_aV,_Xp,_aV)),_10H=B(_10c(_10B,_aV,_Xp,_aV)),_10I=B(_10c(_10G.a,_10G.b,_10H.a,_10H.b));return B(_10p(_ZT,_10I.a,_10I.b));});return new T2(0,new T(function(){return B(_cv(_10C,_10F));}),new T(function(){return B(_eO(_10E,B(_ZV(_Xq,B(_of(_10F,_Xp)),_10B))));}));},_10J=function(_10K,_){var _10L=__get(_10K,0),_10M=__get(_10K,1),_10N=Number(_10L),_10O=jsTrunc(_10N),_10P=Number(_10M),_10Q=jsTrunc(_10P);return new T2(0,_10O,_10Q);},_10R=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_10S=660865024,_10T=465661287,_10U=new T2(1,_10T,_10),_10V=new T2(1,_10S,_10U),_10W=new T(function(){return B(_Xi(_ws,_10V));}),_10X=function(_){var _10Y=__app0(E(_10R)),_10Z=B(_10J(_10Y,_));return new T(function(){var _110=E(_10Z);if(!B(_cn(_10W,_ZU))){return B(_cv(B(_of(B(_aR(E(_110.a))),_Xp)),B(_Yl(B(_of(B(_of(B(_aR(E(_110.b))),_Xp)),_Xp)),_10W))));}else{return E(_9U);}});},_111=new T(function(){return B(err(_sr));}),_112=new T(function(){return B(err(_sp));}),_113=new T(function(){return B(A3(_Fz,_G2,_DC,_Fp));}),_114=new T1(0,1),_115=new T1(0,10),_116=function(_117){while(1){var _118=E(_117);if(!_118._){_117=new T1(1,I_fromInt(_118.a));continue;}else{return new F(function(){return I_toString(_118.a);});}}},_119=function(_11a,_11b){return new F(function(){return _y(fromJSStr(B(_116(_11a))),_11b);});},_11c=new T1(0,0),_11d=function(_11e,_11f,_11g){if(_11e<=6){return new F(function(){return _119(_11f,_11g);});}else{if(!B(_d7(_11f,_11c))){return new F(function(){return _119(_11f,_11g);});}else{return new T2(1,_H,new T(function(){return B(_y(fromJSStr(B(_116(_11f))),new T2(1,_G,_11g)));}));}}},_11h=function(_11i){return new F(function(){return _11d(0,_11i,_10);});},_11j=new T(function(){return B(_cn(_115,_ZU));}),_11k=function(_11l){while(1){if(!B(_cn(_11l,_ZU))){if(!E(_11j)){if(!B(_cn(B(_YJ(_11l,_115)),_ZU))){return new F(function(){return _11h(_11l);});}else{var _11m=B(_Yl(_11l,_115));_11l=_11m;continue;}}else{return E(_9U);}}else{return __Z;}}},_11n=46,_11o=48,_11p=function(_11q,_11r,_11s){if(!B(_d7(_11s,_ZU))){var _11t=B(A1(_11q,_11s));if(!B(_cn(_11t,_ZU))){var _11u=B(_Yw(_11s,_11t)),_11v=_11u.b,_11w=new T(function(){var _11x=Math.log(B(_fM(_11t)))/Math.log(10),_11y=_11x&4294967295,_11z=function(_11A){if(_11A>=0){var _11B=E(_11A);if(!_11B){var _11C=B(_Yl(B(_eO(B(_cv(B(_of(_11v,_aV)),_11t)),_114)),_11t));}else{var _11C=B(_Yl(B(_eO(B(_cv(B(_of(_11v,B(_ov(_115,_11B)))),_11t)),_114)),_11t));}var _11D=function(_11E){var _11F=B(_11d(0,_11C,_10)),_11G=_11A-B(_mt(_11F,0))|0;if(0>=_11G){if(!E(_11r)){return E(_11F);}else{return new F(function(){return _11k(_11C);});}}else{var _11H=new T(function(){if(!E(_11r)){return E(_11F);}else{return B(_11k(_11C));}}),_11I=function(_11J){var _11K=E(_11J);return (_11K==1)?E(new T2(1,_11o,_11H)):new T2(1,_11o,new T(function(){return B(_11I(_11K-1|0));}));};return new F(function(){return _11I(_11G);});}};if(!E(_11r)){var _11L=B(_11D(_));return (_11L._==0)?__Z:new T2(1,_11n,_11L);}else{if(!B(_cn(_11C,_ZU))){var _11M=B(_11D(_));return (_11M._==0)?__Z:new T2(1,_11n,_11M);}else{return __Z;}}}else{return E(_pr);}};if(_11y>=_11x){return B(_11z(_11y));}else{return B(_11z(_11y+1|0));}},1);return new F(function(){return _y(B(_11d(0,_11u.a,_10)),_11w);});}else{return E(_9U);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_11p(_11q,_11r,B(_ft(_11s))));}));});}},_11N=function(_11O,_11P,_){var _11Q=B(_10X(_)),_11R=new T(function(){var _11S=new T(function(){var _11T=new T(function(){var _11U=B(_y(B(_11p(_Xq,_ws,B(_10D(_11Q)).b)),_Xs));if(!_11U._){return E(_Q9);}else{var _11V=B(_Q4(_11U.a,_11U.b));if(!_11V._){return B(_Xx(_10,_10,_Ru));}else{var _11W=_11V.a,_11X=E(_11V.b);if(!_11X._){return B(_Xx(new T2(1,_11W,_10),_10,_Ru));}else{var _11Y=E(_11W),_11Z=new T(function(){var _120=B(_H6(46,_11X.a,_11X.b));return new T2(0,_120.a,_120.b);});if(E(_11Y)==46){return B(_Xx(_10,new T2(1,new T(function(){return E(E(_11Z).a);}),new T(function(){return E(E(_11Z).b);})),_Ru));}else{return B(_Xx(new T2(1,_11Y,new T(function(){return E(E(_11Z).a);})),new T(function(){return E(E(_11Z).b);}),_Ru));}}}}}),_121=B(_Gb(B(_sw(_113,_11T))));if(!_121._){return E(_112);}else{if(!E(_121.b)._){return B(_pO(3,B(_I(0,E(_121.a)+(imul(E(_11P),E(_11O)-1|0)|0)|0,_10))));}else{return E(_111);}}}),_122=B(_Gb(B(_sw(_113,_11S))));if(!_122._){return E(_112);}else{if(!E(_122.b)._){return E(_122.a);}else{return E(_111);}}});return new T2(0,new T(function(){return B(_av(_11R,_11O));}),_11R);},_123=function(_124,_125){while(1){var _126=E(_124);if(!_126._){return E(_125);}else{_124=_126.b;_125=_126.a;continue;}}},_127=function(_128,_129,_12a){return new F(function(){return _123(_129,_128);});},_12b=function(_12c,_12d){while(1){var _12e=E(_12c);if(!_12e._){return E(_12d);}else{_12c=_12e.b;_12d=_12e.a;continue;}}},_12f=function(_12g,_12h,_12i){return new F(function(){return _12b(_12h,_12g);});},_12j=function(_12k,_12l){while(1){var _12m=E(_12l);if(!_12m._){return __Z;}else{var _12n=_12m.b,_12o=E(_12k);if(_12o==1){return E(_12n);}else{_12k=_12o-1|0;_12l=_12n;continue;}}}},_12p=function(_12q,_12r){var _12s=new T(function(){var _12t=_12q+1|0;if(_12t>0){return B(_12j(_12t,_12r));}else{return E(_12r);}});if(0>=_12q){return E(_12s);}else{var _12u=function(_12v,_12w){var _12x=E(_12v);if(!_12x._){return E(_12s);}else{var _12y=_12x.a,_12z=E(_12w);return (_12z==1)?new T2(1,_12y,_12s):new T2(1,_12y,new T(function(){return B(_12u(_12x.b,_12z-1|0));}));}};return new F(function(){return _12u(_12r,_12q);});}},_12A=new T(function(){return B(unCStr(":"));}),_12B=function(_12C){var _12D=E(_12C);if(!_12D._){return __Z;}else{var _12E=new T(function(){return B(_y(_12A,new T(function(){return B(_12B(_12D.b));},1)));},1);return new F(function(){return _y(_12D.a,_12E);});}},_12F=function(_12G,_12H){var _12I=new T(function(){return B(_y(_12A,new T(function(){return B(_12B(_12H));},1)));},1);return new F(function(){return _y(_12G,_12I);});},_12J=function(_12K){return new F(function(){return _KF("Check.hs:161:7-35|(co : na : xs)");});},_12L=new T(function(){return B(_12J(_));}),_12M=0,_12N=new T(function(){return B(unCStr("!"));}),_12O=new T(function(){return B(err(_sp));}),_12P=new T(function(){return B(err(_sr));}),_12Q=new T(function(){return B(A3(_Fz,_G2,_DC,_Fp));}),_12R=function(_12S,_12T){var _12U=E(_12T);if(!_12U._){return E(_12L);}else{var _12V=E(_12U.b);if(!_12V._){return E(_12L);}else{var _12W=E(_12U.a),_12X=new T(function(){var _12Y=B(_H6(58,_12V.a,_12V.b));return new T2(0,_12Y.a,_12Y.b);}),_12Z=function(_130,_131,_132){var _133=function(_134){if((_12S+1|0)!=_134){return new T3(0,_12S+1|0,_131,_12U);}else{var _135=E(_132);return (_135._==0)?new T3(0,_12M,_131,_10):new T3(0,_12M,_131,new T(function(){var _136=B(_12F(_135.a,_135.b));if(!_136._){return E(_Q9);}else{return B(_Q4(_136.a,_136.b));}}));}};if(!B(_qJ(_130,_12N))){var _137=B(_Gb(B(_sw(_12Q,_130))));if(!_137._){return E(_12O);}else{if(!E(_137.b)._){return new F(function(){return _133(E(_137.a));});}else{return E(_12P);}}}else{return new F(function(){return _133( -1);});}};if(E(_12W)==58){return new F(function(){return _12Z(_10,new T(function(){return E(E(_12X).a);}),new T(function(){return E(E(_12X).b);}));});}else{var _138=E(_12X),_139=E(_138.b);if(!_139._){return E(_12L);}else{return new F(function(){return _12Z(new T2(1,_12W,_138.a),_139.a,_139.b);});}}}}},_13a=function(_13b,_13c){while(1){var _13d=E(_13c);if(!_13d._){return __Z;}else{var _13e=_13d.b,_13f=E(_13b);if(_13f==1){return E(_13e);}else{_13b=_13f-1|0;_13c=_13e;continue;}}}},_13g=function(_13h,_13i,_13j){var _13k=new T2(1,_13i,new T(function(){var _13l=_13h+1|0;if(_13l>0){return B(_13a(_13l,_13j));}else{return E(_13j);}}));if(0>=_13h){return E(_13k);}else{var _13m=function(_13n,_13o){var _13p=E(_13n);if(!_13p._){return E(_13k);}else{var _13q=_13p.a,_13r=E(_13o);return (_13r==1)?new T2(1,_13q,_13k):new T2(1,_13q,new T(function(){return B(_13m(_13p.b,_13r-1|0));}));}};return new F(function(){return _13m(_13j,_13h);});}},_13s=new T2(0,_PM,_E7),_13t=function(_13u,_13v,_13w){while(1){var _13x=E(_13w);if(!_13x._){return E(_13s);}else{var _13y=_13x.b,_13z=E(_13x.a),_13A=E(_13z.a);if(_13u!=E(_13A.a)){_13w=_13y;continue;}else{if(_13v!=E(_13A.b)){_13w=_13y;continue;}else{return E(_13z.b);}}}}},_13B=function(_13C,_13D){while(1){var _13E=E(_13D);if(!_13E._){return __Z;}else{var _13F=_13E.b,_13G=E(_13C);if(_13G==1){return E(_13F);}else{_13C=_13G-1|0;_13D=_13F;continue;}}}},_13H=function(_13I,_13J,_13K){var _13L=E(_13I);if(_13L==1){return E(_13K);}else{return new F(function(){return _13B(_13L-1|0,_13K);});}},_13M=function(_13N,_13O,_13P){return new T2(1,new T(function(){if(0>=_13N){return __Z;}else{return B(_pO(_13N,new T2(1,_13O,_13P)));}}),new T(function(){if(_13N>0){return B(_13Q(_13N,B(_13H(_13N,_13O,_13P))));}else{return B(_13M(_13N,_13O,_13P));}}));},_13Q=function(_13R,_13S){var _13T=E(_13S);if(!_13T._){return __Z;}else{var _13U=_13T.a,_13V=_13T.b;return new T2(1,new T(function(){if(0>=_13R){return __Z;}else{return B(_pO(_13R,_13T));}}),new T(function(){if(_13R>0){return B(_13Q(_13R,B(_13H(_13R,_13U,_13V))));}else{return B(_13M(_13R,_13U,_13V));}}));}},_13W=function(_13X,_13Y,_13Z){var _140=_13Y-1|0;if(0<=_140){var _141=E(_13X),_142=function(_143){var _144=new T(function(){if(_143!=_140){return B(_142(_143+1|0));}else{return __Z;}}),_145=function(_146){var _147=E(_146);return (_147._==0)?E(_144):new T2(1,new T(function(){var _148=E(_13Z);if(!_148._){return E(_13s);}else{var _149=_148.b,_14a=E(_148.a),_14b=E(_14a.a),_14c=E(_147.a);if(_14c!=E(_14b.a)){return B(_13t(_14c,_143,_149));}else{if(_143!=E(_14b.b)){return B(_13t(_14c,_143,_149));}else{return E(_14a.b);}}}}),new T(function(){return B(_145(_147.b));}));};return new F(function(){return _145(B(_8s(0,_141-1|0)));});};return new F(function(){return _13Q(_141,B(_142(0)));});}else{return __Z;}},_14d=function(_14e){return new F(function(){return _KF("Check.hs:66:21-47|(l : r : _)");});},_14f=new T(function(){return B(_14d(_));}),_14g=61,_14h=function(_14i,_14j){while(1){var _14k=E(_14i);if(!_14k._){return E(_14j);}else{_14i=_14k.b;_14j=_14k.a;continue;}}},_14l=function(_14m,_14n,_14o){return new F(function(){return _14h(_14n,_14m);});},_14p=function(_14q,_14r){var _14s=E(_14r);if(!_14s._){return new T2(0,_10,_10);}else{var _14t=_14s.a;if(!B(A1(_14q,_14t))){var _14u=new T(function(){var _14v=B(_14p(_14q,_14s.b));return new T2(0,_14v.a,_14v.b);});return new T2(0,new T2(1,_14t,new T(function(){return E(E(_14u).a);})),new T(function(){return E(E(_14u).b);}));}else{return new T2(0,_10,_14s);}}},_14w=function(_14x,_14y){while(1){var _14z=E(_14y);if(!_14z._){return __Z;}else{if(!B(A1(_14x,_14z.a))){return E(_14z);}else{_14y=_14z.b;continue;}}}},_14A=function(_14B){var _14C=_14B>>>0;if(_14C>887){var _14D=u_iswspace(_14B);return (E(_14D)==0)?false:true;}else{var _14E=E(_14C);return (_14E==32)?true:(_14E-9>>>0>4)?(E(_14E)==160)?true:false:true;}},_14F=function(_14G){return new F(function(){return _14A(E(_14G));});},_14H=function(_14I){var _14J=B(_14w(_14F,_14I));if(!_14J._){return __Z;}else{var _14K=new T(function(){var _14L=B(_14p(_14F,_14J));return new T2(0,_14L.a,_14L.b);});return new T2(1,new T(function(){return E(E(_14K).a);}),new T(function(){return B(_14H(E(_14K).b));}));}},_14M=function(_14N){if(!B(_4B(_h7,_14g,_14N))){return new T2(0,_14N,_10);}else{var _14O=new T(function(){var _14P=E(_14N);if(!_14P._){return E(_14f);}else{var _14Q=E(_14P.b);if(!_14Q._){return E(_14f);}else{var _14R=_14Q.a,_14S=_14Q.b,_14T=E(_14P.a);if(E(_14T)==61){return new T2(0,_10,new T(function(){return E(B(_H6(61,_14R,_14S)).a);}));}else{var _14U=B(_H6(61,_14R,_14S)),_14V=E(_14U.b);if(!_14V._){return E(_14f);}else{return new T2(0,new T2(1,_14T,_14U.a),_14V.a);}}}}});return new T2(0,new T(function(){var _14W=B(_14H(E(_14O).a));if(!_14W._){return __Z;}else{return B(_14l(_14W.a,_14W.b,_Ru));}}),new T(function(){var _14X=B(_14H(E(_14O).b));if(!_14X._){return __Z;}else{return E(_14X.a);}}));}},_14Y=function(_14Z){var _150=E(_14Z);if(!_150._){return new T2(0,_10,_10);}else{var _151=E(_150.a),_152=new T(function(){var _153=B(_14Y(_150.b));return new T2(0,_153.a,_153.b);});return new T2(0,new T2(1,_151.a,new T(function(){return E(E(_152).a);})),new T2(1,_151.b,new T(function(){return E(E(_152).b);})));}},_154=function(_155,_156,_157){var _158=new T(function(){var _159=B(_14Y(_157));return new T2(0,_159.a,_159.b);});return new T2(0,new T2(1,_155,new T(function(){return E(E(_158).a);})),new T2(1,_156,new T(function(){return E(E(_158).b);})));},_15a=new T(function(){return B(unCStr("\u3053\u306e\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u304c\u898b\u3048\u3066\u3090\u307e\u3059\u304b\uff1f\u3002\n\u3053\u306e\u30e1\u30c3\u30bb\u30fc\u30b8\u306f \u7406\uff1a\u308a\uff1a\u89e3\uff1a\u304b\u3044\uff1a\u3067\u304d\u307e\u3059\u304b\uff1f\u3002\n\u3069\u3046\u304b \u305d\u306e\u307e\u307e\u7acb\uff1a\u305f\uff1a\u3061\u53bb\uff1a\u3055\uff1a\u3089\u305a\u306b \u8b80\uff1a\u3088\uff1a\u3093\u3067\u304f\u3060\u3055\u3044\u3002\n\u79c1\u306f \u4eca\uff1a\u3044\u307e\uff1a 4.8\u6b21\uff1a\u3058\uff1a\u5143\uff1a\u3052\u3093\uff1a\u306b\u3090\u307e\u3059\u3002\n5\u6b21\u5143\u306b\u3042\u304c\u308b\u9014\uff1a\u3068\uff1a\u4e2d\uff1a\u3061\u3046\uff1a \u9593\uff1a\u307e\uff1a\u8005\uff1a\u3082\u306e\uff1a\u306b\u3064\u304b\u307e\u308a \u3053\u306e\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u306b\u9589\uff1a\u3068\uff1a\u3058\u8fbc\uff1a\u3053\uff1a\u3081\u3089\u308c\u3066\u3057\u307e\u3072\u307e\u3057\u305f\u3002\n\u3069\u3046\u304b \u52a9\uff1a\u305f\u3059\uff1a\u3051\u3066\u304f\u3060\u3055\u3044 {ch.\u52a9\u3051\u308b,s0.\u52a9\u3051\u306a\u3044,se}"));}),_15b=new T(function(){return B(unCStr("s0_1"));}),_15c=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u6578\u306e\u90e8\u5c4b\u306b\u5165\u308a\u307e\u305b\u3046 {e.X.jl1}{e.c0&s1.m1:s1}"));}),_15d=new T2(0,_15b,_15c),_15e=new T(function(){return B(unCStr("s0_2"));}),_15f=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u7406\u306e\u90e8\u5c4b\u306b\u5165\u308a\u307e\u305b\u3046 {e.X.jl2}{e.c0&s2.m1:s2}"));}),_15g=new T2(0,_15e,_15f),_15h=new T(function(){return B(unCStr("s0_3"));}),_15i=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u53f2\u306e\u90e8\u5c4b\u306b\u5165\u308a\u307e\u305b\u3046 {e.X.jl3}{e.c0&s3.m1:s3}"));}),_15j=new T2(0,_15h,_15i),_15k=new T(function(){return B(unCStr("s4"));}),_15l=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_15m=new T2(0,_15k,_15l),_15n=new T2(1,_15m,_10),_15o=new T(function(){return B(unCStr("s3"));}),_15p=new T(function(){return B(unCStr("\n\u3053\u306e\u4e16\u754c\u306b\u907a\uff1a\u306e\u3053\uff1a\u3055\u308c\u305f\u8a00\uff1a\u3053\u3068\uff1a\u8449\uff1a\u3070\uff1a \u305d\u308c\u304c \u53f2\uff1a\u3075\u307f\uff1a \u3067\u3059\u3002\n\u79c1\u305f\u3061\u306f \u305d\u308c\u306b\u3088\u3063\u3066 \u4eba\uff1a\u3058\u3093\uff1a\u751f\uff1a\u305b\u3044\uff1a\u306e\u9577\u3055\u3092\u306f\u308b\u304b\u306b\u8d8a\uff1a\u3053\uff1a\u3048\u305f \u8a18\uff1a\u304d\uff1a\u61b6\uff1a\u304a\u304f\uff1a\u3092\u8fbf\uff1a\u305f\u3069\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3059\u3054\u3044\u3053\u3068\u3060\u3068 \u601d\u3072\u307e\u305b\u3093\u304b"));}),_15q=new T2(0,_15o,_15p),_15r=new T2(1,_15q,_15n),_15s=new T(function(){return B(unCStr("s2"));}),_15t=new T(function(){return B(unCStr("\n\u3082\u306e\u3054\u3068\u306e\u7b4b\uff1a\u3059\u3058\uff1a\u9053\uff1a\u307f\u3061\uff1a\u304c \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u3067\u3059\u3002\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306e\u3053\u3068 \u5618\uff1a\u3046\u305d\uff1a\u306e\u3053\u3068\u3002\n\u6b63\uff1a\u305f\u3060\uff1a\u3057\u3044\u3053\u3068 \u9593\uff1a\u307e\uff1a\u9055\uff1a\u3061\u304c\uff1a\u3063\u3066\u3090\u308b\u3053\u3068\u3002\n\u305d\u308c\u3092 \u306f\u3063\u304d\u308a\u3055\u305b\u308b\u306e\u304c \u7406 \u3067\u3059"));}),_15u=new T2(0,_15s,_15t),_15v=new T2(1,_15u,_15r),_15w=new T(function(){return B(unCStr("s1c"));}),_15x=new T(function(){return B(unCStr("\n\u6249\u304c\u958b\u304b\u308c\u305f\u3084\u3046\u3067\u3059 {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"));}),_15y=new T2(0,_15w,_15x),_15z=new T2(1,_15y,_15v),_15A=new T(function(){return B(unCStr("s104"));}),_15B=new T(function(){return B(unCStr("\n\u706b\uff1a\u3072\uff1a(\uff11)\u3068\u6c34\uff1a\u307f\u3065\uff1a(\uff12)\u3092\u5408\u306f\u305b\u308b\u3068 \u3072\u307f\u3064(\uff13) \u306b\u306a\u308a\u307e\u3059\u3002\n\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u306f \u307e\u3046\u958b\uff1a\u3072\u3089\uff1a\u304b\u308c\u308b\u3067\u305b\u3046\u3002\n\u9375\uff1a\u304b\u304e\uff1a\u3092\u624b\u306b\u5165\u308c\u305f\u306e\u3067\u3059\u304b\u3089 {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"));}),_15C=new T2(0,_15A,_15B),_15D=new T2(1,_15C,_15z),_15E=new T(function(){return B(unCStr("s103"));}),_15F=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u304c\u5b58\u5728\u3059\u308b\u9650\uff1a\u304b\u304e\uff1a\u308a \u6578\u306f\u7121\uff1a\u3080\uff1a\u9650\uff1a\u3052\u3093\uff1a\u306b\u3064\u304f\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3053\u308c\u3089\u304c\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u306b\u7f6e\uff1a\u304a\uff1a\u304b\u308c\u3066\u3090\u305f\u4f4d\uff1a\u3044\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u5165\uff1a\u3044\uff1a\u308c\u66ff\uff1a\u304b\uff1a\u3078\u305f\u3089 \u4f55\uff1a\u306a\u306b\uff1a\u304b\u8d77\uff1a\u304a\uff1a\u3053\u308a\u3055\u3046\u3067\u3059 {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"));}),_15G=new T2(0,_15E,_15F),_15H=new T2(1,_15G,_15D),_15I=new T(function(){return B(unCStr("s102"));}),_15J=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u3068\u3044\u3075\u5b58\u5728\u3068 \uff1c\u7121\u3044\uff1e\u3068\u3044\u3075\u5b58\u5728\u304c\u3067\u304d\u307e\u3057\u305f\u3002\n\uff1c\u5b58\u5728\uff1e\u3092 1 \u3068\u3059\u308b\u306a\u3089 \u3053\u308c\u3089\u3092\u5408\u306f\u305b\u305f\u540d\u524d\u3092\u3064\u304f\u308a\u307e\u305b\u3046 {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"));}),_15K=new T2(0,_15I,_15J),_15L=new T2(1,_15K,_15H),_15M=new T(function(){return B(unCStr("s1_3"));}),_15N=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u5206\u3051\u305f\u3068\u601d\uff1a\u304a\u3082\uff1a\u306f\u306a\u3044\u306e\u3067\u3042\u308c\u3070\u3002\n\u305d\u308c\u306f \u5206\u304b\u308c\u3066\u3090\u307e\u305b\u3093"));}),_15O=new T2(0,_15M,_15N),_15P=new T2(1,_15O,_15L),_15Q=new T(function(){return B(unCStr("s1_2"));}),_15R=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u4e16\u754c\u3092 \u5206\u3051\u3066\n\u300c\u5728\uff1a\u3042\uff1a\u308b\u3002\n\u300c\u7121\uff1a\u306a\uff1a\u3044\u3002\n\u3092\u3064\u304f\u308a\u307e\u3057\u305f\u3002\n\u305d\u308c\u3067\u306f \u3053\u306e \uff1c\u5728\u308b\uff1e\u3092 1 \u3068\u547c\uff1a\u3088\uff1a\u3073\u307e\u305b\u3046 {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"));}),_15S=new T2(0,_15Q,_15R),_15T=new T2(1,_15S,_15P),_15U=new T(function(){return B(unCStr("s101"));}),_15V=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u3053\u308c\u3092\u53d6\uff1a\u3068\uff1a\u3063\u305f\u306e\u3067 \u305d\u308c\u306f \u307e\u3046\u3053\u3053\u306b\u3042\u308a\u307e\u305b\u3093\u3002\n\u3053\u308c\u306f \u5206\u3051\u305f\u3053\u3068\u306b\u306a\u308a\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_2.\u3044\u3044\u3048,s1_3}"));}),_15W=new T2(0,_15U,_15V),_15X=new T2(1,_15W,_15T),_15Y=new T(function(){return B(unCStr("s1_1"));}),_15Z=new T(function(){return B(unCStr("\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306b\u5206\u3051\u3089\u308c\u306a\u3044\u306e\u3067\u305b\u3046\u304b"));}),_160=new T2(0,_15Y,_15Z),_161=new T2(1,_160,_15X),_162=new T(function(){return B(unCStr("s1_0"));}),_163=new T(function(){return B(unCStr("\n\u3067\u306f \u5206\u3051\u3066\u304f\u3060\u3055\u3044 {ct.0.Fr}{d.b0}{e.e0.m0:s101}"));}),_164=new T2(0,_162,_163),_165=new T2(1,_164,_161),_166=new T(function(){return B(unCStr("s100"));}),_167=new T(function(){return B(unCStr("\n\u3053\u308c\u306f \u5206\u3051\u3089\u308c\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_0.\u3044\u3044\u3048,s1_1}"));}),_168=new T2(0,_166,_167),_169=new T2(1,_168,_165),_16a=new T(function(){return B(unCStr("s1"));}),_16b=new T(function(){return B(unCStr("\n\u3082\u306e\u3092 \u304b\u305e\u3078\u308b\u306e\u304c \u6578\uff1a\u304b\u305a\uff1a\u3067\u3059\u3002\n\u3082\u3057 \u79c1\u305f\u3061\u304c \u3053\u306e\u4e16\u754c\u3092 \u5206\uff1a\u308f\uff1a\u3051\u3066\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u306a\u3044\u306a\u3089 \u6578\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3084\u3046\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u5206\u3051\u3089\u308c\u3066\u3090\u308b\u304b\u3089 \u6578\u3078\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059 {da}{e.b0.m0:s100}"));}),_16c=new T2(0,_16a,_16b),_16d=new T2(1,_16c,_169),_16e=new T(function(){return B(unCStr("nubatama"));}),_16f=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_16g=new T2(0,_16e,_16f),_16h=new T2(1,_16g,_16d),_16i=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_16j=new T(function(){return B(unCStr("msgW"));}),_16k=new T2(0,_16j,_16i),_16l=new T2(1,_16k,_16h),_16m=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_16n=new T(function(){return B(unCStr("msgR"));}),_16o=new T2(0,_16n,_16m),_16p=new T2(1,_16o,_16l),_16q=new T(function(){return B(unCStr("s0_n"));}),_16r=new T(function(){return B(unCStr("\n\u4ed6\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u3082\u898b\u3066\u307f\u3066\u304f\u3060\u3055\u3044"));}),_16s=new T2(0,_16q,_16r),_16t=new T2(1,_16s,_16p),_16u=new T2(1,_15j,_16t),_16v=new T2(1,_15g,_16u),_16w=new T2(1,_15d,_16v),_16x=new T(function(){return B(unCStr("s0S"));}),_16y=new T(function(){return B(unCStr("\n\u3053\u3053\u306f \u53f2\uff1a\u3075\u307f\uff1a\u306e\u90e8\uff1a\u3078\uff1a\u5c4b\uff1a\u3084\uff1a\u3002\n\u3053\u3053\u306b\u5165\u308a\u307e\u3059\u304b\uff1f {ch.\u5165\u308b,s0_3.\u5165\u3089\u306a\u3044,s0_n}"));}),_16z=new T2(0,_16x,_16y),_16A=new T2(1,_16z,_16w),_16B=new T(function(){return B(unCStr("s0W"));}),_16C=new T(function(){return B(unCStr("\n\u3053\u3053\u306f \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u306e\u90e8\uff1a\u3078\uff1a\u5c4b\uff1a\u3084\uff1a\u3002\n\u3053\u3053\u306b\u5165\u308a\u307e\u3059\u304b\uff1f {ch.\u5165\u308b,s0_2.\u5165\u3089\u306a\u3044,s0_n}"));}),_16D=new T2(0,_16B,_16C),_16E=new T2(1,_16D,_16A),_16F=new T(function(){return B(unCStr("s0E"));}),_16G=new T(function(){return B(unCStr("\n\u3053\u3053\u306f \u6578\uff1a\u304b\u305a\uff1a\u306e\u90e8\uff1a\u3078\uff1a\u5c4b\uff1a\u3084\uff1a\u3002\n\u3053\u3053\u306b\u5165\u308a\u307e\u3059\u304b\uff1f {ch.\u5165\u308b,s0_1.\u5165\u3089\u306a\u3044,s0_n}"));}),_16H=new T2(0,_16F,_16G),_16I=new T2(1,_16H,_16E),_16J=new T(function(){return B(unCStr("se"));}),_16K=new T(function(){return B(unCStr("\n\u6b98\uff1a\u3056\u3093\uff1a\u5ff5\uff1a\u306d\u3093\uff1a\u3067\u3059\u30fb\u30fb\u30fb"));}),_16L=new T2(0,_16J,_16K),_16M=new T2(1,_16L,_16I),_16N=new T(function(){return B(unCStr("s0"));}),_16O=new T(function(){return B(unCStr("\n{sm}\n\u3042\u308a\u304c\u305f\u3046\u3054\u3056\u3044\u307e\u3059\u30fb\u30fb\u30fb\u3002\n\u79c1\uff1a\u308f\u305f\u304f\u3057\uff1a\u306f \u7406\uff1a\u308f\uff1a\u7531\uff1a\u3051\uff1a\u3042\u3063\u3066 \u540d\uff1a\u306a\uff1a\u3092\u660e\uff1a\u3042\uff1a\u304b\u305b\u307e\u305b\u3093\u304c\u3002\n\u3042\u306a\u305f\u65b9\uff1a\u304c\u305f\uff1a\u304c\u4f4f\uff1a\u3059\uff1a\u3080\u6b21\u5143\u3068\u6df1\uff1a\u3075\u304b\uff1a\u304f\u95dc\uff1a\u304b\u304b\uff1a\u306f\u3063\u3066\u3090\u308b\u8005\uff1a\u3082\u306e\uff1a\u3067\u3059\u3002\n\u4eca \u3042\u306a\u305f\u304c\u773c\uff1a\u3081\uff1a\u306e\u524d\uff1a\u307e\u3078\uff1a\u306b\u611f\uff1a\u304b\u3093\uff1a\u3058\u3066\u3090\u308b\u4e16\u754c\u306f 4\u756a\uff1a\u3070\u3093\uff1a\u76ee\uff1a\u3081\uff1a\u306e\u6b21\u5143\u3067\u3059\u3002\n\u3053\u3053\u306b \u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u304c\u5927\uff1a\u305f\u3044\uff1a\u5207\uff1a\u305b\u3064\uff1a\u306b\u3057\u3066\u3090\u308b\u5b9d\uff1a\u305f\u304b\u3089\uff1a\u304c 3\u3064 \u9593\uff1a\u307e\uff1a\u8005\uff1a\u3082\u306e\uff1a\u306b\u3088\u3063\u3066 \u96a0\uff1a\u304b\u304f\uff1a\u3055\u308c\u3066\u3090\u308b\u3084\u3046\u3067\u3059\u3002\n\u3069\u3046\u304b \u305d\u308c\u3089\u3092\u898b\uff1a\u307f\uff1a\u3064\u3051\u51fa\uff1a\u3060\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n\u305d\u308c\u3089\u306e\u5b9d\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u304c\u3042\u308c\u3070 \u79c1\u306f\u6b21\u5143\u3092\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057 \u5143\uff1a\u3082\u3068\uff1a\u306e\u5c45\uff1a\u3090\uff1a\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u3078\u6b78\uff1a\u304b\u3078\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u5fc5\uff1a\u304b\u306a\u3089\uff1a\u305a\u304a\u79ae\uff1a\u308c\u3044\uff1a\u3092\u3044\u305f\u3057\u307e\u3059\u3002\n\u96a0\u3055\u308c\u3066\u3090\u308b\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u5834\u6240\u307e\u3067\u306f \u4eca\u306e\u79c1\u304b\u3089\u306f\u3069\u3046\u3057\u3066\u3082\u898b\u3048\u307e\u305b\u3093\u3002\n\u3069\u3046\u305e \u3088\u308d\u3057\u304f\u304a\u9858\uff1a\u306d\u304c\uff1a\u3072\u3044\u305f\u3057\u307e\u3059\u30fb\u30fb\u30fb {e.bE.m0:s0E}{e.bW.m0:s0W}{e.bS.m0:s0S}"));}),_16P=new T2(0,_16N,_16O),_16Q=new T2(1,_16P,_16M),_16R=new T(function(){return B(unCStr("initMsg"));}),_16S=new T(function(){var _16T=B(_154(_16R,_15a,_16Q));return new T2(0,_16T.a,_16T.b);}),_16U=new T(function(){return E(E(_16S).b);}),_16V=new T(function(){return E(E(_16S).a);}),_16W=function(_16X){if(!B(_4B(_qe,_16X,_16V))){return __Z;}else{return new F(function(){return _6R(_16U,B(_LJ(_qe,_16X,_16V)));});}},_16Y=7,_16Z=new T2(0,_16Y,_16Y),_170=new T2(1,_16Z,_10),_171=5,_172=new T2(0,_171,_171),_173=new T2(1,_172,_170),_174=new T2(1,_172,_173),_175=new T2(1,_172,_174),_176=new T2(1,_172,_175),_177=2,_178=4,_179=new T2(0,_178,_177),_17a=new T2(1,_179,_10),_17b=new T2(0,_177,_177),_17c=new T2(1,_17b,_17a),_17d=new T2(1,_17b,_17c),_17e=new T2(1,_17b,_17d),_17f=0,_17g=new T2(0,_177,_17f),_17h=new T2(1,_17g,_17e),_17i=function(_17j){var _17k=E(_17j);return E(_12M);},_17l=new T(function(){return B(unCStr("msgW"));}),_17m=new T(function(){return B(_16W(_17l));}),_17n=new T(function(){return B(unCStr("@@@@@"));}),_17o=new T(function(){var _17p=E(_17n);if(!_17p._){return E(_nh);}else{return E(_17p.a);}}),_17q=87,_17r=new T2(0,_17q,_Ed),_17s=new T2(0,_17f,_177),_17t=new T2(0,_17s,_17r),_17u=69,_17v=new T2(0,_17u,_Ed),_17w=new T2(0,_179,_17v),_17x=83,_17y=new T2(0,_17x,_Ed),_17z=new T2(0,_177,_178),_17A=new T2(0,_17z,_17y),_17B=new T2(1,_17A,_10),_17C=new T2(1,_17w,_17B),_17D=new T2(1,_17t,_17C),_17E=new T(function(){return B(_13W(_171,5,_17D));}),_17F=new T(function(){return B(unCStr("msgR"));}),_17G=new T(function(){return B(_16W(_17F));}),_17H=new T(function(){return B(_KF("Check.hs:131:22-33|(ch : po)"));}),_17I=new T(function(){return B(_e7("Check.hs:(102,1)-(151,19)|function trEvent"));}),_17J=48,_17K=new T2(0,_17J,_Ed),_17L=new T2(0,_17g,_17K),_17M=new T2(1,_17L,_10),_17N=new T2(1,_10,_10),_17O=new T2(1,_10,_17N),_17P=new T2(1,_10,_17O),_17Q=new T2(1,_17M,_17P),_17R=new T2(1,_17D,_17Q),_17S=function(_17T){var _17U=E(_17T);if(!_17U._){return __Z;}else{var _17V=_17U.b,_17W=E(_17U.a),_17X=_17W.b,_17Y=E(_17W.a),_17Z=function(_180){if(E(_17Y)==32){return new T2(1,_17W,new T(function(){return B(_17S(_17V));}));}else{switch(E(_17X)){case 0:return new T2(1,new T2(0,_17Y,_E7),new T(function(){return B(_17S(_17V));}));case 1:return new T2(1,new T2(0,_17Y,_EI),new T(function(){return B(_17S(_17V));}));case 2:return new T2(1,new T2(0,_17Y,_Ej),new T(function(){return B(_17S(_17V));}));case 3:return new T2(1,new T2(0,_17Y,_Ep),new T(function(){return B(_17S(_17V));}));case 4:return new T2(1,new T2(0,_17Y,_Ev),new T(function(){return B(_17S(_17V));}));case 5:return new T2(1,new T2(0,_17Y,_EW),new T(function(){return B(_17S(_17V));}));case 6:return new T2(1,new T2(0,_17Y,_EP),new T(function(){return B(_17S(_17V));}));case 7:return new T2(1,new T2(0,_17Y,_EI),new T(function(){return B(_17S(_17V));}));default:return new T2(1,new T2(0,_17Y,_EB),new T(function(){return B(_17S(_17V));}));}}};if(E(_17Y)==32){return new F(function(){return _17Z(_);});}else{switch(E(_17X)){case 0:return new T2(1,new T2(0,_17Y,_EB),new T(function(){return B(_17S(_17V));}));case 1:return new F(function(){return _17Z(_);});break;case 2:return new F(function(){return _17Z(_);});break;case 3:return new F(function(){return _17Z(_);});break;case 4:return new F(function(){return _17Z(_);});break;case 5:return new F(function(){return _17Z(_);});break;case 6:return new F(function(){return _17Z(_);});break;case 7:return new F(function(){return _17Z(_);});break;default:return new F(function(){return _17Z(_);});}}}},_181=function(_182){var _183=E(_182);return (_183._==0)?__Z:new T2(1,new T(function(){return B(_17S(_183.a));}),new T(function(){return B(_181(_183.b));}));},_184=function(_185){var _186=E(_185);if(!_186._){return __Z;}else{var _187=_186.b,_188=E(_186.a),_189=_188.b,_18a=E(_188.a),_18b=function(_18c){if(E(_18a)==32){return new T2(1,_188,new T(function(){return B(_184(_187));}));}else{switch(E(_189)){case 0:return new T2(1,new T2(0,_18a,_E7),new T(function(){return B(_184(_187));}));case 1:return new T2(1,new T2(0,_18a,_Ed),new T(function(){return B(_184(_187));}));case 2:return new T2(1,new T2(0,_18a,_Ej),new T(function(){return B(_184(_187));}));case 3:return new T2(1,new T2(0,_18a,_Ep),new T(function(){return B(_184(_187));}));case 4:return new T2(1,new T2(0,_18a,_Ev),new T(function(){return B(_184(_187));}));case 5:return new T2(1,new T2(0,_18a,_EW),new T(function(){return B(_184(_187));}));case 6:return new T2(1,new T2(0,_18a,_EP),new T(function(){return B(_184(_187));}));case 7:return new T2(1,new T2(0,_18a,_Ed),new T(function(){return B(_184(_187));}));default:return new T2(1,new T2(0,_18a,_EB),new T(function(){return B(_184(_187));}));}}};if(E(_18a)==32){return new F(function(){return _18b(_);});}else{if(E(_189)==8){return new T2(1,new T2(0,_18a,_E7),new T(function(){return B(_184(_187));}));}else{return new F(function(){return _18b(_);});}}}},_18d=function(_18e){var _18f=E(_18e);return (_18f._==0)?__Z:new T2(1,new T(function(){return B(_184(_18f.a));}),new T(function(){return B(_18d(_18f.b));}));},_18g=function(_18h,_18i,_18j,_18k,_18l,_18m,_18n,_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z,_18A,_18B,_18C,_18D,_18E,_18F,_18G,_18H,_18I,_18J,_18K,_18L,_18M){var _18N=E(_18i);if(!_18N._){return E(_17I);}else{var _18O=_18N.b,_18P=E(_18N.a);switch(E(_18P)){case 97:var _18Q=new T(function(){var _18R=E(_18O);if(!_18R._){return E(_17H);}else{return new T2(0,_18R.a,_18R.b);}}),_18S=new T(function(){var _18T=B(_14M(E(_18Q).b));return new T2(0,_18T.a,_18T.b);}),_18U=B(_Gb(B(_sw(_12Q,new T(function(){return E(E(_18S).b);})))));if(!_18U._){return E(_12O);}else{if(!E(_18U.b)._){var _18V=new T(function(){var _18W=B(_Gb(B(_sw(_12Q,new T(function(){return E(E(_18S).a);})))));if(!_18W._){return E(_12O);}else{if(!E(_18W.b)._){return E(_18W.a);}else{return E(_12P);}}},1);return {_:0,a:E({_:0,a:E(_18j),b:E(B(_Ke(_18V,E(_18U.a),new T(function(){return E(E(_18Q).a);}),_E7,_18k))),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};}else{return E(_12P);}}break;case 104:return {_:0,a:E({_:0,a:E(_18j),b:E(B(_181(_18k))),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};case 106:var _18X=E(_18O);if(!_18X._){return {_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k: -1,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};}else{if(E(_18X.a)==108){var _18Y=B(_Gb(B(_sw(_12Q,_18X.b))));return (_18Y._==0)?E(_12O):(E(_18Y.b)._==0)?{_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(B(_12p(_18h,_18u))),e:E(B(_12p(_18h,_18v))),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:E(_18Y.a),l:E(_18C),m:_18D,n:E({_:0,a:E(_ws),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)}:E(_12P);}else{var _18Z=B(_Gb(B(_sw(_12Q,_18X))));return (_18Z._==0)?E(_12O):(E(_18Z.b)._==0)?{_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:E(_18Z.a),l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)}:E(_12P);}}break;case 108:return {_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(B(_12p(_18h,_18u))),e:E(B(_12p(_18h,_18v))),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_ws),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};case 109:var _190=B(_12R(B(_6R(_18v,_18h)),_18O)),_191=_190.c,_192=B(_qJ(_191,_10));if(!E(_192)){var _193=B(_13g(_18h,new T2(0,new T(function(){return E(B(_6R(_18u,_18h)).a);}),new T2(1,_18P,_191)),_18u));}else{var _193=B(_12p(_18h,_18u));}if(!E(_192)){var _194=B(_13g(_18h,_190.a,_18v));}else{var _194=B(_12p(_18h,_18v));}return {_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(B(_16W(_190.b))),d:E(_193),e:E(_194),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_ws),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};case 114:var _195=B(_6R(_176,_18n));return {_:0,a:E({_:0,a:E(B(_6R(_17h,_18n))),b:E(B(_13W(_195.a,E(_195.b),new T(function(){return B(_6R(_17R,_18n));})))),c:B(_6R(_17n,_18n)),d:32,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_195),c:E(_17G),d:E(_18u),e:E(B(_6e(_17i,_18v))),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_ws),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};case 115:return {_:0,a:E({_:0,a:E(_18j),b:E(B(_18d(_18k))),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};case 116:var _196=B(_6R(_18v,_18h)),_197=B(_12R(_196,_18O)),_198=E(_197.a);if(!E(_198)){var _199=true;}else{var _199=false;}if(!E(_199)){var _19a=B(_13g(_18h,_198,_18v));}else{var _19a=B(_13g(_18h,_196+1|0,_18v));}if(!E(_199)){var _19b=__Z;}else{var _19b=E(_197.b);}if(!B(_qJ(_19b,_10))){var _19c=B(_18g(_18h,_19b,_18j,_18k,_18l,_18m,_18n,_18o,_18p,_18q,_18r,_18s,_18t,_18u,_19a,_18w,_18x,_18y,_18z,_18A,_18B,_18C,_18D,_18E,_18F,_18G,_18H,_18I,_18J,_18K,_18L,_18M)),_19d=E(_19c.a);return {_:0,a:E({_:0,a:E(_19d.a),b:E(_19d.b),c:_19d.c,d:_19d.d,e:_19d.e,f:_19d.f,g:E(B(_y(_18p,_18N))),h:E(_19d.h),i:E(_19d.i)}),b:E(_19c.b),c:E(_19c.c),d:E(_19c.d),e:E(_19c.e),f:E(_19c.f),g:E(_19c.g),h:_19c.h,i:_19c.i,j:_19c.j,k:_19c.k,l:E(_19c.l),m:_19c.m,n:E(_19c.n),o:E(_19c.o)};}else{return {_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_19a),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};}break;case 119:return {_:0,a:E({_:0,a:E(_17g),b:E(_17E),c:E(_17o),d:32,e:0,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_172),c:E(_17m),d:E(_18u),e:E(B(_6e(_17i,_18v))),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_ws),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};default:return {_:0,a:E({_:0,a:E(_18j),b:E(_18k),c:_18l,d:_18m,e:_18n,f:_18o,g:E(B(_y(_18p,_18N))),h:E(_18q),i:E(_18r)}),b:E(_18s),c:E(_18t),d:E(_18u),e:E(_18v),f:E(_18w),g:E(_18x),h:_18y,i:_18z,j:_18A,k:_18B,l:E(_18C),m:_18D,n:E({_:0,a:E(_18E),b:E(_18F),c:E(_18G),d:E(_18H),e:E(_18I),f:E(_18J),g:E(_18K),h:E(_18L)}),o:E(_18M)};}}},_19e=function(_19f,_19g,_19h,_19i,_19j,_19k,_19l,_19m,_19n,_19o,_19p,_19q,_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C,_19D,_19E,_19F,_19G,_19H,_19I,_19J,_19K){var _19L=E(_19g);if(!_19L._){return E(_17I);}else{var _19M=_19L.b,_19N=E(_19L.a);switch(E(_19N)){case 97:var _19O=new T(function(){var _19P=E(_19M);if(!_19P._){return E(_17H);}else{return new T2(0,_19P.a,_19P.b);}}),_19Q=new T(function(){var _19R=B(_14M(E(_19O).b));return new T2(0,_19R.a,_19R.b);}),_19S=B(_Gb(B(_sw(_12Q,new T(function(){return E(E(_19Q).b);})))));if(!_19S._){return E(_12O);}else{if(!E(_19S.b)._){var _19T=new T(function(){var _19U=B(_Gb(B(_sw(_12Q,new T(function(){return E(E(_19Q).a);})))));if(!_19U._){return E(_12O);}else{if(!E(_19U.b)._){return E(_19U.a);}else{return E(_12P);}}},1);return {_:0,a:E({_:0,a:E(_19h),b:E(B(_Ke(_19T,E(_19S.a),new T(function(){return E(E(_19O).a);}),_E7,_19i))),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};}else{return E(_12P);}}break;case 104:return {_:0,a:E({_:0,a:E(_19h),b:E(B(_181(_19i))),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};case 106:var _19V=E(_19M);if(!_19V._){return {_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k: -1,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};}else{if(E(_19V.a)==108){var _19W=E(_19f),_19X=B(_Gb(B(_sw(_12Q,_19V.b))));return (_19X._==0)?E(_12O):(E(_19X.b)._==0)?{_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(B(_12p(_19W,_19s))),e:E(B(_12p(_19W,_19t))),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:E(_19X.a),l:E(_19A),m:_19B,n:E({_:0,a:E(_ws),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)}:E(_12P);}else{var _19Y=B(_Gb(B(_sw(_12Q,_19V))));return (_19Y._==0)?E(_12O):(E(_19Y.b)._==0)?{_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:E(_19Y.a),l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)}:E(_12P);}}break;case 108:var _19Z=E(_19f);return {_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(B(_12p(_19Z,_19s))),e:E(B(_12p(_19Z,_19t))),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_ws),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};case 109:var _1a0=E(_19f),_1a1=B(_12R(B(_6R(_19t,_1a0)),_19M)),_1a2=_1a1.c,_1a3=B(_qJ(_1a2,_10));if(!E(_1a3)){var _1a4=B(_13g(_1a0,new T2(0,new T(function(){return E(B(_6R(_19s,_1a0)).a);}),new T2(1,_19N,_1a2)),_19s));}else{var _1a4=B(_12p(_1a0,_19s));}if(!E(_1a3)){var _1a5=B(_13g(_1a0,_1a1.a,_19t));}else{var _1a5=B(_12p(_1a0,_19t));}return {_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(B(_16W(_1a1.b))),d:E(_1a4),e:E(_1a5),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_ws),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};case 114:var _1a6=B(_6R(_176,_19l));return {_:0,a:E({_:0,a:E(B(_6R(_17h,_19l))),b:E(B(_13W(_1a6.a,E(_1a6.b),new T(function(){return B(_6R(_17R,_19l));})))),c:B(_6R(_17n,_19l)),d:32,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_1a6),c:E(_17G),d:E(_19s),e:E(B(_6e(_17i,_19t))),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_ws),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};case 115:return {_:0,a:E({_:0,a:E(_19h),b:E(B(_18d(_19i))),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};case 116:var _1a7=E(_19f),_1a8=B(_6R(_19t,_1a7)),_1a9=B(_12R(_1a8,_19M)),_1aa=E(_1a9.a);if(!E(_1aa)){var _1ab=true;}else{var _1ab=false;}if(!E(_1ab)){var _1ac=B(_13g(_1a7,_1aa,_19t));}else{var _1ac=B(_13g(_1a7,_1a8+1|0,_19t));}if(!E(_1ab)){var _1ad=__Z;}else{var _1ad=E(_1a9.b);}if(!B(_qJ(_1ad,_10))){var _1ae=B(_18g(_1a7,_1ad,_19h,_19i,_19j,_19k,_19l,_19m,_19n,_19o,_19p,_19q,_19r,_19s,_1ac,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C,_19D,_19E,_19F,_19G,_19H,_19I,_19J,_19K)),_1af=E(_1ae.a);return {_:0,a:E({_:0,a:E(_1af.a),b:E(_1af.b),c:_1af.c,d:_1af.d,e:_1af.e,f:_1af.f,g:E(B(_y(_19n,_19L))),h:E(_1af.h),i:E(_1af.i)}),b:E(_1ae.b),c:E(_1ae.c),d:E(_1ae.d),e:E(_1ae.e),f:E(_1ae.f),g:E(_1ae.g),h:_1ae.h,i:_1ae.i,j:_1ae.j,k:_1ae.k,l:E(_1ae.l),m:_1ae.m,n:E(_1ae.n),o:E(_1ae.o)};}else{return {_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_1ac),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};}break;case 119:return {_:0,a:E({_:0,a:E(_17g),b:E(_17E),c:E(_17o),d:32,e:0,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_172),c:E(_17m),d:E(_19s),e:E(B(_6e(_17i,_19t))),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_ws),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};default:return {_:0,a:E({_:0,a:E(_19h),b:E(_19i),c:_19j,d:_19k,e:_19l,f:_19m,g:E(B(_y(_19n,_19L))),h:E(_19o),i:E(_19p)}),b:E(_19q),c:E(_19r),d:E(_19s),e:E(_19t),f:E(_19u),g:E(_19v),h:_19w,i:_19x,j:_19y,k:_19z,l:E(_19A),m:_19B,n:E({_:0,a:E(_19C),b:E(_19D),c:E(_19E),d:E(_19F),e:E(_19G),f:E(_19H),g:E(_19I),h:E(_19J)}),o:E(_19K)};}}},_1ag=function(_1ah,_1ai){while(1){var _1aj=E(_1ai);if(!_1aj._){return __Z;}else{var _1ak=_1aj.b,_1al=E(_1ah);if(_1al==1){return E(_1ak);}else{_1ah=_1al-1|0;_1ai=_1ak;continue;}}}},_1am=new T(function(){return B(unCStr("X"));}),_1an=new T(function(){return B(_e7("Check.hs:(81,7)-(86,39)|function chAnd"));}),_1ao=38,_1ap=function(_1aq,_1ar,_1as,_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC,_1aD,_1aE,_1aF,_1aG,_1aH){var _1aI=E(_1as);if(!_1aI._){return {_:0,a:_1at,b:_1au,c:_1av,d:_1aw,e:_1ax,f:_1ay,g:_1az,h:_1aA,i:_1aB,j:_1aC,k:_1aD,l:_1aE,m:_1aF,n:_1aG,o:_1aH};}else{var _1aJ=_1aI.b,_1aK=E(_1aI.a),_1aL=_1aK.a,_1aM=_1aK.b,_1aN=function(_1aO,_1aP,_1aQ){var _1aR=function(_1aS,_1aT){if(!B(_qJ(_1aS,_10))){var _1aU=E(_1at),_1aV=E(_1aG),_1aW=B(_19e(_1aT,_1aS,_1aU.a,_1aU.b,_1aU.c,_1aU.d,_1aU.e,_1aU.f,_1aU.g,_1aU.h,_1aU.i,_1au,_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC,_1aD,_1aE,_1aF,_1aV.a,_1aV.b,_1aV.c,_1aV.d,_1aV.e,_1aV.f,_1aV.g,_1aV.h,_1aH)),_1aX=_1aW.a,_1aY=_1aW.b,_1aZ=_1aW.c,_1b0=_1aW.d,_1b1=_1aW.e,_1b2=_1aW.f,_1b3=_1aW.g,_1b4=_1aW.h,_1b5=_1aW.i,_1b6=_1aW.j,_1b7=_1aW.k,_1b8=_1aW.l,_1b9=_1aW.m,_1ba=_1aW.n,_1bb=_1aW.o;if(B(_mt(_1b1,0))!=B(_mt(_1ax,0))){return {_:0,a:_1aX,b:_1aY,c:_1aZ,d:_1b0,e:_1b1,f:_1b2,g:_1b3,h:_1b4,i:_1b5,j:_1b6,k:_1b7,l:_1b8,m:_1b9,n:_1ba,o:_1bb};}else{return new F(function(){return _1ap(new T(function(){return E(_1aq)+1|0;}),_1ar,_1aJ,_1aX,_1aY,_1aZ,_1b0,_1b1,_1b2,_1b3,_1b4,_1b5,_1b6,_1b7,_1b8,_1b9,_1ba,_1bb);});}}else{return new F(function(){return _1ap(new T(function(){return E(_1aq)+1|0;}),_1ar,_1aJ,_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC,_1aD,_1aE,_1aF,_1aG,_1aH);});}},_1bc=B(_mt(_1ar,0))-B(_mt(new T2(1,_1aO,_1aP),0))|0;if(_1bc>0){var _1bd=B(_1ag(_1bc,_1ar));}else{var _1bd=E(_1ar);}if(E(B(_127(_1aO,_1aP,_Ru)))==63){var _1be=B(_Q4(_1aO,_1aP));}else{var _1be=new T2(1,_1aO,_1aP);}var _1bf=function(_1bg){if(!B(_4B(_h7,_1ao,_1aL))){return new T2(0,_1aM,_1aq);}else{var _1bh=function(_1bi){while(1){var _1bj=B((function(_1bk){var _1bl=E(_1bk);if(!_1bl._){return true;}else{var _1bm=_1bl.b,_1bn=E(_1bl.a);if(!_1bn._){return E(_1an);}else{switch(E(_1bn.a)){case 99:var _1bo=E(_1at);if(!E(_1bo.i)){return false;}else{var _1bp=function(_1bq){while(1){var _1br=E(_1bq);if(!_1br._){return true;}else{var _1bs=_1br.b,_1bt=E(_1br.a);if(!_1bt._){return E(_1an);}else{if(E(_1bt.a)==115){var _1bu=B(_Gb(B(_sw(_12Q,_1bt.b))));if(!_1bu._){return E(_12O);}else{if(!E(_1bu.b)._){if(_1bo.e!=E(_1bu.a)){return false;}else{_1bq=_1bs;continue;}}else{return E(_12P);}}}else{_1bq=_1bs;continue;}}}}};return new F(function(){return _1bp(_1bm);});}break;case 115:var _1bv=E(_1at),_1bw=_1bv.e,_1bx=B(_Gb(B(_sw(_12Q,_1bn.b))));if(!_1bx._){return E(_12O);}else{if(!E(_1bx.b)._){if(_1bw!=E(_1bx.a)){return false;}else{var _1by=function(_1bz){while(1){var _1bA=E(_1bz);if(!_1bA._){return true;}else{var _1bB=_1bA.b,_1bC=E(_1bA.a);if(!_1bC._){return E(_1an);}else{switch(E(_1bC.a)){case 99:if(!E(_1bv.i)){return false;}else{_1bz=_1bB;continue;}break;case 115:var _1bD=B(_Gb(B(_sw(_12Q,_1bC.b))));if(!_1bD._){return E(_12O);}else{if(!E(_1bD.b)._){if(_1bw!=E(_1bD.a)){return false;}else{_1bz=_1bB;continue;}}else{return E(_12P);}}break;default:_1bz=_1bB;continue;}}}}};return new F(function(){return _1by(_1bm);});}}else{return E(_12P);}}break;default:_1bi=_1bm;return __continue;}}}})(_1bi));if(_1bj!=__continue){return _1bj;}}};return (!B(_1bh(_1aQ)))?(!B(_qJ(_1be,_1am)))?new T2(0,_10,_1aq):new T2(0,_1aM,_1aq):new T2(0,_1aM,_1aq);}};if(E(B(_12f(_1aO,_1aP,_Ru)))==63){if(!B(_69(_1bd,_10))){var _1bE=E(_1bd);if(!_1bE._){return E(_Q9);}else{if(!B(_qJ(_1be,B(_Q4(_1bE.a,_1bE.b))))){if(!B(_qJ(_1be,_1am))){return new F(function(){return _1aR(_10,_1aq);});}else{return new F(function(){return _1aR(_1aM,_1aq);});}}else{var _1bF=B(_1bf(_));return new F(function(){return _1aR(_1bF.a,_1bF.b);});}}}else{if(!B(_qJ(_1be,_1bd))){if(!B(_qJ(_1be,_1am))){return new F(function(){return _1aR(_10,_1aq);});}else{return new F(function(){return _1aR(_1aM,_1aq);});}}else{var _1bG=B(_1bf(_));return new F(function(){return _1aR(_1bG.a,_1bG.b);});}}}else{if(!B(_qJ(_1be,_1bd))){if(!B(_qJ(_1be,_1am))){return new F(function(){return _1aR(_10,_1aq);});}else{return new F(function(){return _1aR(_1aM,_1aq);});}}else{var _1bH=B(_1bf(_));return new F(function(){return _1aR(_1bH.a,_1bH.b);});}}},_1bI=E(_1aL);if(!_1bI._){return E(_Ru);}else{var _1bJ=_1bI.a,_1bK=E(_1bI.b);if(!_1bK._){return new F(function(){return _1aN(_1bJ,_10,_10);});}else{var _1bL=E(_1bJ),_1bM=new T(function(){var _1bN=B(_H6(38,_1bK.a,_1bK.b));return new T2(0,_1bN.a,_1bN.b);});if(E(_1bL)==38){return E(_Ru);}else{return new F(function(){return _1aN(_1bL,new T(function(){return E(E(_1bM).a);}),new T(function(){return E(E(_1bM).b);}));});}}}}},_1bO="]",_1bP="}",_1bQ=":",_1bR=",",_1bS=new T(function(){return eval("JSON.stringify");}),_1bT="false",_1bU="null",_1bV="[",_1bW="{",_1bX="\"",_1bY="true",_1bZ=function(_1c0,_1c1){var _1c2=E(_1c1);switch(_1c2._){case 0:return new T2(0,new T(function(){return jsShow(_1c2.a);}),_1c0);case 1:return new T2(0,new T(function(){var _1c3=__app1(E(_1bS),_1c2.a);return String(_1c3);}),_1c0);case 2:return (!E(_1c2.a))?new T2(0,_1bT,_1c0):new T2(0,_1bY,_1c0);case 3:var _1c4=E(_1c2.a);if(!_1c4._){return new T2(0,_1bV,new T2(1,_1bO,_1c0));}else{var _1c5=new T(function(){var _1c6=new T(function(){var _1c7=function(_1c8){var _1c9=E(_1c8);if(!_1c9._){return E(new T2(1,_1bO,_1c0));}else{var _1ca=new T(function(){var _1cb=B(_1bZ(new T(function(){return B(_1c7(_1c9.b));}),_1c9.a));return new T2(1,_1cb.a,_1cb.b);});return new T2(1,_1bR,_1ca);}};return B(_1c7(_1c4.b));}),_1cc=B(_1bZ(_1c6,_1c4.a));return new T2(1,_1cc.a,_1cc.b);});return new T2(0,_1bV,_1c5);}break;case 4:var _1cd=E(_1c2.a);if(!_1cd._){return new T2(0,_1bW,new T2(1,_1bP,_1c0));}else{var _1ce=E(_1cd.a),_1cf=new T(function(){var _1cg=new T(function(){var _1ch=function(_1ci){var _1cj=E(_1ci);if(!_1cj._){return E(new T2(1,_1bP,_1c0));}else{var _1ck=E(_1cj.a),_1cl=new T(function(){var _1cm=B(_1bZ(new T(function(){return B(_1ch(_1cj.b));}),_1ck.b));return new T2(1,_1cm.a,_1cm.b);});return new T2(1,_1bR,new T2(1,_1bX,new T2(1,_1ck.a,new T2(1,_1bX,new T2(1,_1bQ,_1cl)))));}};return B(_1ch(_1cd.b));}),_1cn=B(_1bZ(_1cg,_1ce.b));return new T2(1,_1cn.a,_1cn.b);});return new T2(0,_1bW,new T2(1,new T(function(){var _1co=__app1(E(_1bS),E(_1ce.a));return String(_1co);}),new T2(1,_1bQ,_1cf)));}break;default:return new T2(0,_1bU,_1c0);}},_1cp=new T(function(){return toJSStr(_10);}),_1cq=function(_1cr){var _1cs=B(_1bZ(_10,_1cr)),_1ct=jsCat(new T2(1,_1cs.a,_1cs.b),E(_1cp));return E(_1ct);},_1cu=function(_1cv){var _1cw=E(_1cv);if(!_1cw._){return new T2(0,_10,_10);}else{var _1cx=E(_1cw.a),_1cy=new T(function(){var _1cz=B(_1cu(_1cw.b));return new T2(0,_1cz.a,_1cz.b);});return new T2(0,new T2(1,_1cx.a,new T(function(){return E(E(_1cy).a);})),new T2(1,_1cx.b,new T(function(){return E(E(_1cy).b);})));}},_1cA=function(_1cB){var _1cC=E(_1cB);switch(_1cC){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1cC>>>0>1114111){return new F(function(){return _wC(_1cC);});}else{return _1cC;}}},_1cD=function(_1cE,_1cF,_1cG){while(1){var _1cH=E(_1cF);if(!_1cH._){return (E(_1cG)._==0)?true:false;}else{var _1cI=E(_1cG);if(!_1cI._){return false;}else{if(!B(A3(_4z,_1cE,_1cH.a,_1cI.a))){return false;}else{_1cF=_1cH.b;_1cG=_1cI.b;continue;}}}}},_1cJ=function(_1cK,_1cL){return (!B(_1cD(_rg,_1cK,_1cL)))?true:false;},_1cM=function(_1cN,_1cO){return new F(function(){return _1cD(_rg,_1cN,_1cO);});},_1cP=new T2(0,_1cM,_1cJ),_1cQ=function(_1cR){var _1cS=E(_1cR);if(!_1cS._){return new T2(0,_10,_10);}else{var _1cT=E(_1cS.a),_1cU=new T(function(){var _1cV=B(_1cQ(_1cS.b));return new T2(0,_1cV.a,_1cV.b);});return new T2(0,new T2(1,_1cT.a,new T(function(){return E(E(_1cU).a);})),new T2(1,_1cT.b,new T(function(){return E(E(_1cU).b);})));}},_1cW=function(_1cX,_1cY){while(1){var _1cZ=E(_1cY);if(!_1cZ._){return __Z;}else{var _1d0=_1cZ.b,_1d1=E(_1cX);if(_1d1==1){return E(_1d0);}else{_1cX=_1d1-1|0;_1cY=_1d0;continue;}}}},_1d2=function(_1d3,_1d4){while(1){var _1d5=E(_1d4);if(!_1d5._){return __Z;}else{var _1d6=_1d5.b,_1d7=E(_1d3);if(_1d7==1){return E(_1d6);}else{_1d3=_1d7-1|0;_1d4=_1d6;continue;}}}},_1d8=function(_1d9){return new F(function(){return _Gi(_1d9,_10);});},_1da=function(_1db,_1dc,_1dd,_1de){var _1df=new T(function(){return B(_LJ(_h7,_1dc,_1dd));}),_1dg=new T(function(){var _1dh=E(_1df),_1di=new T(function(){var _1dj=_1dh+1|0;if(_1dj>0){return B(_1d2(_1dj,_1dd));}else{return E(_1dd);}});if(0>=_1dh){return E(_1di);}else{var _1dk=function(_1dl,_1dm){var _1dn=E(_1dl);if(!_1dn._){return E(_1di);}else{var _1do=_1dn.a,_1dp=E(_1dm);return (_1dp==1)?new T2(1,_1do,_1di):new T2(1,_1do,new T(function(){return B(_1dk(_1dn.b,_1dp-1|0));}));}};return B(_1dk(_1dd,_1dh));}}),_1dq=new T(function(){var _1dr=E(_1df),_1ds=new T(function(){if(E(_1dc)==94){return B(A2(_1db,new T(function(){return B(_6R(_1de,_1dr+1|0));}),new T(function(){return B(_6R(_1de,_1dr));})));}else{return B(A2(_1db,new T(function(){return B(_6R(_1de,_1dr));}),new T(function(){return B(_6R(_1de,_1dr+1|0));})));}}),_1dt=new T2(1,_1ds,new T(function(){var _1du=_1dr+2|0;if(_1du>0){return B(_1cW(_1du,_1de));}else{return E(_1de);}}));if(0>=_1dr){return E(_1dt);}else{var _1dv=function(_1dw,_1dx){var _1dy=E(_1dw);if(!_1dy._){return E(_1dt);}else{var _1dz=_1dy.a,_1dA=E(_1dx);return (_1dA==1)?new T2(1,_1dz,_1dt):new T2(1,_1dz,new T(function(){return B(_1dv(_1dy.b,_1dA-1|0));}));}};return B(_1dv(_1de,_1dr));}});return (E(_1dc)==94)?new T2(0,new T(function(){return B(_1d8(_1dg));}),new T(function(){return B(_1d8(_1dq));})):new T2(0,_1dg,_1dq);},_1dB=new T(function(){return B(_cn(_oM,_oL));}),_1dC=function(_1dD,_1dE,_1dF){while(1){if(!E(_1dB)){if(!B(_cn(B(_Z9(_1dE,_oM)),_oL))){if(!B(_cn(_1dE,_aV))){var _1dG=B(_of(_1dD,_1dD)),_1dH=B(_YU(B(_eO(_1dE,_aV)),_oM)),_1dI=B(_of(_1dD,_1dF));_1dD=_1dG;_1dE=_1dH;_1dF=_1dI;continue;}else{return new F(function(){return _of(_1dD,_1dF);});}}else{var _1dG=B(_of(_1dD,_1dD)),_1dH=B(_YU(_1dE,_oM));_1dD=_1dG;_1dE=_1dH;continue;}}else{return E(_9U);}}},_1dJ=function(_1dK,_1dL){while(1){if(!E(_1dB)){if(!B(_cn(B(_Z9(_1dL,_oM)),_oL))){if(!B(_cn(_1dL,_aV))){return new F(function(){return _1dC(B(_of(_1dK,_1dK)),B(_YU(B(_eO(_1dL,_aV)),_oM)),_1dK);});}else{return E(_1dK);}}else{var _1dM=B(_of(_1dK,_1dK)),_1dN=B(_YU(_1dL,_oM));_1dK=_1dM;_1dL=_1dN;continue;}}else{return E(_9U);}}},_1dO=function(_1dP,_1dQ){if(!B(_d7(_1dQ,_oL))){if(!B(_cn(_1dQ,_oL))){return new F(function(){return _1dJ(_1dP,_1dQ);});}else{return E(_aV);}}else{return E(_pr);}},_1dR=94,_1dS=45,_1dT=43,_1dU=42,_1dV=function(_1dW,_1dX){while(1){var _1dY=B((function(_1dZ,_1e0){var _1e1=E(_1e0);if(!_1e1._){return __Z;}else{if((B(_mt(_1dZ,0))+1|0)==B(_mt(_1e1,0))){if(!B(_4B(_h7,_1dR,_1dZ))){if(!B(_4B(_h7,_1dU,_1dZ))){if(!B(_4B(_h7,_1dT,_1dZ))){if(!B(_4B(_h7,_1dS,_1dZ))){return E(_1e1);}else{var _1e2=B(_1da(_eO,45,_1dZ,_1e1));_1dW=_1e2.a;_1dX=_1e2.b;return __continue;}}else{var _1e3=B(_1da(_cv,43,_1dZ,_1e1));_1dW=_1e3.a;_1dX=_1e3.b;return __continue;}}else{var _1e4=B(_1da(_of,42,_1dZ,_1e1));_1dW=_1e4.a;_1dX=_1e4.b;return __continue;}}else{var _1e5=B(_1da(_1dO,94,new T(function(){return B(_1d8(_1dZ));}),new T(function(){return B(_Gi(_1e1,_10));})));_1dW=_1e5.a;_1dX=_1e5.b;return __continue;}}else{return __Z;}}})(_1dW,_1dX));if(_1dY!=__continue){return _1dY;}}},_1e6=function(_1e7){var _1e8=E(_1e7);if(!_1e8._){return new T2(0,_10,_10);}else{var _1e9=E(_1e8.a),_1ea=new T(function(){var _1eb=B(_1e6(_1e8.b));return new T2(0,_1eb.a,_1eb.b);});return new T2(0,new T2(1,_1e9.a,new T(function(){return E(E(_1ea).a);})),new T2(1,_1e9.b,new T(function(){return E(E(_1ea).b);})));}},_1ec=new T(function(){return B(unCStr("0123456789+-"));}),_1ed=function(_1ee){while(1){var _1ef=E(_1ee);if(!_1ef._){return true;}else{if(!B(_4B(_h7,_1ef.a,_1ec))){return false;}else{_1ee=_1ef.b;continue;}}}},_1eg=new T(function(){return B(err(_sp));}),_1eh=new T(function(){return B(err(_sr));}),_1ei=function(_1ej,_1ek){var _1el=function(_1em,_1en){var _1eo=function(_1ep){return new F(function(){return A1(_1en,new T(function(){return B(_ft(_1ep));}));});},_1eq=new T(function(){return B(_D5(function(_1er){return new F(function(){return A3(_1ej,_1er,_1em,_1eo);});}));}),_1es=function(_1et){return E(_1eq);},_1eu=function(_1ev){return new F(function(){return A2(_BM,_1ev,_1es);});},_1ew=new T(function(){return B(_D5(function(_1ex){var _1ey=E(_1ex);if(_1ey._==4){var _1ez=E(_1ey.a);if(!_1ez._){return new F(function(){return A3(_1ej,_1ey,_1em,_1en);});}else{if(E(_1ez.a)==45){if(!E(_1ez.b)._){return E(new T1(1,_1eu));}else{return new F(function(){return A3(_1ej,_1ey,_1em,_1en);});}}else{return new F(function(){return A3(_1ej,_1ey,_1em,_1en);});}}}else{return new F(function(){return A3(_1ej,_1ey,_1em,_1en);});}}));}),_1eA=function(_1eB){return E(_1ew);};return new T1(1,function(_1eC){return new F(function(){return A2(_BM,_1eC,_1eA);});});};return new F(function(){return _DW(_1el,_1ek);});},_1eD=function(_1eE){var _1eF=E(_1eE);if(_1eF._==5){var _1eG=B(_FU(_1eF.a));return (_1eG._==0)?E(_FZ):function(_1eH,_1eI){return new F(function(){return A1(_1eI,_1eG.a);});};}else{return E(_FZ);}},_1eJ=new T(function(){return B(A3(_1ei,_1eD,_DC,_Fp));}),_1eK=function(_1eL,_1eM){var _1eN=E(_1eM);if(!_1eN._){return __Z;}else{var _1eO=_1eN.a,_1eP=_1eN.b,_1eQ=function(_1eR){var _1eS=B(_1e6(_1eL)),_1eT=_1eS.a;return (!B(_4B(_qe,_1eO,_1eT)))?__Z:new T2(1,new T(function(){return B(_6R(_1eS.b,B(_LJ(_qe,_1eO,_1eT))));}),new T(function(){return B(_1eK(_1eL,_1eP));}));};if(!B(_69(_1eO,_10))){if(!B(_1ed(_1eO))){return new F(function(){return _1eQ(_);});}else{return new T2(1,new T(function(){var _1eU=B(_Gb(B(_sw(_1eJ,_1eO))));if(!_1eU._){return E(_1eg);}else{if(!E(_1eU.b)._){return E(_1eU.a);}else{return E(_1eh);}}}),new T(function(){return B(_1eK(_1eL,_1eP));}));}}else{return new F(function(){return _1eQ(_);});}}},_1eV=new T(function(){return B(unCStr("+-*^"));}),_1eW=new T(function(){return B(unCStr("0123456789"));}),_1eX=new T(function(){return B(_KF("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1eY=new T2(1,_10,_10),_1eZ=function(_1f0){var _1f1=E(_1f0);if(!_1f1._){return new T2(0,_1eY,_10);}else{var _1f2=_1f1.a,_1f3=new T(function(){var _1f4=B(_1eZ(_1f1.b)),_1f5=E(_1f4.a);if(!_1f5._){return E(_1eX);}else{return new T3(0,_1f5.a,_1f5.b,_1f4.b);}});return (!B(_4B(_h7,_1f2,_1eW)))?(!B(_4B(_h7,_1f2,_1eV)))?new T2(0,new T2(1,new T2(1,_1f2,new T(function(){return E(E(_1f3).a);})),new T(function(){return E(E(_1f3).b);})),new T(function(){return E(E(_1f3).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1f3).a);}),new T(function(){return E(E(_1f3).b);}))),new T2(1,_1f2,new T(function(){return E(E(_1f3).c);}))):new T2(0,new T2(1,new T2(1,_1f2,new T(function(){return E(E(_1f3).a);})),new T(function(){return E(E(_1f3).b);})),new T(function(){return E(E(_1f3).c);}));}},_1f6=function(_1f7,_1f8){var _1f9=new T(function(){var _1fa=B(_1eZ(_1f8)),_1fb=E(_1fa.a);if(!_1fb._){return E(_1eX);}else{return new T3(0,_1fb.a,_1fb.b,_1fa.b);}});return (!B(_4B(_h7,_1f7,_1eW)))?(!B(_4B(_h7,_1f7,_1eV)))?new T2(0,new T2(1,new T2(1,_1f7,new T(function(){return E(E(_1f9).a);})),new T(function(){return E(E(_1f9).b);})),new T(function(){return E(E(_1f9).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1f9).a);}),new T(function(){return E(E(_1f9).b);}))),new T2(1,_1f7,new T(function(){return E(E(_1f9).c);}))):new T2(0,new T2(1,new T2(1,_1f7,new T(function(){return E(E(_1f9).a);})),new T(function(){return E(E(_1f9).b);})),new T(function(){return E(E(_1f9).c);}));},_1fc=function(_1fd,_1fe){while(1){var _1ff=E(_1fd);if(!_1ff._){return E(_1fe);}else{_1fd=_1ff.b;_1fe=_1ff.a;continue;}}},_1fg=function(_1fh,_1fi,_1fj){return new F(function(){return _1fc(_1fi,_1fh);});},_1fk=function(_1fl,_1fm){var _1fn=E(_1fm);if(!_1fn._){return __Z;}else{var _1fo=B(_1f6(_1fn.a,_1fn.b)),_1fp=B(_1dV(_1fo.b,B(_1eK(_1fl,_1fo.a))));if(!_1fp._){return E(_1fn);}else{return new F(function(){return _11d(0,B(_1fg(_1fp.a,_1fp.b,_Ru)),_10);});}}},_1fq=function(_1fr,_1fs){var _1ft=function(_1fu,_1fv){while(1){var _1fw=B((function(_1fx,_1fy){var _1fz=E(_1fy);if(!_1fz._){return (!B(_qJ(_1fx,_10)))?new T2(0,_ws,_1fx):new T2(0,_wr,_10);}else{var _1fA=_1fz.b,_1fB=B(_1cQ(_1fz.a)).a;if(!B(_4B(_h7,_14g,_1fB))){var _1fC=_1fx;_1fu=_1fC;_1fv=_1fA;return __continue;}else{var _1fD=B(_14M(_1fB)),_1fE=_1fD.a,_1fF=_1fD.b;if(!B(_69(_1fF,_10))){if(!B(_qJ(B(_1fk(_1fr,_1fE)),B(_1fk(_1fr,_1fF))))){return new T2(0,_wr,_10);}else{var _1fG=new T(function(){if(!B(_qJ(_1fx,_10))){return B(_y(_1fx,new T(function(){return B(unAppCStr(" ",_1fE));},1)));}else{return E(_1fE);}});_1fu=_1fG;_1fv=_1fA;return __continue;}}else{return new T2(0,_wr,_10);}}}})(_1fu,_1fv));if(_1fw!=__continue){return _1fw;}}};return new F(function(){return _1ft(_10,_1fs);});},_1fH=function(_1fI,_1fJ){var _1fK=new T(function(){var _1fL=B(_Gb(B(_sw(_113,new T(function(){return B(_pO(3,B(_I(0,imul(E(_1fJ),E(_1fI)-1|0)|0,_10))));})))));if(!_1fL._){return E(_112);}else{if(!E(_1fL.b)._){return E(_1fL.a);}else{return E(_111);}}});return new T2(0,new T(function(){return B(_av(_1fK,_1fI));}),_1fK);},_1fM=function(_1fN,_1fO){while(1){var _1fP=E(_1fO);if(!_1fP._){return __Z;}else{var _1fQ=_1fP.b,_1fR=E(_1fN);if(_1fR==1){return E(_1fQ);}else{_1fN=_1fR-1|0;_1fO=_1fQ;continue;}}}},_1fS=function(_1fT,_1fU){while(1){var _1fV=E(_1fU);if(!_1fV._){return __Z;}else{var _1fW=_1fV.b,_1fX=E(_1fT);if(_1fX==1){return E(_1fW);}else{_1fT=_1fX-1|0;_1fU=_1fW;continue;}}}},_1fY=64,_1fZ=new T2(1,_1fY,_10),_1g0=function(_1g1,_1g2){return new F(function(){return _6R(_1g1,E(_1g2));});},_1g3=function(_1g4,_1g5,_1g6,_1g7){return (!B(_qJ(_1g4,_1g6)))?true:(!B(_cn(_1g5,_1g7)))?true:false;},_1g8=function(_1g9,_1ga){var _1gb=E(_1g9),_1gc=E(_1ga);return new F(function(){return _1g3(_1gb.a,_1gb.b,_1gc.a,_1gc.b);});},_1gd=function(_1ge,_1gf,_1gg,_1gh){if(!B(_qJ(_1ge,_1gg))){return false;}else{return new F(function(){return _cn(_1gf,_1gh);});}},_1gi=function(_1gj,_1gk){var _1gl=E(_1gj),_1gm=E(_1gk);return new F(function(){return _1gd(_1gl.a,_1gl.b,_1gm.a,_1gm.b);});},_1gn=new T2(0,_1gi,_1g8),_1go=function(_1gp){var _1gq=E(_1gp);if(!_1gq._){return new T2(0,_10,_10);}else{var _1gr=E(_1gq.a),_1gs=new T(function(){var _1gt=B(_1go(_1gq.b));return new T2(0,_1gt.a,_1gt.b);});return new T2(0,new T2(1,_1gr.a,new T(function(){return E(E(_1gs).a);})),new T2(1,_1gr.b,new T(function(){return E(E(_1gs).b);})));}},_1gu=function(_1gv){var _1gw=E(_1gv);if(!_1gw._){return new T2(0,_10,_10);}else{var _1gx=E(_1gw.a),_1gy=new T(function(){var _1gz=B(_1gu(_1gw.b));return new T2(0,_1gz.a,_1gz.b);});return new T2(0,new T2(1,_1gx.a,new T(function(){return E(E(_1gy).a);})),new T2(1,_1gx.b,new T(function(){return E(E(_1gy).b);})));}},_1gA=function(_1gB){var _1gC=E(_1gB);if(!_1gC._){return new T2(0,_10,_10);}else{var _1gD=E(_1gC.a),_1gE=new T(function(){var _1gF=B(_1gA(_1gC.b));return new T2(0,_1gF.a,_1gF.b);});return new T2(0,new T2(1,_1gD.a,new T(function(){return E(E(_1gE).a);})),new T2(1,_1gD.b,new T(function(){return E(E(_1gE).b);})));}},_1gG=function(_1gH,_1gI){return (_1gH<=_1gI)?new T2(1,_1gH,new T(function(){return B(_1gG(_1gH+1|0,_1gI));})):__Z;},_1gJ=new T(function(){return B(_1gG(65,90));}),_1gK=function(_1gL){return (_1gL<=122)?new T2(1,_1gL,new T(function(){return B(_1gK(_1gL+1|0));})):E(_1gJ);},_1gM=new T(function(){return B(_1gK(97));}),_1gN=function(_1gO){while(1){var _1gP=E(_1gO);if(!_1gP._){return true;}else{if(!B(_4B(_h7,_1gP.a,_1gM))){return false;}else{_1gO=_1gP.b;continue;}}}},_1gQ=new T1(0,2),_1gR=new T1(0,1),_1gS=new T1(0,0),_1gT=new T2(0,_10,_1gS),_1gU=new T(function(){return B(err(_sp));}),_1gV=new T(function(){return B(err(_sr));}),_1gW=new T(function(){return B(A3(_1ei,_1eD,_DC,_Fp));}),_1gX=new T2(0,_10,_10),_1gY=function(_1gZ,_1h0,_1h1){var _1h2=new T(function(){var _1h3=B(_1go(_1h0));return new T2(0,_1h3.a,_1h3.b);}),_1h4=new T(function(){return E(E(_1h2).b);}),_1h5=new T(function(){var _1h6=B(_1gu(E(_1h2).a));return new T2(0,_1h6.a,_1h6.b);}),_1h7=new T(function(){return E(E(_1h5).b);}),_1h8=new T(function(){return E(E(_1h5).a);}),_1h9=function(_1ha){while(1){var _1hb=B((function(_1hc){var _1hd=E(_1hc);if(!_1hd._){return __Z;}else{var _1he=_1hd.b,_1hf=new T(function(){return E(B(_1gA(_1hd.a)).a);}),_1hg=new T(function(){return B(_4B(_h7,_14g,_1hf));}),_1hh=new T(function(){if(!E(_1hg)){return E(_1gX);}else{var _1hi=B(_14M(_1hf));return new T2(0,_1hi.a,_1hi.b);}}),_1hj=new T(function(){return E(E(_1hh).a);}),_1hk=new T(function(){return B(_LJ(_qe,_1hj,_1h8));});if(!B(_4B(_qe,_1hj,_1h8))){var _1hl=false;}else{var _1hl=B(_6R(_1h4,E(_1hk)))==E(_1gZ);}var _1hm=new T(function(){return E(E(_1hh).b);}),_1hn=new T(function(){return B(_LJ(_qe,_1hm,_1h8));}),_1ho=new T(function(){if(!B(_4B(_qe,_1hm,_1h8))){return false;}else{return B(_6R(_1h4,E(_1hn)))==E(_1gZ);}}),_1hp=function(_1hq){var _1hr=function(_1hs){return (!E(_1hl))?__Z:(!E(_1ho))?__Z:new T2(1,new T2(0,_1hj,new T(function(){return B(_1g0(_1h7,_1hk));})),new T2(1,new T2(0,_1hm,new T(function(){return B(_1g0(_1h7,_1hn));})),_10));};if(!E(_1hl)){if(!E(_1ho)){return new F(function(){return _1hr(_);});}else{return new T2(1,new T2(0,_1hm,new T(function(){return B(_1g0(_1h7,_1hn));})),_10);}}else{return new F(function(){return _1hr(_);});}};if(!E(_1hl)){var _1ht=B(_1hp(_));}else{if(!E(_1ho)){var _1hu=new T2(1,new T2(0,_1hj,new T(function(){return B(_1g0(_1h7,_1hk));})),_10);}else{var _1hu=B(_1hp(_));}var _1ht=_1hu;}if(!B(_1cD(_1gn,_1ht,_10))){return new F(function(){return _y(_1ht,new T(function(){return B(_1h9(_1he));},1));});}else{if(!E(_1hg)){_1ha=_1he;return __continue;}else{var _1hv=new T(function(){if(!E(_1hl)){return E(_1ho);}else{return true;}}),_1hw=function(_1hx){return (!B(_1gN(_1hm)))?E(_1gS):(!E(_1hv))?(!B(_69(_1hj,_10)))?(!B(_1ed(_1hj)))?E(_1gS):E(_1gQ):E(_1gS):E(_1gS);};if(!B(_1gN(_1hj))){var _1hy=B(_1hw(_));}else{if(!E(_1hv)){if(!B(_69(_1hm,_10))){if(!B(_1ed(_1hm))){var _1hz=B(_1hw(_));}else{var _1hz=E(_1gR);}var _1hA=_1hz;}else{var _1hA=B(_1hw(_));}var _1hB=_1hA;}else{var _1hB=B(_1hw(_));}var _1hy=_1hB;}if(!B(_cY(_1hy,_1gS))){_1ha=_1he;return __continue;}else{var _1hC=new T(function(){if(!B(_cn(_1hy,_1gR))){if(!B(_cn(_1hy,_1gQ))){return E(_1gT);}else{return new T2(0,_1hm,new T(function(){var _1hD=B(_Gb(B(_sw(_1gW,_1hj))));if(!_1hD._){return E(_1gU);}else{if(!E(_1hD.b)._){return E(_1hD.a);}else{return E(_1gV);}}}));}}else{return new T2(0,_1hj,new T(function(){var _1hE=B(_Gb(B(_sw(_1gW,_1hm))));if(!_1hE._){return E(_1gU);}else{if(!E(_1hE.b)._){return E(_1hE.a);}else{return E(_1gV);}}}));}});return new T2(1,_1hC,new T(function(){return B(_1h9(_1he));}));}}}}})(_1ha));if(_1hb!=__continue){return _1hb;}}};return new F(function(){return _1h9(_1h1);});},_1hF=102,_1hG=101,_1hH=new T(function(){return B(unCStr("=="));}),_1hI=new T(function(){return B(_e7("Action.hs:(102,17)-(106,70)|case"));}),_1hJ=new T(function(){return B(_e7("Action.hs:(117,9)-(132,75)|function wnMove\'"));}),_1hK=5,_1hL=117,_1hM=98,_1hN=110,_1hO=118,_1hP=function(_1hQ,_1hR,_1hS,_1hT,_1hU,_1hV,_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1){var _1i2=B(_6R(B(_6R(_1hU,_1hR)),_1hQ)),_1i3=_1i2.a,_1i4=_1i2.b;if(E(_1hW)==32){if(!B(_4B(_h7,_1i3,_1fZ))){var _1i5=false;}else{switch(E(_1i4)){case 0:var _1i6=true;break;case 1:var _1i6=false;break;case 2:var _1i6=false;break;case 3:var _1i6=false;break;case 4:var _1i6=false;break;case 5:var _1i6=false;break;case 6:var _1i6=false;break;case 7:var _1i6=false;break;default:var _1i6=false;}var _1i5=_1i6;}var _1i7=_1i5;}else{var _1i7=false;}if(E(_1hW)==32){if(E(_1i3)==32){var _1i8=false;}else{switch(E(_1i4)){case 0:if(!E(_1i7)){var _1i9=true;}else{var _1i9=false;}var _1ia=_1i9;break;case 1:var _1ia=false;break;case 2:var _1ia=false;break;case 3:var _1ia=false;break;case 4:var _1ia=false;break;case 5:var _1ia=false;break;case 6:var _1ia=false;break;case 7:var _1ia=false;break;default:if(!E(_1i7)){var _1ib=true;}else{var _1ib=false;}var _1ia=_1ib;}var _1i8=_1ia;}var _1ic=_1i8;}else{var _1ic=false;}var _1id=new T(function(){return B(_Ke(_1hQ,_1hR,new T(function(){if(!E(_1ic)){if(!E(_1i7)){return E(_1i3);}else{return _1hV;}}else{return E(_SN);}}),_1i4,_1hU));});switch(E(_1i4)){case 3:var _1ie=true;break;case 4:if(E(_1hW)==32){var _1if=true;}else{var _1if=false;}var _1ie=_1if;break;default:var _1ie=false;}if(!E(_1ie)){var _1ig=E(_1id);}else{var _1ih=E(_1hS),_1ii=new T(function(){return B(_6R(_1id,_1hR));}),_1ij=function(_1ik,_1il){var _1im=E(_1ik);if(_1im==( -1)){return E(_1id);}else{var _1in=new T(function(){return B(_Ke(_1hQ,_1hR,_SN,_E7,_1id));}),_1io=E(_1il);if(_1io==( -1)){var _1ip=__Z;}else{var _1ip=B(_6R(_1in,_1io));}if(E(B(_6R(_1ip,_1im)).a)==32){var _1iq=new T(function(){var _1ir=new T(function(){return B(_6R(_1ii,_1hQ));}),_1is=new T2(1,new T2(0,new T(function(){return E(E(_1ir).a);}),new T(function(){return E(E(_1ir).b);})),new T(function(){var _1it=_1im+1|0;if(_1it>0){return B(_1fS(_1it,_1ip));}else{return E(_1ip);}}));if(0>=_1im){return E(_1is);}else{var _1iu=function(_1iv,_1iw){var _1ix=E(_1iv);if(!_1ix._){return E(_1is);}else{var _1iy=_1ix.a,_1iz=E(_1iw);return (_1iz==1)?new T2(1,_1iy,_1is):new T2(1,_1iy,new T(function(){return B(_1iu(_1ix.b,_1iz-1|0));}));}};return B(_1iu(_1ip,_1im));}}),_1iA=new T2(1,_1iq,new T(function(){var _1iB=_1il+1|0;if(_1iB>0){return B(_1fM(_1iB,_1in));}else{return E(_1in);}}));if(0>=_1il){return E(_1iA);}else{var _1iC=function(_1iD,_1iE){var _1iF=E(_1iD);if(!_1iF._){return E(_1iA);}else{var _1iG=_1iF.a,_1iH=E(_1iE);return (_1iH==1)?new T2(1,_1iG,_1iA):new T2(1,_1iG,new T(function(){return B(_1iC(_1iF.b,_1iH-1|0));}));}};return new F(function(){return _1iC(_1in,_1il);});}}else{return E(_1id);}}};if(_1hQ<=_1ih){if(_1ih<=_1hQ){var _1iI=E(_1hT);if(_1hR<=_1iI){if(_1iI<=_1hR){var _1iJ=E(_1hI);}else{var _1iK=E(_1hR);if(!_1iK){var _1iL=B(_1ij( -1, -1));}else{var _1iL=B(_1ij(_1hQ,_1iK-1|0));}var _1iJ=_1iL;}var _1iM=_1iJ;}else{if(_1hR!=(B(_mt(_1id,0))-1|0)){var _1iN=B(_1ij(_1hQ,_1hR+1|0));}else{var _1iN=B(_1ij( -1, -1));}var _1iM=_1iN;}var _1iO=_1iM;}else{var _1iP=E(_1hQ);if(!_1iP){var _1iQ=B(_1ij( -1, -1));}else{var _1iQ=B(_1ij(_1iP-1|0,_1hR));}var _1iO=_1iQ;}var _1iR=_1iO;}else{if(_1hQ!=(B(_mt(_1ii,0))-1|0)){var _1iS=B(_1ij(_1hQ+1|0,_1hR));}else{var _1iS=B(_1ij( -1, -1));}var _1iR=_1iS;}var _1ig=_1iR;}if(!E(_1i0)){var _1iT=E(_1ig);}else{var _1iU=new T(function(){var _1iV=E(_1ig);if(!_1iV._){return E(_nh);}else{return B(_mt(_1iV.a,0));}}),_1iW=new T(function(){return B(_mt(_1ig,0));}),_1iX=function(_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4){while(1){var _1j5=B((function(_1j6,_1j7,_1j8,_1j9,_1ja,_1jb,_1jc){var _1jd=E(_1jc);if(!_1jd._){return E(_1j9);}else{var _1je=_1jd.b,_1jf=E(_1jd.a);if(!_1jf._){return E(_1hJ);}else{var _1jg=_1jf.b,_1jh=E(_1jf.a);if(E(_1jh.b)==5){var _1ji=new T(function(){var _1jj=B(_1fH(_1hK,_1j6));return new T2(0,_1jj.a,_1jj.b);}),_1jk=new T(function(){var _1jl=function(_1jm,_1jn){var _1jo=function(_1jp){return new F(function(){return _Ke(_1j7,_1j8,_SN,_E7,new T(function(){return B(_Ke(_1jm,_1jn,_1jh.a,_EW,_1j9));}));});};if(_1jm!=_1j7){return new F(function(){return _1jo(_);});}else{if(_1jn!=_1j8){return new F(function(){return _1jo(_);});}else{return E(_1j9);}}};switch(E(E(_1ji).a)){case 1:var _1jq=_1j7-1|0;if(_1jq<0){return B(_1jl(_1j7,_1j8));}else{if(_1jq>=E(_1iU)){return B(_1jl(_1j7,_1j8));}else{if(_1j8<0){return B(_1jl(_1j7,_1j8));}else{if(_1j8>=E(_1iW)){return B(_1jl(_1j7,_1j8));}else{if(_1jq!=_1ja){if(E(B(_6R(B(_6R(_1j9,_1j8)),_1jq)).a)==32){return B(_1jl(_1jq,_1j8));}else{return B(_1jl(_1j7,_1j8));}}else{if(_1j8!=_1jb){if(E(B(_6R(B(_6R(_1j9,_1j8)),_1jq)).a)==32){return B(_1jl(_1jq,_1j8));}else{return B(_1jl(_1j7,_1j8));}}else{return B(_1jl(_1j7,_1j8));}}}}}}break;case 2:if(_1j7<0){return B(_1jl(_1j7,_1j8));}else{if(_1j7>=E(_1iU)){return B(_1jl(_1j7,_1j8));}else{var _1jr=_1j8-1|0;if(_1jr<0){return B(_1jl(_1j7,_1j8));}else{if(_1jr>=E(_1iW)){return B(_1jl(_1j7,_1j8));}else{if(_1j7!=_1ja){if(E(B(_6R(B(_6R(_1j9,_1jr)),_1j7)).a)==32){return B(_1jl(_1j7,_1jr));}else{return B(_1jl(_1j7,_1j8));}}else{if(_1jr!=_1jb){if(E(B(_6R(B(_6R(_1j9,_1jr)),_1j7)).a)==32){return B(_1jl(_1j7,_1jr));}else{return B(_1jl(_1j7,_1j8));}}else{return B(_1jl(_1j7,_1j8));}}}}}}break;case 3:var _1js=_1j7+1|0;if(_1js<0){return B(_1jl(_1j7,_1j8));}else{if(_1js>=E(_1iU)){return B(_1jl(_1j7,_1j8));}else{if(_1j8<0){return B(_1jl(_1j7,_1j8));}else{if(_1j8>=E(_1iW)){return B(_1jl(_1j7,_1j8));}else{if(_1js!=_1ja){if(E(B(_6R(B(_6R(_1j9,_1j8)),_1js)).a)==32){return B(_1jl(_1js,_1j8));}else{return B(_1jl(_1j7,_1j8));}}else{if(_1j8!=_1jb){if(E(B(_6R(B(_6R(_1j9,_1j8)),_1js)).a)==32){return B(_1jl(_1js,_1j8));}else{return B(_1jl(_1j7,_1j8));}}else{return B(_1jl(_1j7,_1j8));}}}}}}break;case 4:if(_1j7<0){return B(_1jl(_1j7,_1j8));}else{if(_1j7>=E(_1iU)){return B(_1jl(_1j7,_1j8));}else{var _1jt=_1j8+1|0;if(_1jt<0){return B(_1jl(_1j7,_1j8));}else{if(_1jt>=E(_1iW)){return B(_1jl(_1j7,_1j8));}else{if(_1j7!=_1ja){if(E(B(_6R(B(_6R(_1j9,_1jt)),_1j7)).a)==32){return B(_1jl(_1j7,_1jt));}else{return B(_1jl(_1j7,_1j8));}}else{if(_1jt!=_1jb){if(E(B(_6R(B(_6R(_1j9,_1jt)),_1j7)).a)==32){return B(_1jl(_1j7,_1jt));}else{return B(_1jl(_1j7,_1j8));}}else{return B(_1jl(_1j7,_1j8));}}}}}}break;default:if(_1j7<0){return B(_1jl(_1j7,_1j8));}else{if(_1j7>=E(_1iU)){return B(_1jl(_1j7,_1j8));}else{if(_1j8<0){return B(_1jl(_1j7,_1j8));}else{if(_1j8>=E(_1iW)){return B(_1jl(_1j7,_1j8));}else{if(_1j7!=_1ja){var _1ju=E(B(_6R(B(_6R(_1j9,_1j8)),_1j7)).a);return B(_1jl(_1j7,_1j8));}else{if(_1j8!=_1jb){var _1jv=E(B(_6R(B(_6R(_1j9,_1j8)),_1j7)).a);return B(_1jl(_1j7,_1j8));}else{return B(_1jl(_1j7,_1j8));}}}}}}}}),_1jw=E(_1jg);if(!_1jw._){var _1jx=_1j8+1|0,_1jy=_1ja,_1jz=_1jb;_1iY=new T(function(){return E(E(_1ji).b);},1);_1iZ=0;_1j0=_1jx;_1j1=_1jk;_1j2=_1jy;_1j3=_1jz;_1j4=_1je;return __continue;}else{return new F(function(){return _1jA(new T(function(){return E(E(_1ji).b);},1),_1j7+1|0,_1j8,_1jk,_1ja,_1jb,_1jw.a,_1jw.b,_1je);});}}else{var _1jB=E(_1jg);if(!_1jB._){var _1jC=_1j6,_1jx=_1j8+1|0,_1jD=_1j9,_1jy=_1ja,_1jz=_1jb;_1iY=_1jC;_1iZ=0;_1j0=_1jx;_1j1=_1jD;_1j2=_1jy;_1j3=_1jz;_1j4=_1je;return __continue;}else{return new F(function(){return _1jA(_1j6,_1j7+1|0,_1j8,_1j9,_1ja,_1jb,_1jB.a,_1jB.b,_1je);});}}}}})(_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4));if(_1j5!=__continue){return _1j5;}}},_1jA=function(_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ,_1jK,_1jL,_1jM){while(1){var _1jN=B((function(_1jO,_1jP,_1jQ,_1jR,_1jS,_1jT,_1jU,_1jV,_1jW){var _1jX=E(_1jU);if(E(_1jX.b)==5){var _1jY=new T(function(){var _1jZ=B(_1fH(_1hK,_1jO));return new T2(0,_1jZ.a,_1jZ.b);}),_1k0=new T(function(){var _1k1=function(_1k2,_1k3){var _1k4=function(_1k5){return new F(function(){return _Ke(_1jP,_1jQ,_SN,_E7,new T(function(){return B(_Ke(_1k2,_1k3,_1jX.a,_EW,_1jR));}));});};if(_1k2!=_1jP){return new F(function(){return _1k4(_);});}else{if(_1k3!=_1jQ){return new F(function(){return _1k4(_);});}else{return E(_1jR);}}};switch(E(E(_1jY).a)){case 1:var _1k6=_1jP-1|0;if(_1k6<0){return B(_1k1(_1jP,_1jQ));}else{if(_1k6>=E(_1iU)){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ>=E(_1iW)){return B(_1k1(_1jP,_1jQ));}else{if(_1k6!=_1jS){if(E(B(_6R(B(_6R(_1jR,_1jQ)),_1k6)).a)==32){return B(_1k1(_1k6,_1jQ));}else{return B(_1k1(_1jP,_1jQ));}}else{if(_1jQ!=_1jT){if(E(B(_6R(B(_6R(_1jR,_1jQ)),_1k6)).a)==32){return B(_1k1(_1k6,_1jQ));}else{return B(_1k1(_1jP,_1jQ));}}else{return B(_1k1(_1jP,_1jQ));}}}}}}break;case 2:if(_1jP<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jP>=E(_1iU)){return B(_1k1(_1jP,_1jQ));}else{var _1k7=_1jQ-1|0;if(_1k7<0){return B(_1k1(_1jP,_1jQ));}else{if(_1k7>=E(_1iW)){return B(_1k1(_1jP,_1jQ));}else{if(_1jP!=_1jS){if(E(B(_6R(B(_6R(_1jR,_1k7)),_1jP)).a)==32){return B(_1k1(_1jP,_1k7));}else{return B(_1k1(_1jP,_1jQ));}}else{if(_1k7!=_1jT){if(E(B(_6R(B(_6R(_1jR,_1k7)),_1jP)).a)==32){return B(_1k1(_1jP,_1k7));}else{return B(_1k1(_1jP,_1jQ));}}else{return B(_1k1(_1jP,_1jQ));}}}}}}break;case 3:var _1k8=_1jP+1|0;if(_1k8<0){return B(_1k1(_1jP,_1jQ));}else{if(_1k8>=E(_1iU)){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ>=E(_1iW)){return B(_1k1(_1jP,_1jQ));}else{if(_1k8!=_1jS){if(E(B(_6R(B(_6R(_1jR,_1jQ)),_1k8)).a)==32){return B(_1k1(_1k8,_1jQ));}else{return B(_1k1(_1jP,_1jQ));}}else{if(_1jQ!=_1jT){if(E(B(_6R(B(_6R(_1jR,_1jQ)),_1k8)).a)==32){return B(_1k1(_1k8,_1jQ));}else{return B(_1k1(_1jP,_1jQ));}}else{return B(_1k1(_1jP,_1jQ));}}}}}}break;case 4:if(_1jP<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jP>=E(_1iU)){return B(_1k1(_1jP,_1jQ));}else{var _1k9=_1jQ+1|0;if(_1k9<0){return B(_1k1(_1jP,_1jQ));}else{if(_1k9>=E(_1iW)){return B(_1k1(_1jP,_1jQ));}else{if(_1jP!=_1jS){if(E(B(_6R(B(_6R(_1jR,_1k9)),_1jP)).a)==32){return B(_1k1(_1jP,_1k9));}else{return B(_1k1(_1jP,_1jQ));}}else{if(_1k9!=_1jT){if(E(B(_6R(B(_6R(_1jR,_1k9)),_1jP)).a)==32){return B(_1k1(_1jP,_1k9));}else{return B(_1k1(_1jP,_1jQ));}}else{return B(_1k1(_1jP,_1jQ));}}}}}}break;default:if(_1jP<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jP>=E(_1iU)){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ<0){return B(_1k1(_1jP,_1jQ));}else{if(_1jQ>=E(_1iW)){return B(_1k1(_1jP,_1jQ));}else{if(_1jP!=_1jS){var _1ka=E(B(_6R(B(_6R(_1jR,_1jQ)),_1jP)).a);return B(_1k1(_1jP,_1jQ));}else{if(_1jQ!=_1jT){var _1kb=E(B(_6R(B(_6R(_1jR,_1jQ)),_1jP)).a);return B(_1k1(_1jP,_1jQ));}else{return B(_1k1(_1jP,_1jQ));}}}}}}}}),_1kc=E(_1jV);if(!_1kc._){return new F(function(){return _1iX(new T(function(){return E(E(_1jY).b);},1),0,_1jQ+1|0,_1k0,_1jS,_1jT,_1jW);});}else{var _1kd=_1jP+1|0,_1ke=_1jQ,_1kf=_1jS,_1kg=_1jT,_1kh=_1jW;_1jE=new T(function(){return E(E(_1jY).b);},1);_1jF=_1kd;_1jG=_1ke;_1jH=_1k0;_1jI=_1kf;_1jJ=_1kg;_1jK=_1kc.a;_1jL=_1kc.b;_1jM=_1kh;return __continue;}}else{var _1ki=E(_1jV);if(!_1ki._){return new F(function(){return _1iX(_1jO,0,_1jQ+1|0,_1jR,_1jS,_1jT,_1jW);});}else{var _1kj=_1jO,_1kd=_1jP+1|0,_1ke=_1jQ,_1kk=_1jR,_1kf=_1jS,_1kg=_1jT,_1kh=_1jW;_1jE=_1kj;_1jF=_1kd;_1jG=_1ke;_1jH=_1kk;_1jI=_1kf;_1jJ=_1kg;_1jK=_1ki.a;_1jL=_1ki.b;_1jM=_1kh;return __continue;}}})(_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ,_1jK,_1jL,_1jM));if(_1jN!=__continue){return _1jN;}}},_1iT=B(_1iX(_1hY,0,0,_1ig,_1hQ,_1hR,_1ig));}var _1kl=function(_1km){var _1kn=function(_1ko){var _1kp=new T(function(){switch(E(_1i4)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1kq=new T(function(){if(!E(_1ie)){if(!E(_1kp)){return new T2(0,_1hQ,_1hR);}else{return new T2(0,_1hS,_1hT);}}else{if(!B(_1cD(_1cP,_1iT,_1id))){if(!E(_1kp)){return new T2(0,_1hQ,_1hR);}else{return new T2(0,_1hS,_1hT);}}else{return new T2(0,_1hS,_1hT);}}}),_1kr=new T(function(){return E(E(_1kq).b);}),_1ks=new T(function(){return E(E(_1kq).a);});if(!E(_1ie)){var _1kt=E(_1i1);}else{var _1kt=E(B(_1fq(new T(function(){return B(_1gY(_1hX,_10,_1iT));}),_1iT)).a);}var _1ku=new T(function(){if(!E(_1ic)){if(!E(_1i7)){var _1kv=function(_1kw){var _1kx=function(_1ky){var _1kz=E(_1i4);if(_1kz==4){return new T2(1,_1hN,new T2(1,_1i3,_10));}else{if(!E(_1kp)){return (E(_1kz)==2)?new T2(1,_1hL,new T2(1,_1i3,_10)):__Z;}else{var _1kA=E(_1i3);return (E(_1kA)==61)?new T2(1,_1hM,new T2(1,_1kA,new T(function(){return B(_I(0,_1hR,_10));}))):new T2(1,_1hM,new T2(1,_1kA,_10));}}};if(!E(_1ie)){return new F(function(){return _1kx(_);});}else{if(E(_1hS)!=E(_1ks)){return new T2(1,_1hO,new T2(1,_1i3,_10));}else{if(E(_1hT)!=E(_1kr)){return new T2(1,_1hO,new T2(1,_1i3,_10));}else{return new F(function(){return _1kx(_);});}}}};if(!E(_1ie)){return B(_1kv(_));}else{if(!E(_1kt)){return B(_1kv(_));}else{return E(_1hH);}}}else{return new T2(1,_1hF,new T2(1,_1i3,_10));}}else{return new T2(1,_1hG,new T2(1,_1i3,_10));}},1);return {_:0,a:new T2(0,_1ks,_1kr),b:_1iT,c:_1km,d:_1ko,e:_1hX,f:_1hY,g:B(_y(_1hZ,_1ku)),h:_1i0,i:E(_1kt)};};if(!E(_1ic)){return new F(function(){return _1kn(_1hW);});}else{return new F(function(){return _1kn(E(_1i3));});}};if(!E(_1i7)){return new F(function(){return _1kl(_1hV);});}else{return new F(function(){return _1kl(E(_1i3));});}},_1kB=new T2(1,_5V,_10),_1kC=5,_1kD=new T2(1,_1kC,_10),_1kE=function(_1kF,_1kG){while(1){var _1kH=E(_1kF);if(!_1kH._){return E(_1kG);}else{_1kF=_1kH.b;_1kG=_1kH.a;continue;}}},_1kI=57,_1kJ=48,_1kK=new T2(1,_1fY,_10),_1kL=new T(function(){return B(err(_sr));}),_1kM=new T(function(){return B(err(_sp));}),_1kN=new T(function(){return B(A3(_Fz,_G2,_DC,_Fp));}),_1kO=function(_1kP,_1kQ){if((_1kQ-48|0)>>>0>9){var _1kR=_1kQ+_1kP|0,_1kS=function(_1kT){if(!B(_4B(_h7,_1kT,_1kK))){return E(_1kT);}else{return new F(function(){return _1kO(_1kP,_1kT);});}};if(_1kR<=122){if(_1kR>=97){if(_1kR>>>0>1114111){return new F(function(){return _wC(_1kR);});}else{return new F(function(){return _1kS(_1kR);});}}else{if(_1kR<=90){if(_1kR>>>0>1114111){return new F(function(){return _wC(_1kR);});}else{return new F(function(){return _1kS(_1kR);});}}else{var _1kU=65+(_1kR-90|0)|0;if(_1kU>>>0>1114111){return new F(function(){return _wC(_1kU);});}else{return new F(function(){return _1kS(_1kU);});}}}}else{var _1kV=97+(_1kR-122|0)|0;if(_1kV>>>0>1114111){return new F(function(){return _wC(_1kV);});}else{return new F(function(){return _1kS(_1kV);});}}}else{var _1kW=B(_Gb(B(_sw(_1kN,new T2(1,_1kQ,_10)))));if(!_1kW._){return E(_1kM);}else{if(!E(_1kW.b)._){var _1kX=E(_1kW.a)+_1kP|0;switch(_1kX){case  -1:return E(_1kJ);case 10:return E(_1kI);default:return new F(function(){return _1kE(B(_I(0,_1kX,_10)),_Ru);});}}else{return E(_1kL);}}}},_1kY=function(_1kZ,_1l0){if((_1kZ-48|0)>>>0>9){return _1l0;}else{var _1l1=B(_Gb(B(_sw(_1kN,new T2(1,_1kZ,_10)))));if(!_1l1._){return E(_1kM);}else{if(!E(_1l1.b)._){return new F(function(){return _1kO(E(_1l1.a),_1l0);});}else{return E(_1kL);}}}},_1l2=function(_1l3,_1l4){return new F(function(){return _1kY(E(_1l3),E(_1l4));});},_1l5=new T2(1,_1l2,_10),_1l6=112,_1l7=111,_1l8=function(_1l9,_1la,_1lb,_1lc,_1ld,_1le,_1lf,_1lg,_1lh,_1li){var _1lj=new T(function(){return B(_6R(B(_6R(_1lb,_1la)),E(_1l9)));}),_1lk=new T(function(){return E(E(_1lj).b);}),_1ll=new T(function(){if(E(_1lk)==4){return true;}else{return false;}}),_1lm=new T(function(){return E(E(_1lj).a);});if(E(_1ld)==32){var _1ln=false;}else{if(E(_1lm)==32){var _1lo=true;}else{var _1lo=false;}var _1ln=_1lo;}var _1lp=new T(function(){var _1lq=new T(function(){return B(A3(_6R,_1kB,B(_LJ(_h7,_1lc,_1fZ)),_1ld));});if(!E(_1ln)){if(!E(_1ll)){return E(_1lm);}else{if(!B(_4B(_3M,_1le,_1kD))){return E(_1lm);}else{return B(A(_6R,[_1l5,B(_LJ(_3M,_1le,_1kD)),_1lq,_1lm]));}}}else{return E(_1lq);}}),_1lr=B(_Ke(_1l9,_1la,_1lp,_1lk,_1lb));if(!E(_1ln)){var _1ls=B(_1fq(new T(function(){return B(_1gY(_1le,_10,_1lr));}),_1lr)).a;return {_:0,a:new T2(0,_1l9,_1la),b:_1lr,c:_1lc,d:_1ld,e:_1le,f:_1lf,g:B(_y(_1lg,new T(function(){if(!E(_1ls)){if(!E(_1ll)){return __Z;}else{return new T2(1,_1l6,new T2(1,_1lp,_10));}}else{return E(_1hH);}},1))),h:_1lh,i:E(_1ls)};}else{var _1lt=B(_1fq(new T(function(){return B(_1gY(_1le,_10,_1lr));}),_1lr)).a;return {_:0,a:new T2(0,_1l9,_1la),b:_1lr,c:_1lc,d:32,e:_1le,f:_1lf,g:B(_y(_1lg,new T(function(){if(!E(_1lt)){return new T2(1,_1l7,new T2(1,_1lp,_10));}else{return E(_1hH);}},1))),h:_1lh,i:E(_1lt)};}},_1lu=new T(function(){return B(_e7("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1lv=function(_1lw,_1lx){while(1){var _1ly=E(_1lx);if(!_1ly._){return false;}else{var _1lz=_1ly.b,_1lA=E(_1lw),_1lB=_1lA.a,_1lC=_1lA.b,_1lD=E(_1ly.a);if(!_1lD._){return E(_1lu);}else{var _1lE=E(_1lD.a),_1lF=_1lE.a,_1lG=_1lE.b,_1lH=E(_1lD.b);if(!_1lH._){var _1lI=E(_1lB),_1lJ=E(_1lI);if(_1lJ==32){switch(E(_1lC)){case 0:if(!E(_1lG)){return true;}else{_1lw=new T2(0,_1lI,_E7);_1lx=_1lz;continue;}break;case 1:if(E(_1lG)==1){return true;}else{_1lw=new T2(0,_1lI,_Ed);_1lx=_1lz;continue;}break;case 2:if(E(_1lG)==2){return true;}else{_1lw=new T2(0,_1lI,_Ej);_1lx=_1lz;continue;}break;case 3:if(E(_1lG)==3){return true;}else{_1lw=new T2(0,_1lI,_Ep);_1lx=_1lz;continue;}break;case 4:if(E(_1lG)==4){return true;}else{_1lw=new T2(0,_1lI,_Ev);_1lx=_1lz;continue;}break;case 5:if(E(_1lG)==5){return true;}else{_1lw=new T2(0,_1lI,_EW);_1lx=_1lz;continue;}break;case 6:if(E(_1lG)==6){return true;}else{_1lw=new T2(0,_1lI,_EP);_1lx=_1lz;continue;}break;case 7:if(E(_1lG)==7){return true;}else{_1lw=new T2(0,_1lI,_EI);_1lx=_1lz;continue;}break;default:if(E(_1lG)==8){return true;}else{_1lw=new T2(0,_1lI,_EB);_1lx=_1lz;continue;}}}else{if(_1lJ!=E(_1lF)){_1lw=_1lA;_1lx=_1lz;continue;}else{switch(E(_1lC)){case 0:if(!E(_1lG)){return true;}else{_1lw=new T2(0,_1lI,_E7);_1lx=_1lz;continue;}break;case 1:if(E(_1lG)==1){return true;}else{_1lw=new T2(0,_1lI,_Ed);_1lx=_1lz;continue;}break;case 2:if(E(_1lG)==2){return true;}else{_1lw=new T2(0,_1lI,_Ej);_1lx=_1lz;continue;}break;case 3:if(E(_1lG)==3){return true;}else{_1lw=new T2(0,_1lI,_Ep);_1lx=_1lz;continue;}break;case 4:if(E(_1lG)==4){return true;}else{_1lw=new T2(0,_1lI,_Ev);_1lx=_1lz;continue;}break;case 5:if(E(_1lG)==5){return true;}else{_1lw=new T2(0,_1lI,_EW);_1lx=_1lz;continue;}break;case 6:if(E(_1lG)==6){return true;}else{_1lw=new T2(0,_1lI,_EP);_1lx=_1lz;continue;}break;case 7:if(E(_1lG)==7){return true;}else{_1lw=new T2(0,_1lI,_EI);_1lx=_1lz;continue;}break;default:if(E(_1lG)==8){return true;}else{_1lw=new T2(0,_1lI,_EB);_1lx=_1lz;continue;}}}}}else{var _1lK=E(_1lB),_1lL=E(_1lK);if(_1lL==32){switch(E(_1lC)){case 0:if(!E(_1lG)){return true;}else{_1lw=new T2(0,_1lK,_E7);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 1:if(E(_1lG)==1){return true;}else{_1lw=new T2(0,_1lK,_Ed);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 2:if(E(_1lG)==2){return true;}else{_1lw=new T2(0,_1lK,_Ej);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 3:if(E(_1lG)==3){return true;}else{_1lw=new T2(0,_1lK,_Ep);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 4:if(E(_1lG)==4){return true;}else{_1lw=new T2(0,_1lK,_Ev);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 5:if(E(_1lG)==5){return true;}else{_1lw=new T2(0,_1lK,_EW);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 6:if(E(_1lG)==6){return true;}else{_1lw=new T2(0,_1lK,_EP);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 7:if(E(_1lG)==7){return true;}else{_1lw=new T2(0,_1lK,_EI);_1lx=new T2(1,_1lH,_1lz);continue;}break;default:if(E(_1lG)==8){return true;}else{_1lw=new T2(0,_1lK,_EB);_1lx=new T2(1,_1lH,_1lz);continue;}}}else{if(_1lL!=E(_1lF)){_1lw=_1lA;_1lx=new T2(1,_1lH,_1lz);continue;}else{switch(E(_1lC)){case 0:if(!E(_1lG)){return true;}else{_1lw=new T2(0,_1lK,_E7);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 1:if(E(_1lG)==1){return true;}else{_1lw=new T2(0,_1lK,_Ed);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 2:if(E(_1lG)==2){return true;}else{_1lw=new T2(0,_1lK,_Ej);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 3:if(E(_1lG)==3){return true;}else{_1lw=new T2(0,_1lK,_Ep);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 4:if(E(_1lG)==4){return true;}else{_1lw=new T2(0,_1lK,_Ev);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 5:if(E(_1lG)==5){return true;}else{_1lw=new T2(0,_1lK,_EW);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 6:if(E(_1lG)==6){return true;}else{_1lw=new T2(0,_1lK,_EP);_1lx=new T2(1,_1lH,_1lz);continue;}break;case 7:if(E(_1lG)==7){return true;}else{_1lw=new T2(0,_1lK,_EI);_1lx=new T2(1,_1lH,_1lz);continue;}break;default:if(E(_1lG)==8){return true;}else{_1lw=new T2(0,_1lK,_EB);_1lx=new T2(1,_1lH,_1lz);continue;}}}}}}}}},_1lM=new T(function(){return B(unCStr("\n"));}),_1lN=function(_1lO,_1lP,_){var _1lQ=jsWriteHandle(E(_1lO),toJSStr(E(_1lP)));return _gE;},_1lR=function(_1lS,_1lT,_){var _1lU=E(_1lS),_1lV=jsWriteHandle(_1lU,toJSStr(E(_1lT)));return new F(function(){return _1lN(_1lU,_1lM,_);});},_1lW=function(_1lX){var _1lY=E(_1lX);if(!_1lY._){return __Z;}else{return new F(function(){return _y(_1lY.a,new T(function(){return B(_1lW(_1lY.b));},1));});}},_1lZ=0,_1m0= -1,_1m1= -2,_1m2=new T(function(){return B(unCStr("removed"));}),_1m3=new T(function(){return B(unCStr("loadError"));}),_1m4=new T(function(){return B(unCStr("saved"));}),_1m5=new T(function(){return B(err(_sp));}),_1m6=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1m7=10,_1m8=3,_1m9=new T(function(){return B(unCStr("Coding : yokoP"));}),_1ma=8,_1mb=new T(function(){return B(unCStr("Congratulations!"));}),_1mc=5,_1md=32,_1me=new T2(0,_1md,_EW),_1mf=99,_1mg=new T(function(){return B(err(_sr));}),_1mh=64,_1mi=new T(function(){return B(_mt(_17R,0));}),_1mj=new T(function(){return B(_6R(_j4,1));}),_1mk=new T(function(){return B(_6R(_j4,2));}),_1ml=new T(function(){return B(unCStr("loadError"));}),_1mm=new T(function(){return B(unCStr(","));}),_1mn=new T(function(){return B(unCStr("~"));}),_1mo=new T(function(){return B(unCStr("savedata"));}),_1mp=new T(function(){return B(unCStr("---"));}),_1mq=0,_1mr=new T(function(){return B(A3(_Fz,_G2,_DC,_Fp));}),_1ms=new T(function(){return B(unCStr("choice"));}),_1mt=new T2(1,_6D,_10),_1mu=new T(function(){return B(_8k(_1ms,_1mt));}),_1mv=new T2(1,_6D,_1mu),_1mw=new T(function(){return B(unAppCStr("[]",_10));}),_1mx=new T(function(){return B(unCStr("\""));}),_1my=function(_1mz){var _1mA=B(_Gb(B(_sw(_1mr,_1mz))));return (_1mA._==0)?E(_1m5):(E(_1mA.b)._==0)?E(_1mA.a):E(_1mg);},_1mB=new T2(1,_10,_10),_1mC=new T(function(){return B(_6e(_1my,_1mB));}),_1mD=new T2(1,_6D,_10),_1mE=new T(function(){var _1mF=E(_17n);if(!_1mF._){return E(_nh);}else{return E(_1mF.a);}}),_1mG=new T(function(){return B(_13W(_171,5,_17D));}),_1mH=new T(function(){return B(unCStr("Thank you for playing!"));}),_1mI=17,_1mJ=2,_1mK=function(_1mL){return E(_1mL).c;},_1mM=function(_1mN,_1mO){var _1mP=E(_1mO);return (_1mP._==0)?__Z:new T2(1,_1mN,new T2(1,_1mP.a,new T(function(){return B(_1mM(_1mN,_1mP.b));})));},_1mQ=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1mR=new T(function(){return B(unCStr("tail"));}),_1mS=new T(function(){return B(_ne(_1mR));}),_1mT=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1mU=new T2(1,_2B,_10),_1mV=function(_1mW,_1mX){return new T2(1,_6D,new T(function(){return B(_8k(_1mW,new T2(1,_6D,_1mX)));}));},_1mY=function(_1mZ){var _1n0=E(_1mZ);if(!_1n0._){return E(_1mU);}else{var _1n1=new T(function(){var _1n2=E(_1n0.a),_1n3=new T(function(){return B(A3(_s8,_6x,new T2(1,function(_1n4){return new F(function(){return _1mV(_1n2.a,_1n4);});},new T2(1,function(_1n5){return new F(function(){return _1mV(_1n2.b,_1n5);});},_10)),new T2(1,_G,new T(function(){return B(_1mY(_1n0.b));}))));});return new T2(1,_H,_1n3);});return new T2(1,_2A,_1n1);}},_1n6=function(_1n7){var _1n8=E(_1n7);if(!_1n8._){return E(_1mU);}else{var _1n9=new T(function(){return B(_I(0,E(_1n8.a),new T(function(){return B(_1n6(_1n8.b));})));});return new T2(1,_2A,_1n9);}},_1na=function(_1nb){var _1nc=E(_1nb);if(!_1nc._){return E(_1mU);}else{var _1nd=new T(function(){var _1ne=E(_1nc.a),_1nf=new T(function(){return B(A3(_s8,_6x,new T2(1,function(_1ng){return new F(function(){return _1mV(_1ne.a,_1ng);});},new T2(1,function(_1nh){return new F(function(){return _1mV(_1ne.b,_1nh);});},_10)),new T2(1,_G,new T(function(){return B(_1na(_1nc.b));}))));});return new T2(1,_H,_1nf);});return new T2(1,_2A,_1nd);}},_1ni=new T(function(){return B(unCStr("True"));}),_1nj=new T(function(){return B(unCStr("False"));}),_1nk=function(_){return new F(function(){return jsMkStdout();});},_1nl=new T(function(){return B(_3(_1nk));}),_1nm=new T(function(){return B(_KF("Browser.hs:82:24-56|(Right j)"));}),_1nn=function(_1no){var _1np=jsParseJSON(toJSStr(E(_1no)));return (_1np._==0)?E(_1nm):E(_1np.a);},_1nq=function(_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ,_1o0,_){var _1o1={_:0,a:E(_1nS),b:E(_1nT),c:E(_1nU),d:E(_1nV),e:E(_1nW),f:E(_1nX),g:E(_1nY),h:E(_1nZ)},_1o2=new T2(0,_1nK,_1nL),_1o3=new T2(0,_1nE,_1nF),_1o4={_:0,a:E(_1nv),b:E(_1nw),c:_1nx,d:_1ny,e:_1nz,f:_1nA,g:E(_1nB),h:E(_1nC),i:E(_1nD)};if(!E(_1nX)){var _1o5=function(_1o6){var _1o7=new T(function(){var _1o8=E(_1ns)/16,_1o9=_1o8&4294967295;if(_1o8>=_1o9){return _1o9-2|0;}else{return (_1o9-1|0)-2|0;}});if(!E(_1nV)){if(!E(_1nZ)){return {_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E(_1o1),o:E(_1o0)};}else{var _1oa=function(_){var _1ob=function(_){var _1oc=function(_){var _1od=B(_1lR(_1nl,new T2(1,_6D,new T(function(){return B(_8k(_1nB,_1mD));})),_)),_1oe=function(_){var _1of=B(_1lR(_1nl,B(_I(0,_1nP,_10)),_)),_1og=B(_11N(_1mc,_1nA,_)),_1oh=E(_1nr),_1oi=_1oh.a,_1oj=_1oh.b,_1ok=new T(function(){return B(_1cA(E(_1nu)));}),_1ol=new T(function(){var _1om=function(_1on,_1oo){var _1op=E(_1nv);return new F(function(){return _1hP(_1on,_1oo,_1op.a,_1op.b,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD);});};switch(E(_1ok)){case 72:var _1oq=E(_1nv),_1or=_1oq.a,_1os=E(_1oq.b);if(0<=(_1os-1|0)){var _1ot=B(_1om(E(_1or),_1os-1|0));return {_:0,a:E(_1ot.a),b:E(_1ot.b),c:_1ot.c,d:_1ot.d,e:_1ot.e,f:_1ot.f,g:E(_1ot.g),h:E(_1ot.h),i:E(_1ot.i)};}else{var _1ou=B(_1om(E(_1or),_1os));return {_:0,a:E(_1ou.a),b:E(_1ou.b),c:_1ou.c,d:_1ou.d,e:_1ou.e,f:_1ou.f,g:E(_1ou.g),h:E(_1ou.h),i:E(_1ou.i)};}break;case 75:var _1ov=E(_1nv),_1ow=_1ov.b,_1ox=E(_1ov.a);if(0<=(_1ox-1|0)){var _1oy=B(_1om(_1ox-1|0,E(_1ow)));return {_:0,a:E(_1oy.a),b:E(_1oy.b),c:_1oy.c,d:_1oy.d,e:_1oy.e,f:_1oy.f,g:E(_1oy.g),h:E(_1oy.h),i:E(_1oy.i)};}else{var _1oz=B(_1om(_1ox,E(_1ow)));return {_:0,a:E(_1oz.a),b:E(_1oz.b),c:_1oz.c,d:_1oz.d,e:_1oz.e,f:_1oz.f,g:E(_1oz.g),h:E(_1oz.h),i:E(_1oz.i)};}break;case 77:var _1oA=E(_1nv),_1oB=_1oA.b,_1oC=E(_1oA.a);if(E(_1nE)!=(_1oC+1|0)){var _1oD=B(_1om(_1oC+1|0,E(_1oB)));return {_:0,a:E(_1oD.a),b:E(_1oD.b),c:_1oD.c,d:_1oD.d,e:_1oD.e,f:_1oD.f,g:E(_1oD.g),h:E(_1oD.h),i:E(_1oD.i)};}else{var _1oE=B(_1om(_1oC,E(_1oB)));return {_:0,a:E(_1oE.a),b:E(_1oE.b),c:_1oE.c,d:_1oE.d,e:_1oE.e,f:_1oE.f,g:E(_1oE.g),h:E(_1oE.h),i:E(_1oE.i)};}break;case 80:var _1oF=E(_1nv),_1oG=_1oF.a,_1oH=E(_1oF.b);if(E(_1nF)!=(_1oH+1|0)){var _1oI=B(_1om(E(_1oG),_1oH+1|0));return {_:0,a:E(_1oI.a),b:E(_1oI.b),c:_1oI.c,d:_1oI.d,e:_1oI.e,f:_1oI.f,g:E(_1oI.g),h:E(_1oI.h),i:E(_1oI.i)};}else{var _1oJ=B(_1om(E(_1oG),_1oH));return {_:0,a:E(_1oJ.a),b:E(_1oJ.b),c:_1oJ.c,d:_1oJ.d,e:_1oJ.e,f:_1oJ.f,g:E(_1oJ.g),h:E(_1oJ.h),i:E(_1oJ.i)};}break;case 104:var _1oK=E(_1nv),_1oL=_1oK.b,_1oM=E(_1oK.a);if(0<=(_1oM-1|0)){var _1oN=B(_1om(_1oM-1|0,E(_1oL)));return {_:0,a:E(_1oN.a),b:E(_1oN.b),c:_1oN.c,d:_1oN.d,e:_1oN.e,f:_1oN.f,g:E(_1oN.g),h:E(_1oN.h),i:E(_1oN.i)};}else{var _1oO=B(_1om(_1oM,E(_1oL)));return {_:0,a:E(_1oO.a),b:E(_1oO.b),c:_1oO.c,d:_1oO.d,e:_1oO.e,f:_1oO.f,g:E(_1oO.g),h:E(_1oO.h),i:E(_1oO.i)};}break;case 106:var _1oP=E(_1nv),_1oQ=_1oP.a,_1oR=E(_1oP.b);if(E(_1nF)!=(_1oR+1|0)){var _1oS=B(_1om(E(_1oQ),_1oR+1|0));return {_:0,a:E(_1oS.a),b:E(_1oS.b),c:_1oS.c,d:_1oS.d,e:_1oS.e,f:_1oS.f,g:E(_1oS.g),h:E(_1oS.h),i:E(_1oS.i)};}else{var _1oT=B(_1om(E(_1oQ),_1oR));return {_:0,a:E(_1oT.a),b:E(_1oT.b),c:_1oT.c,d:_1oT.d,e:_1oT.e,f:_1oT.f,g:E(_1oT.g),h:E(_1oT.h),i:E(_1oT.i)};}break;case 107:var _1oU=E(_1nv),_1oV=_1oU.a,_1oW=E(_1oU.b);if(0<=(_1oW-1|0)){var _1oX=B(_1om(E(_1oV),_1oW-1|0));return {_:0,a:E(_1oX.a),b:E(_1oX.b),c:_1oX.c,d:_1oX.d,e:_1oX.e,f:_1oX.f,g:E(_1oX.g),h:E(_1oX.h),i:E(_1oX.i)};}else{var _1oY=B(_1om(E(_1oV),_1oW));return {_:0,a:E(_1oY.a),b:E(_1oY.b),c:_1oY.c,d:_1oY.d,e:_1oY.e,f:_1oY.f,g:E(_1oY.g),h:E(_1oY.h),i:E(_1oY.i)};}break;case 108:var _1oZ=E(_1nv),_1p0=_1oZ.b,_1p1=E(_1oZ.a);if(E(_1nE)!=(_1p1+1|0)){var _1p2=B(_1om(_1p1+1|0,E(_1p0)));return {_:0,a:E(_1p2.a),b:E(_1p2.b),c:_1p2.c,d:_1p2.d,e:_1p2.e,f:_1p2.f,g:E(_1p2.g),h:E(_1p2.h),i:E(_1p2.i)};}else{var _1p3=B(_1om(_1p1,E(_1p0)));return {_:0,a:E(_1p3.a),b:E(_1p3.b),c:_1p3.c,d:_1p3.d,e:_1p3.e,f:_1p3.f,g:E(_1p3.g),h:E(_1p3.h),i:E(_1p3.i)};}break;default:var _1p4=E(_1nv),_1p5=B(_1om(E(_1p4.a),E(_1p4.b)));return {_:0,a:E(_1p5.a),b:E(_1p5.b),c:_1p5.c,d:_1p5.d,e:_1p5.e,f:_1p5.f,g:E(_1p5.g),h:E(_1p5.h),i:E(_1p5.i)};}}),_1p6=new T(function(){if(E(_1ok)==32){var _1p7=E(_1ol),_1p8=E(_1p7.a),_1p9=B(_1l8(_1p8.a,E(_1p8.b),_1p7.b,_1p7.c,_1p7.d,_1p7.e,_1p7.f,_1p7.g,_1p7.h,_1p7.i));return {_:0,a:E(_1p9.a),b:E(_1p9.b),c:_1p9.c,d:_1p9.d,e:_1p9.e,f:_1p9.f,g:E(_1p9.g),h:E(_1p9.h),i:E(_1p9.i)};}else{return E(_1ol);}}),_1pa=new T(function(){var _1pb=E(_1p6),_1pc=_1pb.g,_1pd=B(_1ap(_1mq,_1pc,_1nH,{_:0,a:E(_1pb.a),b:E(_1pb.b),c:_1pb.c,d:_1pb.d,e:_1pb.e,f:E(E(_1og).b),g:E(_1pc),h:E(_1pb.h),i:E(_1pb.i)},_1o3,_1nG,_1nH,_1nI,_1nJ,_1o2,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1o1,_1o0));return {_:0,a:E(_1pd.a),b:E(_1pd.b),c:E(_1pd.c),d:E(_1pd.d),e:E(_1pd.e),f:E(_1pd.f),g:E(_1pd.g),h:_1pd.h,i:_1pd.i,j:_1pd.j,k:_1pd.k,l:E(_1pd.l),m:_1pd.m,n:E(_1pd.n),o:E(_1pd.o)};}),_1pe=B(_nq(_1oi,_1oj,new T(function(){return E(_1o7)-E(E(E(_1pa).b).a)|0;}),_nP,new T(function(){return E(E(E(_1pa).a).b);}),_)),_1pf=E(_1ok),_1pg=function(_,_1ph){var _1pi=function(_1pj){var _1pk=B(_1lR(_1nl,B(_8q(_1ph)),_)),_1pl=E(_1pa),_1pm=_1pl.d,_1pn=_1pl.e,_1po=_1pl.f,_1pp=_1pl.h,_1pq=_1pl.i,_1pr=_1pl.j,_1ps=_1pl.k,_1pt=_1pl.l,_1pu=_1pl.m,_1pv=_1pl.o,_1pw=E(_1pl.n),_1px=_1pw.a,_1py=_1pw.d,_1pz=_1pw.e,_1pA=_1pw.f,_1pB=_1pw.g,_1pC=_1pw.h,_1pD=E(_1pl.a),_1pE=_1pD.e,_1pF=_1pD.f,_1pG=E(_1pl.g),_1pH=function(_1pI){var _1pJ=function(_1pK){if(_1pK!=E(_1mi)){var _1pL=B(_6R(_176,_1pK)),_1pM=_1pL.a,_1pN=E(_1pL.b),_1pO=B(_13W(_1pM,_1pN,new T(function(){return B(_6R(_17R,_1pK));})));return new F(function(){return _1nq(_1oh,_1ns,_1nt,_1mh,B(_6R(_17h,_1pK)),_1pO,B(_6R(_17n,_1pK)),32,_1pK,_1pF,B(_y(_1pD.g,new T2(1,_1mf,new T(function(){return B(_I(0,_1pE,_10));})))),B(_1lv(_1me,_1pO)),_wr,_1pM,_1pN,_10,_1pm,_1pn,_1po,_1pG.a,_1pG.b,_1pp,_1pq,_1pr, -1,_1pt,_1pu,_wr,_wr,_wr,_1py,_1pz,_1pA,_1pB,_1pC,_1pv,_);});}else{var _1pP=__app1(E(_ni),_1oj),_1pQ=B(A2(_nj,_1oi,_)),_1pR=B(A(_mO,[_1oi,_j3,_1mJ,_1mc,_1mb,_])),_1pS=B(A(_mO,[_1oi,_j3,_1m8,_1ma,_1m9,_])),_1pT=B(A(_mO,[_1oi,_j3,_1m8,_1m7,_1m6,_])),_1pU=B(A(_mO,[_1oi,_j3,_1mJ,_1mI,_1mH,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_17g),b:E(_1mG),c:E(_1mE),d:32,e:0,f:_1pF,g:E(_10),h:E(_1pD.h),i:E(_wr)}),b:E(_172),c:E(_1pl.c),d:E(_1pm),e:E(_1pn),f:E(_1po),g:E(_1pG),h:_1pp,i:_1pq,j:_1pr,k:_1ps,l:E(_1pt),m:_1pu,n:E({_:0,a:E(_1px),b:E(_wr),c:E(_wr),d:E(_1py),e:E(_1pz),f:E(_1pA),g:E(_1pB),h:E(_1pC)}),o:E(_1pv)};});}};if(_1ps>=0){return new F(function(){return _1pJ(_1ps);});}else{return new F(function(){return _1pJ(_1pE+1|0);});}};if(!E(_1px)){if(E(_1pf)==110){return new F(function(){return _1pH(_);});}else{var _1pV=new T(function(){return E(E(_1ol).a);});if(E(_1pD.d)==32){var _1pW=B(A(_mO,[_1oi,_1mj,new T(function(){return (E(E(_1pV).a)+1|0)+(E(_1o7)-E(_1nE)|0)|0;},1),new T(function(){return (E(E(_1pV).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1mK(_1p6));}),_10),_]));return _1pl;}else{var _1pX=B(A(_mO,[_1oi,_1mk,new T(function(){return (E(E(_1pV).a)+1|0)+(E(_1o7)-E(_1nE)|0)|0;},1),new T(function(){return (E(E(_1pV).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1mK(_1p6));}),_10),_]));return _1pl;}}}else{return new F(function(){return _1pH(_);});}};if(E(_1pf)==114){if(!B(_69(_1ph,_1ml))){var _1pY=E(_1ph);if(!_1pY._){return _1pa;}else{var _1pZ=_1pY.b;return new T(function(){var _1q0=E(_1pa),_1q1=E(_1q0.a),_1q2=E(_1pY.a),_1q3=E(_1q2);if(_1q3==34){var _1q4=B(_Q4(_1q2,_1pZ));if(!_1q4._){var _1q5=E(_1mS);}else{var _1q6=E(_1q4.b);if(!_1q6._){var _1q7=E(_1mB);}else{var _1q8=_1q6.a,_1q9=E(_1q6.b);if(!_1q9._){var _1qa=new T2(1,new T2(1,_1q8,_10),_10);}else{var _1qb=E(_1q8),_1qc=new T(function(){var _1qd=B(_H6(126,_1q9.a,_1q9.b));return new T2(0,_1qd.a,_1qd.b);});if(E(_1qb)==126){var _1qe=new T2(1,_10,new T2(1,new T(function(){return E(E(_1qc).a);}),new T(function(){return E(E(_1qc).b);})));}else{var _1qe=new T2(1,new T2(1,_1qb,new T(function(){return E(E(_1qc).a);})),new T(function(){return E(E(_1qc).b);}));}var _1qa=_1qe;}var _1q7=_1qa;}var _1q5=_1q7;}var _1qf=_1q5;}else{var _1qg=E(_1pZ);if(!_1qg._){var _1qh=new T2(1,new T2(1,_1q2,_10),_10);}else{var _1qi=new T(function(){var _1qj=B(_H6(126,_1qg.a,_1qg.b));return new T2(0,_1qj.a,_1qj.b);});if(E(_1q3)==126){var _1qk=new T2(1,_10,new T2(1,new T(function(){return E(E(_1qi).a);}),new T(function(){return E(E(_1qi).b);})));}else{var _1qk=new T2(1,new T2(1,_1q2,new T(function(){return E(E(_1qi).a);})),new T(function(){return E(E(_1qi).b);}));}var _1qh=_1qk;}var _1qf=_1qh;}var _1ql=B(_Gb(B(_sw(_1mr,new T(function(){return B(_sg(_1qf));})))));if(!_1ql._){return E(_1m5);}else{if(!E(_1ql.b)._){var _1qm=E(_1ql.a),_1qn=B(_6R(_176,_1qm)),_1qo=B(_6R(_1qf,1));if(!_1qo._){var _1qp=__Z;}else{var _1qq=E(_1qo.b);if(!_1qq._){var _1qr=__Z;}else{var _1qs=E(_1qo.a),_1qt=new T(function(){var _1qu=B(_H6(44,_1qq.a,_1qq.b));return new T2(0,_1qu.a,_1qu.b);});if(E(_1qs)==44){var _1qv=B(_WK(_10,new T(function(){return E(E(_1qt).a);}),new T(function(){return E(E(_1qt).b);})));}else{var _1qv=B(_WO(new T2(1,_1qs,new T(function(){return E(E(_1qt).a);})),new T(function(){return E(E(_1qt).b);})));}var _1qr=_1qv;}var _1qp=_1qr;}var _1qw=B(_6R(_1qf,2));if(!_1qw._){var _1qx=E(_1mC);}else{var _1qy=_1qw.a,_1qz=E(_1qw.b);if(!_1qz._){var _1qA=B(_6e(_1my,new T2(1,new T2(1,_1qy,_10),_10)));}else{var _1qB=E(_1qy),_1qC=new T(function(){var _1qD=B(_H6(44,_1qz.a,_1qz.b));return new T2(0,_1qD.a,_1qD.b);});if(E(_1qB)==44){var _1qE=B(_6e(_1my,new T2(1,_10,new T2(1,new T(function(){return E(E(_1qC).a);}),new T(function(){return E(E(_1qC).b);})))));}else{var _1qE=B(_6e(_1my,new T2(1,new T2(1,_1qB,new T(function(){return E(E(_1qC).a);})),new T(function(){return E(E(_1qC).b);}))));}var _1qA=_1qE;}var _1qx=_1qA;}return {_:0,a:E({_:0,a:E(B(_6R(_17h,_1qm))),b:E(B(_13W(_1qn.a,E(_1qn.b),new T(function(){return B(_6R(_17R,_1qm));})))),c:B(_6R(_17n,_1qm)),d:32,e:_1qm,f:_1q1.f,g:E(_1q1.g),h:E(_1q1.h),i:E(_1q1.i)}),b:E(_1qn),c:E(_1q0.c),d:E(_1qp),e:E(_1qx),f:E(_1q0.f),g:E(_1q0.g),h:_1q0.h,i:_1q0.i,j:_1q0.j,k:_1q0.k,l:E(_1q0.l),m:_1q0.m,n:E(_1q0.n),o:E(_1q0.o)};}else{return E(_1mg);}}});}}else{return new F(function(){return _1pi(_);});}}else{return new F(function(){return _1pi(_);});}};switch(E(_1pf)){case 100:var _1qF=__app1(E(_1mQ),toJSStr(E(_1mo)));return new F(function(){return _1pg(_,_1m2);});break;case 114:var _1qG=B(_WZ(_6w,toJSStr(E(_1mo)),_));return new F(function(){return _1pg(_,new T(function(){var _1qH=E(_1qG);if(!_1qH._){return E(_1m3);}else{return fromJSStr(B(_1cq(_1qH.a)));}}));});break;case 115:var _1qI=new T(function(){var _1qJ=new T(function(){var _1qK=new T(function(){var _1qL=B(_6e(_6B,_1nI));if(!_1qL._){return __Z;}else{return B(_1lW(new T2(1,_1qL.a,new T(function(){return B(_1mM(_1mm,_1qL.b));}))));}}),_1qM=new T(function(){var _1qN=function(_1qO){var _1qP=E(_1qO);if(!_1qP._){return __Z;}else{var _1qQ=E(_1qP.a);return new T2(1,_1qQ.a,new T2(1,_1qQ.b,new T(function(){return B(_1qN(_1qP.b));})));}},_1qR=B(_1qN(_1nH));if(!_1qR._){return __Z;}else{return B(_1lW(new T2(1,_1qR.a,new T(function(){return B(_1mM(_1mm,_1qR.b));}))));}});return B(_1mM(_1mn,new T2(1,_1qM,new T2(1,_1qK,_10))));});return B(_y(B(_1lW(new T2(1,new T(function(){return B(_I(0,_1nz,_10));}),_1qJ))),_1mx));}),_1qS=__app2(E(_1mT),toJSStr(E(_1mo)),B(_1cq(B(_1nn(B(unAppCStr("\"",_1qI)))))));return new F(function(){return _1pg(_,_1m4);});break;default:return new F(function(){return _1pg(_,_1mp);});}};if(!E(_1nD)){var _1qT=B(_1lR(_1nl,_1nj,_));return new F(function(){return _1oe(_);});}else{var _1qU=B(_1lR(_1nl,_1ni,_));return new F(function(){return _1oe(_);});}},_1qV=E(_1nJ);if(!_1qV._){var _1qW=B(_1lR(_1nl,_1mw,_));return new F(function(){return _1oc(_);});}else{var _1qX=new T(function(){var _1qY=E(_1qV.a),_1qZ=new T(function(){return B(A3(_s8,_6x,new T2(1,function(_1r0){return new F(function(){return _1mV(_1qY.a,_1r0);});},new T2(1,function(_1r1){return new F(function(){return _1mV(_1qY.b,_1r1);});},_10)),new T2(1,_G,new T(function(){return B(_1mY(_1qV.b));}))));});return new T2(1,_H,_1qZ);}),_1r2=B(_1lR(_1nl,new T2(1,_2C,_1qX),_));return new F(function(){return _1oc(_);});}},_1r3=E(_1nI);if(!_1r3._){var _1r4=B(_1lR(_1nl,_1mw,_));return new F(function(){return _1ob(_);});}else{var _1r5=new T(function(){return B(_I(0,E(_1r3.a),new T(function(){return B(_1n6(_1r3.b));})));}),_1r6=B(_1lR(_1nl,new T2(1,_2C,_1r5),_));return new F(function(){return _1ob(_);});}},_1r7=E(_1nH);if(!_1r7._){var _1r8=B(_1lR(_1nl,_1mw,_));return new F(function(){return _1oa(_);});}else{var _1r9=new T(function(){var _1ra=E(_1r7.a),_1rb=new T(function(){return B(A3(_s8,_6x,new T2(1,function(_1rc){return new F(function(){return _1mV(_1ra.a,_1rc);});},new T2(1,function(_1rd){return new F(function(){return _1mV(_1ra.b,_1rd);});},_10)),new T2(1,_G,new T(function(){return B(_1na(_1r7.b));}))));});return new T2(1,_H,_1rb);}),_1re=B(_1lR(_1nl,new T2(1,_2C,_1r9),_));return new F(function(){return _1oa(_);});}}}else{if(!E(_1nY)){return {_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E({_:0,a:E(_1nS),b:E(_1nT),c:E(_1nU),d:E(_wr),e:E(_1nW),f:E(_wr),g:E(_wr),h:E(_1nZ)}),o:E(_1o0)};}else{var _1rf=B(_1lR(_1nl,_1mv,_)),_1rg=new T(function(){var _1rh=B(_1cu(_1nQ));return new T2(0,_1rh.a,_1rh.b);}),_1ri=new T(function(){return E(E(_1rg).a);}),_1rj=function(_1rk,_1rl){var _1rm=E(_1rk);switch(_1rm){case  -2:return {_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E(_1o1),o:E(_1o0)};case  -1:var _1rn=E(_1nr),_1ro=B(_nQ(_1rn.a,_1rn.b,_1o7,{_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E(_1o1),o:E(_1o0)},_));return new T(function(){return {_:0,a:E(_1o4),b:E(_1o3),c:E(B(_16W(new T(function(){return B(_6R(E(_1rg).b,_1nR));})))),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E({_:0,a:E(_1nS),b:E(_1nT),c:E(_ws),d:E(_wr),e:E(_1nW),f:E(_wr),g:E(_wr),h:E(_1nZ)}),o:E(_1o0)};});default:var _1rp=E(_1nr),_1rq=B(_nQ(_1rp.a,_1rp.b,_1o7,{_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E(_1o1),o:E(_1o0)},_)),_1rr=new T(function(){if(!E(_1nZ)){return E(_1mJ);}else{return 2+(E(_1nF)+3|0)|0;}}),_1rs=B(_ja(_1rp,_1nt,0,_1rr,new T(function(){var _1rt=E(_1ns)/28,_1ru=_1rt&4294967295;if(_1rt>=_1ru){return (_1ru-1|0)+_1nO|0;}else{return ((_1ru-1|0)-1|0)+_1nO|0;}}),_1rr,B(_T2(_1nG,_1ri,_1rl)),_));return {_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1rm,n:E(_1o1),o:E(_1o0)};}};switch(E(B(_1cA(E(_1nu))))){case 32:return new F(function(){return _1rj( -1,_1m0);});break;case 72:var _1rv=E(_1nR);if(!_1rv){var _1rw=B(_mt(_1ri,0))-1|0;return new F(function(){return _1rj(_1rw,_1rw);});}else{var _1rx=_1rv-1|0;return new F(function(){return _1rj(_1rx,_1rx);});}break;case 75:if(_1nR!=(B(_mt(_1ri,0))-1|0)){var _1ry=_1nR+1|0;return new F(function(){return _1rj(_1ry,_1ry);});}else{return new F(function(){return _1rj(0,_1lZ);});}break;case 77:var _1rz=E(_1nR);if(!_1rz){var _1rA=B(_mt(_1ri,0))-1|0;return new F(function(){return _1rj(_1rA,_1rA);});}else{var _1rB=_1rz-1|0;return new F(function(){return _1rj(_1rB,_1rB);});}break;case 80:if(_1nR!=(B(_mt(_1ri,0))-1|0)){var _1rC=_1nR+1|0;return new F(function(){return _1rj(_1rC,_1rC);});}else{return new F(function(){return _1rj(0,_1lZ);});}break;case 104:if(_1nR!=(B(_mt(_1ri,0))-1|0)){var _1rD=_1nR+1|0;return new F(function(){return _1rj(_1rD,_1rD);});}else{return new F(function(){return _1rj(0,_1lZ);});}break;case 106:if(_1nR!=(B(_mt(_1ri,0))-1|0)){var _1rE=_1nR+1|0;return new F(function(){return _1rj(_1rE,_1rE);});}else{return new F(function(){return _1rj(0,_1lZ);});}break;case 107:var _1rF=E(_1nR);if(!_1rF){var _1rG=B(_mt(_1ri,0))-1|0;return new F(function(){return _1rj(_1rG,_1rG);});}else{var _1rH=_1rF-1|0;return new F(function(){return _1rj(_1rH,_1rH);});}break;case 108:var _1rI=E(_1nR);if(!_1rI){var _1rJ=B(_mt(_1ri,0))-1|0;return new F(function(){return _1rj(_1rJ,_1rJ);});}else{var _1rK=_1rI-1|0;return new F(function(){return _1rj(_1rK,_1rK);});}break;default:return new F(function(){return _1rj( -2,_1m1);});}}}};if(!E(_1nU)){return new F(function(){return _1o5(_);});}else{if(!E(_1nV)){return new F(function(){return _VK(_1nr,_1ns,_1nt,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS,_1nT,_wr,_1nW,_ws,_1nY,_1nZ,_1o0,_);});}else{return new F(function(){return _1o5(_);});}}}else{return {_:0,a:E(_1o4),b:E(_1o3),c:E(_1nG),d:E(_1nH),e:E(_1nI),f:E(_1nJ),g:E(_1o2),h:_1nM,i:_1nN,j:_1nO,k:_1nP,l:E(_1nQ),m:_1nR,n:E(_1o1),o:E(_1o0)};}},_1rL=function(_1rM,_1rN,_1rO){var _1rP=E(_1rO);if(!_1rP._){return 0;}else{var _1rQ=_1rP.b,_1rR=E(_1rP.a),_1rS=_1rR.a,_1rT=_1rR.b;return (_1rM<=_1rS)?1+B(_1rL(_1rM,_1rN,_1rQ))|0:(_1rM>=_1rS+_1rR.c)?1+B(_1rL(_1rM,_1rN,_1rQ))|0:(_1rN<=_1rT)?1+B(_1rL(_1rM,_1rN,_1rQ))|0:(_1rN>=_1rT+_1rR.d)?1+B(_1rL(_1rM,_1rN,_1rQ))|0:1;}},_1rU=function(_1rV,_1rW,_1rX){var _1rY=E(_1rX);if(!_1rY._){return 0;}else{var _1rZ=_1rY.b,_1s0=E(_1rY.a),_1s1=_1s0.a,_1s2=_1s0.b;if(_1rV<=_1s1){return 1+B(_1rU(_1rV,_1rW,_1rZ))|0;}else{if(_1rV>=_1s1+_1s0.c){return 1+B(_1rU(_1rV,_1rW,_1rZ))|0;}else{var _1s3=E(_1rW);return (_1s3<=_1s2)?1+B(_1rL(_1rV,_1s3,_1rZ))|0:(_1s3>=_1s2+_1s0.d)?1+B(_1rL(_1rV,_1s3,_1rZ))|0:1;}}}},_1s4=function(_1s5,_1s6,_1s7){var _1s8=E(_1s7);if(!_1s8._){return 0;}else{var _1s9=_1s8.b,_1sa=E(_1s8.a),_1sb=_1sa.a,_1sc=_1sa.b,_1sd=E(_1s5);if(_1sd<=_1sb){return 1+B(_1rU(_1sd,_1s6,_1s9))|0;}else{if(_1sd>=_1sb+_1sa.c){return 1+B(_1rU(_1sd,_1s6,_1s9))|0;}else{var _1se=E(_1s6);return (_1se<=_1sc)?1+B(_1rL(_1sd,_1se,_1s9))|0:(_1se>=_1sc+_1sa.d)?1+B(_1rL(_1sd,_1se,_1s9))|0:1;}}}},_1sf=function(_1sg,_1sh){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1sh)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1sh)-100,E(_1sg),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1sg),100);}),new T2(1,new T(function(){return new T4(0,E(_1sg)-100,100,100,E(_1sh)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1sg)-200,E(_1sh)-200);}),_10)))));},_1si=32,_1sj=76,_1sk=75,_1sl=74,_1sm=72,_1sn=64,_1so=function(_1sp,_1sq,_1sr,_1ss){var _1st=new T(function(){var _1su=E(_1sq),_1sv=E(_1su.a),_1sw=_1sv.a,_1sx=_1sv.b,_1sy=B(_1sf(_1sw,_1sx)),_1sz=new T(function(){var _1sA=E(_1su.b);return new T2(0,new T(function(){return B(_g8(_1sw,_1sA.a));}),new T(function(){return B(_g8(_1sx,_1sA.b));}));});switch(B(_1s4(new T(function(){return E(_1sr)*E(E(_1sz).a);},1),new T(function(){return E(_1ss)*E(E(_1sz).b);},1),new T2(1,_1sy.a,_1sy.b)))){case 1:return E(_1sm);break;case 2:return E(_1sl);break;case 3:return E(_1sk);break;case 4:return E(_1sj);break;case 5:return E(_1si);break;default:return E(_1sn);}});return function(_1sB,_){var _1sC=E(E(_1sq).a),_1sD=E(_1sB),_1sE=E(_1sD.a),_1sF=E(_1sD.b),_1sG=E(_1sD.g),_1sH=E(_1sD.n);return new F(function(){return _1nq(_1sp,_1sC.a,_1sC.b,_1st,_1sE.a,_1sE.b,_1sE.c,_1sE.d,_1sE.e,_1sE.f,_1sE.g,_1sE.h,_1sE.i,_1sF.a,_1sF.b,_1sD.c,_1sD.d,_1sD.e,_1sD.f,_1sG.a,_1sG.b,_1sD.h,_1sD.i,_1sD.j,_1sD.k,_1sD.l,_1sD.m,_1sH.a,_1sH.b,_1sH.c,_1sH.d,_1sH.e,_1sH.f,_1sH.g,_1sH.h,_1sD.o,_);});};},_1sI=0,_1sJ=2,_1sK=2,_1sL=0,_1sM=new T(function(){return eval("document");}),_1sN=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1sO=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1sP=function(_1sQ){return E(E(_1sQ).b);},_1sR=function(_1sS,_1sT){return new F(function(){return A2(_1sP,_1sS,function(_){var _1sU=E(_1sT),_1sV=__app1(E(_1sO),_1sU);if(!_1sV){return _0;}else{var _1sW=__app1(E(_1sN),_1sU);return new T1(1,new T2(0,_1sW,_1sU));}});});},_1sX=new T(function(){var _1sY=E(_17n);if(!_1sY._){return E(_nh);}else{return {_:0,a:E(_17g),b:E(B(_13W(_171,5,_17D))),c:E(_1sY.a),d:32,e:0,f:0,g:E(_10),h:E(_wr),i:E(_wr)};}}),_1sZ=0,_1t0=new T2(0,_1sZ,_1sZ),_1t1={_:0,a:E(_wr),b:E(_wr),c:E(_ws),d:E(_wr),e:E(_wr),f:E(_wr),g:E(_wr),h:E(_wr)},_1t2=new T(function(){return {_:0,a:E(_1sX),b:E(_172),c:E(_15a),d:E(_10),e:E(_10),f:E(_10),g:E(_1t0),h:0,i:0,j:0,k: -1,l:E(_10),m:0,n:E(_1t1),o:E(_10)};}),_1t3=new T1(0,100),_1t4=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/fi/Main.hs:14:3-9"));}),_1t5=new T6(0,_0,_2V,_10,_1t4,_0,_0),_1t6=new T(function(){return B(_2T(_1t5));}),_1t7=new T(function(){return B(unCStr("Pattern match failure in do expression at /home/yokop/Documents/haskell/fi/Main.hs:15:3-8"));}),_1t8=new T6(0,_0,_2V,_10,_1t7,_0,_0),_1t9=new T(function(){return B(_2T(_1t8));}),_1ta=new T1(1,50),_1tb=function(_1tc){return E(E(_1tc).a);},_1td=function(_1te){return E(E(_1te).a);},_1tf=function(_1tg){return E(E(_1tg).b);},_1th=function(_1ti){return E(E(_1ti).b);},_1tj=function(_1tk){return E(E(_1tk).a);},_1tl=function(_){return new F(function(){return nMV(_0);});},_1tm=new T(function(){return B(_3(_1tl));}),_1tn=function(_1to){return E(E(_1to).b);},_1tp=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1tq=function(_1tr){return E(E(_1tr).d);},_1ts=function(_1tt,_1tu,_1tv,_1tw,_1tx,_1ty){var _1tz=B(_1tb(_1tt)),_1tA=B(_1td(_1tz)),_1tB=new T(function(){return B(_1sP(_1tz));}),_1tC=new T(function(){return B(_1tq(_1tA));}),_1tD=new T(function(){return B(A1(_1tu,_1tw));}),_1tE=new T(function(){return B(A2(_1tj,_1tv,_1tx));}),_1tF=function(_1tG){return new F(function(){return A1(_1tC,new T3(0,_1tE,_1tD,_1tG));});},_1tH=function(_1tI){var _1tJ=new T(function(){var _1tK=new T(function(){var _1tL=__createJSFunc(2,function(_1tM,_){var _1tN=B(A2(E(_1tI),_1tM,_));return _7;}),_1tO=_1tL;return function(_){return new F(function(){return __app3(E(_1tp),E(_1tD),E(_1tE),_1tO);});};});return B(A1(_1tB,_1tK));});return new F(function(){return A3(_1tf,_1tA,_1tJ,_1tF);});},_1tP=new T(function(){var _1tQ=new T(function(){return B(_1sP(_1tz));}),_1tR=function(_1tS){var _1tT=new T(function(){return B(A1(_1tQ,function(_){var _=wMV(E(_1tm),new T1(1,_1tS));return new F(function(){return A(_1th,[_1tv,_1tx,_1tS,_]);});}));});return new F(function(){return A3(_1tf,_1tA,_1tT,_1ty);});};return B(A2(_1tn,_1tt,_1tR));});return new F(function(){return A3(_1tf,_1tA,_1tP,_1tH);});},_1tU=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1tV=function(_){var _1tW=rMV(E(_1tm)),_1tX=E(_1tW);if(!_1tX._){var _1tY=__app1(E(_1tU),E(_7));return new F(function(){return _gF(_);});}else{var _1tZ=__app1(E(_1tU),E(_1tX.a));return new F(function(){return _gF(_);});}},_1u0=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1u1=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1u2=function(_1u3,_1u4,_1u5){var _1u6=B(_1tb(_1u3)),_1u7=new T(function(){return B(_1sP(_1u6));}),_1u8=function(_1u9){var _1ua=function(_){var _1ub=E(_1u4);if(!_1ub._){var _1uc=B(A1(_1u9,_gE)),_1ud=__createJSFunc(0,function(_){var _1ue=B(A1(_1uc,_));return _7;}),_1uf=__app2(E(_1u1),_1ub.a,_1ud);return new T(function(){var _1ug=Number(_1uf),_1uh=jsTrunc(_1ug);return new T2(0,_1uh,E(_1ub));});}else{var _1ui=B(A1(_1u9,_gE)),_1uj=__createJSFunc(0,function(_){var _1uk=B(A1(_1ui,_));return _7;}),_1ul=__app2(E(_1u0),_1ub.a,_1uj);return new T(function(){var _1um=Number(_1ul),_1un=jsTrunc(_1um);return new T2(0,_1un,E(_1ub));});}};return new F(function(){return A1(_1u7,_1ua);});},_1uo=new T(function(){return B(A2(_1tn,_1u3,function(_1up){return E(_1u5);}));});return new F(function(){return A3(_1tf,B(_1td(_1u6)),_1uo,_1u8);});},_1uq=function(_,_1ur){var _1us=E(_1ur);if(!_1us._){return new F(function(){return die(_1t6);});}else{var _1ut=_1us.a,_1uu=B(A3(_1sR,_5X,_1ut,_)),_1uv=E(_1uu);if(!_1uv._){return new F(function(){return die(_1t9);});}else{var _1uw=E(_1uv.a),_1ux=B(_63(_1uw.b,_)),_1uy=_1ux,_1uz=nMV(_1t2),_1uA=_1uz,_1uB=B(A(_1ts,[_5Y,_3E,_u,_1sM,_1sJ,function(_1uC,_){var _1uD=B(_1tV(_)),_1uE=rMV(_1uA),_1uF=E(E(_1uy).a),_1uG=E(_1uE),_1uH=E(_1uG.a),_1uI=E(_1uG.b),_1uJ=E(_1uG.g),_1uK=E(_1uG.n),_1uL=B(_1nq(_1uw,_1uF.a,_1uF.b,E(_1uC).a,_1uH.a,_1uH.b,_1uH.c,_1uH.d,_1uH.e,_1uH.f,_1uH.g,_1uH.h,_1uH.i,_1uI.a,_1uI.b,_1uG.c,_1uG.d,_1uG.e,_1uG.f,_1uJ.a,_1uJ.b,_1uG.h,_1uG.i,_1uG.j,_1uG.k,_1uG.l,_1uG.m,_1uK.a,_1uK.b,_1uK.c,_1uK.d,_1uK.e,_1uK.f,_1uK.g,_1uK.h,_1uG.o,_)),_=wMV(_1uA,_1uL);return _gE;},_])),_1uM=B(A(_1ts,[_5Y,_3E,_3D,_1ut,_1sI,function(_1uN,_){var _1uO=E(E(_1uN).a),_1uP=rMV(_1uA),_1uQ=B(A(_1so,[_1uw,_1uy,_1uO.a,_1uO.b,_1uP,_])),_=wMV(_1uA,_1uQ);return _gE;},_])),_1uR=B(A(_1ts,[_5Y,_3E,_5d,_1ut,_1sL,function(_1uS,_){var _1uT=E(_1uS),_1uU=rMV(_1uA),_1uV=E(_1uU);if(!E(E(_1uV.n).e)){var _=wMV(_1uA,_1uV);return _gE;}else{var _1uW=B(_1tV(_)),_=wMV(_1uA,_1uV);return _gE;}},_])),_1uX=function(_){var _1uY=rMV(_1uA),_=wMV(_1uA,new T(function(){var _1uZ=E(_1uY),_1v0=E(_1uZ.n);return {_:0,a:E(_1uZ.a),b:E(_1uZ.b),c:E(_1uZ.c),d:E(_1uZ.d),e:E(_1uZ.e),f:E(_1uZ.f),g:E(_1uZ.g),h:_1uZ.h,i:_1uZ.i,j:_1uZ.j,k:_1uZ.k,l:E(_1uZ.l),m:_1uZ.m,n:E({_:0,a:E(_1v0.a),b:E(_1v0.b),c:E(_1v0.c),d:E(_1v0.d),e:E(_wr),f:E(_1v0.f),g:E(_1v0.g),h:E(_1v0.h)}),o:E(_1uZ.o)};}));return _gE;},_1v1=function(_1v2,_){var _1v3=E(_1v2),_1v4=rMV(_1uA),_=wMV(_1uA,new T(function(){var _1v5=E(_1v4),_1v6=E(_1v5.n);return {_:0,a:E(_1v5.a),b:E(_1v5.b),c:E(_1v5.c),d:E(_1v5.d),e:E(_1v5.e),f:E(_1v5.f),g:E(_1v5.g),h:_1v5.h,i:_1v5.i,j:_1v5.j,k:_1v5.k,l:E(_1v5.l),m:_1v5.m,n:E({_:0,a:E(_1v6.a),b:E(_1v6.b),c:E(_1v6.c),d:E(_1v6.d),e:E(_ws),f:E(_1v6.f),g:E(_1v6.g),h:E(_1v6.h)}),o:E(_1v5.o)};})),_1v7=B(A(_1u2,[_5Y,_1t3,_1uX,_]));return _gE;},_1v8=B(A(_1ts,[_5Y,_3E,_5d,_1ut,_1sK,_1v1,_])),_1v9=B(A(_1u2,[_5Y,_1ta,function(_){var _1va=rMV(_1uA),_1vb=E(E(_1uy).a),_1vc=E(_1va),_1vd=E(_1vc.a),_1ve=E(_1vc.b),_1vf=E(_1vc.g),_1vg=E(_1vc.n),_1vh=B(_TH(_1uw,_1vb.a,_1vb.b,_1vd.a,_1vd.b,_1vd.c,_1vd.d,_1vd.e,_1vd.f,_1vd.g,_1vd.h,_1vd.i,_1ve.a,_1ve.b,_1vc.c,_1vc.d,_1vc.e,_1vc.f,_1vf.a,_1vf.b,_1vc.h,_1vc.i,_1vc.j,_1vc.k,_1vc.l,_1vc.m,_1vg.a,_1vg.b,_1vg.c,_1vg.d,_1vg.e,_1vg.f,_1vg.g,_1vg.h,_1vc.o,_)),_=wMV(_1uA,_1vh);return _gE;},_]));return _gE;}}},_1vi="src",_1vj=new T(function(){return B(unCStr("img"));}),_1vk=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1vl=function(_1vm,_1vn){return new F(function(){return A2(_1sP,_1vm,function(_){var _1vo=__app1(E(_1vk),toJSStr(E(_1vj))),_1vp=__app3(E(_i1),_1vo,E(_1vi),E(_1vn));return _1vo;});});},_1vq=new T(function(){return B(unCStr(".png"));}),_1vr=function(_1vs,_1vt){var _1vu=E(_1vs);if(_1vu==( -1)){return __Z;}else{var _1vv=new T(function(){var _1vw=new T(function(){return toJSStr(B(_y(_1vt,new T(function(){return B(_y(B(_I(0,_1vu,_10)),_1vq));},1))));});return B(_1vl(_5X,_1vw));});return new F(function(){return _y(B(_1vr(_1vu-1|0,_1vt)),new T2(1,_1vv,_10));});}},_1vx=new T(function(){return B(unCStr("WstImage/wst"));}),_1vy=new T(function(){return B(_1vr(120,_1vx));}),_1vz=function(_1vA,_){var _1vB=E(_1vA);if(!_1vB._){return _10;}else{var _1vC=B(A1(_1vB.a,_)),_1vD=B(_1vz(_1vB.b,_));return new T2(1,_1vC,_1vD);}},_1vE=new T(function(){return B(unCStr("Images/img"));}),_1vF=new T(function(){return B(_1vr(5,_1vE));}),_1vG=function(_1vH,_){var _1vI=E(_1vH);if(!_1vI._){return _10;}else{var _1vJ=B(A1(_1vI.a,_)),_1vK=B(_1vG(_1vI.b,_));return new T2(1,_1vJ,_1vK);}},_1vL=function(_){var _1vM=B(_1vG(_1vF,_)),_1vN=B(_1vz(_1vy,_)),_1vO=__app1(E(_1),"canvas2"),_1vP=__eq(_1vO,E(_7));if(!E(_1vP)){var _1vQ=__isUndef(_1vO);if(!E(_1vQ)){return new F(function(){return _1uq(_,new T1(1,_1vO));});}else{return new F(function(){return _1uq(_,_0);});}}else{return new F(function(){return _1uq(_,_0);});}},_1vR=function(_){return new F(function(){return _1vL(_);});};
var hasteMain = function() {B(A(_1vR, [0]));};window.onload = hasteMain;