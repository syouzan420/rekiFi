"use strict";
var __haste_prog_id = '5665dcc0ebaeede8615c9e71b72ec121698d89fa99683f2bed18c6cb7fec4287';
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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n="deltaZ",_o="deltaY",_p="deltaX",_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v,_w){var _x=jsShowI(_v);return new F(function(){return _q(fromJSStr(_x),_w);});},_y=41,_z=40,_A=function(_B,_C,_D){if(_C>=0){return new F(function(){return _u(_C,_D);});}else{if(_B<=6){return new F(function(){return _u(_C,_D);});}else{return new T2(1,_z,new T(function(){var _E=jsShowI(_C);return B(_q(fromJSStr(_E),new T2(1,_y,_D)));}));}}},_F=new T(function(){return B(unCStr(")"));}),_G=new T(function(){return B(_A(0,2,_F));}),_H=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_G));}),_I=function(_J){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_A(0,_J,_H));}))));});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L)),_N=jsTrunc(_M);if(_N<0){return B(_I(_N));}else{if(_N>2){return B(_I(_N));}else{return _N;}}});},_O=0,_P=new T3(0,_O,_O,_O),_Q="button",_R=new T(function(){return eval("jsGetMouseCoords");}),_S=__Z,_T=function(_U,_){var _V=E(_U);if(!_V._){return _S;}else{var _W=B(_T(_V.b,_));return new T2(1,new T(function(){var _X=Number(E(_V.a));return jsTrunc(_X);}),_W);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _T(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return new T(function(){var _15=Number(E(_14));return jsTrunc(_15);});},_16=new T2(0,_13,_11),_17=function(_18,_){var _19=E(_18);if(!_19._){return _S;}else{var _1a=B(_17(_19.b,_));return new T2(1,_19.a,_1a);}},_1b=new T(function(){return B(unCStr("base"));}),_1c=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1d=new T(function(){return B(unCStr("IOException"));}),_1e=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1b,_1c,_1d),_1f=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1e,_S,_S),_1g=function(_1h){return E(_1f);},_1i=function(_1j){return E(E(_1j).a);},_1k=function(_1l,_1m,_1n){var _1o=B(A1(_1l,_)),_1p=B(A1(_1m,_)),_1q=hs_eqWord64(_1o.a,_1p.a);if(!_1q){return __Z;}else{var _1r=hs_eqWord64(_1o.b,_1p.b);return (!_1r)?__Z:new T1(1,_1n);}},_1s=function(_1t){var _1u=E(_1t);return new F(function(){return _1k(B(_1i(_1u.a)),_1g,_1u.b);});},_1v=new T(function(){return B(unCStr(": "));}),_1w=new T(function(){return B(unCStr(")"));}),_1x=new T(function(){return B(unCStr(" ("));}),_1y=new T(function(){return B(unCStr("interrupted"));}),_1z=new T(function(){return B(unCStr("system error"));}),_1A=new T(function(){return B(unCStr("unsatisified constraints"));}),_1B=new T(function(){return B(unCStr("user error"));}),_1C=new T(function(){return B(unCStr("permission denied"));}),_1D=new T(function(){return B(unCStr("illegal operation"));}),_1E=new T(function(){return B(unCStr("end of file"));}),_1F=new T(function(){return B(unCStr("resource exhausted"));}),_1G=new T(function(){return B(unCStr("resource busy"));}),_1H=new T(function(){return B(unCStr("does not exist"));}),_1I=new T(function(){return B(unCStr("already exists"));}),_1J=new T(function(){return B(unCStr("resource vanished"));}),_1K=new T(function(){return B(unCStr("timeout"));}),_1L=new T(function(){return B(unCStr("unsupported operation"));}),_1M=new T(function(){return B(unCStr("hardware fault"));}),_1N=new T(function(){return B(unCStr("inappropriate type"));}),_1O=new T(function(){return B(unCStr("invalid argument"));}),_1P=new T(function(){return B(unCStr("failed"));}),_1Q=new T(function(){return B(unCStr("protocol error"));}),_1R=function(_1S,_1T){switch(E(_1S)){case 0:return new F(function(){return _q(_1I,_1T);});break;case 1:return new F(function(){return _q(_1H,_1T);});break;case 2:return new F(function(){return _q(_1G,_1T);});break;case 3:return new F(function(){return _q(_1F,_1T);});break;case 4:return new F(function(){return _q(_1E,_1T);});break;case 5:return new F(function(){return _q(_1D,_1T);});break;case 6:return new F(function(){return _q(_1C,_1T);});break;case 7:return new F(function(){return _q(_1B,_1T);});break;case 8:return new F(function(){return _q(_1A,_1T);});break;case 9:return new F(function(){return _q(_1z,_1T);});break;case 10:return new F(function(){return _q(_1Q,_1T);});break;case 11:return new F(function(){return _q(_1P,_1T);});break;case 12:return new F(function(){return _q(_1O,_1T);});break;case 13:return new F(function(){return _q(_1N,_1T);});break;case 14:return new F(function(){return _q(_1M,_1T);});break;case 15:return new F(function(){return _q(_1L,_1T);});break;case 16:return new F(function(){return _q(_1K,_1T);});break;case 17:return new F(function(){return _q(_1J,_1T);});break;default:return new F(function(){return _q(_1y,_1T);});}},_1U=new T(function(){return B(unCStr("}"));}),_1V=new T(function(){return B(unCStr("{handle: "));}),_1W=function(_1X,_1Y,_1Z,_20,_21,_22){var _23=new T(function(){var _24=new T(function(){var _25=new T(function(){var _26=E(_20);if(!_26._){return E(_22);}else{var _27=new T(function(){return B(_q(_26,new T(function(){return B(_q(_1w,_22));},1)));},1);return B(_q(_1x,_27));}},1);return B(_1R(_1Y,_25));}),_28=E(_1Z);if(!_28._){return E(_24);}else{return B(_q(_28,new T(function(){return B(_q(_1v,_24));},1)));}}),_29=E(_21);if(!_29._){var _2a=E(_1X);if(!_2a._){return E(_23);}else{var _2b=E(_2a.a);if(!_2b._){var _2c=new T(function(){var _2d=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2d));},1);return new F(function(){return _q(_1V,_2c);});}else{var _2e=new T(function(){var _2f=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2f));},1);return new F(function(){return _q(_1V,_2e);});}}}else{return new F(function(){return _q(_29.a,new T(function(){return B(_q(_1v,_23));},1));});}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _1W(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_S);});},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1W(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1W(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2g,_2G),_2K=new T(function(){return new T5(0,_1g,_2J,_2L,_1s,_2g);}),_2L=function(_2M){return new T2(0,_2K,_2M);},_2N=__Z,_2O=7,_2P=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2Q=new T6(0,_2N,_2O,_S,_2P,_2N,_2N),_2R=new T(function(){return B(_2L(_2Q));}),_2S=function(_){return new F(function(){return die(_2R);});},_2T=function(_2U){return E(E(_2U).a);},_2V=function(_2W,_2X,_2Y,_){var _2Z=__arr2lst(0,_2Y),_30=B(_17(_2Z,_)),_31=E(_30);if(!_31._){return new F(function(){return _2S(_);});}else{var _32=E(_31.b);if(!_32._){return new F(function(){return _2S(_);});}else{if(!E(_32.b)._){var _33=B(A3(_2T,_2W,_31.a,_)),_34=B(A3(_2T,_2X,_32.a,_));return new T2(0,_33,_34);}else{return new F(function(){return _2S(_);});}}}},_35=function(_){return new F(function(){return __jsNull();});},_36=function(_37){var _38=B(A1(_37,_));return E(_38);},_39=new T(function(){return B(_36(_35));}),_3a=new T(function(){return E(_39);}),_3b=function(_3c,_3d,_){if(E(_3c)==7){var _3e=__app1(E(_R),_3d),_3f=B(_2V(_16,_16,_3e,_)),_3g=__get(_3d,E(_p)),_3h=__get(_3d,E(_o)),_3i=__get(_3d,E(_n));return new T(function(){return new T3(0,E(_3f),E(_2N),E(new T3(0,_3g,_3h,_3i)));});}else{var _3j=__app1(E(_R),_3d),_3k=B(_2V(_16,_16,_3j,_)),_3l=__get(_3d,E(_Q)),_3m=__eq(_3l,E(_3a));if(!E(_3m)){var _3n=__isUndef(_3l);if(!E(_3n)){var _3o=B(_K(_3l,_));return new T(function(){return new T3(0,E(_3k),E(new T1(1,_3o)),E(_P));});}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}},_3p=function(_3q,_3r,_){return new F(function(){return _3b(_3q,E(_3r),_);});},_3s="mouseout",_3t="mouseover",_3u="mousemove",_3v="mouseup",_3w="mousedown",_3x="dblclick",_3y="click",_3z="wheel",_3A=function(_3B){switch(E(_3B)){case 0:return E(_3y);case 1:return E(_3x);case 2:return E(_3w);case 3:return E(_3v);case 4:return E(_3u);case 5:return E(_3t);case 6:return E(_3s);default:return E(_3z);}},_3C=new T2(0,_3A,_3p),_3D=function(_3E){return E(_3E);},_3F=function(_3G,_3H){return E(_3G)==E(_3H);},_3I=function(_3J,_3K){return E(_3J)!=E(_3K);},_3L=new T2(0,_3F,_3I),_3M="screenY",_3N="screenX",_3O="clientY",_3P="clientX",_3Q="pageY",_3R="pageX",_3S="target",_3T="identifier",_3U=function(_3V,_){var _3W=__get(_3V,E(_3T)),_3X=__get(_3V,E(_3S)),_3Y=__get(_3V,E(_3R)),_3Z=__get(_3V,E(_3Q)),_40=__get(_3V,E(_3P)),_41=__get(_3V,E(_3O)),_42=__get(_3V,E(_3N)),_43=__get(_3V,E(_3M));return new T(function(){var _44=Number(_3W),_45=jsTrunc(_44);return new T5(0,_45,_3X,E(new T2(0,new T(function(){var _46=Number(_3Y);return jsTrunc(_46);}),new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}))),E(new T2(0,new T(function(){var _48=Number(_40);return jsTrunc(_48);}),new T(function(){var _49=Number(_41);return jsTrunc(_49);}))),E(new T2(0,new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}),new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}))));});},_4c=function(_4d,_){var _4e=E(_4d);if(!_4e._){return _S;}else{var _4f=B(_3U(E(_4e.a),_)),_4g=B(_4c(_4e.b,_));return new T2(1,_4f,_4g);}},_4h="touches",_4i=function(_4j){return E(E(_4j).b);},_4k=function(_4l,_4m,_){var _4n=__arr2lst(0,_4m),_4o=new T(function(){return B(_4i(_4l));}),_4p=function(_4q,_){var _4r=E(_4q);if(!_4r._){return _S;}else{var _4s=B(A2(_4o,_4r.a,_)),_4t=B(_4p(_4r.b,_));return new T2(1,_4s,_4t);}};return new F(function(){return _4p(_4n,_);});},_4u=function(_4v,_){return new F(function(){return _4k(_16,E(_4v),_);});},_4w=new T2(0,_11,_4u),_4x=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4y=function(_4z){return E(E(_4z).a);},_4A=function(_4B,_4C,_4D){while(1){var _4E=E(_4D);if(!_4E._){return false;}else{if(!B(A3(_4y,_4B,_4C,_4E.a))){_4D=_4E.b;continue;}else{return true;}}}},_4F=function(_4G,_4H){while(1){var _4I=B((function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return __Z;}else{var _4M=_4L.a,_4N=_4L.b;if(!B(A1(_4J,_4M))){var _4O=_4J;_4G=_4O;_4H=_4N;return __continue;}else{return new T2(1,_4M,new T(function(){return B(_4F(_4J,_4N));}));}}})(_4G,_4H));if(_4I!=__continue){return _4I;}}},_4P=function(_4Q,_){var _4R=__get(_4Q,E(_4h)),_4S=__arr2lst(0,_4R),_4T=B(_4c(_4S,_)),_4U=__app1(E(_4x),_4Q),_4V=B(_2V(_4w,_4w,_4U,_)),_4W=E(_4V),_4X=new T(function(){var _4Y=function(_4Z){return new F(function(){return _4A(_3L,new T(function(){return E(_4Z).a;}),_4W.a);});};return B(_4F(_4Y,_4T));}),_50=new T(function(){var _51=function(_52){return new F(function(){return _4A(_3L,new T(function(){return E(_52).a;}),_4W.b);});};return B(_4F(_51,_4T));});return new T3(0,_4T,_50,_4X);},_53=function(_54,_55,_){return new F(function(){return _4P(E(_55),_);});},_56="touchcancel",_57="touchend",_58="touchmove",_59="touchstart",_5a=function(_5b){switch(E(_5b)){case 0:return E(_59);case 1:return E(_58);case 2:return E(_57);default:return E(_56);}},_5c=new T2(0,_5a,_53),_5d=function(_5e,_5f,_){var _5g=B(A1(_5e,_)),_5h=B(A1(_5f,_));return _5g;},_5i=function(_5j,_5k,_){var _5l=B(A1(_5j,_)),_5m=B(A1(_5k,_));return new T(function(){return B(A1(_5l,_5m));});},_5n=function(_5o,_5p,_){var _5q=B(A1(_5p,_));return _5o;},_5r=function(_5s,_5t,_){var _5u=B(A1(_5t,_));return new T(function(){return B(A1(_5s,_5u));});},_5v=new T2(0,_5r,_5n),_5w=function(_5x,_){return _5x;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5z,_));return new F(function(){return A1(_5A,_);});},_5C=new T5(0,_5v,_5w,_5i,_5y,_5d),_5D=new T(function(){return E(_2K);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H){return new T6(0,_2N,_2O,_S,_5H,_2N,_2N);},_5I=function(_5J,_){var _5K=new T(function(){return B(A2(_5E,_5D,new T(function(){return B(A1(_5G,_5J));})));});return new F(function(){return die(_5K);});},_5L=function(_5M,_){return new F(function(){return _5I(_5M,_);});},_5N=function(_5O){return new F(function(){return A1(_5L,_5O);});},_5P=function(_5Q,_5R,_){var _5S=B(A1(_5Q,_));return new F(function(){return A2(_5R,_5S,_);});},_5T=new T5(0,_5C,_5P,_5y,_5w,_5N),_5U=function(_5V){return E(_5V);},_5W=new T2(0,_5T,_5U),_5X=new T2(0,_5W,_5w),_5Y=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_60=new T(function(){return eval("(function(cv){return cv.height})");}),_61=new T(function(){return eval("(function(cv){return cv.width})");}),_62=function(_63,_){var _64=__app1(E(_61),_63),_65=__app1(E(_60),_63),_66=__app1(E(_5Z),_63),_67=__app1(E(_5Y),_63);return new T2(0,new T2(0,_64,_65),new T2(0,_66,_67));},_68=function(_69,_6a){while(1){var _6b=E(_69);if(!_6b._){return (E(_6a)._==0)?true:false;}else{var _6c=E(_6a);if(!_6c._){return false;}else{if(E(_6b.a)!=E(_6c.a)){return false;}else{_69=_6b.b;_6a=_6c.b;continue;}}}}},_6d=function(_6e,_6f){var _6g=E(_6f);return (_6g._==0)?__Z:new T2(1,new T(function(){return B(A1(_6e,_6g.a));}),new T(function(){return B(_6d(_6e,_6g.b));}));},_6h=function(_6i){return new T1(3,E(B(_6d(_5U,_6i))));},_6j="Tried to deserialie a non-array to a list!",_6k=new T1(0,_6j),_6l=new T1(1,_S),_6m=function(_6n){var _6o=E(_6n);if(!_6o._){return E(_6l);}else{var _6p=B(_6m(_6o.b));return (_6p._==0)?new T1(0,_6p.a):new T1(1,new T2(1,_6o.a,_6p.a));}},_6q=function(_6r){var _6s=E(_6r);if(_6s._==3){return new F(function(){return _6m(_6s.a);});}else{return E(_6k);}},_6t=function(_6u){return new T1(1,_6u);},_6v=new T4(0,_5U,_6h,_6t,_6q),_6w=function(_6x,_6y,_6z){return new F(function(){return A1(_6x,new T2(1,_2s,new T(function(){return B(A1(_6y,_6z));})));});},_6A=function(_6B){return new F(function(){return _A(0,E(_6B),_S);});},_6C=34,_6D=new T2(1,_6C,_S),_6E=new T(function(){return B(unCStr("!!: negative index"));}),_6F=new T(function(){return B(unCStr("Prelude."));}),_6G=new T(function(){return B(_q(_6F,_6E));}),_6H=new T(function(){return B(err(_6G));}),_6I=new T(function(){return B(unCStr("!!: index too large"));}),_6J=new T(function(){return B(_q(_6F,_6I));}),_6K=new T(function(){return B(err(_6J));}),_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O._){return E(_6K);}else{var _6P=E(_6N);if(!_6P){return E(_6O.a);}else{_6M=_6O.b;_6N=_6P-1|0;continue;}}}},_6Q=function(_6R,_6S){if(_6S>=0){return new F(function(){return _6L(_6R,_6S);});}else{return E(_6H);}},_6T=new T(function(){return B(unCStr("ACK"));}),_6U=new T(function(){return B(unCStr("BEL"));}),_6V=new T(function(){return B(unCStr("BS"));}),_6W=new T(function(){return B(unCStr("SP"));}),_6X=new T2(1,_6W,_S),_6Y=new T(function(){return B(unCStr("US"));}),_6Z=new T2(1,_6Y,_6X),_70=new T(function(){return B(unCStr("RS"));}),_71=new T2(1,_70,_6Z),_72=new T(function(){return B(unCStr("GS"));}),_73=new T2(1,_72,_71),_74=new T(function(){return B(unCStr("FS"));}),_75=new T2(1,_74,_73),_76=new T(function(){return B(unCStr("ESC"));}),_77=new T2(1,_76,_75),_78=new T(function(){return B(unCStr("SUB"));}),_79=new T2(1,_78,_77),_7a=new T(function(){return B(unCStr("EM"));}),_7b=new T2(1,_7a,_79),_7c=new T(function(){return B(unCStr("CAN"));}),_7d=new T2(1,_7c,_7b),_7e=new T(function(){return B(unCStr("ETB"));}),_7f=new T2(1,_7e,_7d),_7g=new T(function(){return B(unCStr("SYN"));}),_7h=new T2(1,_7g,_7f),_7i=new T(function(){return B(unCStr("NAK"));}),_7j=new T2(1,_7i,_7h),_7k=new T(function(){return B(unCStr("DC4"));}),_7l=new T2(1,_7k,_7j),_7m=new T(function(){return B(unCStr("DC3"));}),_7n=new T2(1,_7m,_7l),_7o=new T(function(){return B(unCStr("DC2"));}),_7p=new T2(1,_7o,_7n),_7q=new T(function(){return B(unCStr("DC1"));}),_7r=new T2(1,_7q,_7p),_7s=new T(function(){return B(unCStr("DLE"));}),_7t=new T2(1,_7s,_7r),_7u=new T(function(){return B(unCStr("SI"));}),_7v=new T2(1,_7u,_7t),_7w=new T(function(){return B(unCStr("SO"));}),_7x=new T2(1,_7w,_7v),_7y=new T(function(){return B(unCStr("CR"));}),_7z=new T2(1,_7y,_7x),_7A=new T(function(){return B(unCStr("FF"));}),_7B=new T2(1,_7A,_7z),_7C=new T(function(){return B(unCStr("VT"));}),_7D=new T2(1,_7C,_7B),_7E=new T(function(){return B(unCStr("LF"));}),_7F=new T2(1,_7E,_7D),_7G=new T(function(){return B(unCStr("HT"));}),_7H=new T2(1,_7G,_7F),_7I=new T2(1,_6V,_7H),_7J=new T2(1,_6U,_7I),_7K=new T2(1,_6T,_7J),_7L=new T(function(){return B(unCStr("ENQ"));}),_7M=new T2(1,_7L,_7K),_7N=new T(function(){return B(unCStr("EOT"));}),_7O=new T2(1,_7N,_7M),_7P=new T(function(){return B(unCStr("ETX"));}),_7Q=new T2(1,_7P,_7O),_7R=new T(function(){return B(unCStr("STX"));}),_7S=new T2(1,_7R,_7Q),_7T=new T(function(){return B(unCStr("SOH"));}),_7U=new T2(1,_7T,_7S),_7V=new T(function(){return B(unCStr("NUL"));}),_7W=new T2(1,_7V,_7U),_7X=92,_7Y=new T(function(){return B(unCStr("\\DEL"));}),_7Z=new T(function(){return B(unCStr("\\a"));}),_80=new T(function(){return B(unCStr("\\\\"));}),_81=new T(function(){return B(unCStr("\\SO"));}),_82=new T(function(){return B(unCStr("\\r"));}),_83=new T(function(){return B(unCStr("\\f"));}),_84=new T(function(){return B(unCStr("\\v"));}),_85=new T(function(){return B(unCStr("\\n"));}),_86=new T(function(){return B(unCStr("\\t"));}),_87=new T(function(){return B(unCStr("\\b"));}),_88=function(_89,_8a){if(_89<=127){var _8b=E(_89);switch(_8b){case 92:return new F(function(){return _q(_80,_8a);});break;case 127:return new F(function(){return _q(_7Y,_8a);});break;default:if(_8b<32){var _8c=E(_8b);switch(_8c){case 7:return new F(function(){return _q(_7Z,_8a);});break;case 8:return new F(function(){return _q(_87,_8a);});break;case 9:return new F(function(){return _q(_86,_8a);});break;case 10:return new F(function(){return _q(_85,_8a);});break;case 11:return new F(function(){return _q(_84,_8a);});break;case 12:return new F(function(){return _q(_83,_8a);});break;case 13:return new F(function(){return _q(_82,_8a);});break;case 14:return new F(function(){return _q(_81,new T(function(){var _8d=E(_8a);if(!_8d._){return __Z;}else{if(E(_8d.a)==72){return B(unAppCStr("\\&",_8d));}else{return E(_8d);}}},1));});break;default:return new F(function(){return _q(new T2(1,_7X,new T(function(){return B(_6Q(_7W,_8c));})),_8a);});}}else{return new T2(1,_8b,_8a);}}}else{var _8e=new T(function(){var _8f=jsShowI(_89);return B(_q(fromJSStr(_8f),new T(function(){var _8g=E(_8a);if(!_8g._){return __Z;}else{var _8h=E(_8g.a);if(_8h<48){return E(_8g);}else{if(_8h>57){return E(_8g);}else{return B(unAppCStr("\\&",_8g));}}}},1)));});return new T2(1,_7X,_8e);}},_8i=new T(function(){return B(unCStr("\\\""));}),_8j=function(_8k,_8l){var _8m=E(_8k);if(!_8m._){return E(_8l);}else{var _8n=_8m.b,_8o=E(_8m.a);if(_8o==34){return new F(function(){return _q(_8i,new T(function(){return B(_8j(_8n,_8l));},1));});}else{return new F(function(){return _88(_8o,new T(function(){return B(_8j(_8n,_8l));}));});}}},_8p=function(_8q){return new T2(1,_6C,new T(function(){return B(_8j(_8q,_6D));}));},_8r=function(_8s,_8t){if(_8s<=_8t){var _8u=function(_8v){return new T2(1,_8v,new T(function(){if(_8v!=_8t){return B(_8u(_8v+1|0));}else{return __Z;}}));};return new F(function(){return _8u(_8s);});}else{return __Z;}},_8w=function(_8x){return new F(function(){return _8r(E(_8x),2147483647);});},_8y=function(_8z,_8A,_8B){if(_8B<=_8A){var _8C=new T(function(){var _8D=_8A-_8z|0,_8E=function(_8F){return (_8F>=(_8B-_8D|0))?new T2(1,_8F,new T(function(){return B(_8E(_8F+_8D|0));})):new T2(1,_8F,_S);};return B(_8E(_8A));});return new T2(1,_8z,_8C);}else{return (_8B<=_8z)?new T2(1,_8z,_S):__Z;}},_8G=function(_8H,_8I,_8J){if(_8J>=_8I){var _8K=new T(function(){var _8L=_8I-_8H|0,_8M=function(_8N){return (_8N<=(_8J-_8L|0))?new T2(1,_8N,new T(function(){return B(_8M(_8N+_8L|0));})):new T2(1,_8N,_S);};return B(_8M(_8I));});return new T2(1,_8H,_8K);}else{return (_8J>=_8H)?new T2(1,_8H,_S):__Z;}},_8O=function(_8P,_8Q){if(_8Q<_8P){return new F(function(){return _8y(_8P,_8Q, -2147483648);});}else{return new F(function(){return _8G(_8P,_8Q,2147483647);});}},_8R=function(_8S,_8T){return new F(function(){return _8O(E(_8S),E(_8T));});},_8U=function(_8V,_8W,_8X){if(_8W<_8V){return new F(function(){return _8y(_8V,_8W,_8X);});}else{return new F(function(){return _8G(_8V,_8W,_8X);});}},_8Y=function(_8Z,_90,_91){return new F(function(){return _8U(E(_8Z),E(_90),E(_91));});},_92=function(_93,_94){return new F(function(){return _8r(E(_93),E(_94));});},_95=function(_96){return E(_96);},_97=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_98=new T(function(){return B(err(_97));}),_99=function(_9a){var _9b=E(_9a);return (_9b==( -2147483648))?E(_98):_9b-1|0;},_9c=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f){var _9g=E(_9f);return (_9g==2147483647)?E(_9d):_9g+1|0;},_9h={_:0,a:_9e,b:_99,c:_95,d:_95,e:_8w,f:_8R,g:_92,h:_8Y},_9i=function(_9j,_9k){if(_9j<=0){if(_9j>=0){return new F(function(){return quot(_9j,_9k);});}else{if(_9k<=0){return new F(function(){return quot(_9j,_9k);});}else{return quot(_9j+1|0,_9k)-1|0;}}}else{if(_9k>=0){if(_9j>=0){return new F(function(){return quot(_9j,_9k);});}else{if(_9k<=0){return new F(function(){return quot(_9j,_9k);});}else{return quot(_9j+1|0,_9k)-1|0;}}}else{return quot(_9j-1|0,_9k)-1|0;}}},_9l=new T(function(){return B(unCStr("base"));}),_9m=new T(function(){return B(unCStr("GHC.Exception"));}),_9n=new T(function(){return B(unCStr("ArithException"));}),_9o=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9l,_9m,_9n),_9p=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9o,_S,_S),_9q=function(_9r){return E(_9p);},_9s=function(_9t){var _9u=E(_9t);return new F(function(){return _1k(B(_1i(_9u.a)),_9q,_9u.b);});},_9v=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9w=new T(function(){return B(unCStr("denormal"));}),_9x=new T(function(){return B(unCStr("divide by zero"));}),_9y=new T(function(){return B(unCStr("loss of precision"));}),_9z=new T(function(){return B(unCStr("arithmetic underflow"));}),_9A=new T(function(){return B(unCStr("arithmetic overflow"));}),_9B=function(_9C,_9D){switch(E(_9C)){case 0:return new F(function(){return _q(_9A,_9D);});break;case 1:return new F(function(){return _q(_9z,_9D);});break;case 2:return new F(function(){return _q(_9y,_9D);});break;case 3:return new F(function(){return _q(_9x,_9D);});break;case 4:return new F(function(){return _q(_9w,_9D);});break;default:return new F(function(){return _q(_9v,_9D);});}},_9E=function(_9F){return new F(function(){return _9B(_9F,_S);});},_9G=function(_9H,_9I,_9J){return new F(function(){return _9B(_9I,_9J);});},_9K=function(_9L,_9M){return new F(function(){return _2v(_9B,_9L,_9M);});},_9N=new T3(0,_9G,_9E,_9K),_9O=new T(function(){return new T5(0,_9q,_9N,_9P,_9s,_9E);}),_9P=function(_9Q){return new T2(0,_9O,_9Q);},_9R=3,_9S=new T(function(){return B(_9P(_9R));}),_9T=new T(function(){return die(_9S);}),_9U=0,_9V=new T(function(){return B(_9P(_9U));}),_9W=new T(function(){return die(_9V);}),_9X=function(_9Y,_9Z){var _a0=E(_9Z);switch(_a0){case  -1:var _a1=E(_9Y);if(_a1==( -2147483648)){return E(_9W);}else{return new F(function(){return _9i(_a1, -1);});}break;case 0:return E(_9T);default:return new F(function(){return _9i(_9Y,_a0);});}},_a2=function(_a3,_a4){return new F(function(){return _9X(E(_a3),E(_a4));});},_a5=0,_a6=new T2(0,_9W,_a5),_a7=function(_a8,_a9){var _aa=E(_a8),_ab=E(_a9);switch(_ab){case  -1:var _ac=E(_aa);if(_ac==( -2147483648)){return E(_a6);}else{if(_ac<=0){if(_ac>=0){var _ad=quotRemI(_ac, -1);return new T2(0,_ad.a,_ad.b);}else{var _ae=quotRemI(_ac, -1);return new T2(0,_ae.a,_ae.b);}}else{var _af=quotRemI(_ac-1|0, -1);return new T2(0,_af.a-1|0,(_af.b+( -1)|0)+1|0);}}break;case 0:return E(_9T);default:if(_aa<=0){if(_aa>=0){var _ag=quotRemI(_aa,_ab);return new T2(0,_ag.a,_ag.b);}else{if(_ab<=0){var _ah=quotRemI(_aa,_ab);return new T2(0,_ah.a,_ah.b);}else{var _ai=quotRemI(_aa+1|0,_ab);return new T2(0,_ai.a-1|0,(_ai.b+_ab|0)-1|0);}}}else{if(_ab>=0){if(_aa>=0){var _aj=quotRemI(_aa,_ab);return new T2(0,_aj.a,_aj.b);}else{if(_ab<=0){var _ak=quotRemI(_aa,_ab);return new T2(0,_ak.a,_ak.b);}else{var _al=quotRemI(_aa+1|0,_ab);return new T2(0,_al.a-1|0,(_al.b+_ab|0)-1|0);}}}else{var _am=quotRemI(_aa-1|0,_ab);return new T2(0,_am.a-1|0,(_am.b+_ab|0)+1|0);}}}},_an=function(_ao,_ap){var _aq=_ao%_ap;if(_ao<=0){if(_ao>=0){return E(_aq);}else{if(_ap<=0){return E(_aq);}else{var _ar=E(_aq);return (_ar==0)?0:_ar+_ap|0;}}}else{if(_ap>=0){if(_ao>=0){return E(_aq);}else{if(_ap<=0){return E(_aq);}else{var _as=E(_aq);return (_as==0)?0:_as+_ap|0;}}}else{var _at=E(_aq);return (_at==0)?0:_at+_ap|0;}}},_au=function(_av,_aw){var _ax=E(_aw);switch(_ax){case  -1:return E(_a5);case 0:return E(_9T);default:return new F(function(){return _an(E(_av),_ax);});}},_ay=function(_az,_aA){var _aB=E(_az),_aC=E(_aA);switch(_aC){case  -1:var _aD=E(_aB);if(_aD==( -2147483648)){return E(_9W);}else{return new F(function(){return quot(_aD, -1);});}break;case 0:return E(_9T);default:return new F(function(){return quot(_aB,_aC);});}},_aE=function(_aF,_aG){var _aH=E(_aF),_aI=E(_aG);switch(_aI){case  -1:var _aJ=E(_aH);if(_aJ==( -2147483648)){return E(_a6);}else{var _aK=quotRemI(_aJ, -1);return new T2(0,_aK.a,_aK.b);}break;case 0:return E(_9T);default:var _aL=quotRemI(_aH,_aI);return new T2(0,_aL.a,_aL.b);}},_aM=function(_aN,_aO){var _aP=E(_aO);switch(_aP){case  -1:return E(_a5);case 0:return E(_9T);default:return E(_aN)%_aP;}},_aQ=function(_aR){return new T1(0,_aR);},_aS=function(_aT){return new F(function(){return _aQ(E(_aT));});},_aU=new T1(0,1),_aV=function(_aW){return new T2(0,E(B(_aQ(E(_aW)))),E(_aU));},_aX=function(_aY,_aZ){return imul(E(_aY),E(_aZ))|0;},_b0=function(_b1,_b2){return E(_b1)+E(_b2)|0;},_b3=function(_b4,_b5){return E(_b4)-E(_b5)|0;},_b6=function(_b7){var _b8=E(_b7);return (_b8<0)? -_b8:E(_b8);},_b9=function(_ba){var _bb=E(_ba);if(!_bb._){return E(_bb.a);}else{return new F(function(){return I_toInt(_bb.a);});}},_bc=function(_bd){return new F(function(){return _b9(_bd);});},_be=function(_bf){return  -E(_bf);},_bg= -1,_bh=0,_bi=1,_bj=function(_bk){var _bl=E(_bk);return (_bl>=0)?(E(_bl)==0)?E(_bh):E(_bi):E(_bg);},_bm={_:0,a:_b0,b:_b3,c:_aX,d:_be,e:_b6,f:_bj,g:_bc},_bn=function(_bo,_bp){var _bq=E(_bo),_br=E(_bp);return (_bq>_br)?E(_bq):E(_br);},_bs=function(_bt,_bu){var _bv=E(_bt),_bw=E(_bu);return (_bv>_bw)?E(_bw):E(_bv);},_bx=function(_by,_bz){return (_by>=_bz)?(_by!=_bz)?2:1:0;},_bA=function(_bB,_bC){return new F(function(){return _bx(E(_bB),E(_bC));});},_bD=function(_bE,_bF){return E(_bE)>=E(_bF);},_bG=function(_bH,_bI){return E(_bH)>E(_bI);},_bJ=function(_bK,_bL){return E(_bK)<=E(_bL);},_bM=function(_bN,_bO){return E(_bN)<E(_bO);},_bP={_:0,a:_3L,b:_bA,c:_bM,d:_bJ,e:_bG,f:_bD,g:_bn,h:_bs},_bQ=new T3(0,_bm,_bP,_aV),_bR={_:0,a:_bQ,b:_9h,c:_ay,d:_aM,e:_a2,f:_au,g:_aE,h:_a7,i:_aS},_bS=function(_bT){var _bU=E(_bT);return new F(function(){return Math.log(_bU+(_bU+1)*Math.sqrt((_bU-1)/(_bU+1)));});},_bV=function(_bW){var _bX=E(_bW);return new F(function(){return Math.log(_bX+Math.sqrt(1+_bX*_bX));});},_bY=function(_bZ){var _c0=E(_bZ);return 0.5*Math.log((1+_c0)/(1-_c0));},_c1=function(_c2,_c3){return Math.log(E(_c3))/Math.log(E(_c2));},_c4=3.141592653589793,_c5=new T1(0,1),_c6=function(_c7,_c8){var _c9=E(_c7);if(!_c9._){var _ca=_c9.a,_cb=E(_c8);if(!_cb._){var _cc=_cb.a;return (_ca!=_cc)?(_ca>_cc)?2:0:1;}else{var _cd=I_compareInt(_cb.a,_ca);return (_cd<=0)?(_cd>=0)?1:2:0;}}else{var _ce=_c9.a,_cf=E(_c8);if(!_cf._){var _cg=I_compareInt(_ce,_cf.a);return (_cg>=0)?(_cg<=0)?1:2:0;}else{var _ch=I_compare(_ce,_cf.a);return (_ch>=0)?(_ch<=0)?1:2:0;}}},_ci=function(_cj,_ck){var _cl=E(_cj);return (_cl._==0)?_cl.a*Math.pow(2,_ck):I_toNumber(_cl.a)*Math.pow(2,_ck);},_cm=function(_cn,_co){var _cp=E(_cn);if(!_cp._){var _cq=_cp.a,_cr=E(_co);return (_cr._==0)?_cq==_cr.a:(I_compareInt(_cr.a,_cq)==0)?true:false;}else{var _cs=_cp.a,_ct=E(_co);return (_ct._==0)?(I_compareInt(_cs,_ct.a)==0)?true:false:(I_compare(_cs,_ct.a)==0)?true:false;}},_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx._){var _cy=_cx.a,_cz=E(_cw);if(!_cz._){var _cA=_cz.a,_cB=addC(_cy,_cA);if(!E(_cB.b)){return new T1(0,_cB.a);}else{_cv=new T1(1,I_fromInt(_cy));_cw=new T1(1,I_fromInt(_cA));continue;}}else{_cv=new T1(1,I_fromInt(_cy));_cw=_cz;continue;}}else{var _cC=E(_cw);if(!_cC._){_cv=_cx;_cw=new T1(1,I_fromInt(_cC.a));continue;}else{return new T1(1,I_add(_cx.a,_cC.a));}}}},_cD=function(_cE,_cF){while(1){var _cG=E(_cE);if(!_cG._){var _cH=E(_cG.a);if(_cH==( -2147483648)){_cE=new T1(1,I_fromInt( -2147483648));continue;}else{var _cI=E(_cF);if(!_cI._){var _cJ=_cI.a;return new T2(0,new T1(0,quot(_cH,_cJ)),new T1(0,_cH%_cJ));}else{_cE=new T1(1,I_fromInt(_cH));_cF=_cI;continue;}}}else{var _cK=E(_cF);if(!_cK._){_cE=_cG;_cF=new T1(1,I_fromInt(_cK.a));continue;}else{var _cL=I_quotRem(_cG.a,_cK.a);return new T2(0,new T1(1,_cL.a),new T1(1,_cL.b));}}}},_cM=new T1(0,0),_cN=function(_cO,_cP){while(1){var _cQ=E(_cO);if(!_cQ._){_cO=new T1(1,I_fromInt(_cQ.a));continue;}else{return new T1(1,I_shiftLeft(_cQ.a,_cP));}}},_cR=function(_cS,_cT,_cU){if(!B(_cm(_cU,_cM))){var _cV=B(_cD(_cT,_cU)),_cW=_cV.a;switch(B(_c6(B(_cN(_cV.b,1)),_cU))){case 0:return new F(function(){return _ci(_cW,_cS);});break;case 1:if(!(B(_b9(_cW))&1)){return new F(function(){return _ci(_cW,_cS);});}else{return new F(function(){return _ci(B(_cu(_cW,_c5)),_cS);});}break;default:return new F(function(){return _ci(B(_cu(_cW,_c5)),_cS);});}}else{return E(_9T);}},_cX=function(_cY,_cZ){var _d0=E(_cY);if(!_d0._){var _d1=_d0.a,_d2=E(_cZ);return (_d2._==0)?_d1>_d2.a:I_compareInt(_d2.a,_d1)<0;}else{var _d3=_d0.a,_d4=E(_cZ);return (_d4._==0)?I_compareInt(_d3,_d4.a)>0:I_compare(_d3,_d4.a)>0;}},_d5=new T1(0,1),_d6=function(_d7,_d8){var _d9=E(_d7);if(!_d9._){var _da=_d9.a,_db=E(_d8);return (_db._==0)?_da<_db.a:I_compareInt(_db.a,_da)>0;}else{var _dc=_d9.a,_dd=E(_d8);return (_dd._==0)?I_compareInt(_dc,_dd.a)<0:I_compare(_dc,_dd.a)<0;}},_de=new T(function(){return B(unCStr("base"));}),_df=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dg=new T(function(){return B(unCStr("PatternMatchFail"));}),_dh=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_de,_df,_dg),_di=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dh,_S,_S),_dj=function(_dk){return E(_di);},_dl=function(_dm){var _dn=E(_dm);return new F(function(){return _1k(B(_1i(_dn.a)),_dj,_dn.b);});},_do=function(_dp){return E(E(_dp).a);},_dq=function(_dr){return new T2(0,_ds,_dr);},_dt=function(_du,_dv){return new F(function(){return _q(E(_du).a,_dv);});},_dw=function(_dx,_dy){return new F(function(){return _2v(_dt,_dx,_dy);});},_dz=function(_dA,_dB,_dC){return new F(function(){return _q(E(_dB).a,_dC);});},_dD=new T3(0,_dz,_do,_dw),_ds=new T(function(){return new T5(0,_dj,_dD,_dq,_dl,_do);}),_dE=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dF=function(_dG,_dH){return new F(function(){return die(new T(function(){return B(A2(_5E,_dH,_dG));}));});},_dI=function(_dJ,_9Q){return new F(function(){return _dF(_dJ,_9Q);});},_dK=function(_dL,_dM){var _dN=E(_dM);if(!_dN._){return new T2(0,_S,_S);}else{var _dO=_dN.a;if(!B(A1(_dL,_dO))){return new T2(0,_S,_dN);}else{var _dP=new T(function(){var _dQ=B(_dK(_dL,_dN.b));return new T2(0,_dQ.a,_dQ.b);});return new T2(0,new T2(1,_dO,new T(function(){return E(E(_dP).a);})),new T(function(){return E(E(_dP).b);}));}}},_dR=32,_dS=new T(function(){return B(unCStr("\n"));}),_dT=function(_dU){return (E(_dU)==124)?false:true;},_dV=function(_dW,_dX){var _dY=B(_dK(_dT,B(unCStr(_dW)))),_dZ=_dY.a,_e0=function(_e1,_e2){var _e3=new T(function(){var _e4=new T(function(){return B(_q(_dX,new T(function(){return B(_q(_e2,_dS));},1)));});return B(unAppCStr(": ",_e4));},1);return new F(function(){return _q(_e1,_e3);});},_e5=E(_dY.b);if(!_e5._){return new F(function(){return _e0(_dZ,_S);});}else{if(E(_e5.a)==124){return new F(function(){return _e0(_dZ,new T2(1,_dR,_e5.b));});}else{return new F(function(){return _e0(_dZ,_S);});}}},_e6=function(_e7){return new F(function(){return _dI(new T1(0,new T(function(){return B(_dV(_e7,_dE));})),_ds);});},_e8=function(_e9){var _ea=function(_eb,_ec){while(1){if(!B(_d6(_eb,_e9))){if(!B(_cX(_eb,_e9))){if(!B(_cm(_eb,_e9))){return new F(function(){return _e6("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ec);}}else{return _ec-1|0;}}else{var _ed=B(_cN(_eb,1)),_ee=_ec+1|0;_eb=_ed;_ec=_ee;continue;}}};return new F(function(){return _ea(_d5,0);});},_ef=function(_eg){var _eh=E(_eg);if(!_eh._){var _ei=_eh.a>>>0;if(!_ei){return  -1;}else{var _ej=function(_ek,_el){while(1){if(_ek>=_ei){if(_ek<=_ei){if(_ek!=_ei){return new F(function(){return _e6("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_el);}}else{return _el-1|0;}}else{var _em=imul(_ek,2)>>>0,_en=_el+1|0;_ek=_em;_el=_en;continue;}}};return new F(function(){return _ej(1,0);});}}else{return new F(function(){return _e8(_eh);});}},_eo=function(_ep){var _eq=E(_ep);if(!_eq._){var _er=_eq.a>>>0;if(!_er){return new T2(0, -1,0);}else{var _es=function(_et,_eu){while(1){if(_et>=_er){if(_et<=_er){if(_et!=_er){return new F(function(){return _e6("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_eu);}}else{return _eu-1|0;}}else{var _ev=imul(_et,2)>>>0,_ew=_eu+1|0;_et=_ev;_eu=_ew;continue;}}};return new T2(0,B(_es(1,0)),(_er&_er-1>>>0)>>>0&4294967295);}}else{var _ex=_eq.a;return new T2(0,B(_ef(_eq)),I_compareInt(I_and(_ex,I_sub(_ex,I_fromInt(1))),0));}},_ey=function(_ez,_eA){var _eB=E(_ez);if(!_eB._){var _eC=_eB.a,_eD=E(_eA);return (_eD._==0)?_eC<=_eD.a:I_compareInt(_eD.a,_eC)>=0;}else{var _eE=_eB.a,_eF=E(_eA);return (_eF._==0)?I_compareInt(_eE,_eF.a)<=0:I_compare(_eE,_eF.a)<=0;}},_eG=function(_eH,_eI){while(1){var _eJ=E(_eH);if(!_eJ._){var _eK=_eJ.a,_eL=E(_eI);if(!_eL._){return new T1(0,(_eK>>>0&_eL.a>>>0)>>>0&4294967295);}else{_eH=new T1(1,I_fromInt(_eK));_eI=_eL;continue;}}else{var _eM=E(_eI);if(!_eM._){_eH=_eJ;_eI=new T1(1,I_fromInt(_eM.a));continue;}else{return new T1(1,I_and(_eJ.a,_eM.a));}}}},_eN=function(_eO,_eP){while(1){var _eQ=E(_eO);if(!_eQ._){var _eR=_eQ.a,_eS=E(_eP);if(!_eS._){var _eT=_eS.a,_eU=subC(_eR,_eT);if(!E(_eU.b)){return new T1(0,_eU.a);}else{_eO=new T1(1,I_fromInt(_eR));_eP=new T1(1,I_fromInt(_eT));continue;}}else{_eO=new T1(1,I_fromInt(_eR));_eP=_eS;continue;}}else{var _eV=E(_eP);if(!_eV._){_eO=_eQ;_eP=new T1(1,I_fromInt(_eV.a));continue;}else{return new T1(1,I_sub(_eQ.a,_eV.a));}}}},_eW=new T1(0,2),_eX=function(_eY,_eZ){var _f0=E(_eY);if(!_f0._){var _f1=(_f0.a>>>0&(2<<_eZ>>>0)-1>>>0)>>>0,_f2=1<<_eZ>>>0;return (_f2<=_f1)?(_f2>=_f1)?1:2:0;}else{var _f3=B(_eG(_f0,B(_eN(B(_cN(_eW,_eZ)),_d5)))),_f4=B(_cN(_d5,_eZ));return (!B(_cX(_f4,_f3)))?(!B(_d6(_f4,_f3)))?1:2:0;}},_f5=function(_f6,_f7){while(1){var _f8=E(_f6);if(!_f8._){_f6=new T1(1,I_fromInt(_f8.a));continue;}else{return new T1(1,I_shiftRight(_f8.a,_f7));}}},_f9=function(_fa,_fb,_fc,_fd){var _fe=B(_eo(_fd)),_ff=_fe.a;if(!E(_fe.b)){var _fg=B(_ef(_fc));if(_fg<((_ff+_fa|0)-1|0)){var _fh=_ff+(_fa-_fb|0)|0;if(_fh>0){if(_fh>_fg){if(_fh<=(_fg+1|0)){if(!E(B(_eo(_fc)).b)){return 0;}else{return new F(function(){return _ci(_c5,_fa-_fb|0);});}}else{return 0;}}else{var _fi=B(_f5(_fc,_fh));switch(B(_eX(_fc,_fh-1|0))){case 0:return new F(function(){return _ci(_fi,_fa-_fb|0);});break;case 1:if(!(B(_b9(_fi))&1)){return new F(function(){return _ci(_fi,_fa-_fb|0);});}else{return new F(function(){return _ci(B(_cu(_fi,_c5)),_fa-_fb|0);});}break;default:return new F(function(){return _ci(B(_cu(_fi,_c5)),_fa-_fb|0);});}}}else{return new F(function(){return _ci(_fc,(_fa-_fb|0)-_fh|0);});}}else{if(_fg>=_fb){var _fj=B(_f5(_fc,(_fg+1|0)-_fb|0));switch(B(_eX(_fc,_fg-_fb|0))){case 0:return new F(function(){return _ci(_fj,((_fg-_ff|0)+1|0)-_fb|0);});break;case 2:return new F(function(){return _ci(B(_cu(_fj,_c5)),((_fg-_ff|0)+1|0)-_fb|0);});break;default:if(!(B(_b9(_fj))&1)){return new F(function(){return _ci(_fj,((_fg-_ff|0)+1|0)-_fb|0);});}else{return new F(function(){return _ci(B(_cu(_fj,_c5)),((_fg-_ff|0)+1|0)-_fb|0);});}}}else{return new F(function(){return _ci(_fc, -_ff);});}}}else{var _fk=B(_ef(_fc))-_ff|0,_fl=function(_fm){var _fn=function(_fo,_fp){if(!B(_ey(B(_cN(_fp,_fb)),_fo))){return new F(function(){return _cR(_fm-_fb|0,_fo,_fp);});}else{return new F(function(){return _cR((_fm-_fb|0)+1|0,_fo,B(_cN(_fp,1)));});}};if(_fm>=_fb){if(_fm!=_fb){return new F(function(){return _fn(_fc,new T(function(){return B(_cN(_fd,_fm-_fb|0));}));});}else{return new F(function(){return _fn(_fc,_fd);});}}else{return new F(function(){return _fn(new T(function(){return B(_cN(_fc,_fb-_fm|0));}),_fd);});}};if(_fa>_fk){return new F(function(){return _fl(_fa);});}else{return new F(function(){return _fl(_fk);});}}},_fq=new T1(0,2147483647),_fr=new T(function(){return B(_cu(_fq,_d5));}),_fs=function(_ft){var _fu=E(_ft);if(!_fu._){var _fv=E(_fu.a);return (_fv==( -2147483648))?E(_fr):new T1(0, -_fv);}else{return new T1(1,I_negate(_fu.a));}},_fw=new T(function(){return 0/0;}),_fx=new T(function(){return  -1/0;}),_fy=new T(function(){return 1/0;}),_fz=0,_fA=function(_fB,_fC){if(!B(_cm(_fC,_cM))){if(!B(_cm(_fB,_cM))){if(!B(_d6(_fB,_cM))){return new F(function(){return _f9( -1021,53,_fB,_fC);});}else{return  -B(_f9( -1021,53,B(_fs(_fB)),_fC));}}else{return E(_fz);}}else{return (!B(_cm(_fB,_cM)))?(!B(_d6(_fB,_cM)))?E(_fy):E(_fx):E(_fw);}},_fD=function(_fE){var _fF=E(_fE);return new F(function(){return _fA(_fF.a,_fF.b);});},_fG=function(_fH){return 1/E(_fH);},_fI=function(_fJ){var _fK=E(_fJ);return (_fK!=0)?(_fK<=0)? -_fK:E(_fK):E(_fz);},_fL=function(_fM){var _fN=E(_fM);if(!_fN._){return _fN.a;}else{return new F(function(){return I_toNumber(_fN.a);});}},_fO=function(_fP){return new F(function(){return _fL(_fP);});},_fQ=1,_fR= -1,_fS=function(_fT){var _fU=E(_fT);return (_fU<=0)?(_fU>=0)?E(_fU):E(_fR):E(_fQ);},_fV=function(_fW,_fX){return E(_fW)-E(_fX);},_fY=function(_fZ){return  -E(_fZ);},_g0=function(_g1,_g2){return E(_g1)+E(_g2);},_g3=function(_g4,_g5){return E(_g4)*E(_g5);},_g6={_:0,a:_g0,b:_fV,c:_g3,d:_fY,e:_fI,f:_fS,g:_fO},_g7=function(_g8,_g9){return E(_g8)/E(_g9);},_ga=new T4(0,_g6,_g7,_fG,_fD),_gb=function(_gc){return new F(function(){return Math.acos(E(_gc));});},_gd=function(_ge){return new F(function(){return Math.asin(E(_ge));});},_gf=function(_gg){return new F(function(){return Math.atan(E(_gg));});},_gh=function(_gi){return new F(function(){return Math.cos(E(_gi));});},_gj=function(_gk){return new F(function(){return cosh(E(_gk));});},_gl=function(_gm){return new F(function(){return Math.exp(E(_gm));});},_gn=function(_go){return new F(function(){return Math.log(E(_go));});},_gp=function(_gq,_gr){return new F(function(){return Math.pow(E(_gq),E(_gr));});},_gs=function(_gt){return new F(function(){return Math.sin(E(_gt));});},_gu=function(_gv){return new F(function(){return sinh(E(_gv));});},_gw=function(_gx){return new F(function(){return Math.sqrt(E(_gx));});},_gy=function(_gz){return new F(function(){return Math.tan(E(_gz));});},_gA=function(_gB){return new F(function(){return tanh(E(_gB));});},_gC={_:0,a:_ga,b:_c4,c:_gl,d:_gn,e:_gw,f:_gp,g:_c1,h:_gs,i:_gh,j:_gy,k:_gd,l:_gb,m:_gf,n:_gu,o:_gj,p:_gA,q:_bV,r:_bS,s:_bY},_gD=0,_gE=function(_){return _gD;},_gF=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gG=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gH=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gI=function(_gJ,_gK,_gL,_){var _gM=__app1(E(_gG),_gL),_gN=__app2(E(_gH),_gL,E(_gJ)),_gO=B(A2(_gK,_gL,_)),_gP=__app1(E(_gF),_gL);return new F(function(){return _gE(_);});},_gQ=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gR=function(_gS,_gT,_gU,_gV,_){var _gW=__app1(E(_gG),_gV),_gX=__app3(E(_gQ),_gV,E(_gS),E(_gT)),_gY=B(A2(_gU,_gV,_)),_gZ=__app1(E(_gF),_gV);return new F(function(){return _gE(_);});},_h0=function(_h1,_h2){return E(_h1)!=E(_h2);},_h3=function(_h4,_h5){return E(_h4)==E(_h5);},_h6=new T2(0,_h3,_h0),_h7=function(_h8){return E(E(_h8).a);},_h9=function(_ha){return E(E(_ha).a);},_hb=function(_hc){return E(E(_hc).b);},_hd=function(_he){return E(E(_he).g);},_hf=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hg=0,_hh=3.3333333333333335,_hi=16.666666666666668,_hj=function(_hk){return E(E(_hk).b);},_hl=new T1(0,0),_hm=new T1(0,2),_hn=function(_ho){return E(E(_ho).i);},_hp=function(_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx){var _hy=new T(function(){var _hz=E(_hx);if(_hz<=31){return B(_4A(_h6,_hz,_hf));}else{if(_hz>=128){return B(_4A(_h6,_hz,_hf));}else{return true;}}}),_hA=new T(function(){if(E(_ht)==8){return new T2(0,new T(function(){return B(_fL(B(A2(_hn,_hr,_hv))))*28+20;}),new T(function(){return B(_fL(B(A2(_hn,_hs,_hw))))*20+8*(E(_hu)-1);}));}else{return new T2(0,new T(function(){return B(_fL(B(A2(_hn,_hr,_hv))))*28;}),new T(function(){return B(_fL(B(A2(_hn,_hs,_hw))))*20;}));}}),_hB=new T(function(){var _hC=B(_h7(_hq));if(!E(_hy)){return B(A2(_hd,B(_h9(_hC)),_hl));}else{return B(A3(_hb,_hC,new T(function(){return B(_hj(_hq));}),new T(function(){return B(A2(_hd,B(_h9(_hC)),_hm));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hA).a);}),new T(function(){return E(E(_hA).b);})),new T2(0,new T(function(){if(!E(_hy)){return E(_hg);}else{return E(_hh);}}),new T(function(){if(!E(_hy)){return E(_hg);}else{return E(_hi);}})),_hB);},_hD=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hE=function(_hF,_hG,_hH){var _hI=new T(function(){return toJSStr(E(_hH));});return function(_hJ,_){var _hK=__app4(E(_hD),E(_hJ),E(_hI),E(_hF),E(_hG));return new F(function(){return _gE(_);});};},_hL=0,_hM=",",_hN="rgba(",_hO=new T(function(){return toJSStr(_S);}),_hP="rgb(",_hQ=")",_hR=new T2(1,_hQ,_S),_hS=function(_hT){var _hU=E(_hT);if(!_hU._){var _hV=jsCat(new T2(1,_hP,new T2(1,new T(function(){return String(_hU.a);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.b);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.c);}),_hR)))))),E(_hO));return E(_hV);}else{var _hW=jsCat(new T2(1,_hN,new T2(1,new T(function(){return String(_hU.a);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.b);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.c);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.d);}),_hR)))))))),E(_hO));return E(_hW);}},_hX="strokeStyle",_hY="fillStyle",_hZ=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i0=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i1=function(_i2,_i3){var _i4=new T(function(){return B(_hS(_i2));});return function(_i5,_){var _i6=E(_i5),_i7=E(_hY),_i8=E(_hZ),_i9=__app2(_i8,_i6,_i7),_ia=E(_hX),_ib=__app2(_i8,_i6,_ia),_ic=E(_i4),_id=E(_i0),_ie=__app3(_id,_i6,_i7,_ic),_if=__app3(_id,_i6,_ia,_ic),_ig=B(A2(_i3,_i6,_)),_ih=String(_i9),_ii=__app3(_id,_i6,_i7,_ih),_ij=String(_ib),_ik=__app3(_id,_i6,_ia,_ij);return new F(function(){return _gE(_);});};},_il="font",_im=function(_in,_io){var _ip=new T(function(){return toJSStr(E(_in));});return function(_iq,_){var _ir=E(_iq),_is=E(_il),_it=__app2(E(_hZ),_ir,_is),_iu=E(_i0),_iv=__app3(_iu,_ir,_is,E(_ip)),_iw=B(A2(_io,_ir,_)),_ix=String(_it),_iy=__app3(_iu,_ir,_is,_ix);return new F(function(){return _gE(_);});};},_iz=new T(function(){return B(unCStr("px IPAGothic"));}),_iA=function(_iB,_iC,_iD,_iE,_iF,_iG,_iH,_){var _iI=new T(function(){var _iJ=new T(function(){var _iK=B(_hp(_gC,_bR,_bR,_iD,_iE,_iF,_iG,_iH)),_iL=E(_iK.a),_iM=E(_iK.b);return new T5(0,_iL.a,_iL.b,_iM.a,_iM.b,_iK.c);}),_iN=new T(function(){var _iO=E(_iJ);return E(_iO.a)+E(_iO.c);}),_iP=new T(function(){var _iQ=E(_iJ);return E(_iQ.b)-E(_iQ.d);}),_iR=new T(function(){return E(E(_iJ).e);}),_iS=new T(function(){return B(_hE(_hL,_hL,new T2(1,_iH,_S)));}),_iT=function(_iU,_){return new F(function(){return _gI(_iR,_iS,E(_iU),_);});};return B(_im(new T(function(){return B(_q(B(_A(0,E(_iD),_S)),_iz));},1),function(_iV,_){return new F(function(){return _gR(_iN,_iP,_iT,E(_iV),_);});}));});return new F(function(){return A(_i1,[_iC,_iI,_iB,_]);});},_iW=new T3(0,153,255,255),_iX=new T2(1,_iW,_S),_iY=new T3(0,255,153,204),_iZ=new T2(1,_iY,_iX),_j0=new T3(0,255,204,153),_j1=new T2(1,_j0,_iZ),_j2=new T3(0,200,255,200),_j3=new T2(1,_j2,_j1),_j4=20,_j5=64,_j6=1,_j7=2,_j8=8,_j9=function(_ja,_jb,_jc,_jd,_je,_jf,_jg,_){while(1){var _jh=B((function(_ji,_jj,_jk,_jl,_jm,_jn,_jo,_){var _jp=E(_jo);if(!_jp._){return _gD;}else{var _jq=_jp.b,_jr=E(_jp.a),_js=E(_jr);switch(_js){case 10:var _jt=_ji,_ju=_jj,_jv=_jl,_jw=_jl;_ja=_jt;_jb=_ju;_jc=0;_jd=_jv;_je=new T(function(){return E(_jm)-1|0;});_jf=_jw;_jg=_jq;return __continue;case 123:return new F(function(){return _jx(_ji,_jj,_jk,_jl,_jm,_jn,_jq,_);});break;case 65306:var _jy=new T(function(){return B(_6Q(_j3,_jk));}),_jz=function(_jA,_jB,_jC,_jD,_jE,_jF,_){while(1){var _jG=B((function(_jH,_jI,_jJ,_jK,_jL,_jM,_){var _jN=E(_jM);if(!_jN._){return _gD;}else{var _jO=_jN.b,_jP=E(_jN.a);if(E(_jP)==65306){var _jQ=new T(function(){var _jR=E(_jL);if((_jR+1)*20<=E(_jj)-10){return new T2(0,_jK,_jR+1|0);}else{return new T2(0,new T(function(){return E(_jK)-1|0;}),_jI);}});return new F(function(){return _j9(_jH,_jj,_jk,_jI,new T(function(){return E(E(_jQ).a);}),new T(function(){return E(E(_jQ).b);}),_jO,_);});}else{var _jS=E(_jH),_jT=B(_iA(_jS.a,_jy,_j8,_jJ,_jK,_jL,_jP,_)),_jU=_jI,_jV=_jJ+1,_jW=_jK,_jX=_jL;_jA=_jS;_jB=_jU;_jC=_jV;_jD=_jW;_jE=_jX;_jF=_jO;return __continue;}}})(_jA,_jB,_jC,_jD,_jE,_jF,_));if(_jG!=__continue){return _jG;}}};return new F(function(){return _jz(_ji,_jl,0,new T(function(){if(E(_jl)!=E(_jn)){return E(_jm);}else{return E(_jm)+1|0;}}),new T(function(){var _jY=E(_jn);if(E(_jl)!=_jY){return _jY-1|0;}else{var _jZ=(E(_jj)-10)/20,_k0=_jZ&4294967295;if(_jZ>=_k0){return _k0;}else{return _k0-1|0;}}}),_jq,_);});break;default:var _k1=function(_k2,_k3){var _k4=new T(function(){switch(E(_js)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return _jk;}}),_k5=new T(function(){var _k6=E(_jn);if((_k6+1)*20<=E(_jj)-10){return new T2(0,_jm,_k6+1|0);}else{return new T2(0,new T(function(){return E(_jm)-1|0;}),_jl);}});if(E(_k2)==64){return new F(function(){return _k7(_ji,_jj,_k4,_jl,new T(function(){return E(E(_k5).a);}),new T(function(){return E(E(_k5).b);}),_jq,_);});}else{var _k8=E(_ji),_k9=B(_iA(_k8.a,new T(function(){return B(_6Q(_j3,E(_k4)));},1),_j4,_hL,_jm,_jn,_k3,_));return new F(function(){return _k7(_k8,_jj,_k4,_jl,new T(function(){return E(E(_k5).a);}),new T(function(){return E(E(_k5).b);}),_jq,_);});}},_ka=E(_js);switch(_ka){case 42:return new F(function(){return _k1(64,_j5);});break;case 12289:return new F(function(){return _k1(64,_j5);});break;case 12290:return new F(function(){return _k1(64,_j5);});break;default:return new F(function(){return _k1(_ka,_jr);});}}}})(_ja,_jb,_jc,_jd,_je,_jf,_jg,_));if(_jh!=__continue){return _jh;}}},_k7=function(_kb,_kc,_kd,_ke,_kf,_kg,_kh,_){var _ki=E(_kh);if(!_ki._){return _gD;}else{var _kj=_ki.b,_kk=E(_ki.a),_kl=E(_kk);switch(_kl){case 10:return new F(function(){return _j9(_kb,_kc,0,_ke,new T(function(){return E(_kf)-1|0;}),_ke,_kj,_);});break;case 123:return new F(function(){return _jx(_kb,_kc,_kd,_ke,_kf,_kg,_kj,_);});break;case 65306:var _km=new T(function(){return B(_6Q(_j3,E(_kd)));}),_kn=function(_ko,_kp,_kq,_kr,_ks,_kt,_){while(1){var _ku=B((function(_kv,_kw,_kx,_ky,_kz,_kA,_){var _kB=E(_kA);if(!_kB._){return _gD;}else{var _kC=_kB.b,_kD=E(_kB.a);if(E(_kD)==65306){var _kE=new T(function(){var _kF=E(_kz);if((_kF+1)*20<=E(_kc)-10){return new T2(0,_ky,_kF+1|0);}else{return new T2(0,new T(function(){return E(_ky)-1|0;}),_kw);}});return new F(function(){return _k7(_kv,_kc,_kd,_kw,new T(function(){return E(E(_kE).a);}),new T(function(){return E(E(_kE).b);}),_kC,_);});}else{var _kG=E(_kv),_kH=B(_iA(_kG.a,_km,_j8,_kx,_ky,_kz,_kD,_)),_kI=_kw,_kJ=_kx+1,_kK=_ky,_kL=_kz;_ko=_kG;_kp=_kI;_kq=_kJ;_kr=_kK;_ks=_kL;_kt=_kC;return __continue;}}})(_ko,_kp,_kq,_kr,_ks,_kt,_));if(_ku!=__continue){return _ku;}}};return new F(function(){return _kn(_kb,_ke,0,new T(function(){if(E(_ke)!=E(_kg)){return E(_kf);}else{return E(_kf)+1|0;}}),new T(function(){var _kM=E(_kg);if(E(_ke)!=_kM){return _kM-1|0;}else{var _kN=(E(_kc)-10)/20,_kO=_kN&4294967295;if(_kN>=_kO){return _kO;}else{return _kO-1|0;}}}),_kj,_);});break;default:var _kP=function(_kQ,_kR){var _kS=new T(function(){switch(E(_kl)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return E(_kd);}}),_kT=new T(function(){var _kU=E(_kg);if((_kU+1)*20<=E(_kc)-10){return new T2(0,_kf,_kU+1|0);}else{return new T2(0,new T(function(){return E(_kf)-1|0;}),_ke);}});if(E(_kQ)==64){return new F(function(){return _k7(_kb,_kc,_kS,_ke,new T(function(){return E(E(_kT).a);}),new T(function(){return E(E(_kT).b);}),_kj,_);});}else{var _kV=E(_kb),_kW=B(_iA(_kV.a,new T(function(){return B(_6Q(_j3,E(_kS)));},1),_j4,_hL,_kf,_kg,_kR,_));return new F(function(){return _k7(_kV,_kc,_kS,_ke,new T(function(){return E(E(_kT).a);}),new T(function(){return E(E(_kT).b);}),_kj,_);});}},_kX=E(_kl);switch(_kX){case 42:return new F(function(){return _kP(64,_j5);});break;case 12289:return new F(function(){return _kP(64,_j5);});break;case 12290:return new F(function(){return _kP(64,_j5);});break;default:return new F(function(){return _kP(_kX,_kk);});}}}},_jx=function(_kY,_kZ,_l0,_l1,_l2,_l3,_l4,_){while(1){var _l5=B((function(_l6,_l7,_l8,_l9,_la,_lb,_lc,_){var _ld=E(_lc);if(!_ld._){return _gD;}else{var _le=_ld.b;if(E(_ld.a)==125){var _lf=new T(function(){var _lg=E(_lb);if((_lg+1)*20<=E(_l7)-10){return new T2(0,_la,_lg+1|0);}else{return new T2(0,new T(function(){return E(_la)-1|0;}),_l9);}});return new F(function(){return _k7(_l6,_l7,_l8,_l9,new T(function(){return E(E(_lf).a);}),new T(function(){return E(E(_lf).b);}),_le,_);});}else{var _lh=_l6,_li=_l7,_lj=_l8,_lk=_l9,_ll=_la,_lm=_lb;_kY=_lh;_kZ=_li;_l0=_lj;_l1=_lk;_l2=_ll;_l3=_lm;_l4=_le;return __continue;}}})(_kY,_kZ,_l0,_l1,_l2,_l3,_l4,_));if(_l5!=__continue){return _l5;}}},_ln=function(_lo,_lp,_lq,_lr,_ls,_lt,_lu,_lv,_){while(1){var _lw=B((function(_lx,_ly,_lz,_lA,_lB,_lC,_lD,_lE,_){var _lF=E(_lE);if(!_lF._){return _gD;}else{var _lG=_lF.b,_lH=E(_lF.a),_lI=E(_lH);switch(_lI){case 10:var _lJ=_lx,_lK=_ly,_lL=_lz,_lM=_lB,_lN=_lB;_lo=_lJ;_lp=_lK;_lq=_lL;_lr=0;_ls=_lM;_lt=new T(function(){return E(_lC)-1|0;});_lu=_lN;_lv=_lG;return __continue;case 123:return new F(function(){return _jx(new T2(0,_lx,_ly),_lz,_lA,_lB,_lC,_lD,_lG,_);});break;case 65306:var _lO=new T(function(){return B(_6Q(_j3,_lA));}),_lP=function(_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_){while(1){var _lX=B((function(_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_){var _m5=E(_m4);if(!_m5._){return _gD;}else{var _m6=_m5.b,_m7=E(_m5.a);if(E(_m7)==65306){var _m8=new T(function(){var _m9=E(_m3);if((_m9+1)*20<=E(_lz)-10){return new T2(0,_m2,_m9+1|0);}else{return new T2(0,new T(function(){return E(_m2)-1|0;}),_m0);}});return new F(function(){return _ln(_lY,_lZ,_lz,_lA,_m0,new T(function(){return E(E(_m8).a);}),new T(function(){return E(E(_m8).b);}),_m6,_);});}else{var _ma=B(_iA(_lY,_lO,_j8,_m1,_m2,_m3,_m7,_)),_mb=_lY,_mc=_lZ,_md=_m0,_me=_m1+1,_mf=_m2,_mg=_m3;_lQ=_mb;_lR=_mc;_lS=_md;_lT=_me;_lU=_mf;_lV=_mg;_lW=_m6;return __continue;}}})(_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_));if(_lX!=__continue){return _lX;}}};return new F(function(){return _lP(_lx,_ly,_lB,0,new T(function(){if(E(_lB)!=E(_lD)){return E(_lC);}else{return E(_lC)+1|0;}}),new T(function(){var _mh=E(_lD);if(E(_lB)!=_mh){return _mh-1|0;}else{var _mi=(E(_lz)-10)/20,_mj=_mi&4294967295;if(_mi>=_mj){return _mj;}else{return _mj-1|0;}}}),_lG,_);});break;default:var _mk=function(_ml,_mm){var _mn=new T(function(){switch(E(_lI)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return _lA;}}),_mo=new T(function(){var _mp=E(_lD);if((_mp+1)*20<=E(_lz)-10){return new T2(0,_lC,_mp+1|0);}else{return new T2(0,new T(function(){return E(_lC)-1|0;}),_lB);}});if(E(_ml)==64){return new F(function(){return _k7(new T2(0,_lx,_ly),_lz,_mn,_lB,new T(function(){return E(E(_mo).a);}),new T(function(){return E(E(_mo).b);}),_lG,_);});}else{var _mq=B(_iA(_lx,new T(function(){return B(_6Q(_j3,E(_mn)));},1),_j4,_hL,_lC,_lD,_mm,_));return new F(function(){return _k7(new T2(0,_lx,_ly),_lz,_mn,_lB,new T(function(){return E(E(_mo).a);}),new T(function(){return E(E(_mo).b);}),_lG,_);});}},_mr=E(_lI);switch(_mr){case 42:return new F(function(){return _mk(64,_j5);});break;case 12289:return new F(function(){return _mk(64,_j5);});break;case 12290:return new F(function(){return _mk(64,_j5);});break;default:return new F(function(){return _mk(_mr,_lH);});}}}})(_lo,_lp,_lq,_lr,_ls,_lt,_lu,_lv,_));if(_lw!=__continue){return _lw;}}},_ms=function(_mt,_mu){while(1){var _mv=E(_mt);if(!_mv._){return E(_mu);}else{var _mw=_mu+1|0;_mt=_mv.b;_mu=_mw;continue;}}},_mx=function(_my){return E(E(_my).a);},_mz=function(_mA,_mB){var _mC=E(_mB),_mD=new T(function(){var _mE=B(_h9(_mA)),_mF=B(_mz(_mA,B(A3(_mx,_mE,_mC,new T(function(){return B(A2(_hd,_mE,_aU));})))));return new T2(1,_mF.a,_mF.b);});return new T2(0,_mC,_mD);},_mG=new T(function(){var _mH=B(_mz(_ga,_hL));return new T2(1,_mH.a,_mH.b);}),_mI=new T(function(){return B(unCStr("px Courier"));}),_mJ=new T(function(){return B(_A(0,20,_S));}),_mK=new T(function(){return B(_q(_mJ,_mI));}),_mL=function(_mM,_){return _gD;},_mN=function(_mO,_mP,_mQ,_mR,_mS){var _mT=new T(function(){return E(_mQ)*16;}),_mU=new T(function(){return E(_mR)*20;}),_mV=function(_mW,_mX){var _mY=E(_mW);if(!_mY._){return E(_mL);}else{var _mZ=E(_mX);if(!_mZ._){return E(_mL);}else{var _n0=new T(function(){return B(_mV(_mY.b,_mZ.b));}),_n1=new T(function(){var _n2=new T(function(){var _n3=new T(function(){return B(_hE(new T(function(){return E(_mT)+16*E(_mZ.a);}),_mU,new T2(1,_mY.a,_S)));});return B(_im(_mK,_n3));});return B(_i1(_mP,_n2));});return function(_n4,_){var _n5=B(A2(_n1,_n4,_));return new F(function(){return A2(_n0,_n4,_);});};}}};return new F(function(){return A3(_mV,_mS,_mG,_mO);});},_n6=45,_n7=new T(function(){return B(unCStr("-"));}),_n8=new T2(1,_n6,_n7),_n9=function(_na){var _nb=E(_na);return (_nb==1)?E(_n8):new T2(1,_n6,new T(function(){return B(_n9(_nb-1|0));}));},_nc=new T(function(){return B(unCStr(": empty list"));}),_nd=function(_ne){return new F(function(){return err(B(_q(_6F,new T(function(){return B(_q(_ne,_nc));},1))));});},_nf=new T(function(){return B(unCStr("head"));}),_ng=new T(function(){return B(_nd(_nf));}),_nh=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ni=new T(function(){return B(_hE(_hL,_hL,_S));}),_nj=32,_nk=new T(function(){return B(unCStr("|"));}),_nl=function(_nm){var _nn=E(_nm);return (_nn._==0)?E(_nk):new T2(1,new T(function(){var _no=E(_nn.a);switch(E(_no.b)){case 7:return E(_nj);break;case 8:return E(_nj);break;default:return E(_no.a);}}),new T(function(){return B(_nl(_nn.b));}));},_np=function(_nq,_nr,_ns,_nt,_nu,_){var _nv=__app1(E(_nh),_nr),_nw=B(A2(_ni,_nq,_)),_nx=B(unAppCStr("-",new T(function(){var _ny=E(_nu);if(!_ny._){return E(_ng);}else{var _nz=B(_ms(_ny.a,0));if(0>=_nz){return E(_n7);}else{return B(_n9(_nz));}}}))),_nA=B(A(_mN,[_nq,_j2,_ns,_nt,_nx,_])),_nB=function(_nC,_nD,_nE,_){while(1){var _nF=B((function(_nG,_nH,_nI,_){var _nJ=E(_nI);if(!_nJ._){return new F(function(){return A(_mN,[_nq,_j2,_nG,_nH,_nx,_]);});}else{var _nK=B(A(_mN,[_nq,_j2,_nG,_nH,B(unAppCStr("|",new T(function(){return B(_nl(_nJ.a));}))),_])),_nL=_nG;_nC=_nL;_nD=new T(function(){return E(_nH)+1|0;});_nE=_nJ.b;return __continue;}})(_nC,_nD,_nE,_));if(_nF!=__continue){return _nF;}}};return new F(function(){return _nB(_ns,new T(function(){return E(_nt)+1|0;}),_nu,_);});},_nM=new T(function(){return B(_6Q(_j3,1));}),_nN=new T(function(){return B(_6Q(_j3,2));}),_nO=2,_nP=function(_nQ,_nR,_nS,_nT,_){var _nU=__app1(E(_nh),_nR),_nV=B(A2(_ni,_nQ,_)),_nW=E(_nT),_nX=E(_nW.b).a,_nY=E(_nW.a),_nZ=_nY.a;if(!E(E(_nW.t).h)){return _gD;}else{var _o0=B(_np(_nQ,_nR,new T(function(){return E(_nS)-E(_nX)|0;}),_nO,_nY.b,_));return new F(function(){return A(_mN,[_nQ,new T(function(){if(E(_nY.e)==32){return E(_nM);}else{return E(_nN);}}),new T(function(){return ((E(E(_nZ).a)+1|0)+E(_nS)|0)-E(_nX)|0;},1),new T(function(){return (E(E(_nZ).b)+2|0)+1|0;},1),new T2(1,_nY.d,_S),_]);});}},_o1=function(_o2){return E(E(_o2).a);},_o3=function(_o4){return E(E(_o4).a);},_o5=function(_o6,_o7){while(1){var _o8=E(_o6);if(!_o8._){return E(_o7);}else{_o6=_o8.b;_o7=_o8.a;continue;}}},_o9=function(_oa,_ob,_oc){return new F(function(){return _o5(_ob,_oa);});},_od=new T1(0,2),_oe=function(_of,_og){while(1){var _oh=E(_of);if(!_oh._){var _oi=_oh.a,_oj=E(_og);if(!_oj._){var _ok=_oj.a;if(!(imul(_oi,_ok)|0)){return new T1(0,imul(_oi,_ok)|0);}else{_of=new T1(1,I_fromInt(_oi));_og=new T1(1,I_fromInt(_ok));continue;}}else{_of=new T1(1,I_fromInt(_oi));_og=_oj;continue;}}else{var _ol=E(_og);if(!_ol._){_of=_oh;_og=new T1(1,I_fromInt(_ol.a));continue;}else{return new T1(1,I_mul(_oh.a,_ol.a));}}}},_om=function(_on,_oo,_op){while(1){if(!(_oo%2)){var _oq=B(_oe(_on,_on)),_or=quot(_oo,2);_on=_oq;_oo=_or;continue;}else{var _os=E(_oo);if(_os==1){return new F(function(){return _oe(_on,_op);});}else{var _oq=B(_oe(_on,_on)),_ot=B(_oe(_on,_op));_on=_oq;_oo=quot(_os-1|0,2);_op=_ot;continue;}}}},_ou=function(_ov,_ow){while(1){if(!(_ow%2)){var _ox=B(_oe(_ov,_ov)),_oy=quot(_ow,2);_ov=_ox;_ow=_oy;continue;}else{var _oz=E(_ow);if(_oz==1){return E(_ov);}else{return new F(function(){return _om(B(_oe(_ov,_ov)),quot(_oz-1|0,2),_ov);});}}}},_oA=function(_oB){return E(E(_oB).c);},_oC=function(_oD){return E(E(_oD).a);},_oE=function(_oF){return E(E(_oF).b);},_oG=function(_oH){return E(E(_oH).b);},_oI=function(_oJ){return E(E(_oJ).c);},_oK=new T1(0,0),_oL=new T1(0,2),_oM=function(_oN){return E(E(_oN).d);},_oO=function(_oP,_oQ){var _oR=B(_o1(_oP)),_oS=new T(function(){return B(_o3(_oR));}),_oT=new T(function(){return B(A3(_oM,_oP,_oQ,new T(function(){return B(A2(_hd,_oS,_oL));})));});return new F(function(){return A3(_4y,B(_oC(B(_oE(_oR)))),_oT,new T(function(){return B(A2(_hd,_oS,_oK));}));});},_oU=new T(function(){return B(unCStr("Negative exponent"));}),_oV=new T(function(){return B(err(_oU));}),_oW=function(_oX){return E(E(_oX).c);},_oY=function(_oZ,_p0,_p1,_p2){var _p3=B(_o1(_p0)),_p4=new T(function(){return B(_o3(_p3));}),_p5=B(_oE(_p3));if(!B(A3(_oI,_p5,_p2,new T(function(){return B(A2(_hd,_p4,_oK));})))){if(!B(A3(_4y,B(_oC(_p5)),_p2,new T(function(){return B(A2(_hd,_p4,_oK));})))){var _p6=new T(function(){return B(A2(_hd,_p4,_oL));}),_p7=new T(function(){return B(A2(_hd,_p4,_aU));}),_p8=B(_oC(_p5)),_p9=function(_pa,_pb,_pc){while(1){var _pd=B((function(_pe,_pf,_pg){if(!B(_oO(_p0,_pf))){if(!B(A3(_4y,_p8,_pf,_p7))){var _ph=new T(function(){return B(A3(_oW,_p0,new T(function(){return B(A3(_oG,_p4,_pf,_p7));}),_p6));});_pa=new T(function(){return B(A3(_oA,_oZ,_pe,_pe));});_pb=_ph;_pc=new T(function(){return B(A3(_oA,_oZ,_pe,_pg));});return __continue;}else{return new F(function(){return A3(_oA,_oZ,_pe,_pg);});}}else{var _pi=_pg;_pa=new T(function(){return B(A3(_oA,_oZ,_pe,_pe));});_pb=new T(function(){return B(A3(_oW,_p0,_pf,_p6));});_pc=_pi;return __continue;}})(_pa,_pb,_pc));if(_pd!=__continue){return _pd;}}},_pj=function(_pk,_pl){while(1){var _pm=B((function(_pn,_po){if(!B(_oO(_p0,_po))){if(!B(A3(_4y,_p8,_po,_p7))){var _pp=new T(function(){return B(A3(_oW,_p0,new T(function(){return B(A3(_oG,_p4,_po,_p7));}),_p6));});return new F(function(){return _p9(new T(function(){return B(A3(_oA,_oZ,_pn,_pn));}),_pp,_pn);});}else{return E(_pn);}}else{_pk=new T(function(){return B(A3(_oA,_oZ,_pn,_pn));});_pl=new T(function(){return B(A3(_oW,_p0,_po,_p6));});return __continue;}})(_pk,_pl));if(_pm!=__continue){return _pm;}}};return new F(function(){return _pj(_p1,_p2);});}else{return new F(function(){return A2(_hd,_oZ,_aU);});}}else{return E(_oV);}},_pq=new T(function(){return B(err(_oU));}),_pr=function(_ps){var _pt=I_decodeDouble(_ps);return new T2(0,new T1(1,_pt.b),_pt.a);},_pu=function(_pv,_pw){var _px=B(_pr(_pw)),_py=_px.a,_pz=_px.b,_pA=new T(function(){return B(_o3(new T(function(){return B(_o1(_pv));})));});if(_pz<0){var _pB= -_pz;if(_pB>=0){var _pC=E(_pB);if(!_pC){var _pD=E(_aU);}else{var _pD=B(_ou(_od,_pC));}if(!B(_cm(_pD,_cM))){var _pE=B(_cD(_py,_pD));return new T2(0,new T(function(){return B(A2(_hd,_pA,_pE.a));}),new T(function(){return B(_ci(_pE.b,_pz));}));}else{return E(_9T);}}else{return E(_pq);}}else{var _pF=new T(function(){var _pG=new T(function(){return B(_oY(_pA,_bR,new T(function(){return B(A2(_hd,_pA,_od));}),_pz));});return B(A3(_oA,_pA,new T(function(){return B(A2(_hd,_pA,_py));}),_pG));});return new T2(0,_pF,_fz);}},_pH=function(_pI,_pJ){while(1){var _pK=E(_pJ);if(!_pK._){return __Z;}else{var _pL=_pK.b,_pM=E(_pI);if(_pM==1){return E(_pL);}else{_pI=_pM-1|0;_pJ=_pL;continue;}}}},_pN=function(_pO,_pP){var _pQ=E(_pP);if(!_pQ._){return __Z;}else{var _pR=_pQ.a,_pS=E(_pO);return (_pS==1)?new T2(1,_pR,_S):new T2(1,_pR,new T(function(){return B(_pN(_pS-1|0,_pQ.b));}));}},_pT=function(_pU,_pV,_pW,_pX){while(1){if(B(_6Q(new T2(1,_pW,_pX),_pV))!=_pU){var _pY=_pV+1|0;_pV=_pY;continue;}else{if(0>=_pV){return __Z;}else{return new F(function(){return _pN(_pV,new T2(1,_pW,_pX));});}}}},_pZ=function(_q0,_q1,_q2){var _q3=E(_q2);if(!_q3._){return __Z;}else{var _q4=E(_q0);if(B(_6Q(_q3,_q1))!=_q4){return new F(function(){return _pT(_q4,_q1+1|0,_q3.a,_q3.b);});}else{if(0>=_q1){return __Z;}else{return new F(function(){return _pN(_q1,_q3);});}}}},_q5=function(_q6,_q7,_q8){var _q9=_q7+1|0;if(_q9>0){return new F(function(){return _pH(_q9,B(_pZ(_q6,_q9,_q8)));});}else{return new F(function(){return _pZ(_q6,_q9,_q8);});}},_qa=function(_qb,_qc){return (!B(_68(_qb,_qc)))?true:false;},_qd=new T2(0,_68,_qa),_qe=new T(function(){return B(_e6("Event.hs:(65,1)-(66,68)|function addEvent"));}),_qf=0,_qg=function(_qh,_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC){while(1){var _qD=E(_qh);if(!_qD._){return {_:0,a:_qi,b:_qj,c:_qk,d:_ql,e:_qm,f:_qn,g:_qo,h:_qp,i:_qq,j:_qr,k:_qs,l:_qt,m:_qu,n:_qv,o:_qw,p:_qx,q:_qy,r:_qz,s:_qA,t:_qB,u:_qC};}else{var _qE=E(_qD.b);if(!_qE._){return E(_qe);}else{var _qF=new T2(1,new T2(0,_qD.a,_qE.a),_qm),_qG=new T2(1,_qf,_qn);_qh=_qE.b;_qm=_qF;_qn=_qG;continue;}}}},_qH=function(_qI,_qJ,_qK){var _qL=E(_qK);if(!_qL._){return __Z;}else{var _qM=_qL.a,_qN=_qL.b;return (!B(A2(_qI,_qJ,_qM)))?new T2(1,_qM,new T(function(){return B(_qH(_qI,_qJ,_qN));})):E(_qN);}},_qO=function(_qP,_qQ){while(1){var _qR=E(_qP);if(!_qR._){return (E(_qQ)._==0)?true:false;}else{var _qS=E(_qQ);if(!_qS._){return false;}else{if(E(_qR.a)!=E(_qS.a)){return false;}else{_qP=_qR.b;_qQ=_qS.b;continue;}}}}},_qT=function(_qU,_qV){while(1){var _qW=E(_qU);if(!_qW._){return (E(_qV)._==0)?true:false;}else{var _qX=E(_qV);if(!_qX._){return false;}else{if(!B(_68(_qW.a,_qX.a))){return false;}else{_qU=_qW.b;_qV=_qX.b;continue;}}}}},_qY=function(_qZ,_r0){switch(E(_qZ)){case 0:return (E(_r0)==0)?true:false;case 1:return (E(_r0)==1)?true:false;case 2:return (E(_r0)==2)?true:false;case 3:return (E(_r0)==3)?true:false;case 4:return (E(_r0)==4)?true:false;case 5:return (E(_r0)==5)?true:false;case 6:return (E(_r0)==6)?true:false;case 7:return (E(_r0)==7)?true:false;default:return (E(_r0)==8)?true:false;}},_r1=function(_r2,_r3,_r4,_r5){if(_r2!=_r4){return false;}else{return new F(function(){return _qY(_r3,_r5);});}},_r6=function(_r7,_r8){var _r9=E(_r7),_ra=E(_r8);return new F(function(){return _r1(E(_r9.a),_r9.b,E(_ra.a),_ra.b);});},_rb=function(_rc,_rd,_re,_rf){if(_rc!=_re){return true;}else{switch(E(_rd)){case 0:return (E(_rf)==0)?false:true;case 1:return (E(_rf)==1)?false:true;case 2:return (E(_rf)==2)?false:true;case 3:return (E(_rf)==3)?false:true;case 4:return (E(_rf)==4)?false:true;case 5:return (E(_rf)==5)?false:true;case 6:return (E(_rf)==6)?false:true;case 7:return (E(_rf)==7)?false:true;default:return (E(_rf)==8)?false:true;}}},_rg=function(_rh,_ri){var _rj=E(_rh),_rk=E(_ri);return new F(function(){return _rb(E(_rj.a),_rj.b,E(_rk.a),_rk.b);});},_rl=new T2(0,_r6,_rg),_rm=0,_rn=function(_ro,_rp){var _rq=E(_rp);if(!_rq._){return 0;}else{var _rr=_rq.b,_rs=E(_ro),_rt=E(_rq.a),_ru=_rt.b;if(E(_rs.a)!=E(_rt.a)){return 1+B(_rn(_rs,_rr))|0;}else{switch(E(_rs.b)){case 0:return (E(_ru)==0)?0:1+B(_rn(_rs,_rr))|0;case 1:return (E(_ru)==1)?0:1+B(_rn(_rs,_rr))|0;case 2:return (E(_ru)==2)?0:1+B(_rn(_rs,_rr))|0;case 3:return (E(_ru)==3)?0:1+B(_rn(_rs,_rr))|0;case 4:return (E(_ru)==4)?0:1+B(_rn(_rs,_rr))|0;case 5:return (E(_ru)==5)?0:1+B(_rn(_rs,_rr))|0;case 6:return (E(_ru)==6)?0:1+B(_rn(_rs,_rr))|0;case 7:return (E(_ru)==7)?0:1+B(_rn(_rs,_rr))|0;default:return (E(_ru)==8)?0:1+B(_rn(_rs,_rr))|0;}}}},_rv=function(_rw,_rx){return new F(function(){return _rn(_rw,_rx);});},_ry=function(_rz,_rA){var _rB=E(_rA);if(!_rB._){return new T2(0,_rm,_rm);}else{var _rC=_rB.a,_rD=_rB.b;return (!B(_4A(_rl,_rz,_rC)))?new T2(0,new T(function(){return E(B(_ry(_rz,_rD)).a);}),new T(function(){return 1+E(B(_ry(_rz,_rD)).b)|0;})):new T2(0,new T(function(){return B(_rv(_rz,_rC));}),_rm);}},_rE=function(_rF,_rG){while(1){var _rH=E(_rG);if(!_rH._){return __Z;}else{var _rI=_rH.b,_rJ=E(_rF);if(_rJ==1){return E(_rI);}else{_rF=_rJ-1|0;_rG=_rI;continue;}}}},_rK=new T(function(){return B(unCStr("getch"));}),_rL=new T(function(){return B(unCStr("=="));}),_rM=new T(function(){return B(unCStr("&&"));}),_rN=new T(function(){return B(unCStr("||"));}),_rO=new T(function(){return B(unCStr("getpos"));}),_rP=new T(function(){return B(unCStr("ch"));}),_rQ=new T(function(){return B(unCStr("tp"));}),_rR=new T2(1,_rQ,_S),_rS=new T2(1,_rP,_rR),_rT=new T2(0,_rO,_rS),_rU=new T(function(){return B(unCStr("a"));}),_rV=new T(function(){return B(unCStr("b"));}),_rW=new T2(1,_rV,_S),_rX=new T2(1,_rU,_rW),_rY=new T2(0,_rL,_rX),_rZ=new T2(0,_rM,_rX),_s0=new T2(0,_rN,_rX),_s1=new T2(1,_s0,_S),_s2=new T2(1,_rZ,_s1),_s3=new T2(1,_rY,_s2),_s4=new T2(1,_rT,_s3),_s5=new T(function(){return B(unCStr("p"));}),_s6=new T(function(){return B(unCStr("q"));}),_s7=new T2(1,_s6,_S),_s8=new T2(1,_s5,_s7),_s9=new T2(0,_rK,_s8),_sa=new T2(1,_s9,_s4),_sb=new T(function(){return B(unCStr("foldr1"));}),_sc=new T(function(){return B(_nd(_sb));}),_sd=function(_se,_sf){var _sg=E(_sf);if(!_sg._){return E(_sc);}else{var _sh=_sg.a,_si=E(_sg.b);if(!_si._){return E(_sh);}else{return new F(function(){return A2(_se,_sh,new T(function(){return B(_sd(_se,_si));}));});}}},_sj=function(_sk){return E(E(_sk).a);},_sl=function(_sm,_sn,_so){while(1){var _sp=E(_so);if(!_sp._){return __Z;}else{var _sq=E(_sp.a);if(!B(A3(_4y,_sm,_sn,_sq.a))){_so=_sp.b;continue;}else{return new T1(1,_sq.b);}}}},_sr=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_ss=new T(function(){return B(err(_sr));}),_st=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_su=new T(function(){return B(err(_st));}),_sv=new T(function(){return B(unCStr("T"));}),_sw=new T(function(){return B(unCStr("F"));}),_sx=new T(function(){return B(_e6("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sy=function(_sz,_sA){while(1){var _sB=B((function(_sC,_sD){var _sE=E(_sC);switch(_sE._){case 0:var _sF=E(_sD);if(!_sF._){return __Z;}else{_sz=B(A1(_sE.a,_sF.a));_sA=_sF.b;return __continue;}break;case 1:var _sG=B(A1(_sE.a,_sD)),_sH=_sD;_sz=_sG;_sA=_sH;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sE.a,_sD),new T(function(){return B(_sy(_sE.b,_sD));}));default:return E(_sE.a);}})(_sz,_sA));if(_sB!=__continue){return _sB;}}},_sI=function(_sJ,_sK){var _sL=function(_sM){var _sN=E(_sK);if(_sN._==3){return new T2(3,_sN.a,new T(function(){return B(_sI(_sJ,_sN.b));}));}else{var _sO=E(_sJ);if(_sO._==2){return E(_sN);}else{var _sP=E(_sN);if(_sP._==2){return E(_sO);}else{var _sQ=function(_sR){var _sS=E(_sP);if(_sS._==4){var _sT=function(_sU){return new T1(4,new T(function(){return B(_q(B(_sy(_sO,_sU)),_sS.a));}));};return new T1(1,_sT);}else{var _sV=E(_sO);if(_sV._==1){var _sW=_sV.a,_sX=E(_sS);if(!_sX._){return new T1(1,function(_sY){return new F(function(){return _sI(B(A1(_sW,_sY)),_sX);});});}else{var _sZ=function(_t0){return new F(function(){return _sI(B(A1(_sW,_t0)),new T(function(){return B(A1(_sX.a,_t0));}));});};return new T1(1,_sZ);}}else{var _t1=E(_sS);if(!_t1._){return E(_sx);}else{var _t2=function(_t3){return new F(function(){return _sI(_sV,new T(function(){return B(A1(_t1.a,_t3));}));});};return new T1(1,_t2);}}}},_t4=E(_sO);switch(_t4._){case 1:var _t5=E(_sP);if(_t5._==4){var _t6=function(_t7){return new T1(4,new T(function(){return B(_q(B(_sy(B(A1(_t4.a,_t7)),_t7)),_t5.a));}));};return new T1(1,_t6);}else{return new F(function(){return _sQ(_);});}break;case 4:var _t8=_t4.a,_t9=E(_sP);switch(_t9._){case 0:var _ta=function(_tb){var _tc=new T(function(){return B(_q(_t8,new T(function(){return B(_sy(_t9,_tb));},1)));});return new T1(4,_tc);};return new T1(1,_ta);case 1:var _td=function(_te){var _tf=new T(function(){return B(_q(_t8,new T(function(){return B(_sy(B(A1(_t9.a,_te)),_te));},1)));});return new T1(4,_tf);};return new T1(1,_td);default:return new T1(4,new T(function(){return B(_q(_t8,_t9.a));}));}break;default:return new F(function(){return _sQ(_);});}}}}},_tg=E(_sJ);switch(_tg._){case 0:var _th=E(_sK);if(!_th._){var _ti=function(_tj){return new F(function(){return _sI(B(A1(_tg.a,_tj)),new T(function(){return B(A1(_th.a,_tj));}));});};return new T1(0,_ti);}else{return new F(function(){return _sL(_);});}break;case 3:return new T2(3,_tg.a,new T(function(){return B(_sI(_tg.b,_sK));}));default:return new F(function(){return _sL(_);});}},_tk=new T(function(){return B(unCStr("("));}),_tl=new T(function(){return B(unCStr(")"));}),_tm=function(_tn,_to){var _tp=E(_tn);switch(_tp._){case 0:return new T1(0,function(_tq){return new F(function(){return _tm(B(A1(_tp.a,_tq)),_to);});});case 1:return new T1(1,function(_tr){return new F(function(){return _tm(B(A1(_tp.a,_tr)),_to);});});case 2:return new T0(2);case 3:return new F(function(){return _sI(B(A1(_to,_tp.a)),new T(function(){return B(_tm(_tp.b,_to));}));});break;default:var _ts=function(_tt){var _tu=E(_tt);if(!_tu._){return __Z;}else{var _tv=E(_tu.a);return new F(function(){return _q(B(_sy(B(A1(_to,_tv.a)),_tv.b)),new T(function(){return B(_ts(_tu.b));},1));});}},_tw=B(_ts(_tp.a));return (_tw._==0)?new T0(2):new T1(4,_tw);}},_tx=new T0(2),_ty=function(_tz){return new T2(3,_tz,_tx);},_tA=function(_tB,_tC){var _tD=E(_tB);if(!_tD){return new F(function(){return A1(_tC,_gD);});}else{var _tE=new T(function(){return B(_tA(_tD-1|0,_tC));});return new T1(0,function(_tF){return E(_tE);});}},_tG=function(_tH,_tI,_tJ){var _tK=new T(function(){return B(A1(_tH,_ty));}),_tL=function(_tM,_tN,_tO,_tP){while(1){var _tQ=B((function(_tR,_tS,_tT,_tU){var _tV=E(_tR);switch(_tV._){case 0:var _tW=E(_tS);if(!_tW._){return new F(function(){return A1(_tI,_tU);});}else{var _tX=_tT+1|0,_tY=_tU;_tM=B(A1(_tV.a,_tW.a));_tN=_tW.b;_tO=_tX;_tP=_tY;return __continue;}break;case 1:var _tZ=B(A1(_tV.a,_tS)),_u0=_tS,_tX=_tT,_tY=_tU;_tM=_tZ;_tN=_u0;_tO=_tX;_tP=_tY;return __continue;case 2:return new F(function(){return A1(_tI,_tU);});break;case 3:var _u1=new T(function(){return B(_tm(_tV,_tU));});return new F(function(){return _tA(_tT,function(_u2){return E(_u1);});});break;default:return new F(function(){return _tm(_tV,_tU);});}})(_tM,_tN,_tO,_tP));if(_tQ!=__continue){return _tQ;}}};return function(_u3){return new F(function(){return _tL(_tK,_u3,0,_tJ);});};},_u4=function(_u5){return new F(function(){return A1(_u5,_S);});},_u6=function(_u7,_u8){var _u9=function(_ua){var _ub=E(_ua);if(!_ub._){return E(_u4);}else{var _uc=_ub.a;if(!B(A1(_u7,_uc))){return E(_u4);}else{var _ud=new T(function(){return B(_u9(_ub.b));}),_ue=function(_uf){var _ug=new T(function(){return B(A1(_ud,function(_uh){return new F(function(){return A1(_uf,new T2(1,_uc,_uh));});}));});return new T1(0,function(_ui){return E(_ug);});};return E(_ue);}}};return function(_uj){return new F(function(){return A2(_u9,_uj,_u8);});};},_uk=new T0(6),_ul=new T(function(){return B(unCStr("valDig: Bad base"));}),_um=new T(function(){return B(err(_ul));}),_un=function(_uo,_up){var _uq=function(_ur,_us){var _ut=E(_ur);if(!_ut._){var _uu=new T(function(){return B(A1(_us,_S));});return function(_uv){return new F(function(){return A1(_uv,_uu);});};}else{var _uw=E(_ut.a),_ux=function(_uy){var _uz=new T(function(){return B(_uq(_ut.b,function(_uA){return new F(function(){return A1(_us,new T2(1,_uy,_uA));});}));}),_uB=function(_uC){var _uD=new T(function(){return B(A1(_uz,_uC));});return new T1(0,function(_uE){return E(_uD);});};return E(_uB);};switch(E(_uo)){case 8:if(48>_uw){var _uF=new T(function(){return B(A1(_us,_S));});return function(_uG){return new F(function(){return A1(_uG,_uF);});};}else{if(_uw>55){var _uH=new T(function(){return B(A1(_us,_S));});return function(_uI){return new F(function(){return A1(_uI,_uH);});};}else{return new F(function(){return _ux(_uw-48|0);});}}break;case 10:if(48>_uw){var _uJ=new T(function(){return B(A1(_us,_S));});return function(_uK){return new F(function(){return A1(_uK,_uJ);});};}else{if(_uw>57){var _uL=new T(function(){return B(A1(_us,_S));});return function(_uM){return new F(function(){return A1(_uM,_uL);});};}else{return new F(function(){return _ux(_uw-48|0);});}}break;case 16:if(48>_uw){if(97>_uw){if(65>_uw){var _uN=new T(function(){return B(A1(_us,_S));});return function(_uO){return new F(function(){return A1(_uO,_uN);});};}else{if(_uw>70){var _uP=new T(function(){return B(A1(_us,_S));});return function(_uQ){return new F(function(){return A1(_uQ,_uP);});};}else{return new F(function(){return _ux((_uw-65|0)+10|0);});}}}else{if(_uw>102){if(65>_uw){var _uR=new T(function(){return B(A1(_us,_S));});return function(_uS){return new F(function(){return A1(_uS,_uR);});};}else{if(_uw>70){var _uT=new T(function(){return B(A1(_us,_S));});return function(_uU){return new F(function(){return A1(_uU,_uT);});};}else{return new F(function(){return _ux((_uw-65|0)+10|0);});}}}else{return new F(function(){return _ux((_uw-97|0)+10|0);});}}}else{if(_uw>57){if(97>_uw){if(65>_uw){var _uV=new T(function(){return B(A1(_us,_S));});return function(_uW){return new F(function(){return A1(_uW,_uV);});};}else{if(_uw>70){var _uX=new T(function(){return B(A1(_us,_S));});return function(_uY){return new F(function(){return A1(_uY,_uX);});};}else{return new F(function(){return _ux((_uw-65|0)+10|0);});}}}else{if(_uw>102){if(65>_uw){var _uZ=new T(function(){return B(A1(_us,_S));});return function(_v0){return new F(function(){return A1(_v0,_uZ);});};}else{if(_uw>70){var _v1=new T(function(){return B(A1(_us,_S));});return function(_v2){return new F(function(){return A1(_v2,_v1);});};}else{return new F(function(){return _ux((_uw-65|0)+10|0);});}}}else{return new F(function(){return _ux((_uw-97|0)+10|0);});}}}else{return new F(function(){return _ux(_uw-48|0);});}}break;default:return E(_um);}}},_v3=function(_v4){var _v5=E(_v4);if(!_v5._){return new T0(2);}else{return new F(function(){return A1(_up,_v5);});}};return function(_v6){return new F(function(){return A3(_uq,_v6,_5U,_v3);});};},_v7=16,_v8=8,_v9=function(_va){var _vb=function(_vc){return new F(function(){return A1(_va,new T1(5,new T2(0,_v8,_vc)));});},_vd=function(_ve){return new F(function(){return A1(_va,new T1(5,new T2(0,_v7,_ve)));});},_vf=function(_vg){switch(E(_vg)){case 79:return new T1(1,B(_un(_v8,_vb)));case 88:return new T1(1,B(_un(_v7,_vd)));case 111:return new T1(1,B(_un(_v8,_vb)));case 120:return new T1(1,B(_un(_v7,_vd)));default:return new T0(2);}};return function(_vh){return (E(_vh)==48)?E(new T1(0,_vf)):new T0(2);};},_vi=function(_vj){return new T1(0,B(_v9(_vj)));},_vk=function(_vl){return new F(function(){return A1(_vl,_2N);});},_vm=function(_vn){return new F(function(){return A1(_vn,_2N);});},_vo=10,_vp=new T1(0,10),_vq=function(_vr){return new F(function(){return _aQ(E(_vr));});},_vs=new T(function(){return B(unCStr("this should not happen"));}),_vt=new T(function(){return B(err(_vs));}),_vu=function(_vv,_vw){var _vx=E(_vw);if(!_vx._){return __Z;}else{var _vy=E(_vx.b);return (_vy._==0)?E(_vt):new T2(1,B(_cu(B(_oe(_vx.a,_vv)),_vy.a)),new T(function(){return B(_vu(_vv,_vy.b));}));}},_vz=new T1(0,0),_vA=function(_vB,_vC,_vD){while(1){var _vE=B((function(_vF,_vG,_vH){var _vI=E(_vH);if(!_vI._){return E(_vz);}else{if(!E(_vI.b)._){return E(_vI.a);}else{var _vJ=E(_vG);if(_vJ<=40){var _vK=function(_vL,_vM){while(1){var _vN=E(_vM);if(!_vN._){return E(_vL);}else{var _vO=B(_cu(B(_oe(_vL,_vF)),_vN.a));_vL=_vO;_vM=_vN.b;continue;}}};return new F(function(){return _vK(_vz,_vI);});}else{var _vP=B(_oe(_vF,_vF));if(!(_vJ%2)){var _vQ=B(_vu(_vF,_vI));_vB=_vP;_vC=quot(_vJ+1|0,2);_vD=_vQ;return __continue;}else{var _vQ=B(_vu(_vF,new T2(1,_vz,_vI)));_vB=_vP;_vC=quot(_vJ+1|0,2);_vD=_vQ;return __continue;}}}}})(_vB,_vC,_vD));if(_vE!=__continue){return _vE;}}},_vR=function(_vS,_vT){return new F(function(){return _vA(_vS,new T(function(){return B(_ms(_vT,0));},1),B(_6d(_vq,_vT)));});},_vU=function(_vV){var _vW=new T(function(){var _vX=new T(function(){var _vY=function(_vZ){return new F(function(){return A1(_vV,new T1(1,new T(function(){return B(_vR(_vp,_vZ));})));});};return new T1(1,B(_un(_vo,_vY)));}),_w0=function(_w1){if(E(_w1)==43){var _w2=function(_w3){return new F(function(){return A1(_vV,new T1(1,new T(function(){return B(_vR(_vp,_w3));})));});};return new T1(1,B(_un(_vo,_w2)));}else{return new T0(2);}},_w4=function(_w5){if(E(_w5)==45){var _w6=function(_w7){return new F(function(){return A1(_vV,new T1(1,new T(function(){return B(_fs(B(_vR(_vp,_w7))));})));});};return new T1(1,B(_un(_vo,_w6)));}else{return new T0(2);}};return B(_sI(B(_sI(new T1(0,_w4),new T1(0,_w0))),_vX));});return new F(function(){return _sI(new T1(0,function(_w8){return (E(_w8)==101)?E(_vW):new T0(2);}),new T1(0,function(_w9){return (E(_w9)==69)?E(_vW):new T0(2);}));});},_wa=function(_wb){var _wc=function(_wd){return new F(function(){return A1(_wb,new T1(1,_wd));});};return function(_we){return (E(_we)==46)?new T1(1,B(_un(_vo,_wc))):new T0(2);};},_wf=function(_wg){return new T1(0,B(_wa(_wg)));},_wh=function(_wi){var _wj=function(_wk){var _wl=function(_wm){return new T1(1,B(_tG(_vU,_vk,function(_wn){return new F(function(){return A1(_wi,new T1(5,new T3(1,_wk,_wm,_wn)));});})));};return new T1(1,B(_tG(_wf,_vm,_wl)));};return new F(function(){return _un(_vo,_wj);});},_wo=function(_wp){return new T1(1,B(_wh(_wp)));},_wq=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wr=function(_ws){return new F(function(){return _4A(_h6,_ws,_wq);});},_wt=false,_wu=true,_wv=function(_ww){var _wx=new T(function(){return B(A1(_ww,_v8));}),_wy=new T(function(){return B(A1(_ww,_v7));});return function(_wz){switch(E(_wz)){case 79:return E(_wx);case 88:return E(_wy);case 111:return E(_wx);case 120:return E(_wy);default:return new T0(2);}};},_wA=function(_wB){return new T1(0,B(_wv(_wB)));},_wC=function(_wD){return new F(function(){return A1(_wD,_vo);});},_wE=function(_wF){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_A(9,_wF,_S));}))));});},_wG=function(_wH){return new T0(2);},_wI=function(_wJ){var _wK=E(_wJ);if(!_wK._){return E(_wG);}else{var _wL=_wK.a,_wM=E(_wK.b);if(!_wM._){return E(_wL);}else{var _wN=new T(function(){return B(_wI(_wM));}),_wO=function(_wP){return new F(function(){return _sI(B(A1(_wL,_wP)),new T(function(){return B(A1(_wN,_wP));}));});};return E(_wO);}}},_wQ=function(_wR,_wS){var _wT=function(_wU,_wV,_wW){var _wX=E(_wU);if(!_wX._){return new F(function(){return A1(_wW,_wR);});}else{var _wY=E(_wV);if(!_wY._){return new T0(2);}else{if(E(_wX.a)!=E(_wY.a)){return new T0(2);}else{var _wZ=new T(function(){return B(_wT(_wX.b,_wY.b,_wW));});return new T1(0,function(_x0){return E(_wZ);});}}}};return function(_x1){return new F(function(){return _wT(_wR,_x1,_wS);});};},_x2=new T(function(){return B(unCStr("SO"));}),_x3=14,_x4=function(_x5){var _x6=new T(function(){return B(A1(_x5,_x3));});return new T1(1,B(_wQ(_x2,function(_x7){return E(_x6);})));},_x8=new T(function(){return B(unCStr("SOH"));}),_x9=1,_xa=function(_xb){var _xc=new T(function(){return B(A1(_xb,_x9));});return new T1(1,B(_wQ(_x8,function(_xd){return E(_xc);})));},_xe=function(_xf){return new T1(1,B(_tG(_xa,_x4,_xf)));},_xg=new T(function(){return B(unCStr("NUL"));}),_xh=0,_xi=function(_xj){var _xk=new T(function(){return B(A1(_xj,_xh));});return new T1(1,B(_wQ(_xg,function(_xl){return E(_xk);})));},_xm=new T(function(){return B(unCStr("STX"));}),_xn=2,_xo=function(_xp){var _xq=new T(function(){return B(A1(_xp,_xn));});return new T1(1,B(_wQ(_xm,function(_xr){return E(_xq);})));},_xs=new T(function(){return B(unCStr("ETX"));}),_xt=3,_xu=function(_xv){var _xw=new T(function(){return B(A1(_xv,_xt));});return new T1(1,B(_wQ(_xs,function(_xx){return E(_xw);})));},_xy=new T(function(){return B(unCStr("EOT"));}),_xz=4,_xA=function(_xB){var _xC=new T(function(){return B(A1(_xB,_xz));});return new T1(1,B(_wQ(_xy,function(_xD){return E(_xC);})));},_xE=new T(function(){return B(unCStr("ENQ"));}),_xF=5,_xG=function(_xH){var _xI=new T(function(){return B(A1(_xH,_xF));});return new T1(1,B(_wQ(_xE,function(_xJ){return E(_xI);})));},_xK=new T(function(){return B(unCStr("ACK"));}),_xL=6,_xM=function(_xN){var _xO=new T(function(){return B(A1(_xN,_xL));});return new T1(1,B(_wQ(_xK,function(_xP){return E(_xO);})));},_xQ=new T(function(){return B(unCStr("BEL"));}),_xR=7,_xS=function(_xT){var _xU=new T(function(){return B(A1(_xT,_xR));});return new T1(1,B(_wQ(_xQ,function(_xV){return E(_xU);})));},_xW=new T(function(){return B(unCStr("BS"));}),_xX=8,_xY=function(_xZ){var _y0=new T(function(){return B(A1(_xZ,_xX));});return new T1(1,B(_wQ(_xW,function(_y1){return E(_y0);})));},_y2=new T(function(){return B(unCStr("HT"));}),_y3=9,_y4=function(_y5){var _y6=new T(function(){return B(A1(_y5,_y3));});return new T1(1,B(_wQ(_y2,function(_y7){return E(_y6);})));},_y8=new T(function(){return B(unCStr("LF"));}),_y9=10,_ya=function(_yb){var _yc=new T(function(){return B(A1(_yb,_y9));});return new T1(1,B(_wQ(_y8,function(_yd){return E(_yc);})));},_ye=new T(function(){return B(unCStr("VT"));}),_yf=11,_yg=function(_yh){var _yi=new T(function(){return B(A1(_yh,_yf));});return new T1(1,B(_wQ(_ye,function(_yj){return E(_yi);})));},_yk=new T(function(){return B(unCStr("FF"));}),_yl=12,_ym=function(_yn){var _yo=new T(function(){return B(A1(_yn,_yl));});return new T1(1,B(_wQ(_yk,function(_yp){return E(_yo);})));},_yq=new T(function(){return B(unCStr("CR"));}),_yr=13,_ys=function(_yt){var _yu=new T(function(){return B(A1(_yt,_yr));});return new T1(1,B(_wQ(_yq,function(_yv){return E(_yu);})));},_yw=new T(function(){return B(unCStr("SI"));}),_yx=15,_yy=function(_yz){var _yA=new T(function(){return B(A1(_yz,_yx));});return new T1(1,B(_wQ(_yw,function(_yB){return E(_yA);})));},_yC=new T(function(){return B(unCStr("DLE"));}),_yD=16,_yE=function(_yF){var _yG=new T(function(){return B(A1(_yF,_yD));});return new T1(1,B(_wQ(_yC,function(_yH){return E(_yG);})));},_yI=new T(function(){return B(unCStr("DC1"));}),_yJ=17,_yK=function(_yL){var _yM=new T(function(){return B(A1(_yL,_yJ));});return new T1(1,B(_wQ(_yI,function(_yN){return E(_yM);})));},_yO=new T(function(){return B(unCStr("DC2"));}),_yP=18,_yQ=function(_yR){var _yS=new T(function(){return B(A1(_yR,_yP));});return new T1(1,B(_wQ(_yO,function(_yT){return E(_yS);})));},_yU=new T(function(){return B(unCStr("DC3"));}),_yV=19,_yW=function(_yX){var _yY=new T(function(){return B(A1(_yX,_yV));});return new T1(1,B(_wQ(_yU,function(_yZ){return E(_yY);})));},_z0=new T(function(){return B(unCStr("DC4"));}),_z1=20,_z2=function(_z3){var _z4=new T(function(){return B(A1(_z3,_z1));});return new T1(1,B(_wQ(_z0,function(_z5){return E(_z4);})));},_z6=new T(function(){return B(unCStr("NAK"));}),_z7=21,_z8=function(_z9){var _za=new T(function(){return B(A1(_z9,_z7));});return new T1(1,B(_wQ(_z6,function(_zb){return E(_za);})));},_zc=new T(function(){return B(unCStr("SYN"));}),_zd=22,_ze=function(_zf){var _zg=new T(function(){return B(A1(_zf,_zd));});return new T1(1,B(_wQ(_zc,function(_zh){return E(_zg);})));},_zi=new T(function(){return B(unCStr("ETB"));}),_zj=23,_zk=function(_zl){var _zm=new T(function(){return B(A1(_zl,_zj));});return new T1(1,B(_wQ(_zi,function(_zn){return E(_zm);})));},_zo=new T(function(){return B(unCStr("CAN"));}),_zp=24,_zq=function(_zr){var _zs=new T(function(){return B(A1(_zr,_zp));});return new T1(1,B(_wQ(_zo,function(_zt){return E(_zs);})));},_zu=new T(function(){return B(unCStr("EM"));}),_zv=25,_zw=function(_zx){var _zy=new T(function(){return B(A1(_zx,_zv));});return new T1(1,B(_wQ(_zu,function(_zz){return E(_zy);})));},_zA=new T(function(){return B(unCStr("SUB"));}),_zB=26,_zC=function(_zD){var _zE=new T(function(){return B(A1(_zD,_zB));});return new T1(1,B(_wQ(_zA,function(_zF){return E(_zE);})));},_zG=new T(function(){return B(unCStr("ESC"));}),_zH=27,_zI=function(_zJ){var _zK=new T(function(){return B(A1(_zJ,_zH));});return new T1(1,B(_wQ(_zG,function(_zL){return E(_zK);})));},_zM=new T(function(){return B(unCStr("FS"));}),_zN=28,_zO=function(_zP){var _zQ=new T(function(){return B(A1(_zP,_zN));});return new T1(1,B(_wQ(_zM,function(_zR){return E(_zQ);})));},_zS=new T(function(){return B(unCStr("GS"));}),_zT=29,_zU=function(_zV){var _zW=new T(function(){return B(A1(_zV,_zT));});return new T1(1,B(_wQ(_zS,function(_zX){return E(_zW);})));},_zY=new T(function(){return B(unCStr("RS"));}),_zZ=30,_A0=function(_A1){var _A2=new T(function(){return B(A1(_A1,_zZ));});return new T1(1,B(_wQ(_zY,function(_A3){return E(_A2);})));},_A4=new T(function(){return B(unCStr("US"));}),_A5=31,_A6=function(_A7){var _A8=new T(function(){return B(A1(_A7,_A5));});return new T1(1,B(_wQ(_A4,function(_A9){return E(_A8);})));},_Aa=new T(function(){return B(unCStr("SP"));}),_Ab=32,_Ac=function(_Ad){var _Ae=new T(function(){return B(A1(_Ad,_Ab));});return new T1(1,B(_wQ(_Aa,function(_Af){return E(_Ae);})));},_Ag=new T(function(){return B(unCStr("DEL"));}),_Ah=127,_Ai=function(_Aj){var _Ak=new T(function(){return B(A1(_Aj,_Ah));});return new T1(1,B(_wQ(_Ag,function(_Al){return E(_Ak);})));},_Am=new T2(1,_Ai,_S),_An=new T2(1,_Ac,_Am),_Ao=new T2(1,_A6,_An),_Ap=new T2(1,_A0,_Ao),_Aq=new T2(1,_zU,_Ap),_Ar=new T2(1,_zO,_Aq),_As=new T2(1,_zI,_Ar),_At=new T2(1,_zC,_As),_Au=new T2(1,_zw,_At),_Av=new T2(1,_zq,_Au),_Aw=new T2(1,_zk,_Av),_Ax=new T2(1,_ze,_Aw),_Ay=new T2(1,_z8,_Ax),_Az=new T2(1,_z2,_Ay),_AA=new T2(1,_yW,_Az),_AB=new T2(1,_yQ,_AA),_AC=new T2(1,_yK,_AB),_AD=new T2(1,_yE,_AC),_AE=new T2(1,_yy,_AD),_AF=new T2(1,_ys,_AE),_AG=new T2(1,_ym,_AF),_AH=new T2(1,_yg,_AG),_AI=new T2(1,_ya,_AH),_AJ=new T2(1,_y4,_AI),_AK=new T2(1,_xY,_AJ),_AL=new T2(1,_xS,_AK),_AM=new T2(1,_xM,_AL),_AN=new T2(1,_xG,_AM),_AO=new T2(1,_xA,_AN),_AP=new T2(1,_xu,_AO),_AQ=new T2(1,_xo,_AP),_AR=new T2(1,_xi,_AQ),_AS=new T2(1,_xe,_AR),_AT=new T(function(){return B(_wI(_AS));}),_AU=34,_AV=new T1(0,1114111),_AW=92,_AX=39,_AY=function(_AZ){var _B0=new T(function(){return B(A1(_AZ,_xR));}),_B1=new T(function(){return B(A1(_AZ,_xX));}),_B2=new T(function(){return B(A1(_AZ,_y3));}),_B3=new T(function(){return B(A1(_AZ,_y9));}),_B4=new T(function(){return B(A1(_AZ,_yf));}),_B5=new T(function(){return B(A1(_AZ,_yl));}),_B6=new T(function(){return B(A1(_AZ,_yr));}),_B7=new T(function(){return B(A1(_AZ,_AW));}),_B8=new T(function(){return B(A1(_AZ,_AX));}),_B9=new T(function(){return B(A1(_AZ,_AU));}),_Ba=new T(function(){var _Bb=function(_Bc){var _Bd=new T(function(){return B(_aQ(E(_Bc)));}),_Be=function(_Bf){var _Bg=B(_vR(_Bd,_Bf));if(!B(_ey(_Bg,_AV))){return new T0(2);}else{return new F(function(){return A1(_AZ,new T(function(){var _Bh=B(_b9(_Bg));if(_Bh>>>0>1114111){return B(_wE(_Bh));}else{return _Bh;}}));});}};return new T1(1,B(_un(_Bc,_Be)));},_Bi=new T(function(){var _Bj=new T(function(){return B(A1(_AZ,_A5));}),_Bk=new T(function(){return B(A1(_AZ,_zZ));}),_Bl=new T(function(){return B(A1(_AZ,_zT));}),_Bm=new T(function(){return B(A1(_AZ,_zN));}),_Bn=new T(function(){return B(A1(_AZ,_zH));}),_Bo=new T(function(){return B(A1(_AZ,_zB));}),_Bp=new T(function(){return B(A1(_AZ,_zv));}),_Bq=new T(function(){return B(A1(_AZ,_zp));}),_Br=new T(function(){return B(A1(_AZ,_zj));}),_Bs=new T(function(){return B(A1(_AZ,_zd));}),_Bt=new T(function(){return B(A1(_AZ,_z7));}),_Bu=new T(function(){return B(A1(_AZ,_z1));}),_Bv=new T(function(){return B(A1(_AZ,_yV));}),_Bw=new T(function(){return B(A1(_AZ,_yP));}),_Bx=new T(function(){return B(A1(_AZ,_yJ));}),_By=new T(function(){return B(A1(_AZ,_yD));}),_Bz=new T(function(){return B(A1(_AZ,_yx));}),_BA=new T(function(){return B(A1(_AZ,_x3));}),_BB=new T(function(){return B(A1(_AZ,_xL));}),_BC=new T(function(){return B(A1(_AZ,_xF));}),_BD=new T(function(){return B(A1(_AZ,_xz));}),_BE=new T(function(){return B(A1(_AZ,_xt));}),_BF=new T(function(){return B(A1(_AZ,_xn));}),_BG=new T(function(){return B(A1(_AZ,_x9));}),_BH=new T(function(){return B(A1(_AZ,_xh));}),_BI=function(_BJ){switch(E(_BJ)){case 64:return E(_BH);case 65:return E(_BG);case 66:return E(_BF);case 67:return E(_BE);case 68:return E(_BD);case 69:return E(_BC);case 70:return E(_BB);case 71:return E(_B0);case 72:return E(_B1);case 73:return E(_B2);case 74:return E(_B3);case 75:return E(_B4);case 76:return E(_B5);case 77:return E(_B6);case 78:return E(_BA);case 79:return E(_Bz);case 80:return E(_By);case 81:return E(_Bx);case 82:return E(_Bw);case 83:return E(_Bv);case 84:return E(_Bu);case 85:return E(_Bt);case 86:return E(_Bs);case 87:return E(_Br);case 88:return E(_Bq);case 89:return E(_Bp);case 90:return E(_Bo);case 91:return E(_Bn);case 92:return E(_Bm);case 93:return E(_Bl);case 94:return E(_Bk);case 95:return E(_Bj);default:return new T0(2);}};return B(_sI(new T1(0,function(_BK){return (E(_BK)==94)?E(new T1(0,_BI)):new T0(2);}),new T(function(){return B(A1(_AT,_AZ));})));});return B(_sI(new T1(1,B(_tG(_wA,_wC,_Bb))),_Bi));});return new F(function(){return _sI(new T1(0,function(_BL){switch(E(_BL)){case 34:return E(_B9);case 39:return E(_B8);case 92:return E(_B7);case 97:return E(_B0);case 98:return E(_B1);case 102:return E(_B5);case 110:return E(_B3);case 114:return E(_B6);case 116:return E(_B2);case 118:return E(_B4);default:return new T0(2);}}),_Ba);});},_BM=function(_BN){return new F(function(){return A1(_BN,_gD);});},_BO=function(_BP){var _BQ=E(_BP);if(!_BQ._){return E(_BM);}else{var _BR=E(_BQ.a),_BS=_BR>>>0,_BT=new T(function(){return B(_BO(_BQ.b));});if(_BS>887){var _BU=u_iswspace(_BR);if(!E(_BU)){return E(_BM);}else{var _BV=function(_BW){var _BX=new T(function(){return B(A1(_BT,_BW));});return new T1(0,function(_BY){return E(_BX);});};return E(_BV);}}else{var _BZ=E(_BS);if(_BZ==32){var _C0=function(_C1){var _C2=new T(function(){return B(A1(_BT,_C1));});return new T1(0,function(_C3){return E(_C2);});};return E(_C0);}else{if(_BZ-9>>>0>4){if(E(_BZ)==160){var _C4=function(_C5){var _C6=new T(function(){return B(A1(_BT,_C5));});return new T1(0,function(_C7){return E(_C6);});};return E(_C4);}else{return E(_BM);}}else{var _C8=function(_C9){var _Ca=new T(function(){return B(A1(_BT,_C9));});return new T1(0,function(_Cb){return E(_Ca);});};return E(_C8);}}}}},_Cc=function(_Cd){var _Ce=new T(function(){return B(_Cc(_Cd));}),_Cf=function(_Cg){return (E(_Cg)==92)?E(_Ce):new T0(2);},_Ch=function(_Ci){return E(new T1(0,_Cf));},_Cj=new T1(1,function(_Ck){return new F(function(){return A2(_BO,_Ck,_Ch);});}),_Cl=new T(function(){return B(_AY(function(_Cm){return new F(function(){return A1(_Cd,new T2(0,_Cm,_wu));});}));}),_Cn=function(_Co){var _Cp=E(_Co);if(_Cp==38){return E(_Ce);}else{var _Cq=_Cp>>>0;if(_Cq>887){var _Cr=u_iswspace(_Cp);return (E(_Cr)==0)?new T0(2):E(_Cj);}else{var _Cs=E(_Cq);return (_Cs==32)?E(_Cj):(_Cs-9>>>0>4)?(E(_Cs)==160)?E(_Cj):new T0(2):E(_Cj);}}};return new F(function(){return _sI(new T1(0,function(_Ct){return (E(_Ct)==92)?E(new T1(0,_Cn)):new T0(2);}),new T1(0,function(_Cu){var _Cv=E(_Cu);if(E(_Cv)==92){return E(_Cl);}else{return new F(function(){return A1(_Cd,new T2(0,_Cv,_wt));});}}));});},_Cw=function(_Cx,_Cy){var _Cz=new T(function(){return B(A1(_Cy,new T1(1,new T(function(){return B(A1(_Cx,_S));}))));}),_CA=function(_CB){var _CC=E(_CB),_CD=E(_CC.a);if(E(_CD)==34){if(!E(_CC.b)){return E(_Cz);}else{return new F(function(){return _Cw(function(_CE){return new F(function(){return A1(_Cx,new T2(1,_CD,_CE));});},_Cy);});}}else{return new F(function(){return _Cw(function(_CF){return new F(function(){return A1(_Cx,new T2(1,_CD,_CF));});},_Cy);});}};return new F(function(){return _Cc(_CA);});},_CG=new T(function(){return B(unCStr("_\'"));}),_CH=function(_CI){var _CJ=u_iswalnum(_CI);if(!E(_CJ)){return new F(function(){return _4A(_h6,_CI,_CG);});}else{return true;}},_CK=function(_CL){return new F(function(){return _CH(E(_CL));});},_CM=new T(function(){return B(unCStr(",;()[]{}`"));}),_CN=new T(function(){return B(unCStr("=>"));}),_CO=new T2(1,_CN,_S),_CP=new T(function(){return B(unCStr("~"));}),_CQ=new T2(1,_CP,_CO),_CR=new T(function(){return B(unCStr("@"));}),_CS=new T2(1,_CR,_CQ),_CT=new T(function(){return B(unCStr("->"));}),_CU=new T2(1,_CT,_CS),_CV=new T(function(){return B(unCStr("<-"));}),_CW=new T2(1,_CV,_CU),_CX=new T(function(){return B(unCStr("|"));}),_CY=new T2(1,_CX,_CW),_CZ=new T(function(){return B(unCStr("\\"));}),_D0=new T2(1,_CZ,_CY),_D1=new T(function(){return B(unCStr("="));}),_D2=new T2(1,_D1,_D0),_D3=new T(function(){return B(unCStr("::"));}),_D4=new T2(1,_D3,_D2),_D5=new T(function(){return B(unCStr(".."));}),_D6=new T2(1,_D5,_D4),_D7=function(_D8){var _D9=new T(function(){return B(A1(_D8,_uk));}),_Da=new T(function(){var _Db=new T(function(){var _Dc=function(_Dd){var _De=new T(function(){return B(A1(_D8,new T1(0,_Dd)));});return new T1(0,function(_Df){return (E(_Df)==39)?E(_De):new T0(2);});};return B(_AY(_Dc));}),_Dg=function(_Dh){var _Di=E(_Dh);switch(E(_Di)){case 39:return new T0(2);case 92:return E(_Db);default:var _Dj=new T(function(){return B(A1(_D8,new T1(0,_Di)));});return new T1(0,function(_Dk){return (E(_Dk)==39)?E(_Dj):new T0(2);});}},_Dl=new T(function(){var _Dm=new T(function(){return B(_Cw(_5U,_D8));}),_Dn=new T(function(){var _Do=new T(function(){var _Dp=new T(function(){var _Dq=function(_Dr){var _Ds=E(_Dr),_Dt=u_iswalpha(_Ds);return (E(_Dt)==0)?(E(_Ds)==95)?new T1(1,B(_u6(_CK,function(_Du){return new F(function(){return A1(_D8,new T1(3,new T2(1,_Ds,_Du)));});}))):new T0(2):new T1(1,B(_u6(_CK,function(_Dv){return new F(function(){return A1(_D8,new T1(3,new T2(1,_Ds,_Dv)));});})));};return B(_sI(new T1(0,_Dq),new T(function(){return new T1(1,B(_tG(_vi,_wo,_D8)));})));}),_Dw=function(_Dx){return (!B(_4A(_h6,_Dx,_wq)))?new T0(2):new T1(1,B(_u6(_wr,function(_Dy){var _Dz=new T2(1,_Dx,_Dy);if(!B(_4A(_qd,_Dz,_D6))){return new F(function(){return A1(_D8,new T1(4,_Dz));});}else{return new F(function(){return A1(_D8,new T1(2,_Dz));});}})));};return B(_sI(new T1(0,_Dw),_Dp));});return B(_sI(new T1(0,function(_DA){if(!B(_4A(_h6,_DA,_CM))){return new T0(2);}else{return new F(function(){return A1(_D8,new T1(2,new T2(1,_DA,_S)));});}}),_Do));});return B(_sI(new T1(0,function(_DB){return (E(_DB)==34)?E(_Dm):new T0(2);}),_Dn));});return B(_sI(new T1(0,function(_DC){return (E(_DC)==39)?E(new T1(0,_Dg)):new T0(2);}),_Dl));});return new F(function(){return _sI(new T1(1,function(_DD){return (E(_DD)._==0)?E(_D9):new T0(2);}),_Da);});},_DE=0,_DF=function(_DG,_DH){var _DI=new T(function(){var _DJ=new T(function(){var _DK=function(_DL){var _DM=new T(function(){var _DN=new T(function(){return B(A1(_DH,_DL));});return B(_D7(function(_DO){var _DP=E(_DO);return (_DP._==2)?(!B(_qO(_DP.a,_tl)))?new T0(2):E(_DN):new T0(2);}));}),_DQ=function(_DR){return E(_DM);};return new T1(1,function(_DS){return new F(function(){return A2(_BO,_DS,_DQ);});});};return B(A2(_DG,_DE,_DK));});return B(_D7(function(_DT){var _DU=E(_DT);return (_DU._==2)?(!B(_qO(_DU.a,_tk)))?new T0(2):E(_DJ):new T0(2);}));}),_DV=function(_DW){return E(_DI);};return function(_DX){return new F(function(){return A2(_BO,_DX,_DV);});};},_DY=function(_DZ,_E0){var _E1=function(_E2){var _E3=new T(function(){return B(A1(_DZ,_E2));}),_E4=function(_E5){return new F(function(){return _sI(B(A1(_E3,_E5)),new T(function(){return new T1(1,B(_DF(_E1,_E5)));}));});};return E(_E4);},_E6=new T(function(){return B(A1(_DZ,_E0));}),_E7=function(_E8){return new F(function(){return _sI(B(A1(_E6,_E8)),new T(function(){return new T1(1,B(_DF(_E1,_E8)));}));});};return E(_E7);},_E9=0,_Ea=function(_Eb,_Ec){return new F(function(){return A1(_Ec,_E9);});},_Ed=new T(function(){return B(unCStr("Fr"));}),_Ee=new T2(0,_Ed,_Ea),_Ef=1,_Eg=function(_Eh,_Ei){return new F(function(){return A1(_Ei,_Ef);});},_Ej=new T(function(){return B(unCStr("Bl"));}),_Ek=new T2(0,_Ej,_Eg),_El=2,_Em=function(_En,_Eo){return new F(function(){return A1(_Eo,_El);});},_Ep=new T(function(){return B(unCStr("Ex"));}),_Eq=new T2(0,_Ep,_Em),_Er=3,_Es=function(_Et,_Eu){return new F(function(){return A1(_Eu,_Er);});},_Ev=new T(function(){return B(unCStr("Mv"));}),_Ew=new T2(0,_Ev,_Es),_Ex=4,_Ey=function(_Ez,_EA){return new F(function(){return A1(_EA,_Ex);});},_EB=new T(function(){return B(unCStr("Pn"));}),_EC=new T2(0,_EB,_Ey),_ED=8,_EE=function(_EF,_EG){return new F(function(){return A1(_EG,_ED);});},_EH=new T(function(){return B(unCStr("DF"));}),_EI=new T2(0,_EH,_EE),_EJ=new T2(1,_EI,_S),_EK=7,_EL=function(_EM,_EN){return new F(function(){return A1(_EN,_EK);});},_EO=new T(function(){return B(unCStr("DB"));}),_EP=new T2(0,_EO,_EL),_EQ=new T2(1,_EP,_EJ),_ER=6,_ES=function(_ET,_EU){return new F(function(){return A1(_EU,_ER);});},_EV=new T(function(){return B(unCStr("Cm"));}),_EW=new T2(0,_EV,_ES),_EX=new T2(1,_EW,_EQ),_EY=5,_EZ=function(_F0,_F1){return new F(function(){return A1(_F1,_EY);});},_F2=new T(function(){return B(unCStr("Wn"));}),_F3=new T2(0,_F2,_EZ),_F4=new T2(1,_F3,_EX),_F5=new T2(1,_EC,_F4),_F6=new T2(1,_Ew,_F5),_F7=new T2(1,_Eq,_F6),_F8=new T2(1,_Ek,_F7),_F9=new T2(1,_Ee,_F8),_Fa=function(_Fb,_Fc,_Fd){var _Fe=E(_Fb);if(!_Fe._){return new T0(2);}else{var _Ff=E(_Fe.a),_Fg=_Ff.a,_Fh=new T(function(){return B(A2(_Ff.b,_Fc,_Fd));}),_Fi=new T(function(){return B(_D7(function(_Fj){var _Fk=E(_Fj);switch(_Fk._){case 3:return (!B(_qO(_Fg,_Fk.a)))?new T0(2):E(_Fh);case 4:return (!B(_qO(_Fg,_Fk.a)))?new T0(2):E(_Fh);default:return new T0(2);}}));}),_Fl=function(_Fm){return E(_Fi);};return new F(function(){return _sI(new T1(1,function(_Fn){return new F(function(){return A2(_BO,_Fn,_Fl);});}),new T(function(){return B(_Fa(_Fe.b,_Fc,_Fd));}));});}},_Fo=function(_Fp,_Fq){return new F(function(){return _Fa(_F9,_Fp,_Fq);});},_Fr=function(_Fs){var _Ft=function(_Fu){return E(new T2(3,_Fs,_tx));};return new T1(1,function(_Fv){return new F(function(){return A2(_BO,_Fv,_Ft);});});},_Fw=new T(function(){return B(A3(_DY,_Fo,_DE,_Fr));}),_Fx=new T(function(){return B(unCStr("empty"));}),_Fy=new T2(1,_Fx,_S),_Fz=new T(function(){return B(err(_sr));}),_FA=new T(function(){return B(err(_st));}),_FB=function(_FC,_FD){var _FE=function(_FF,_FG){var _FH=function(_FI){return new F(function(){return A1(_FG,new T(function(){return  -E(_FI);}));});},_FJ=new T(function(){return B(_D7(function(_FK){return new F(function(){return A3(_FC,_FK,_FF,_FH);});}));}),_FL=function(_FM){return E(_FJ);},_FN=function(_FO){return new F(function(){return A2(_BO,_FO,_FL);});},_FP=new T(function(){return B(_D7(function(_FQ){var _FR=E(_FQ);if(_FR._==4){var _FS=E(_FR.a);if(!_FS._){return new F(function(){return A3(_FC,_FR,_FF,_FG);});}else{if(E(_FS.a)==45){if(!E(_FS.b)._){return E(new T1(1,_FN));}else{return new F(function(){return A3(_FC,_FR,_FF,_FG);});}}else{return new F(function(){return A3(_FC,_FR,_FF,_FG);});}}}else{return new F(function(){return A3(_FC,_FR,_FF,_FG);});}}));}),_FT=function(_FU){return E(_FP);};return new T1(1,function(_FV){return new F(function(){return A2(_BO,_FV,_FT);});});};return new F(function(){return _DY(_FE,_FD);});},_FW=function(_FX){var _FY=E(_FX);if(!_FY._){var _FZ=_FY.b,_G0=new T(function(){return B(_vA(new T(function(){return B(_aQ(E(_FY.a)));}),new T(function(){return B(_ms(_FZ,0));},1),B(_6d(_vq,_FZ))));});return new T1(1,_G0);}else{return (E(_FY.b)._==0)?(E(_FY.c)._==0)?new T1(1,new T(function(){return B(_vR(_vp,_FY.a));})):__Z:__Z;}},_G1=function(_G2,_G3){return new T0(2);},_G4=function(_G5){var _G6=E(_G5);if(_G6._==5){var _G7=B(_FW(_G6.a));if(!_G7._){return E(_G1);}else{var _G8=new T(function(){return B(_b9(_G7.a));});return function(_G9,_Ga){return new F(function(){return A1(_Ga,_G8);});};}}else{return E(_G1);}},_Gb=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_Gc=new T2(1,_y,_S),_Gd=function(_Ge){while(1){var _Gf=B((function(_Gg){var _Gh=E(_Gg);if(!_Gh._){return __Z;}else{var _Gi=_Gh.b,_Gj=E(_Gh.a);if(!E(_Gj.b)._){return new T2(1,_Gj.a,new T(function(){return B(_Gd(_Gi));}));}else{_Ge=_Gi;return __continue;}}})(_Ge));if(_Gf!=__continue){return _Gf;}}},_Gk=function(_Gl,_Gm){while(1){var _Gn=E(_Gl);if(!_Gn._){return E(_Gm);}else{var _Go=new T2(1,_Gn.a,_Gm);_Gl=_Gn.b;_Gm=_Go;continue;}}},_Gp=function(_Gq,_Gr){var _Gs=E(_Gq);if(!_Gs._){return __Z;}else{var _Gt=E(_Gr);return (_Gt._==0)?__Z:new T2(1,new T2(0,_Gs.a,_Gt.a),new T(function(){return B(_Gp(_Gs.b,_Gt.b));}));}},_Gu=function(_Gv,_Gw,_Gx){while(1){var _Gy=B((function(_Gz,_GA,_GB){var _GC=E(_GB);if(!_GC._){return E(_GA);}else{var _GD=_GC.a,_GE=_GC.b,_GF=B(_sl(_qd,_GD,_sa));if(!_GF._){var _GG=E(_Fy);}else{var _GG=E(_GF.a);}if(!B(_qT(_GG,_Fy))){var _GH=B(_Gk(B(_Gp(B(_Gk(_GA,_S)),new T(function(){return B(_Gk(_GG,_S));},1))),_S)),_GI=B(_ms(_GH,0)),_GJ=new T(function(){var _GK=B(_6d(_sj,_GH));if(!_GK._){return __Z;}else{var _GL=_GK.a,_GM=E(_GK.b);if(!_GM._){return __Z;}else{var _GN=_GM.a;if(!E(_GM.b)._){if(!B(_qO(_GD,_rM))){if(!B(_qO(_GD,_rL))){if(!B(_qO(_GD,_rK))){if(!B(_qO(_GD,_rO))){if(!B(_qO(_GD,_rN))){return __Z;}else{if(!B(_qO(_GL,_sv))){if(!B(_qO(_GN,_sv))){return E(_sw);}else{return E(_sv);}}else{return E(_sv);}}}else{var _GO=B(_ry(new T2(0,new T(function(){var _GP=E(_GL);if(!_GP._){return E(_ng);}else{return E(_GP.a);}}),new T(function(){var _GQ=B(_Gd(B(_sy(_Fw,_GN))));if(!_GQ._){return E(_ss);}else{if(!E(_GQ.b)._){return E(_GQ.a);}else{return E(_su);}}})),E(E(_Gz).a).b)),_GR=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_GS){return new F(function(){return _A(0,E(_GO.a),_GS);});},new T2(1,function(_GT){return new F(function(){return _A(0,E(_GO.b),_GT);});},_S)),_Gc));});return new T2(1,_z,_GR);}}else{return new T2(1,new T(function(){var _GU=B(_Gd(B(_sy(_Gb,_GL))));if(!_GU._){return E(_Fz);}else{if(!E(_GU.b)._){var _GV=B(_Gd(B(_sy(_Gb,_GN))));if(!_GV._){return E(_Fz);}else{if(!E(_GV.b)._){return E(B(_6Q(B(_6Q(E(E(_Gz).a).b,E(_GV.a))),E(_GU.a))).a);}else{return E(_FA);}}}else{return E(_FA);}}}),_S);}}else{if(!B(_qO(_GL,_GN))){return E(_sw);}else{return E(_sv);}}}else{if(!B(_qO(_GL,_sv))){return E(_sw);}else{if(!B(_qO(_GN,_sv))){return E(_sw);}else{return E(_sv);}}}}else{return __Z;}}}});if(_GI>0){var _GW=_Gz,_GX=B(_q(B(_Gk(B(_rE(_GI,B(_Gk(_GA,_S)))),_S)),new T2(1,_GJ,_S)));_Gv=_GW;_Gw=_GX;_Gx=_GE;return __continue;}else{var _GW=_Gz,_GX=B(_q(B(_Gk(B(_Gk(_GA,_S)),_S)),new T2(1,_GJ,_S)));_Gv=_GW;_Gw=_GX;_Gx=_GE;return __continue;}}else{var _GW=_Gz,_GX=B(_q(_GA,new T2(1,_GD,_S)));_Gv=_GW;_Gw=_GX;_Gx=_GE;return __continue;}}})(_Gv,_Gw,_Gx));if(_Gy!=__continue){return _Gy;}}},_GY=new T(function(){return B(_e6("Event.hs:(86,1)-(90,73)|function addMemory"));}),_GZ=function(_H0,_H1){var _H2=E(_H0),_H3=E(_H1);if(!B(_qO(_H2.a,_H3.a))){return false;}else{return new F(function(){return _qO(_H2.b,_H3.b);});}},_H4=new T2(1,_S,_S),_H5=function(_H6,_H7,_H8){var _H9=E(_H8);if(!_H9._){return new T2(0,new T2(1,_H7,_S),_S);}else{var _Ha=E(_H7),_Hb=new T(function(){var _Hc=B(_H5(_H6,_H9.a,_H9.b));return new T2(0,_Hc.a,_Hc.b);});return (_H6!=_Ha)?new T2(0,new T2(1,_Ha,new T(function(){return E(E(_Hb).a);})),new T(function(){return E(E(_Hb).b);})):new T2(0,_S,new T2(1,new T(function(){return E(E(_Hb).a);}),new T(function(){return E(E(_Hb).b);})));}},_Hd=32,_He=function(_Hf){var _Hg=E(_Hf);if(!_Hg._){return __Z;}else{var _Hh=new T(function(){return B(_q(_Hg.a,new T(function(){return B(_He(_Hg.b));},1)));});return new T2(1,_Hd,_Hh);}},_Hi=function(_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE){while(1){var _HF=B((function(_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_HQ,_HR,_HS,_HT,_HU,_HV,_HW,_HX,_HY,_HZ,_I0,_I1){var _I2=E(_HG);if(!_I2._){return {_:0,a:_HH,b:_HI,c:_HJ,d:_HK,e:_HL,f:_HM,g:_HN,h:_HO,i:_HP,j:_HQ,k:_HR,l:_HS,m:_HT,n:_HU,o:_HV,p:_HW,q:_HX,r:_HY,s:_HZ,t:_I0,u:_I1};}else{var _I3=_I2.a,_I4=E(_I2.b);if(!_I4._){return E(_GY);}else{var _I5=new T(function(){var _I6=E(_I4.a);if(!_I6._){var _I7=B(_Gu({_:0,a:E(_HH),b:E(_HI),c:E(_HJ),d:E(_HK),e:E(_HL),f:E(_HM),g:E(_HN),h:E(_HO),i:_HP,j:_HQ,k:_HR,l:_HS,m:E(_HT),n:_HU,o:E(_HV),p:E(_HW),q:_HX,r:E(_HY),s:_HZ,t:E(_I0),u:E(_I1)},_S,_H4));if(!_I7._){return __Z;}else{return B(_q(_I7.a,new T(function(){return B(_He(_I7.b));},1)));}}else{var _I8=_I6.a,_I9=E(_I6.b);if(!_I9._){var _Ia=B(_Gu({_:0,a:E(_HH),b:E(_HI),c:E(_HJ),d:E(_HK),e:E(_HL),f:E(_HM),g:E(_HN),h:E(_HO),i:_HP,j:_HQ,k:_HR,l:_HS,m:E(_HT),n:_HU,o:E(_HV),p:E(_HW),q:_HX,r:E(_HY),s:_HZ,t:E(_I0),u:E(_I1)},_S,new T2(1,new T2(1,_I8,_S),_S)));if(!_Ia._){return __Z;}else{return B(_q(_Ia.a,new T(function(){return B(_He(_Ia.b));},1)));}}else{var _Ib=E(_I8),_Ic=new T(function(){var _Id=B(_H5(95,_I9.a,_I9.b));return new T2(0,_Id.a,_Id.b);});if(E(_Ib)==95){var _Ie=B(_Gu({_:0,a:E(_HH),b:E(_HI),c:E(_HJ),d:E(_HK),e:E(_HL),f:E(_HM),g:E(_HN),h:E(_HO),i:_HP,j:_HQ,k:_HR,l:_HS,m:E(_HT),n:_HU,o:E(_HV),p:E(_HW),q:_HX,r:E(_HY),s:_HZ,t:E(_I0),u:E(_I1)},_S,new T2(1,_S,new T2(1,new T(function(){return E(E(_Ic).a);}),new T(function(){return E(E(_Ic).b);})))));if(!_Ie._){return __Z;}else{return B(_q(_Ie.a,new T(function(){return B(_He(_Ie.b));},1)));}}else{var _If=B(_Gu({_:0,a:E(_HH),b:E(_HI),c:E(_HJ),d:E(_HK),e:E(_HL),f:E(_HM),g:E(_HN),h:E(_HO),i:_HP,j:_HQ,k:_HR,l:_HS,m:E(_HT),n:_HU,o:E(_HV),p:E(_HW),q:_HX,r:E(_HY),s:_HZ,t:E(_I0),u:E(_I1)},_S,new T2(1,new T2(1,_Ib,new T(function(){return E(E(_Ic).a);})),new T(function(){return E(E(_Ic).b);}))));if(!_If._){return __Z;}else{return B(_q(_If.a,new T(function(){return B(_He(_If.b));},1)));}}}}}),_Ig=_HH,_Ih=_HI,_Ii=_HJ,_Ij=_HK,_Ik=_HL,_Il=_HM,_Im=_HO,_In=_HP,_Io=_HQ,_Ip=_HR,_Iq=_HS,_Ir=_HT,_Is=_HU,_It=_HV,_Iu=_HW,_Iv=_HX,_Iw=_HY,_Ix=_HZ,_Iy=_I0,_Iz=_I1;_Hj=_I4.b;_Hk=_Ig;_Hl=_Ih;_Hm=_Ii;_Hn=_Ij;_Ho=_Ik;_Hp=_Il;_Hq=new T2(1,new T2(0,_I3,_I5),new T(function(){var _IA=B(_sl(_qd,_I3,_HN));if(!_IA._){var _IB=__Z;}else{var _IB=E(_IA.a);}if(!B(_qO(_IB,_S))){return B(_qH(_GZ,new T2(0,_I3,_IB),_HN));}else{return E(_HN);}}));_Hr=_Im;_Hs=_In;_Ht=_Io;_Hu=_Ip;_Hv=_Iq;_Hw=_Ir;_Hx=_Is;_Hy=_It;_Hz=_Iu;_HA=_Iv;_HB=_Iw;_HC=_Ix;_HD=_Iy;_HE=_Iz;return __continue;}}})(_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE));if(_HF!=__continue){return _HF;}}},_IC=function(_ID){var _IE=E(_ID);if(!_IE._){return new T2(0,_S,_S);}else{var _IF=E(_IE.a),_IG=new T(function(){var _IH=B(_IC(_IE.b));return new T2(0,_IH.a,_IH.b);});return new T2(0,new T2(1,_IF.a,new T(function(){return E(E(_IG).a);})),new T2(1,_IF.b,new T(function(){return E(E(_IG).b);})));}},_II=function(_IJ,_IK,_IL){while(1){var _IM=B((function(_IN,_IO,_IP){var _IQ=E(_IP);if(!_IQ._){return __Z;}else{var _IR=_IQ.b;if(_IO!=E(_IQ.a)){var _IS=_IN+1|0,_IT=_IO;_IJ=_IS;_IK=_IT;_IL=_IR;return __continue;}else{return new T2(1,_IN,new T(function(){return B(_II(_IN+1|0,_IO,_IR));}));}}})(_IJ,_IK,_IL));if(_IM!=__continue){return _IM;}}},_IU=function(_IV,_IW,_IX){var _IY=E(_IX);if(!_IY._){return __Z;}else{var _IZ=_IY.b,_J0=E(_IW);if(_J0!=E(_IY.a)){return new F(function(){return _II(_IV+1|0,_J0,_IZ);});}else{return new T2(1,_IV,new T(function(){return B(_II(_IV+1|0,_J0,_IZ));}));}}},_J1=function(_J2,_J3,_J4,_J5){var _J6=E(_J5);if(!_J6._){return __Z;}else{var _J7=_J6.b;return (!B(_4A(_3L,_J2,_J4)))?new T2(1,_J6.a,new T(function(){return B(_J1(_J2+1|0,_J3,_J4,_J7));})):new T2(1,_J3,new T(function(){return B(_J1(_J2+1|0,_J3,_J4,_J7));}));}},_J8=function(_J9,_Ja,_Jb){var _Jc=E(_Jb);if(!_Jc._){return __Z;}else{var _Jd=new T(function(){var _Je=B(_IC(_Jc.a)),_Jf=_Je.a,_Jg=new T(function(){return B(_J1(0,_Ja,new T(function(){return B(_IU(0,_J9,_Jf));}),_Je.b));},1);return B(_Gp(_Jf,_Jg));});return new T2(1,_Jd,new T(function(){return B(_J8(_J9,_Ja,_Jc.b));}));}},_Jh=function(_Ji){var _Jj=E(_Ji);return (_Jj._==0)?E(_ng):E(_Jj.a);},_Jk=new T(function(){return B(_e6("Event.hs:(59,1)-(62,93)|function changeType"));}),_Jl=new T(function(){return B(_e6("Event.hs:56:16-116|case"));}),_Jm=new T(function(){return B(unCStr("Wn"));}),_Jn=new T(function(){return B(unCStr("Pn"));}),_Jo=new T(function(){return B(unCStr("Mv"));}),_Jp=new T(function(){return B(unCStr("Fr"));}),_Jq=new T(function(){return B(unCStr("Ex"));}),_Jr=new T(function(){return B(unCStr("DF"));}),_Js=new T(function(){return B(unCStr("DB"));}),_Jt=new T(function(){return B(unCStr("Cm"));}),_Ju=new T(function(){return B(unCStr("Bl"));}),_Jv=function(_Jw){return (!B(_qO(_Jw,_Ju)))?(!B(_qO(_Jw,_Jt)))?(!B(_qO(_Jw,_Js)))?(!B(_qO(_Jw,_Jr)))?(!B(_qO(_Jw,_Jq)))?(!B(_qO(_Jw,_Jp)))?(!B(_qO(_Jw,_Jo)))?(!B(_qO(_Jw,_Jn)))?(!B(_qO(_Jw,_Jm)))?E(_Jl):5:4:3:0:2:8:7:6:1;},_Jx=function(_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT){while(1){var _JU=B((function(_JV,_JW,_JX,_JY,_JZ,_K0,_K1,_K2,_K3,_K4,_K5,_K6,_K7,_K8,_K9,_Ka,_Kb,_Kc,_Kd,_Ke,_Kf,_Kg){var _Kh=E(_JV);if(!_Kh._){return {_:0,a:_JW,b:_JX,c:_JY,d:_JZ,e:_K0,f:_K1,g:_K2,h:_K3,i:_K4,j:_K5,k:_K6,l:_K7,m:_K8,n:_K9,o:_Ka,p:_Kb,q:_Kc,r:_Kd,s:_Ke,t:_Kf,u:_Kg};}else{var _Ki=E(_Kh.b);if(!_Ki._){return E(_Jk);}else{var _Kj=E(_JW),_Kk=_JX,_Kl=_JY,_Km=_JZ,_Kn=_K0,_Ko=_K1,_Kp=_K2,_Kq=_K3,_Kr=_K4,_Ks=_K5,_Kt=_K6,_Ku=_K7,_Kv=_K8,_Kw=_K9,_Kx=_Ka,_Ky=_Kb,_Kz=_Kc,_KA=_Kd,_KB=_Ke,_KC=_Kf,_KD=_Kg;_Jy=_Ki.b;_Jz={_:0,a:E(_Kj.a),b:E(B(_J8(new T(function(){return B(_Jh(_Kh.a));}),new T(function(){return B(_Jv(_Ki.a));}),_Kj.b))),c:E(_Kj.c),d:_Kj.d,e:_Kj.e,f:_Kj.f,g:E(_Kj.g),h:_Kj.h,i:E(_Kj.i),j:E(_Kj.j),k:E(_Kj.k)};_JA=_Kk;_JB=_Kl;_JC=_Km;_JD=_Kn;_JE=_Ko;_JF=_Kp;_JG=_Kq;_JH=_Kr;_JI=_Ks;_JJ=_Kt;_JK=_Ku;_JL=_Kv;_JM=_Kw;_JN=_Kx;_JO=_Ky;_JP=_Kz;_JQ=_KA;_JR=_KB;_JS=_KC;_JT=_KD;return __continue;}}})(_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT));if(_JU!=__continue){return _JU;}}},_KE=function(_KF,_KG){while(1){var _KH=E(_KG);if(!_KH._){return __Z;}else{var _KI=_KH.b,_KJ=E(_KF);if(_KJ==1){return E(_KI);}else{_KF=_KJ-1|0;_KG=_KI;continue;}}}},_KK=function(_KL,_KM){while(1){var _KN=E(_KM);if(!_KN._){return __Z;}else{var _KO=_KN.b,_KP=E(_KL);if(_KP==1){return E(_KO);}else{_KL=_KP-1|0;_KM=_KO;continue;}}}},_KQ=function(_KR,_KS,_KT,_KU,_KV){var _KW=new T(function(){var _KX=E(_KR),_KY=new T(function(){return B(_6Q(_KV,_KS));}),_KZ=new T2(1,new T2(0,_KT,_KU),new T(function(){var _L0=_KX+1|0;if(_L0>0){return B(_KK(_L0,_KY));}else{return E(_KY);}}));if(0>=_KX){return E(_KZ);}else{var _L1=function(_L2,_L3){var _L4=E(_L2);if(!_L4._){return E(_KZ);}else{var _L5=_L4.a,_L6=E(_L3);return (_L6==1)?new T2(1,_L5,_KZ):new T2(1,_L5,new T(function(){return B(_L1(_L4.b,_L6-1|0));}));}};return B(_L1(_KY,_KX));}}),_L7=new T2(1,_KW,new T(function(){var _L8=_KS+1|0;if(_L8>0){return B(_KE(_L8,_KV));}else{return E(_KV);}}));if(0>=_KS){return E(_L7);}else{var _L9=function(_La,_Lb){var _Lc=E(_La);if(!_Lc._){return E(_L7);}else{var _Ld=_Lc.a,_Le=E(_Lb);return (_Le==1)?new T2(1,_Ld,_L7):new T2(1,_Ld,new T(function(){return B(_L9(_Lc.b,_Le-1|0));}));}};return new F(function(){return _L9(_KV,_KS);});}},_Lf=32,_Lg=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Lh=function(_Li){return new F(function(){return _dI(new T1(0,new T(function(){return B(_dV(_Li,_Lg));})),_ds);});},_Lj=function(_Lk){return new F(function(){return _Lh("Event.hs:42:27-53|(x\' : y\' : _)");});},_Ll=new T(function(){return B(_Lj(_));}),_Lm=function(_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI){while(1){var _LJ=B((function(_LK,_LL,_LM,_LN,_LO,_LP,_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5){var _M6=E(_LK);if(!_M6._){return {_:0,a:_LL,b:_LM,c:_LN,d:_LO,e:_LP,f:_LQ,g:_LR,h:_LS,i:_LT,j:_LU,k:_LV,l:_LW,m:_LX,n:_LY,o:_LZ,p:_M0,q:_M1,r:_M2,s:_M3,t:_M4,u:_M5};}else{var _M7=E(_LL),_M8=new T(function(){var _M9=E(_M6.a);if(!_M9._){return E(_Ll);}else{var _Ma=E(_M9.b);if(!_Ma._){return E(_Ll);}else{var _Mb=_Ma.a,_Mc=_Ma.b,_Md=E(_M9.a);if(E(_Md)==44){return new T2(0,_S,new T(function(){return E(B(_H5(44,_Mb,_Mc)).a);}));}else{var _Me=B(_H5(44,_Mb,_Mc)),_Mf=E(_Me.b);if(!_Mf._){return E(_Ll);}else{return new T2(0,new T2(1,_Md,_Me.a),_Mf.a);}}}}}),_Mg=B(_Gd(B(_sy(_Gb,new T(function(){return E(E(_M8).b);})))));if(!_Mg._){return E(_Fz);}else{if(!E(_Mg.b)._){var _Mh=new T(function(){var _Mi=B(_Gd(B(_sy(_Gb,new T(function(){return E(E(_M8).a);})))));if(!_Mi._){return E(_Fz);}else{if(!E(_Mi.b)._){return E(_Mi.a);}else{return E(_FA);}}},1),_Mj=_LM,_Mk=_LN,_Ml=_LO,_Mm=_LP,_Mn=_LQ,_Mo=_LR,_Mp=_LS,_Mq=_LT,_Mr=_LU,_Ms=_LV,_Mt=_LW,_Mu=_LX,_Mv=_LY,_Mw=_LZ,_Mx=_M0,_My=_M1,_Mz=_M2,_MA=_M3,_MB=_M4,_MC=_M5;_Ln=_M6.b;_Lo={_:0,a:E(_M7.a),b:E(B(_KQ(_Mh,E(_Mg.a),_Lf,_E9,_M7.b))),c:E(_M7.c),d:_M7.d,e:_M7.e,f:_M7.f,g:E(_M7.g),h:_M7.h,i:E(_M7.i),j:E(_M7.j),k:E(_M7.k)};_Lp=_Mj;_Lq=_Mk;_Lr=_Ml;_Ls=_Mm;_Lt=_Mn;_Lu=_Mo;_Lv=_Mp;_Lw=_Mq;_Lx=_Mr;_Ly=_Ms;_Lz=_Mt;_LA=_Mu;_LB=_Mv;_LC=_Mw;_LD=_Mx;_LE=_My;_LF=_Mz;_LG=_MA;_LH=_MB;_LI=_MC;return __continue;}else{return E(_FA);}}}})(_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI));if(_LJ!=__continue){return _LJ;}}},_MD=function(_ME,_MF,_MG){var _MH=E(_MG);return (_MH._==0)?0:(!B(A3(_4y,_ME,_MF,_MH.a)))?1+B(_MD(_ME,_MF,_MH.b))|0:0;},_MI=function(_MJ,_MK){while(1){var _ML=E(_MK);if(!_ML._){return __Z;}else{var _MM=_ML.b,_MN=E(_MJ);if(_MN==1){return E(_MM);}else{_MJ=_MN-1|0;_MK=_MM;continue;}}}},_MO=function(_MP,_MQ){var _MR=new T(function(){var _MS=_MP+1|0;if(_MS>0){return B(_MI(_MS,_MQ));}else{return E(_MQ);}});if(0>=_MP){return E(_MR);}else{var _MT=function(_MU,_MV){var _MW=E(_MU);if(!_MW._){return E(_MR);}else{var _MX=_MW.a,_MY=E(_MV);return (_MY==1)?new T2(1,_MX,_MR):new T2(1,_MX,new T(function(){return B(_MT(_MW.b,_MY-1|0));}));}};return new F(function(){return _MT(_MQ,_MP);});}},_MZ=function(_N0,_N1){return new F(function(){return _MO(E(_N0),_N1);});},_N2= -1,_N3=function(_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np){while(1){var _Nq=B((function(_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM){var _NN=E(_Nr);if(!_NN._){return {_:0,a:_Ns,b:_Nt,c:_Nu,d:_Nv,e:_Nw,f:_Nx,g:_Ny,h:_Nz,i:_NA,j:_NB,k:_NC,l:_ND,m:_NE,n:_NF,o:_NG,p:_NH,q:_NI,r:_NJ,s:_NK,t:_NL,u:_NM};}else{var _NO=_NN.a,_NP=B(_6d(_sj,_Nw)),_NQ=B(_4A(_qd,_NO,_NP)),_NR=new T(function(){if(!E(_NQ)){return E(_N2);}else{return B(_MD(_qd,_NO,_NP));}});if(!E(_NQ)){var _NS=E(_Nw);}else{var _NS=B(_MZ(_NR,_Nw));}if(!E(_NQ)){var _NT=E(_Nx);}else{var _NT=B(_MZ(_NR,_Nx));}var _NU=_Ns,_NV=_Nt,_NW=_Nu,_NX=_Nv,_NY=_Ny,_NZ=_Nz,_O0=_NA,_O1=_NB,_O2=_NC,_O3=_ND,_O4=_NE,_O5=_NF,_O6=_NG,_O7=_NH,_O8=_NI,_O9=_NJ,_Oa=_NK,_Ob=_NL,_Oc=_NM;_N4=_NN.b;_N5=_NU;_N6=_NV;_N7=_NW;_N8=_NX;_N9=_NS;_Na=_NT;_Nb=_NY;_Nc=_NZ;_Nd=_O0;_Ne=_O1;_Nf=_O2;_Ng=_O3;_Nh=_O4;_Ni=_O5;_Nj=_O6;_Nk=_O7;_Nl=_O8;_Nm=_O9;_Nn=_Oa;_No=_Ob;_Np=_Oc;return __continue;}})(_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np));if(_Nq!=__continue){return _Nq;}}},_Od=function(_Oe){var _Of=E(_Oe);if(!_Of._){return new T2(0,_S,_S);}else{var _Og=E(_Of.a),_Oh=new T(function(){var _Oi=B(_Od(_Of.b));return new T2(0,_Oi.a,_Oi.b);});return new T2(0,new T2(1,_Og.a,new T(function(){return E(E(_Oh).a);})),new T2(1,_Og.b,new T(function(){return E(E(_Oh).b);})));}},_Oj=function(_Ok){return new F(function(){return _Lh("Event.hs:103:28-52|(c : d : _)");});},_Ol=new T(function(){return B(_Oj(_));}),_Om=function(_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP){while(1){var _OQ=B((function(_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY,_OZ,_P0,_P1,_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb,_Pc,_Pd,_Pe,_Pf,_Pg,_Ph,_Pi,_Pj){var _Pk=E(_OR);if(!_Pk._){return {_:0,a:E(_OS),b:E(_OT),c:E(_OU),d:E(_OV),e:E(_OW),f:E(_OX),g:E(_OY),h:E(_OZ),i:_P0,j:_P1,k:_P2,l:_P3,m:E(_P4),n:_P5,o:E(_P6),p:E(_P7),q:_P8,r:E(_P9),s:_Pa,t:E({_:0,a:E(_Pb),b:E(_Pc),c:E(_Pd),d:E(_wu),e:E(_Pf),f:E(_Pg),g:E(_wu),h:E(_Pi)}),u:E(_Pj)};}else{var _Pl=new T(function(){var _Pm=E(_Pk.a);if(!_Pm._){return E(_Ol);}else{var _Pn=E(_Pm.b);if(!_Pn._){return E(_Ol);}else{var _Po=_Pn.a,_Pp=_Pn.b,_Pq=E(_Pm.a);if(E(_Pq)==44){return new T2(0,_S,new T(function(){return E(B(_H5(44,_Po,_Pp)).a);}));}else{var _Pr=B(_H5(44,_Po,_Pp)),_Ps=E(_Pr.b);if(!_Ps._){return E(_Ol);}else{return new T2(0,new T2(1,_Pq,_Pr.a),_Ps.a);}}}}}),_Pt=_OS,_Pu=_OT,_Pv=_OU,_Pw=_OV,_Px=_OW,_Py=_OX,_Pz=_OY,_PA=_OZ,_PB=_P0,_PC=_P1,_PD=_P2,_PE=_P3,_PF=B(_q(_P4,new T2(1,new T2(0,new T(function(){return E(E(_Pl).a);}),new T(function(){return E(E(_Pl).b);})),_S))),_PG=_P5,_PH=_P6,_PI=_P7,_PJ=_P8,_PK=_P9,_PL=_Pa,_PM=_Pb,_PN=_Pc,_PO=_Pd,_PP=_Pe,_PQ=_Pf,_PR=_Pg,_PS=_Ph,_PT=_Pi,_PU=_Pj;_On=_Pk.b;_Oo=_Pt;_Op=_Pu;_Oq=_Pv;_Or=_Pw;_Os=_Px;_Ot=_Py;_Ou=_Pz;_Ov=_PA;_Ow=_PB;_Ox=_PC;_Oy=_PD;_Oz=_PE;_OA=_PF;_OB=_PG;_OC=_PH;_OD=_PI;_OE=_PJ;_OF=_PK;_OG=_PL;_OH=_PM;_OI=_PN;_OJ=_PO;_OK=_PP;_OL=_PQ;_OM=_PR;_ON=_PS;_OO=_PT;_OP=_PU;return __continue;}})(_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP));if(_OQ!=__continue){return _OQ;}}},_PV=function(_PW){return new F(function(){return _Lh("Event.hs:49:27-53|(x\' : y\' : _)");});},_PX=new T(function(){return B(_PV(_));}),_PY=function(_PZ){return new F(function(){return _Lh("Event.hs:50:27-55|(chs : tps : _)");});},_Q0=new T(function(){return B(_PY(_));}),_Q1=new T(function(){return B(_e6("Event.hs:(47,1)-(53,83)|function putCell"));}),_Q2=function(_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo){while(1){var _Qp=B((function(_Qq,_Qr,_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH,_QI,_QJ,_QK,_QL){var _QM=E(_Qq);if(!_QM._){return {_:0,a:_Qr,b:_Qs,c:_Qt,d:_Qu,e:_Qv,f:_Qw,g:_Qx,h:_Qy,i:_Qz,j:_QA,k:_QB,l:_QC,m:_QD,n:_QE,o:_QF,p:_QG,q:_QH,r:_QI,s:_QJ,t:_QK,u:_QL};}else{var _QN=E(_QM.b);if(!_QN._){return E(_Q1);}else{var _QO=E(_Qr),_QP=new T(function(){var _QQ=E(_QM.a);if(!_QQ._){return E(_PX);}else{var _QR=E(_QQ.b);if(!_QR._){return E(_PX);}else{var _QS=_QR.a,_QT=_QR.b,_QU=E(_QQ.a);if(E(_QU)==44){return new T2(0,_S,new T(function(){return E(B(_H5(44,_QS,_QT)).a);}));}else{var _QV=B(_H5(44,_QS,_QT)),_QW=E(_QV.b);if(!_QW._){return E(_PX);}else{return new T2(0,new T2(1,_QU,_QV.a),_QW.a);}}}}}),_QX=B(_Gd(B(_sy(_Gb,new T(function(){return E(E(_QP).b);})))));if(!_QX._){return E(_Fz);}else{if(!E(_QX.b)._){var _QY=new T(function(){var _QZ=E(_QN.a);if(!_QZ._){return E(_Q0);}else{var _R0=E(_QZ.b);if(!_R0._){return E(_Q0);}else{var _R1=_R0.a,_R2=_R0.b,_R3=E(_QZ.a);if(E(_R3)==44){return new T2(0,_S,new T(function(){return E(B(_H5(44,_R1,_R2)).a);}));}else{var _R4=B(_H5(44,_R1,_R2)),_R5=E(_R4.b);if(!_R5._){return E(_Q0);}else{return new T2(0,new T2(1,_R3,_R4.a),_R5.a);}}}}}),_R6=new T(function(){var _R7=B(_Gd(B(_sy(_Gb,new T(function(){return E(E(_QP).a);})))));if(!_R7._){return E(_Fz);}else{if(!E(_R7.b)._){return E(_R7.a);}else{return E(_FA);}}},1),_R8=_Qs,_R9=_Qt,_Ra=_Qu,_Rb=_Qv,_Rc=_Qw,_Rd=_Qx,_Re=_Qy,_Rf=_Qz,_Rg=_QA,_Rh=_QB,_Ri=_QC,_Rj=_QD,_Rk=_QE,_Rl=_QF,_Rm=_QG,_Rn=_QH,_Ro=_QI,_Rp=_QJ,_Rq=_QK,_Rr=_QL;_Q3=_QN.b;_Q4={_:0,a:E(_QO.a),b:E(B(_KQ(_R6,E(_QX.a),new T(function(){return B(_Jh(E(_QY).a));}),new T(function(){return B(_Jv(E(_QY).b));}),_QO.b))),c:E(_QO.c),d:_QO.d,e:_QO.e,f:_QO.f,g:E(_QO.g),h:_QO.h,i:E(_QO.i),j:E(_QO.j),k:E(_QO.k)};_Q5=_R8;_Q6=_R9;_Q7=_Ra;_Q8=_Rb;_Q9=_Rc;_Qa=_Rd;_Qb=_Re;_Qc=_Rf;_Qd=_Rg;_Qe=_Rh;_Qf=_Ri;_Qg=_Rj;_Qh=_Rk;_Qi=_Rl;_Qj=_Rm;_Qk=_Rn;_Ql=_Ro;_Qm=_Rp;_Qn=_Rq;_Qo=_Rr;return __continue;}else{return E(_FA);}}}}})(_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo));if(_Qp!=__continue){return _Qp;}}},_Rs=function(_Rt){var _Ru=E(_Rt);if(!_Ru._){return new T2(0,_S,_S);}else{var _Rv=E(_Ru.a),_Rw=new T(function(){var _Rx=B(_Rs(_Ru.b));return new T2(0,_Rx.a,_Rx.b);});return new T2(0,new T2(1,_Rv.a,new T(function(){return E(E(_Rw).a);})),new T2(1,_Rv.b,new T(function(){return E(E(_Rw).b);})));}},_Ry=32,_Rz=function(_RA,_RB,_RC,_RD){var _RE=E(_RD);if(!_RE._){return __Z;}else{var _RF=_RE.b;if(!B(_4A(_3L,_RA,_RC))){var _RG=new T(function(){return B(_Rz(new T(function(){return E(_RA)+1|0;}),_RB,_RC,_RF));});return new T2(1,_RE.a,_RG);}else{var _RH=new T(function(){return B(_Rz(new T(function(){return E(_RA)+1|0;}),_RB,_RC,_RF));});return new T2(1,_RB,_RH);}}},_RI=function(_RJ,_RK){var _RL=E(_RK);if(!_RL._){return __Z;}else{var _RM=new T(function(){var _RN=B(_Rs(_RL.a)),_RO=_RN.a,_RP=new T(function(){return B(_IU(0,_RJ,_RO));});return B(_Gp(B(_Rz(_rm,_Ry,_RP,_RO)),new T(function(){return B(_J1(0,_E9,_RP,_RN.b));},1)));});return new T2(1,_RM,new T(function(){return B(_RI(_RJ,_RL.b));}));}},_RQ=function(_RR,_RS){var _RT=E(_RS);return (_RT._==0)?__Z:new T2(1,_RR,new T(function(){return B(_RQ(_RT.a,_RT.b));}));},_RU=new T(function(){return B(unCStr("init"));}),_RV=new T(function(){return B(_nd(_RU));}),_RW=function(_RX,_RY){var _RZ=function(_S0){var _S1=E(_S0);if(!_S1._){return __Z;}else{var _S2=new T(function(){return B(_q(new T2(1,_RX,_S),new T(function(){return B(_RZ(_S1.b));},1)));},1);return new F(function(){return _q(_S1.a,_S2);});}},_S3=B(_RZ(_RY));if(!_S3._){return E(_RV);}else{return new F(function(){return _RQ(_S3.a,_S3.b);});}},_S4=61,_S5=46,_S6=new T(function(){return B(_e6("Event.hs:(93,1)-(99,61)|function makeDecision"));}),_S7=new T(function(){return B(unCStr("sm"));}),_S8=new T(function(){return B(unCStr("rk"));}),_S9=new T(function(){return B(unCStr("if"));}),_Sa=new T(function(){return B(unCStr("hm"));}),_Sb=new T(function(){return B(unCStr("cleq"));}),_Sc=new T(function(){return B(unCStr("da"));}),_Sd=new T(function(){return B(unCStr("ct"));}),_Se=function(_Sf,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA){var _SB=function(_SC,_SD){var _SE=function(_SF){if(!B(_qO(_SC,_Sd))){if(!B(_qO(_SC,_Sc))){var _SG=function(_SH){if(!B(_qO(_SC,_Sb))){var _SI=function(_SJ){if(!B(_qO(_SC,_rP))){if(!B(_qO(_SC,_Sa))){if(!B(_qO(_SC,_S9))){if(!B(_qO(_SC,_S8))){if(!B(_qO(_SC,_S7))){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{var _SK=E(_Sz);return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E({_:0,a:E(_SK.a),b:E(_SK.b),c:E(_SK.c),d:E(_SK.d),e:E(_SK.e),f:E(_SK.f),g:E(_SK.g),h:E(_wu)}),u:E(_SA)};}}else{return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_SD),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}}else{var _SL=E(_SD);if(!_SL._){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{var _SM=_SL.a,_SN=E(_SL.b);if(!_SN._){return E(_S6);}else{var _SO=_SN.a,_SP=B(_Od(_Sm)),_SQ=_SP.a,_SR=_SP.b,_SS=function(_ST){if(!B(_4A(_qd,_SM,_SQ))){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{if(!B(_qO(_SO,B(_6Q(_SR,B(_MD(_qd,_SM,_SQ))))))){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{return new F(function(){return _Se(_ST,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}}},_SU=B(_RW(_S5,_SN.b));if(!_SU._){return new F(function(){return _SS(_S);});}else{var _SV=_SU.a,_SW=E(_SU.b);if(!_SW._){return new F(function(){return _SS(new T2(1,_SV,_S));});}else{var _SX=_SW.a,_SY=_SW.b,_SZ=E(_SV);if(E(_SZ)==47){if(!B(_4A(_qd,_SM,_SQ))){return new F(function(){return _Se(B(_H5(47,_SX,_SY)).a,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}else{if(!B(_qO(_SO,B(_6Q(_SR,B(_MD(_qd,_SM,_SQ))))))){return new F(function(){return _Se(B(_H5(47,_SX,_SY)).a,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}else{return new F(function(){return _Se(_S,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}}}else{if(!B(_4A(_qd,_SM,_SQ))){var _T0=E(B(_H5(47,_SX,_SY)).b);if(!_T0._){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{return new F(function(){return _Se(_T0.a,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}}else{if(!B(_qO(_SO,B(_6Q(_SR,B(_MD(_qd,_SM,_SQ))))))){var _T1=E(B(_H5(47,_SX,_SY)).b);if(!_T1._){return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}else{return new F(function(){return _Se(_T1.a,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}}else{return new F(function(){return _Se(new T2(1,_SZ,new T(function(){return E(B(_H5(47,_SX,_SY)).a);})),_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA);});}}}}}}}}}else{var _T2=E(_Sz);return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E({_:0,a:E(_T2.a),b:E(_T2.b),c:E(_T2.c),d:E(_T2.d),e:E(_T2.e),f:E(_T2.f),g:E(_T2.g),h:E(_wt)}),u:E(_SA)};}}else{var _T3=E(_Sz);return new F(function(){return _Om(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_S,_St,_Su,_Sv,_Sw,_Sx,_Sy,_T3.a,_T3.b,_T3.c,_T3.d,_T3.e,_T3.f,_T3.g,_T3.h,_SA);});}},_T4=E(_SC);if(!_T4._){return new F(function(){return _SI(_);});}else{if(E(_T4.a)==109){if(!E(_T4.b)._){var _T5=B(_Hi(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_T5.a),b:E(_T5.b),c:E(_T5.c),d:E(_T5.d),e:E(_T5.e),f:E(_T5.f),g:E(_T5.g),h:E(_T5.h),i:_T5.i,j:_T5.j,k:_T5.k,l:_T5.l,m:E(_T5.m),n:_T5.n,o:E(_T5.o),p:E(_T5.p),q:_T5.q,r:E(_T5.r),s:_T5.s,t:E(_T5.t),u:E(_T5.u)};}else{return new F(function(){return _SI(_);});}}else{return new F(function(){return _SI(_);});}}}else{var _T6=E(_Sg);return {_:0,a:E({_:0,a:E(_T6.a),b:E(B(_RI(_S4,_T6.b))),c:E(_T6.c),d:_T6.d,e:_T6.e,f:_T6.f,g:E(_T6.g),h:_T6.h,i:E(_T6.i),j:E(_T6.j),k:E(_T6.k)}),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_Sk),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}},_T7=E(_SC);if(!_T7._){return new F(function(){return _SG(_);});}else{var _T8=_T7.b;switch(E(_T7.a)){case 99:if(!E(_T8)._){var _T9=B(_Lm(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_T9.a),b:E(_T9.b),c:E(_T9.c),d:E(_T9.d),e:E(_T9.e),f:E(_T9.f),g:E(_T9.g),h:E(_T9.h),i:_T9.i,j:_T9.j,k:_T9.k,l:_T9.l,m:E(_T9.m),n:_T9.n,o:E(_T9.o),p:E(_T9.p),q:_T9.q,r:E(_T9.r),s:_T9.s,t:E(_T9.t),u:E(_T9.u)};}else{return new F(function(){return _SG(_);});}break;case 112:if(!E(_T8)._){var _Ta=B(_Q2(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_Ta.a),b:E(_Ta.b),c:E(_Ta.c),d:E(_Ta.d),e:E(_Ta.e),f:E(_Ta.f),g:E(_Ta.g),h:E(_Ta.h),i:_Ta.i,j:_Ta.j,k:_Ta.k,l:_Ta.l,m:E(_Ta.m),n:_Ta.n,o:E(_Ta.o),p:E(_Ta.p),q:_Ta.q,r:E(_Ta.r),s:_Ta.s,t:E(_Ta.t),u:E(_Ta.u)};}else{return new F(function(){return _SG(_);});}break;default:return new F(function(){return _SG(_);});}}}else{return {_:0,a:E(_Sg),b:E(_Sh),c:E(_Si),d:E(_Sj),e:E(_S),f:E(_Sl),g:E(_Sm),h:E(_Sn),i:_So,j:_Sp,k:_Sq,l:_Sr,m:E(_Ss),n:_St,o:E(_Su),p:E(_Sv),q:_Sw,r:E(_Sx),s:_Sy,t:E(_Sz),u:E(_SA)};}}else{var _Tb=B(_Jx(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_Tb.a),b:E(_Tb.b),c:E(_Tb.c),d:E(_Tb.d),e:E(_Tb.e),f:E(_Tb.f),g:E(_Tb.g),h:E(_Tb.h),i:_Tb.i,j:_Tb.j,k:_Tb.k,l:_Tb.l,m:E(_Tb.m),n:_Tb.n,o:E(_Tb.o),p:E(_Tb.p),q:_Tb.q,r:E(_Tb.r),s:_Tb.s,t:E(_Tb.t),u:E(_Tb.u)};}},_Tc=E(_SC);if(!_Tc._){return new F(function(){return _SE(_);});}else{var _Td=_Tc.b;switch(E(_Tc.a)){case 100:if(!E(_Td)._){var _Te=B(_N3(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_Te.a),b:E(_Te.b),c:E(_Te.c),d:E(_Te.d),e:E(_Te.e),f:E(_Te.f),g:E(_Te.g),h:E(_Te.h),i:_Te.i,j:_Te.j,k:_Te.k,l:_Te.l,m:E(_Te.m),n:_Te.n,o:E(_Te.o),p:E(_Te.p),q:_Te.q,r:E(_Te.r),s:_Te.s,t:E(_Te.t),u:E(_Te.u)};}else{return new F(function(){return _SE(_);});}break;case 101:if(!E(_Td)._){var _Tf=B(_qg(_SD,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA));return {_:0,a:E(_Tf.a),b:E(_Tf.b),c:E(_Tf.c),d:E(_Tf.d),e:E(_Tf.e),f:E(_Tf.f),g:E(_Tf.g),h:E(_Tf.h),i:_Tf.i,j:_Tf.j,k:_Tf.k,l:_Tf.l,m:E(_Tf.m),n:_Tf.n,o:E(_Tf.o),p:E(_Tf.p),q:_Tf.q,r:E(_Tf.r),s:_Tf.s,t:E(_Tf.t),u:E(_Tf.u)};}else{return new F(function(){return _SE(_);});}break;default:return new F(function(){return _SE(_);});}}},_Tg=E(_Sf);if(!_Tg._){return new F(function(){return _SB(_S,_S);});}else{var _Th=_Tg.a,_Ti=E(_Tg.b);if(!_Ti._){return new F(function(){return _SB(new T2(1,_Th,_S),_S);});}else{var _Tj=E(_Th),_Tk=new T(function(){var _Tl=B(_H5(46,_Ti.a,_Ti.b));return new T2(0,_Tl.a,_Tl.b);});if(E(_Tj)==46){return new F(function(){return _SB(_S,new T2(1,new T(function(){return E(E(_Tk).a);}),new T(function(){return E(E(_Tk).b);})));});}else{return new F(function(){return _SB(new T2(1,_Tj,new T(function(){return E(E(_Tk).a);})),new T(function(){return E(E(_Tk).b);}));});}}}},_Tm=new T(function(){return B(unCStr("last"));}),_Tn=new T(function(){return B(_nd(_Tm));}),_To=32,_Tp=0,_Tq=65306,_Tr=125,_Ts=new T1(0,1),_Tt=function(_Tu,_Tv,_Tw,_Tx,_Ty){var _Tz=new T(function(){return E(_Ty).i;}),_TA=new T(function(){return E(E(_Ty).c);}),_TB=new T(function(){var _TC=E(_Tz)+1|0;if(0>=_TC){return E(_To);}else{var _TD=B(_pN(_TC,_TA));if(!_TD._){return E(_To);}else{return B(_o9(_TD.a,_TD.b,_Tn));}}}),_TE=new T(function(){var _TF=E(_TB);switch(E(_TF)){case 125:return E(_To);break;case 12289:return E(_To);break;case 12290:return E(_To);break;default:return E(_TF);}}),_TG=new T(function(){if(E(_TE)==10){return true;}else{return false;}}),_TH=new T(function(){if(!E(_TG)){if(E(_TE)==12300){return E(_j6);}else{return E(_Ty).j;}}else{return E(_Tp);}}),_TI=new T(function(){var _TJ=E(_Tv)/28,_TK=_TJ&4294967295;if(_TJ>=_TK){return _TK-1|0;}else{return (_TK-1|0)-1|0;}}),_TL=new T(function(){if(!E(E(_Tx).h)){return E(_j7);}else{return 2+(E(E(E(_Ty).b).b)+3|0)|0;}}),_TM=new T(function(){if(!E(_Tz)){return new T2(0,_TI,_TL);}else{return E(E(_Ty).h);}}),_TN=new T(function(){return E(E(_TM).b);}),_TO=new T(function(){return E(E(_TM).a);}),_TP=new T(function(){if(E(_TE)==65306){return true;}else{return false;}}),_TQ=new T(function(){if(!E(_TP)){if(!E(_TG)){var _TR=E(_TN);if((_TR+1)*20<=E(_Tw)-10){return new T2(0,_TO,_TR+1|0);}else{return new T2(0,new T(function(){return E(_TO)-1|0;}),_TL);}}else{return new T2(0,new T(function(){return E(_TO)-1|0;}),_TL);}}else{return new T2(0,_TO,_TN);}}),_TS=new T(function(){if(E(E(_TQ).a)==1){if(E(_TO)==1){return false;}else{return true;}}else{return false;}}),_TT=new T(function(){if(!E(_TP)){return __Z;}else{return B(_q5(_Tq,E(_Tz),_TA));}}),_TU=new T(function(){if(E(_TE)==123){return true;}else{return false;}}),_TV=new T(function(){if(!E(_TU)){return __Z;}else{return B(_q5(_Tr,E(_Tz),_TA));}}),_TW=new T(function(){if(!E(_TU)){var _TX=E(_Ty),_TY=E(_Tx);if(E(_TB)==12290){var _TZ=true;}else{var _TZ=false;}return {_:0,a:E(_TX.a),b:E(_TX.b),c:E(_TX.c),d:E(_TX.d),e:E(_TX.e),f:E(_TX.f),g:E(_TX.g),h:E(_TX.h),i:_TX.i,j:_TX.j,k:_TX.k,l:_TX.l,m:E(_TX.m),n:_TX.n,o:E(_TX.o),p:E(_TX.p),q:_TX.q,r:E(_TX.r),s:_TX.s,t:E({_:0,a:E(_TY.a),b:E(_TY.b),c:E(_TY.c),d:E(_TZ),e:E(_TY.e),f:E(_TY.f),g:E(_TY.g),h:E(_TY.h)}),u:E(_TX.u)};}else{var _U0=E(_Ty),_U1=E(_Tx);if(E(_TB)==12290){var _U2=true;}else{var _U2=false;}return B(_Se(_TV,_U0.a,_U0.b,_U0.c,_U0.d,_U0.e,_U0.f,_U0.g,_U0.h,_U0.i,_U0.j,_U0.k,_U0.l,_U0.m,_U0.n,_U0.o,_U0.p,_U0.q,_U0.r,_U0.s,{_:0,a:E(_U1.a),b:E(_U1.b),c:E(_U1.c),d:E(_U2),e:E(_U1.e),f:E(_U1.f),g:E(_U1.g),h:E(_U1.h)},_U0.u));}}),_U3=new T(function(){return E(E(_TW).t);}),_U4=new T(function(){if(!E(_Tz)){return E(_Tp);}else{return E(_TW).k;}}),_U5=new T(function(){var _U6=E(_TW),_U7=_U6.a,_U8=_U6.b,_U9=_U6.c,_Ua=_U6.d,_Ub=_U6.e,_Uc=_U6.f,_Ud=_U6.g,_Ue=_U6.l,_Uf=_U6.m,_Ug=_U6.n,_Uh=_U6.o,_Ui=_U6.p,_Uj=_U6.q,_Uk=_U6.r,_Ul=_U6.s,_Um=_U6.u;if(!E(_TS)){var _Un=E(_TQ);}else{var _Un=new T2(0,_TO,_TL);}var _Uo=E(_Tz),_Up=function(_Uq){var _Ur=B(_ms(_TA,0))-1|0,_Us=function(_Ut){var _Uu=E(_TH);if(!E(_TS)){var _Uv=E(_U3);return {_:0,a:E(_U7),b:E(_U8),c:E(_U9),d:E(_Ua),e:E(_Ub),f:E(_Uc),g:E(_Ud),h:E(_Un),i:_Ut,j:_Uu,k:E(_U4),l:_Ue,m:E(_Uf),n:_Ug,o:E(_Uh),p:E(_Ui),q:_Uj,r:E(_Uk),s:_Ul,t:E({_:0,a:E(_Uv.a),b:E(_Uv.b),c:(_Uo+_Uq|0)<=_Ur,d:E(_Uv.d),e:E(_Uv.e),f:E(_Uv.f),g:E(_Uv.g),h:E(_Uv.h)}),u:E(_Um)};}else{var _Uw=E(_U3);return {_:0,a:E(_U7),b:E(_U8),c:E(_U9),d:E(_Ua),e:E(_Ub),f:E(_Uc),g:E(_Ud),h:E(_Un),i:_Ut,j:_Uu,k:E(_U4)+1|0,l:_Ue,m:E(_Uf),n:_Ug,o:E(_Uh),p:E(_Ui),q:_Uj,r:E(_Uk),s:_Ul,t:E({_:0,a:E(_Uw.a),b:E(_Uw.b),c:(_Uo+_Uq|0)<=_Ur,d:E(_Uw.d),e:E(_Uw.e),f:E(_Uw.f),g:E(_Uw.g),h:E(_Uw.h)}),u:E(_Um)};}};if((_Uo+_Uq|0)<=_Ur){return new F(function(){return _Us(_Uo+_Uq|0);});}else{return new F(function(){return _Us(0);});}};if(!E(_TP)){if(!E(_TU)){return B(_Up(1));}else{return B(_Up(B(_ms(_TV,0))+2|0));}}else{return B(_Up(B(_ms(_TT,0))+2|0));}}),_Ux=new T(function(){var _Uy=B(_o3(B(_o1(_Tu)))),_Uz=new T(function(){var _UA=B(_pu(_Tu,E(_Tv)/16)),_UB=_UA.a;if(E(_UA.b)>=0){return E(_UB);}else{return B(A3(_oG,_Uy,_UB,new T(function(){return B(A2(_hd,_Uy,_Ts));})));}});return B(A3(_oG,_Uy,_Uz,new T(function(){return B(A2(_hd,_Uy,_hm));})));});return {_:0,a:_TE,b:_TO,c:_TN,d:new T(function(){if(E(_TL)!=E(_TN)){return E(_TO);}else{return E(_TO)+1|0;}}),e:new T(function(){var _UC=E(_TN);if(E(_TL)!=_UC){return _UC-1|0;}else{var _UD=(E(_Tw)-10)/20,_UE=_UD&4294967295;if(_UD>=_UE){return _UE;}else{return _UE-1|0;}}}),f:_TL,g:_Tz,h:_TA,i:new T(function(){return B(_6Q(_j3,E(_TH)));}),j:_TT,k:_TI,l:_Ux,m:_U4,n:_j8,o:_TP,p:_TU,q:_TS,r:_U3,s:_TW,t:_U5};},_UF=function(_UG){var _UH=E(_UG);if(!_UH._){return new T2(0,_S,_S);}else{var _UI=E(_UH.a),_UJ=new T(function(){var _UK=B(_UF(_UH.b));return new T2(0,_UK.a,_UK.b);});return new T2(0,new T2(1,_UI.a,new T(function(){return E(E(_UJ).a);})),new T2(1,_UI.b,new T(function(){return E(E(_UJ).b);})));}},_UL=42,_UM=32,_UN=function(_UO,_UP,_UQ){var _UR=E(_UO);if(!_UR._){return __Z;}else{var _US=_UR.a,_UT=_UR.b;if(_UP!=_UQ){var _UU=E(_US);return (_UU._==0)?E(_ng):(E(_UU.a)==42)?new T2(1,new T2(1,_UM,_UU.b),new T(function(){return B(_UN(_UT,_UP,_UQ+1|0));})):new T2(1,new T2(1,_UM,_UU),new T(function(){return B(_UN(_UT,_UP,_UQ+1|0));}));}else{var _UV=E(_US);return (_UV._==0)?E(_ng):(E(_UV.a)==42)?new T2(1,new T2(1,_UM,_UV),new T(function(){return B(_UN(_UT,_UP,_UQ+1|0));})):new T2(1,new T2(1,_UL,_UV),new T(function(){return B(_UN(_UT,_UP,_UQ+1|0));}));}}},_UW=new T(function(){return B(unCStr("\n\n"));}),_UX=function(_UY){var _UZ=E(_UY);if(!_UZ._){return __Z;}else{var _V0=new T(function(){return B(_q(_UW,new T(function(){return B(_UX(_UZ.b));},1)));},1);return new F(function(){return _q(_UZ.a,_V0);});}},_V1=function(_V2,_V3,_V4){var _V5=new T(function(){var _V6=new T(function(){var _V7=E(_V3);if(!_V7._){return B(_UX(_S));}else{var _V8=_V7.a,_V9=_V7.b,_Va=E(_V4);if(!_Va){var _Vb=E(_V8);if(!_Vb._){return E(_ng);}else{if(E(_Vb.a)==42){return B(_UX(new T2(1,new T2(1,_UM,_Vb),new T(function(){return B(_UN(_V9,0,1));}))));}else{return B(_UX(new T2(1,new T2(1,_UL,_Vb),new T(function(){return B(_UN(_V9,0,1));}))));}}}else{var _Vc=E(_V8);if(!_Vc._){return E(_ng);}else{if(E(_Vc.a)==42){return B(_UX(new T2(1,new T2(1,_UM,_Vc.b),new T(function(){return B(_UN(_V9,_Va,1));}))));}else{return B(_UX(new T2(1,new T2(1,_UM,_Vc),new T(function(){return B(_UN(_V9,_Va,1));}))));}}}}});return B(unAppCStr("\n\n",_V6));},1);return new F(function(){return _q(_V2,_V5);});},_Vd=function(_Ve){return E(E(_Ve).c);},_Vf=function(_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo){var _Vp=new T(function(){if(!E(_Vh)){return E(_Vi);}else{return false;}}),_Vq=new T(function(){if(!E(_Vh)){return false;}else{return E(E(_Vn).g);}}),_Vr=new T(function(){if(!E(_Vq)){if(!E(_Vp)){return B(A2(_hd,_Vg,_hl));}else{return B(A3(_mx,_Vg,new T(function(){return B(A3(_mx,_Vg,_Vl,_Vm));}),new T(function(){return B(A2(_hd,_Vg,_Ts));})));}}else{return B(A3(_mx,_Vg,_Vl,_Vm));}}),_Vs=new T(function(){if(!E(_Vq)){if(!E(_Vp)){return __Z;}else{var _Vt=E(_Vj)+1|0;if(0>=_Vt){return __Z;}else{return B(_pN(_Vt,_Vk));}}}else{return B(_V1(B(_Vd(_Vo)),new T(function(){return E(B(_UF(E(_Vo).m)).a);},1),new T(function(){return E(_Vo).n;},1)));}});return new T4(0,_Vq,_Vp,_Vs,_Vr);},_Vu=function(_Vv,_Vw,_Vx){var _Vy=E(_Vw),_Vz=E(_Vx),_VA=new T(function(){var _VB=B(_h9(_Vv)),_VC=B(_Vu(_Vv,_Vz,B(A3(_oG,_VB,new T(function(){return B(A3(_mx,_VB,_Vz,_Vz));}),_Vy))));return new T2(1,_VC.a,_VC.b);});return new T2(0,_Vy,_VA);},_VD=1,_VE=new T(function(){var _VF=B(_Vu(_ga,_hL,_VD));return new T2(1,_VF.a,_VF.b);}),_VG=function(_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd,_We,_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_){var _Wo={_:0,a:E(_Wf),b:E(_Wg),c:E(_Wh),d:E(_Wi),e:E(_Wj),f:E(_Wk),g:E(_Wl),h:E(_Wm)};if(!E(_Wh)){return {_:0,a:E({_:0,a:E(_VK),b:E(_VL),c:E(_VM),d:_VN,e:_VO,f:_VP,g:E(_VQ),h:_VR,i:E(_VS),j:E(_VT),k:E(_VU)}),b:E(new T2(0,_VV,_VW)),c:E(_VX),d:E(_VY),e:E(_VZ),f:E(_W0),g:E(_W1),h:E(new T2(0,_W2,_W3)),i:_W4,j:_W5,k:_W6,l:_W7,m:E(_W8),n:_W9,o:E(_Wa),p:E(_Wb),q:_Wc,r:E(_Wd),s:_We,t:E(_Wo),u:E(_Wn)};}else{if(!E(_Wi)){var _Wp=B(_Tt(_bR,_VI,_VJ,_Wo,{_:0,a:E({_:0,a:E(_VK),b:E(_VL),c:E(_VM),d:_VN,e:_VO,f:_VP,g:E(_VQ),h:_VR,i:E(_VS),j:E(_VT),k:E(_VU)}),b:E(new T2(0,_VV,_VW)),c:E(_VX),d:E(_VY),e:E(_VZ),f:E(_W0),g:E(_W1),h:E(new T2(0,_W2,_W3)),i:_W4,j:_W5,k:_W6,l:_W7,m:E(_W8),n:_W9,o:E(_Wa),p:E(_Wb),q:_Wc,r:E(_Wd),s:_We,t:E(_Wo),u:E(_Wn)})),_Wq=_Wp.d,_Wr=_Wp.e,_Ws=_Wp.f,_Wt=_Wp.i,_Wu=_Wp.n,_Wv=_Wp.p,_Ww=_Wp.q,_Wx=_Wp.s,_Wy=_Wp.t;if(!E(_Wp.o)){var _Wz=B(_Vf(_bm,_Wv,_Ww,_Wp.g,_Wp.h,_Wp.k,_Wp.m,_Wp.r,_Wx)),_WA=function(_){if(!E(_Wv)){if(!E(_Ww)){var _WB=B(_iA(E(_VH).a,_Wt,_j4,_hL,_Wp.b,_Wp.c,_Wp.a,_));return _Wy;}else{return _Wy;}}else{return _Wy;}},_WC=function(_WD){var _WE=E(_VH),_WF=_WE.a,_WG=_WE.b,_WH=B(_nP(_WF,_WG,_Wp.l,_Wx,_)),_WI=B(_ln(_WF,_WG,_VJ,0,_Ws,_Wz.d,_Ws,_Wz.c,_));return new F(function(){return _WA(_);});};if(!E(_Wz.a)){if(!E(_Wz.b)){return new F(function(){return _WA(_);});}else{return new F(function(){return _WC(_);});}}else{return new F(function(){return _WC(_);});}}else{var _WJ=E(_Wp.j);if(!_WJ._){return _Wy;}else{var _WK=E(_VE);if(!_WK._){return _Wy;}else{var _WL=E(_VH).a,_WM=B(_iA(_WL,_Wt,_Wu,_WK.a,_Wq,_Wr,_WJ.a,_)),_WN=function(_WO,_WP,_){while(1){var _WQ=E(_WO);if(!_WQ._){return _gD;}else{var _WR=E(_WP);if(!_WR._){return _gD;}else{var _WS=B(_iA(_WL,_Wt,_Wu,_WR.a,_Wq,_Wr,_WQ.a,_));_WO=_WQ.b;_WP=_WR.b;continue;}}}},_WT=B(_WN(_WJ.b,_WK.b,_));return _Wy;}}}}else{return {_:0,a:E({_:0,a:E(_VK),b:E(_VL),c:E(_VM),d:_VN,e:_VO,f:_VP,g:E(_VQ),h:_VR,i:E(_VS),j:E(_VT),k:E(_VU)}),b:E(new T2(0,_VV,_VW)),c:E(_VX),d:E(_VY),e:E(_VZ),f:E(_W0),g:E(_W1),h:E(new T2(0,_W2,_W3)),i:_W4,j:_W5,k:_W6,l:_W7,m:E(_W8),n:_W9,o:E(_Wa),p:E(_Wb),q:_Wc,r:E(_Wd),s:_We,t:E(_Wo),u:E(_Wn)};}}},_WU=function(_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_){while(1){var _XC=B(_VG(_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_)),_XD=E(_XC),_XE=_XD.c,_XF=_XD.d,_XG=_XD.e,_XH=_XD.f,_XI=_XD.g,_XJ=_XD.i,_XK=_XD.j,_XL=_XD.k,_XM=_XD.l,_XN=_XD.m,_XO=_XD.n,_XP=_XD.o,_XQ=_XD.p,_XR=_XD.q,_XS=_XD.r,_XT=_XD.s,_XU=_XD.u,_XV=E(_XD.t),_XW=_XV.a,_XX=_XV.b,_XY=_XV.c,_XZ=_XV.e,_Y0=_XV.g,_Y1=_XV.h,_Y2=E(_XD.a),_Y3=E(_XD.b),_Y4=E(_XD.h);if(!E(_XV.d)){if(!E(_Xv)){return {_:0,a:E(_Y2),b:E(_Y3),c:E(_XE),d:E(_XF),e:E(_XG),f:E(_XH),g:E(_XI),h:E(_Y4),i:_XJ,j:_XK,k:_XL,l:_XM,m:E(_XN),n:_XO,o:E(_XP),p:E(_XQ),q:_XR,r:E(_XS),s:_XT,t:E({_:0,a:E(_XW),b:E(_XX),c:E(_XY),d:E(_wt),e:E(_XZ),f:E(_wt),g:E(_Y0),h:E(_Y1)}),u:E(_XU)};}else{_WY=_Y2.a;_WZ=_Y2.b;_X0=_Y2.c;_X1=_Y2.d;_X2=_Y2.e;_X3=_Y2.f;_X4=_Y2.g;_X5=_Y2.h;_X6=_Y2.i;_X7=_Y2.j;_X8=_Y2.k;_X9=_Y3.a;_Xa=_Y3.b;_Xb=_XE;_Xc=_XF;_Xd=_XG;_Xe=_XH;_Xf=_XI;_Xg=_Y4.a;_Xh=_Y4.b;_Xi=_XJ;_Xj=_XK;_Xk=_XL;_Xl=_XM;_Xm=_XN;_Xn=_XO;_Xo=_XP;_Xp=_XQ;_Xq=_XR;_Xr=_XS;_Xs=_XT;_Xt=_XW;_Xu=_XX;_Xv=_XY;_Xw=_wt;_Xx=_XZ;_Xy=_XV.f;_Xz=_Y0;_XA=_Y1;_XB=_XU;continue;}}else{return {_:0,a:E(_Y2),b:E(_Y3),c:E(_XE),d:E(_XF),e:E(_XG),f:E(_XH),g:E(_XI),h:E(_Y4),i:_XJ,j:_XK,k:_XL,l:_XM,m:E(_XN),n:_XO,o:E(_XP),p:E(_XQ),q:_XR,r:E(_XS),s:_XT,t:E({_:0,a:E(_XW),b:E(_XX),c:E(_XY),d:E(_wu),e:E(_XZ),f:E(_wt),g:E(_Y0),h:E(_Y1)}),u:E(_XU)};}}},_Y5=function(_Y6,_Y7,_Y8,_Y9,_Ya,_Yb,_Yc,_Yd,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_){var _YM=B(_VG(_Y6,_Y7,_Y8,_Y9,_Ya,_Yb,_Yc,_Yd,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB,_YC,_YD,_YE,_YF,_wu,_YG,_YH,_YI,_YJ,_YK,_YL,_)),_YN=E(_YM),_YO=_YN.c,_YP=_YN.d,_YQ=_YN.e,_YR=_YN.f,_YS=_YN.g,_YT=_YN.i,_YU=_YN.j,_YV=_YN.k,_YW=_YN.l,_YX=_YN.m,_YY=_YN.n,_YZ=_YN.o,_Z0=_YN.p,_Z1=_YN.q,_Z2=_YN.r,_Z3=_YN.s,_Z4=_YN.u,_Z5=E(_YN.t),_Z6=_Z5.a,_Z7=_Z5.b,_Z8=_Z5.c,_Z9=_Z5.e,_Za=_Z5.g,_Zb=_Z5.h,_Zc=E(_YN.a),_Zd=E(_YN.b),_Ze=E(_YN.h);if(!E(_Z5.d)){return new F(function(){return _WU(_Y6,_Y7,_Y8,_Zc.a,_Zc.b,_Zc.c,_Zc.d,_Zc.e,_Zc.f,_Zc.g,_Zc.h,_Zc.i,_Zc.j,_Zc.k,_Zd.a,_Zd.b,_YO,_YP,_YQ,_YR,_YS,_Ze.a,_Ze.b,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0,_Z1,_Z2,_Z3,_Z6,_Z7,_Z8,_wt,_Z9,_Z5.f,_Za,_Zb,_Z4,_);});}else{return {_:0,a:E(_Zc),b:E(_Zd),c:E(_YO),d:E(_YP),e:E(_YQ),f:E(_YR),g:E(_YS),h:E(_Ze),i:_YT,j:_YU,k:_YV,l:_YW,m:E(_YX),n:_YY,o:E(_YZ),p:E(_Z0),q:_Z1,r:E(_Z2),s:_Z3,t:E({_:0,a:E(_Z6),b:E(_Z7),c:E(_Z8),d:E(_wu),e:E(_Z9),f:E(_wt),g:E(_Za),h:E(_Zb)}),u:E(_Z4)};}},_Zf=function(_Zg){var _Zh=E(_Zg);if(!_Zh._){return __Z;}else{var _Zi=E(_Zh.b);return (_Zi._==0)?__Z:new T2(1,new T2(0,_Zh.a,_Zi.a),new T(function(){return B(_Zf(_Zi.b));}));}},_Zj=function(_Zk,_Zl,_Zm){return new T2(1,new T2(0,_Zk,_Zl),new T(function(){return B(_Zf(_Zm));}));},_Zn=function(_Zo,_Zp){var _Zq=E(_Zp);return (_Zq._==0)?__Z:new T2(1,new T2(0,_Zo,_Zq.a),new T(function(){return B(_Zf(_Zq.b));}));},_Zr=new T(function(){return B(err(_sr));}),_Zs=new T(function(){return B(err(_st));}),_Zt=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_Zu=function(_Zv){var _Zw=B(_Gd(B(_sy(_Zt,_Zv))));return (_Zw._==0)?E(_Zr):(E(_Zw.b)._==0)?E(_Zw.a):E(_Zs);},_Zx="Invalid JSON!",_Zy=new T1(0,_Zx),_Zz="No such value",_ZA=new T1(0,_Zz),_ZB=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_ZC=function(_ZD){return E(E(_ZD).c);},_ZE=function(_ZF,_ZG,_){var _ZH=__app1(E(_ZB),_ZG),_ZI=__eq(_ZH,E(_3a));if(!E(_ZI)){var _ZJ=__isUndef(_ZH);return (E(_ZJ)==0)?new T(function(){var _ZK=String(_ZH),_ZL=jsParseJSON(_ZK);if(!_ZL._){return E(_Zy);}else{return B(A2(_ZC,_ZF,_ZL.a));}}):_ZA;}else{return _ZA;}},_ZM=new T1(0,0),_ZN=function(_ZO,_ZP){while(1){var _ZQ=E(_ZO);if(!_ZQ._){var _ZR=_ZQ.a,_ZS=E(_ZP);if(!_ZS._){return new T1(0,(_ZR>>>0|_ZS.a>>>0)>>>0&4294967295);}else{_ZO=new T1(1,I_fromInt(_ZR));_ZP=_ZS;continue;}}else{var _ZT=E(_ZP);if(!_ZT._){_ZO=_ZQ;_ZP=new T1(1,I_fromInt(_ZT.a));continue;}else{return new T1(1,I_or(_ZQ.a,_ZT.a));}}}},_ZU=function(_ZV){var _ZW=E(_ZV);if(!_ZW._){return E(_ZM);}else{return new F(function(){return _ZN(new T1(0,E(_ZW.a)),B(_cN(B(_ZU(_ZW.b)),31)));});}},_ZX=function(_ZY,_ZZ){if(!E(_ZY)){return new F(function(){return _fs(B(_ZU(_ZZ)));});}else{return new F(function(){return _ZU(_ZZ);});}},_100=1420103680,_101=465,_102=new T2(1,_101,_S),_103=new T2(1,_100,_102),_104=new T(function(){return B(_ZX(_wu,_103));}),_105=function(_106){return E(_104);},_107=new T(function(){return B(unCStr("s"));}),_108=function(_109,_10a){while(1){var _10b=E(_109);if(!_10b._){return E(_10a);}else{_109=_10b.b;_10a=_10b.a;continue;}}},_10c=function(_10d,_10e,_10f){return new F(function(){return _108(_10e,_10d);});},_10g=new T1(0,1),_10h=function(_10i,_10j){var _10k=E(_10i);return new T2(0,_10k,new T(function(){var _10l=B(_10h(B(_cu(_10k,_10j)),_10j));return new T2(1,_10l.a,_10l.b);}));},_10m=function(_10n){var _10o=B(_10h(_10n,_10g));return new T2(1,_10o.a,_10o.b);},_10p=function(_10q,_10r){var _10s=B(_10h(_10q,new T(function(){return B(_eN(_10r,_10q));})));return new T2(1,_10s.a,_10s.b);},_10t=new T1(0,0),_10u=function(_10v,_10w){var _10x=E(_10v);if(!_10x._){var _10y=_10x.a,_10z=E(_10w);return (_10z._==0)?_10y>=_10z.a:I_compareInt(_10z.a,_10y)<=0;}else{var _10A=_10x.a,_10B=E(_10w);return (_10B._==0)?I_compareInt(_10A,_10B.a)>=0:I_compare(_10A,_10B.a)>=0;}},_10C=function(_10D,_10E,_10F){if(!B(_10u(_10E,_10t))){var _10G=function(_10H){return (!B(_d6(_10H,_10F)))?new T2(1,_10H,new T(function(){return B(_10G(B(_cu(_10H,_10E))));})):__Z;};return new F(function(){return _10G(_10D);});}else{var _10I=function(_10J){return (!B(_cX(_10J,_10F)))?new T2(1,_10J,new T(function(){return B(_10I(B(_cu(_10J,_10E))));})):__Z;};return new F(function(){return _10I(_10D);});}},_10K=function(_10L,_10M,_10N){return new F(function(){return _10C(_10L,B(_eN(_10M,_10L)),_10N);});},_10O=function(_10P,_10Q){return new F(function(){return _10C(_10P,_10g,_10Q);});},_10R=function(_10S){return new F(function(){return _b9(_10S);});},_10T=function(_10U){return new F(function(){return _eN(_10U,_10g);});},_10V=function(_10W){return new F(function(){return _cu(_10W,_10g);});},_10X=function(_10Y){return new F(function(){return _aQ(E(_10Y));});},_10Z={_:0,a:_10V,b:_10T,c:_10X,d:_10R,e:_10m,f:_10p,g:_10O,h:_10K},_110=function(_111,_112){while(1){var _113=E(_111);if(!_113._){var _114=E(_113.a);if(_114==( -2147483648)){_111=new T1(1,I_fromInt( -2147483648));continue;}else{var _115=E(_112);if(!_115._){return new T1(0,B(_9i(_114,_115.a)));}else{_111=new T1(1,I_fromInt(_114));_112=_115;continue;}}}else{var _116=_113.a,_117=E(_112);return (_117._==0)?new T1(1,I_div(_116,I_fromInt(_117.a))):new T1(1,I_div(_116,_117.a));}}},_118=function(_119,_11a){if(!B(_cm(_11a,_oK))){return new F(function(){return _110(_119,_11a);});}else{return E(_9T);}},_11b=function(_11c,_11d){while(1){var _11e=E(_11c);if(!_11e._){var _11f=E(_11e.a);if(_11f==( -2147483648)){_11c=new T1(1,I_fromInt( -2147483648));continue;}else{var _11g=E(_11d);if(!_11g._){var _11h=_11g.a;return new T2(0,new T1(0,B(_9i(_11f,_11h))),new T1(0,B(_an(_11f,_11h))));}else{_11c=new T1(1,I_fromInt(_11f));_11d=_11g;continue;}}}else{var _11i=E(_11d);if(!_11i._){_11c=_11e;_11d=new T1(1,I_fromInt(_11i.a));continue;}else{var _11j=I_divMod(_11e.a,_11i.a);return new T2(0,new T1(1,_11j.a),new T1(1,_11j.b));}}}},_11k=function(_11l,_11m){if(!B(_cm(_11m,_oK))){var _11n=B(_11b(_11l,_11m));return new T2(0,_11n.a,_11n.b);}else{return E(_9T);}},_11o=function(_11p,_11q){while(1){var _11r=E(_11p);if(!_11r._){var _11s=E(_11r.a);if(_11s==( -2147483648)){_11p=new T1(1,I_fromInt( -2147483648));continue;}else{var _11t=E(_11q);if(!_11t._){return new T1(0,B(_an(_11s,_11t.a)));}else{_11p=new T1(1,I_fromInt(_11s));_11q=_11t;continue;}}}else{var _11u=_11r.a,_11v=E(_11q);return (_11v._==0)?new T1(1,I_mod(_11u,I_fromInt(_11v.a))):new T1(1,I_mod(_11u,_11v.a));}}},_11w=function(_11x,_11y){if(!B(_cm(_11y,_oK))){return new F(function(){return _11o(_11x,_11y);});}else{return E(_9T);}},_11z=function(_11A,_11B){while(1){var _11C=E(_11A);if(!_11C._){var _11D=E(_11C.a);if(_11D==( -2147483648)){_11A=new T1(1,I_fromInt( -2147483648));continue;}else{var _11E=E(_11B);if(!_11E._){return new T1(0,quot(_11D,_11E.a));}else{_11A=new T1(1,I_fromInt(_11D));_11B=_11E;continue;}}}else{var _11F=_11C.a,_11G=E(_11B);return (_11G._==0)?new T1(0,I_toInt(I_quot(_11F,I_fromInt(_11G.a)))):new T1(1,I_quot(_11F,_11G.a));}}},_11H=function(_11I,_11J){if(!B(_cm(_11J,_oK))){return new F(function(){return _11z(_11I,_11J);});}else{return E(_9T);}},_11K=function(_11L,_11M){if(!B(_cm(_11M,_oK))){var _11N=B(_cD(_11L,_11M));return new T2(0,_11N.a,_11N.b);}else{return E(_9T);}},_11O=function(_11P,_11Q){while(1){var _11R=E(_11P);if(!_11R._){var _11S=E(_11R.a);if(_11S==( -2147483648)){_11P=new T1(1,I_fromInt( -2147483648));continue;}else{var _11T=E(_11Q);if(!_11T._){return new T1(0,_11S%_11T.a);}else{_11P=new T1(1,I_fromInt(_11S));_11Q=_11T;continue;}}}else{var _11U=_11R.a,_11V=E(_11Q);return (_11V._==0)?new T1(1,I_rem(_11U,I_fromInt(_11V.a))):new T1(1,I_rem(_11U,_11V.a));}}},_11W=function(_11X,_11Y){if(!B(_cm(_11Y,_oK))){return new F(function(){return _11O(_11X,_11Y);});}else{return E(_9T);}},_11Z=function(_120){return E(_120);},_121=function(_122){return E(_122);},_123=function(_124){var _125=E(_124);if(!_125._){var _126=E(_125.a);return (_126==( -2147483648))?E(_fr):(_126<0)?new T1(0, -_126):E(_125);}else{var _127=_125.a;return (I_compareInt(_127,0)>=0)?E(_125):new T1(1,I_negate(_127));}},_128=new T1(0, -1),_129=function(_12a){var _12b=E(_12a);if(!_12b._){var _12c=_12b.a;return (_12c>=0)?(E(_12c)==0)?E(_ZM):E(_d5):E(_128);}else{var _12d=I_compareInt(_12b.a,0);return (_12d<=0)?(E(_12d)==0)?E(_ZM):E(_128):E(_d5);}},_12e={_:0,a:_cu,b:_eN,c:_oe,d:_fs,e:_123,f:_129,g:_121},_12f=function(_12g,_12h){var _12i=E(_12g);if(!_12i._){var _12j=_12i.a,_12k=E(_12h);return (_12k._==0)?_12j!=_12k.a:(I_compareInt(_12k.a,_12j)==0)?false:true;}else{var _12l=_12i.a,_12m=E(_12h);return (_12m._==0)?(I_compareInt(_12l,_12m.a)==0)?false:true:(I_compare(_12l,_12m.a)==0)?false:true;}},_12n=new T2(0,_cm,_12f),_12o=function(_12p,_12q){return (!B(_ey(_12p,_12q)))?E(_12p):E(_12q);},_12r=function(_12s,_12t){return (!B(_ey(_12s,_12t)))?E(_12t):E(_12s);},_12u={_:0,a:_12n,b:_c6,c:_d6,d:_ey,e:_cX,f:_10u,g:_12o,h:_12r},_12v=function(_12w){return new T2(0,E(_12w),E(_aU));},_12x=new T3(0,_12e,_12u,_12v),_12y={_:0,a:_12x,b:_10Z,c:_11H,d:_11W,e:_118,f:_11w,g:_11K,h:_11k,i:_11Z},_12z=new T1(0,0),_12A=function(_12B,_12C,_12D){var _12E=B(A1(_12B,_12C));if(!B(_cm(_12E,_12z))){return new F(function(){return _110(B(_oe(_12C,_12D)),_12E);});}else{return E(_9T);}},_12F=function(_12G,_12H){while(1){if(!B(_cm(_12H,_oK))){var _12I=_12H,_12J=B(_11W(_12G,_12H));_12G=_12I;_12H=_12J;continue;}else{return E(_12G);}}},_12K=5,_12L=new T(function(){return B(_9P(_12K));}),_12M=new T(function(){return die(_12L);}),_12N=function(_12O,_12P){if(!B(_cm(_12P,_oK))){var _12Q=B(_12F(B(_123(_12O)),B(_123(_12P))));return (!B(_cm(_12Q,_oK)))?new T2(0,B(_11z(_12O,_12Q)),B(_11z(_12P,_12Q))):E(_9T);}else{return E(_12M);}},_12R=function(_12S,_12T,_12U,_12V){var _12W=B(_oe(_12T,_12U));return new F(function(){return _12N(B(_oe(B(_oe(_12S,_12V)),B(_129(_12W)))),B(_123(_12W)));});},_12X=function(_12Y,_12Z,_130){var _131=new T(function(){if(!B(_cm(_130,_oK))){var _132=B(_cD(_12Z,_130));return new T2(0,_132.a,_132.b);}else{return E(_9T);}}),_133=new T(function(){return B(A2(_hd,B(_o3(B(_o1(_12Y)))),new T(function(){return E(E(_131).a);})));});return new T2(0,_133,new T(function(){return new T2(0,E(E(_131).b),E(_130));}));},_134=function(_135,_136,_137){var _138=B(_12X(_135,_136,_137)),_139=_138.a,_13a=E(_138.b);if(!B(_d6(B(_oe(_13a.a,_aU)),B(_oe(_oK,_13a.b))))){return E(_139);}else{var _13b=B(_o3(B(_o1(_135))));return new F(function(){return A3(_oG,_13b,_139,new T(function(){return B(A2(_hd,_13b,_aU));}));});}},_13c=479723520,_13d=40233135,_13e=new T2(1,_13d,_S),_13f=new T2(1,_13c,_13e),_13g=new T(function(){return B(_ZX(_wu,_13f));}),_13h=new T1(0,40587),_13i=function(_13j){var _13k=new T(function(){var _13l=B(_12R(_13j,_aU,_104,_aU)),_13m=B(_12R(_13g,_aU,_104,_aU)),_13n=B(_12R(_13l.a,_13l.b,_13m.a,_13m.b));return B(_134(_12y,_13n.a,_13n.b));});return new T2(0,new T(function(){return B(_cu(_13h,_13k));}),new T(function(){return B(_eN(_13j,B(_12A(_105,B(_oe(_13k,_104)),_13g))));}));},_13o=function(_13p,_){var _13q=__get(_13p,0),_13r=__get(_13p,1),_13s=Number(_13q),_13t=jsTrunc(_13s),_13u=Number(_13r),_13v=jsTrunc(_13u);return new T2(0,_13t,_13v);},_13w=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_13x=660865024,_13y=465661287,_13z=new T2(1,_13y,_S),_13A=new T2(1,_13x,_13z),_13B=new T(function(){return B(_ZX(_wu,_13A));}),_13C=function(_){var _13D=__app0(E(_13w)),_13E=B(_13o(_13D,_));return new T(function(){var _13F=E(_13E);if(!B(_cm(_13B,_12z))){return B(_cu(B(_oe(B(_aQ(E(_13F.a))),_104)),B(_110(B(_oe(B(_oe(B(_aQ(E(_13F.b))),_104)),_104)),_13B))));}else{return E(_9T);}});},_13G=new T(function(){return B(err(_st));}),_13H=new T(function(){return B(err(_sr));}),_13I=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_13J=new T1(0,1),_13K=new T1(0,10),_13L=function(_13M){while(1){var _13N=E(_13M);if(!_13N._){_13M=new T1(1,I_fromInt(_13N.a));continue;}else{return new F(function(){return I_toString(_13N.a);});}}},_13O=function(_13P,_13Q){return new F(function(){return _q(fromJSStr(B(_13L(_13P))),_13Q);});},_13R=new T1(0,0),_13S=function(_13T,_13U,_13V){if(_13T<=6){return new F(function(){return _13O(_13U,_13V);});}else{if(!B(_d6(_13U,_13R))){return new F(function(){return _13O(_13U,_13V);});}else{return new T2(1,_z,new T(function(){return B(_q(fromJSStr(B(_13L(_13U))),new T2(1,_y,_13V)));}));}}},_13W=function(_13X){return new F(function(){return _13S(0,_13X,_S);});},_13Y=new T(function(){return B(_cm(_13K,_12z));}),_13Z=function(_140){while(1){if(!B(_cm(_140,_12z))){if(!E(_13Y)){if(!B(_cm(B(_11o(_140,_13K)),_12z))){return new F(function(){return _13W(_140);});}else{var _141=B(_110(_140,_13K));_140=_141;continue;}}else{return E(_9T);}}else{return __Z;}}},_142=46,_143=48,_144=function(_145,_146,_147){if(!B(_d6(_147,_12z))){var _148=B(A1(_145,_147));if(!B(_cm(_148,_12z))){var _149=B(_11b(_147,_148)),_14a=_149.b,_14b=new T(function(){var _14c=Math.log(B(_fL(_148)))/Math.log(10),_14d=_14c&4294967295,_14e=function(_14f){if(_14f>=0){var _14g=E(_14f);if(!_14g){var _14h=B(_110(B(_eN(B(_cu(B(_oe(_14a,_aU)),_148)),_13J)),_148));}else{var _14h=B(_110(B(_eN(B(_cu(B(_oe(_14a,B(_ou(_13K,_14g)))),_148)),_13J)),_148));}var _14i=function(_14j){var _14k=B(_13S(0,_14h,_S)),_14l=_14f-B(_ms(_14k,0))|0;if(0>=_14l){if(!E(_146)){return E(_14k);}else{return new F(function(){return _13Z(_14h);});}}else{var _14m=new T(function(){if(!E(_146)){return E(_14k);}else{return B(_13Z(_14h));}}),_14n=function(_14o){var _14p=E(_14o);return (_14p==1)?E(new T2(1,_143,_14m)):new T2(1,_143,new T(function(){return B(_14n(_14p-1|0));}));};return new F(function(){return _14n(_14l);});}};if(!E(_146)){var _14q=B(_14i(_));return (_14q._==0)?__Z:new T2(1,_142,_14q);}else{if(!B(_cm(_14h,_12z))){var _14r=B(_14i(_));return (_14r._==0)?__Z:new T2(1,_142,_14r);}else{return __Z;}}}else{return E(_pq);}};if(_14d>=_14c){return B(_14e(_14d));}else{return B(_14e(_14d+1|0));}},1);return new F(function(){return _q(B(_13S(0,_149.a,_S)),_14b);});}else{return E(_9T);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_144(_145,_146,B(_fs(_147))));}));});}},_14s=function(_14t,_14u,_){var _14v=B(_13C(_)),_14w=new T(function(){var _14x=new T(function(){var _14y=new T(function(){var _14z=B(_q(B(_144(_105,_wu,B(_13i(_14v)).b)),_107));if(!_14z._){return E(_RV);}else{var _14A=B(_RQ(_14z.a,_14z.b));if(!_14A._){return B(_10c(_S,_S,_Tn));}else{var _14B=_14A.a,_14C=E(_14A.b);if(!_14C._){return B(_10c(new T2(1,_14B,_S),_S,_Tn));}else{var _14D=E(_14B),_14E=new T(function(){var _14F=B(_H5(46,_14C.a,_14C.b));return new T2(0,_14F.a,_14F.b);});if(E(_14D)==46){return B(_10c(_S,new T2(1,new T(function(){return E(E(_14E).a);}),new T(function(){return E(E(_14E).b);})),_Tn));}else{return B(_10c(new T2(1,_14D,new T(function(){return E(E(_14E).a);})),new T(function(){return E(E(_14E).b);}),_Tn));}}}}}),_14G=B(_Gd(B(_sy(_13I,_14y))));if(!_14G._){return E(_13H);}else{if(!E(_14G.b)._){return B(_pN(3,B(_A(0,E(_14G.a)+(imul(E(_14u),E(_14t)-1|0)|0)|0,_S))));}else{return E(_13G);}}}),_14H=B(_Gd(B(_sy(_13I,_14x))));if(!_14H._){return E(_13H);}else{if(!E(_14H.b)._){return E(_14H.a);}else{return E(_13G);}}});return new T2(0,new T(function(){return B(_au(_14w,_14t));}),_14w);},_14I=function(_14J,_14K){while(1){var _14L=E(_14K);if(!_14L._){return __Z;}else{var _14M=_14L.b,_14N=E(_14J);if(_14N==1){return E(_14M);}else{_14J=_14N-1|0;_14K=_14M;continue;}}}},_14O=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_14P=new T(function(){return B(err(_14O));}),_14Q=0,_14R=function(_14S,_14T,_14U){return new F(function(){return _A(E(_14S),E(_14T),_14U);});},_14V=function(_14W,_14X){return new F(function(){return _A(0,E(_14W),_14X);});},_14Y=function(_14Z,_150){return new F(function(){return _2v(_14V,_14Z,_150);});},_151=new T3(0,_14R,_6A,_14Y),_152=0,_153=new T(function(){return B(unCStr(" out of range "));}),_154=new T(function(){return B(unCStr("}.index: Index "));}),_155=new T(function(){return B(unCStr("Ix{"));}),_156=new T2(1,_y,_S),_157=new T2(1,_y,_156),_158=0,_159=function(_15a){return E(E(_15a).a);},_15b=function(_15c,_15d,_15e,_15f,_15g){var _15h=new T(function(){var _15i=new T(function(){var _15j=new T(function(){var _15k=new T(function(){var _15l=new T(function(){return B(A3(_sd,_6w,new T2(1,new T(function(){return B(A3(_159,_15e,_158,_15f));}),new T2(1,new T(function(){return B(A3(_159,_15e,_158,_15g));}),_S)),_157));});return B(_q(_153,new T2(1,_z,new T2(1,_z,_15l))));});return B(A(_159,[_15e,_152,_15d,new T2(1,_y,_15k)]));});return B(_q(_154,new T2(1,_z,_15j)));},1);return B(_q(_15c,_15i));},1);return new F(function(){return err(B(_q(_155,_15h)));});},_15m=function(_15n,_15o,_15p,_15q,_15r){return new F(function(){return _15b(_15n,_15o,_15r,_15p,_15q);});},_15s=function(_15t,_15u,_15v,_15w){var _15x=E(_15v);return new F(function(){return _15m(_15t,_15u,_15x.a,_15x.b,_15w);});},_15y=function(_15z,_15A,_15B,_15C){return new F(function(){return _15s(_15C,_15B,_15A,_15z);});},_15D=new T(function(){return B(unCStr("Int"));}),_15E=function(_15F,_15G,_15H){return new F(function(){return _15y(_151,new T2(0,_15G,_15H),_15F,_15D);});},_15I=new T(function(){return B(unCStr("Negative range size"));}),_15J=new T(function(){return B(err(_15I));}),_15K=function(_15L){var _15M=B(A1(_15L,_));return E(_15M);},_15N=function(_15O,_15P,_15Q,_){var _15R=E(_15O);if(!_15R){return new T2(0,_S,_15P);}else{var _15S=new T(function(){return B(_ms(_15Q,0))-1|0;}),_15T=B(_14s(new T(function(){return E(_15S)+1|0;}),_15P,_)),_15U=E(_15T),_15V=_15U.a,_15W=_15U.b,_15X=new T(function(){var _15Y=E(_15V);if(B(_ms(_15Q,0))>=(_15Y+1|0)){var _15Z=new T(function(){var _160=_15Y+1|0;if(_160>0){return B(_14I(_160,_15Q));}else{return E(_15Q);}});if(0>=_15Y){return E(_15Z);}else{var _161=function(_162,_163){var _164=E(_162);if(!_164._){return E(_15Z);}else{var _165=_164.a,_166=E(_163);return (_166==1)?new T2(1,_165,_15Z):new T2(1,_165,new T(function(){return B(_161(_164.b,_166-1|0));}));}};return B(_161(_15Q,_15Y));}}else{return E(_15Q);}}),_167=B(_15N(_15R-1|0,_15W,_15X,_)),_168=new T(function(){var _169=function(_){var _16a=E(_15S),_16b=function(_16c){if(_16c>=0){var _16d=newArr(_16c,_14P),_16e=_16d,_16f=E(_16c);if(!_16f){return new T4(0,E(_14Q),E(_16a),0,_16e);}else{var _16g=function(_16h,_16i,_){while(1){var _16j=E(_16h);if(!_16j._){return E(_);}else{var _=_16e[_16i]=_16j.a;if(_16i!=(_16f-1|0)){var _16k=_16i+1|0;_16h=_16j.b;_16i=_16k;continue;}else{return E(_);}}}},_=B(_16g(_15Q,0,_));return new T4(0,E(_14Q),E(_16a),_16f,_16e);}}else{return E(_15J);}};if(0>_16a){return new F(function(){return _16b(0);});}else{return new F(function(){return _16b(_16a+1|0);});}},_16l=B(_15K(_169)),_16m=E(_16l.a),_16n=E(_16l.b),_16o=E(_15V);if(_16m>_16o){return B(_15E(_16o,_16m,_16n));}else{if(_16o>_16n){return B(_15E(_16o,_16m,_16n));}else{return E(_16l.d[_16o-_16m|0]);}}});return new T2(0,new T2(1,_168,new T(function(){return B(_sj(_167));})),_15W);}},_16p=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_16q=function(_16r,_16s,_16t,_16u,_){var _16v=__app1(E(_gG),_16u),_16w=__app3(E(_16p),_16u,E(_16r),E(_16s)),_16x=B(A2(_16t,_16u,_)),_16y=__app1(E(_gF),_16u);return new F(function(){return _gE(_);});},_16z=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_16A=function(_16B,_16C,_16D,_16E,_){var _16F=__app4(E(_16z),_16E,_16B,_16C,_16D);return new F(function(){return _gE(_);});},_16G=2,_16H=function(_16I,_16J,_16K,_16L,_16M,_16N,_){var _16O=function(_16P,_){return new F(function(){return _16q(_16G,_16G,function(_16Q,_){return new F(function(){return _16A(B(_6Q(_16J,E(_16N))),0,0,E(_16Q),_);});},E(_16P),_);});};return new F(function(){return _gR(new T(function(){return E(_16K)-E(_16L)*16;},1),new T(function(){return E(_16M)*20;},1),_16O,_16I,_);});},_16R=new T(function(){return B(_6Q(_j3,1));}),_16S=1,_16T=function(_16U){return E(_16U).d;},_16V=function(_16W,_16X,_16Y,_16Z,_170,_171,_){var _172=new T(function(){return E(E(_171).r);}),_173=new T(function(){return E(E(_172).a);}),_174=new T(function(){if(!B(_an(E(_171).s,10))){var _175=E(E(_172).b);if(!(_175%2)){return _175+1|0;}else{return _175-1|0;}}else{return E(E(_172).b);}}),_176=new T(function(){var _177=E(_171);return {_:0,a:E(_177.a),b:E(_177.b),c:E(_177.c),d:E(_177.d),e:E(_177.e),f:E(_177.f),g:E(_177.g),h:E(_177.h),i:_177.i,j:_177.j,k:_177.k,l:_177.l,m:E(_177.m),n:_177.n,o:E(_177.o),p:E(_177.p),q:_177.q,r:E(new T2(0,_173,_174)),s:_177.s,t:E(_177.t),u:E(_177.u)};}),_178=new T(function(){return E(E(_176).a);}),_179=new T(function(){return E(E(_176).b);}),_17a=new T(function(){return E(E(_179).a);}),_17b=new T(function(){var _17c=E(_16Y)/16,_17d=_17c&4294967295;if(_17c>=_17d){return _17d-2|0;}else{return (_17d-1|0)-2|0;}}),_17e=B(_np(_16W,_16X,new T(function(){return B(_b3(_17b,_17a));}),_nO,new T(function(){return E(E(_178).b);}),_)),_17f=new T(function(){return E(E(E(_176).a).a);}),_17g=B(A(_mN,[_16W,new T(function(){if(E(E(_178).e)==32){return E(_nM);}else{return E(_nN);}}),new T(function(){return ((E(E(_17f).a)+E(_17b)|0)-E(_17a)|0)+1|0;},1),new T(function(){return (E(E(_17f).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_16T(_178));}),_S),_])),_17h=E(_176),_17i=_17h.c,_17j=_17h.k,_17k=E(_17h.t),_17l=new T(function(){var _17m=E(_16Y)/28,_17n=_17m&4294967295;if(_17m>=_17n){return (_17n-1|0)+_17j|0;}else{return ((_17n-1|0)-1|0)+_17j|0;}}),_17o=new T(function(){return (2+E(E(_179).b)|0)+3|0;}),_17p=new T2(0,_16W,_16X),_17q=function(_){var _17r=function(_){var _17s=function(_){var _17t=B(_16H(_16W,new T(function(){return E(E(_170).b);},1),_16Y,new T(function(){return E(_17a)+10|0;},1),_nO,new T(function(){return (imul(E(_173),8)|0)+E(_174)|0;},1),_));return _17h;};if(!E(_17h.p)._){return new F(function(){return _17s(_);});}else{var _17u=B(A(_mN,[_16W,_16R,_16S,_16S,B(_A(0,_17h.q,_S)),_]));return new F(function(){return _17s(_);});}};if(!E(_17k.g)){return new F(function(){return _17r(_);});}else{var _17v=B(_j9(_17p,_16Z,0,_17o,_17l,_17o,B(_V1(_17i,new T(function(){return B(_6d(_sj,_17h.m));},1),_17h.n)),_));return new F(function(){return _17r(_);});}};if(!E(_17k.c)){var _17w=B(_j9(_17p,_16Z,0,_17o,_17l,_17o,_17i,_));return new F(function(){return _17q(_);});}else{return new F(function(){return _17q(_);});}},_17x=function(_17y,_17z){while(1){var _17A=E(_17y);if(!_17A._){return E(_17z);}else{_17y=_17A.b;_17z=_17A.a;continue;}}},_17B=function(_17C,_17D,_17E){return new F(function(){return _17x(_17D,_17C);});},_17F=function(_17G,_17H){while(1){var _17I=E(_17G);if(!_17I._){return E(_17H);}else{_17G=_17I.b;_17H=_17I.a;continue;}}},_17J=function(_17K,_17L,_17M){return new F(function(){return _17F(_17L,_17K);});},_17N=function(_17O,_17P){while(1){var _17Q=E(_17P);if(!_17Q._){return __Z;}else{var _17R=_17Q.b,_17S=E(_17O);if(_17S==1){return E(_17R);}else{_17O=_17S-1|0;_17P=_17R;continue;}}}},_17T=function(_17U,_17V){var _17W=new T(function(){var _17X=_17U+1|0;if(_17X>0){return B(_17N(_17X,_17V));}else{return E(_17V);}});if(0>=_17U){return E(_17W);}else{var _17Y=function(_17Z,_180){var _181=E(_17Z);if(!_181._){return E(_17W);}else{var _182=_181.a,_183=E(_180);return (_183==1)?new T2(1,_182,_17W):new T2(1,_182,new T(function(){return B(_17Y(_181.b,_183-1|0));}));}};return new F(function(){return _17Y(_17V,_17U);});}},_184=new T(function(){return B(unCStr(":"));}),_185=function(_186){var _187=E(_186);if(!_187._){return __Z;}else{var _188=new T(function(){return B(_q(_184,new T(function(){return B(_185(_187.b));},1)));},1);return new F(function(){return _q(_187.a,_188);});}},_189=function(_18a,_18b){var _18c=new T(function(){return B(_q(_184,new T(function(){return B(_185(_18b));},1)));},1);return new F(function(){return _q(_18a,_18c);});},_18d=function(_18e){return new F(function(){return _Lh("Check.hs:173:7-35|(co : na : xs)");});},_18f=new T(function(){return B(_18d(_));}),_18g=new T(function(){return B(err(_sr));}),_18h=new T(function(){return B(err(_st));}),_18i=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_18j=0,_18k=new T(function(){return B(unCStr("!"));}),_18l=function(_18m,_18n){var _18o=E(_18n);if(!_18o._){return E(_18f);}else{var _18p=E(_18o.b);if(!_18p._){return E(_18f);}else{var _18q=E(_18o.a),_18r=new T(function(){var _18s=B(_H5(58,_18p.a,_18p.b));return new T2(0,_18s.a,_18s.b);}),_18t=function(_18u,_18v,_18w){var _18x=function(_18y){if((_18m+1|0)!=_18y){return new T3(0,_18m+1|0,_18v,_18o);}else{var _18z=E(_18w);return (_18z._==0)?new T3(0,_18j,_18v,_S):new T3(0,_18j,_18v,new T(function(){var _18A=B(_189(_18z.a,_18z.b));if(!_18A._){return E(_RV);}else{return B(_RQ(_18A.a,_18A.b));}}));}};if(!B(_qO(_18u,_18k))){var _18B=B(_Gd(B(_sy(_18i,_18u))));if(!_18B._){return E(_18g);}else{if(!E(_18B.b)._){return new F(function(){return _18x(E(_18B.a));});}else{return E(_18h);}}}else{return new F(function(){return _18x( -1);});}};if(E(_18q)==58){return new F(function(){return _18t(_S,new T(function(){return E(E(_18r).a);}),new T(function(){return E(E(_18r).b);}));});}else{var _18C=E(_18r),_18D=E(_18C.b);if(!_18D._){return E(_18f);}else{return new F(function(){return _18t(new T2(1,_18q,_18C.a),_18D.a,_18D.b);});}}}}},_18E=function(_18F,_18G){while(1){var _18H=E(_18G);if(!_18H._){return __Z;}else{var _18I=_18H.b,_18J=E(_18F);if(_18J==1){return E(_18I);}else{_18F=_18J-1|0;_18G=_18I;continue;}}}},_18K=function(_18L,_18M,_18N){var _18O=new T2(1,_18M,new T(function(){var _18P=_18L+1|0;if(_18P>0){return B(_18E(_18P,_18N));}else{return E(_18N);}}));if(0>=_18L){return E(_18O);}else{var _18Q=function(_18R,_18S){var _18T=E(_18R);if(!_18T._){return E(_18O);}else{var _18U=_18T.a,_18V=E(_18S);return (_18V==1)?new T2(1,_18U,_18O):new T2(1,_18U,new T(function(){return B(_18Q(_18T.b,_18V-1|0));}));}};return new F(function(){return _18Q(_18N,_18L);});}},_18W=new T2(0,_Ry,_E9),_18X=function(_18Y,_18Z,_190){while(1){var _191=E(_190);if(!_191._){return E(_18W);}else{var _192=_191.b,_193=E(_191.a),_194=E(_193.a);if(_18Y!=E(_194.a)){_190=_192;continue;}else{if(_18Z!=E(_194.b)){_190=_192;continue;}else{return E(_193.b);}}}}},_195=function(_196,_197){while(1){var _198=E(_197);if(!_198._){return __Z;}else{var _199=_198.b,_19a=E(_196);if(_19a==1){return E(_199);}else{_196=_19a-1|0;_197=_199;continue;}}}},_19b=function(_19c,_19d,_19e){var _19f=E(_19c);if(_19f==1){return E(_19e);}else{return new F(function(){return _195(_19f-1|0,_19e);});}},_19g=function(_19h,_19i,_19j){return new T2(1,new T(function(){if(0>=_19h){return __Z;}else{return B(_pN(_19h,new T2(1,_19i,_19j)));}}),new T(function(){if(_19h>0){return B(_19k(_19h,B(_19b(_19h,_19i,_19j))));}else{return B(_19g(_19h,_19i,_19j));}}));},_19k=function(_19l,_19m){var _19n=E(_19m);if(!_19n._){return __Z;}else{var _19o=_19n.a,_19p=_19n.b;return new T2(1,new T(function(){if(0>=_19l){return __Z;}else{return B(_pN(_19l,_19n));}}),new T(function(){if(_19l>0){return B(_19k(_19l,B(_19b(_19l,_19o,_19p))));}else{return B(_19g(_19l,_19o,_19p));}}));}},_19q=function(_19r,_19s,_19t){var _19u=_19s-1|0;if(0<=_19u){var _19v=E(_19r),_19w=function(_19x){var _19y=new T(function(){if(_19x!=_19u){return B(_19w(_19x+1|0));}else{return __Z;}}),_19z=function(_19A){var _19B=E(_19A);return (_19B._==0)?E(_19y):new T2(1,new T(function(){var _19C=E(_19t);if(!_19C._){return E(_18W);}else{var _19D=_19C.b,_19E=E(_19C.a),_19F=E(_19E.a),_19G=E(_19B.a);if(_19G!=E(_19F.a)){return B(_18X(_19G,_19x,_19D));}else{if(_19x!=E(_19F.b)){return B(_18X(_19G,_19x,_19D));}else{return E(_19E.b);}}}}),new T(function(){return B(_19z(_19B.b));}));};return new F(function(){return _19z(B(_8r(0,_19v-1|0)));});};return new F(function(){return _19k(_19v,B(_19w(0)));});}else{return __Z;}},_19H=function(_19I){return new F(function(){return _Lh("Check.hs:72:21-47|(l : r : _)");});},_19J=new T(function(){return B(_19H(_));}),_19K=61,_19L=function(_19M,_19N){while(1){var _19O=E(_19M);if(!_19O._){return E(_19N);}else{_19M=_19O.b;_19N=_19O.a;continue;}}},_19P=function(_19Q,_19R,_19S){return new F(function(){return _19L(_19R,_19Q);});},_19T=function(_19U,_19V){var _19W=E(_19V);if(!_19W._){return new T2(0,_S,_S);}else{var _19X=_19W.a;if(!B(A1(_19U,_19X))){var _19Y=new T(function(){var _19Z=B(_19T(_19U,_19W.b));return new T2(0,_19Z.a,_19Z.b);});return new T2(0,new T2(1,_19X,new T(function(){return E(E(_19Y).a);})),new T(function(){return E(E(_19Y).b);}));}else{return new T2(0,_S,_19W);}}},_1a0=function(_1a1,_1a2){while(1){var _1a3=E(_1a2);if(!_1a3._){return __Z;}else{if(!B(A1(_1a1,_1a3.a))){return E(_1a3);}else{_1a2=_1a3.b;continue;}}}},_1a4=function(_1a5){var _1a6=_1a5>>>0;if(_1a6>887){var _1a7=u_iswspace(_1a5);return (E(_1a7)==0)?false:true;}else{var _1a8=E(_1a6);return (_1a8==32)?true:(_1a8-9>>>0>4)?(E(_1a8)==160)?true:false:true;}},_1a9=function(_1aa){return new F(function(){return _1a4(E(_1aa));});},_1ab=function(_1ac){var _1ad=B(_1a0(_1a9,_1ac));if(!_1ad._){return __Z;}else{var _1ae=new T(function(){var _1af=B(_19T(_1a9,_1ad));return new T2(0,_1af.a,_1af.b);});return new T2(1,new T(function(){return E(E(_1ae).a);}),new T(function(){return B(_1ab(E(_1ae).b));}));}},_1ag=function(_1ah){if(!B(_4A(_h6,_19K,_1ah))){return new T2(0,_1ah,_S);}else{var _1ai=new T(function(){var _1aj=E(_1ah);if(!_1aj._){return E(_19J);}else{var _1ak=E(_1aj.b);if(!_1ak._){return E(_19J);}else{var _1al=_1ak.a,_1am=_1ak.b,_1an=E(_1aj.a);if(E(_1an)==61){return new T2(0,_S,new T(function(){return E(B(_H5(61,_1al,_1am)).a);}));}else{var _1ao=B(_H5(61,_1al,_1am)),_1ap=E(_1ao.b);if(!_1ap._){return E(_19J);}else{return new T2(0,new T2(1,_1an,_1ao.a),_1ap.a);}}}}});return new T2(0,new T(function(){var _1aq=B(_1ab(E(_1ai).a));if(!_1aq._){return __Z;}else{return B(_19P(_1aq.a,_1aq.b,_Tn));}}),new T(function(){var _1ar=B(_1ab(E(_1ai).b));if(!_1ar._){return __Z;}else{return E(_1ar.a);}}));}},_1as=function(_1at,_1au){return new F(function(){return _17T(E(_1at),_1au);});},_1av=function(_1aw){var _1ax=E(_1aw);if(!_1ax._){return new T2(0,_S,_S);}else{var _1ay=E(_1ax.a),_1az=new T(function(){var _1aA=B(_1av(_1ax.b));return new T2(0,_1aA.a,_1aA.b);});return new T2(0,new T2(1,_1ay.a,new T(function(){return E(E(_1az).a);})),new T2(1,_1ay.b,new T(function(){return E(E(_1az).b);})));}},_1aB=new T(function(){return B(unCStr("\u306a\u305c \u308f\u305f\u3057\u306f \u3053\u3053\u306b\u3090\u3066\u3002\n\u306a\u305c \u308f\u305f\u3057\u306f \u3053\u306e\u3084\u3046\u306b\u601d\u3075\u306e\u3060\u3089\u3046\u3002\n\u306a\u3093\u306e\u305f\u3081\u306b \u308f\u305f\u3057\u306f\u3002\n\u751f\u304d\u3066\u3090\u308b\u306e\u3060\u3089\u3046\u30fb\u30fb\u30fb\u3002 {e.X.m1:s0}{sm}"));}),_1aC=new T(function(){return B(unCStr("s0_2"));}),_1aD=new T(function(){return B(unCStr("\n\u7406\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl2}{e.c0&s2.m1:s2}"));}),_1aE=new T2(0,_1aC,_1aD),_1aF=new T(function(){return B(unCStr("s0_3"));}),_1aG=new T(function(){return B(unCStr("\n\u53f2\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl3}{e.c0&s3.m1:s3}"));}),_1aH=new T2(0,_1aF,_1aG),_1aI=new T(function(){return B(unCStr("s0_n"));}),_1aJ=new T(function(){return B(unCStr("\n\u4ed6\u306e\u6249\u3082\u898b\u3066\u307f\u3084\u3046\u304b"));}),_1aK=new T2(0,_1aI,_1aJ),_1aL=new T(function(){return B(unCStr("s4"));}),_1aM=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_1aN=new T2(0,_1aL,_1aM),_1aO=new T2(1,_1aN,_S),_1aP=new T(function(){return B(unCStr("sc3"));}),_1aQ=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002"));}),_1aR=new T2(0,_1aP,_1aQ),_1aS=new T2(1,_1aR,_1aO),_1aT=new T(function(){return B(unCStr("s3"));}),_1aU=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066 {rk.1.z.abc.sc3}"));}),_1aV=new T2(0,_1aT,_1aU),_1aW=new T2(1,_1aV,_1aS),_1aX=new T(function(){return B(unCStr("s2"));}),_1aY=new T(function(){return B(unCStr("\n\u3082\u306e\u3054\u3068\u306e\u7b4b\uff1a\u3059\u3058\uff1a\u9053\uff1a\u307f\u3061\uff1a\u304c \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u3067\u3059\u3002\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306e\u3053\u3068 \u5618\uff1a\u3046\u305d\uff1a\u306e\u3053\u3068\u3002\n\u6b63\uff1a\u305f\u3060\uff1a\u3057\u3044\u3053\u3068 \u9593\uff1a\u307e\uff1a\u9055\uff1a\u3061\u304c\uff1a\u3063\u3066\u3090\u308b\u3053\u3068\u3002\n\u305d\u308c\u3092 \u306f\u3063\u304d\u308a\u3055\u305b\u308b\u306e\u304c \u7406 \u3067\u3059"));}),_1aZ=new T2(0,_1aX,_1aY),_1b0=new T2(1,_1aZ,_1aW),_1b1=new T(function(){return B(unCStr("s1c"));}),_1b2=new T(function(){return B(unCStr("\n\u6249\u304c\u958b\u304b\u308c\u305f\u3084\u3046\u3067\u3059 {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"));}),_1b3=new T2(0,_1b1,_1b2),_1b4=new T2(1,_1b3,_1b0),_1b5=new T(function(){return B(unCStr("s104"));}),_1b6=new T(function(){return B(unCStr("\n\u706b\uff1a\u3072\uff1a(\uff11)\u3068\u6c34\uff1a\u307f\u3065\uff1a(\uff12)\u3092\u5408\u306f\u305b\u308b\u3068 \u3072\u307f\u3064(\uff13) \u306b\u306a\u308a\u307e\u3059\u3002\n\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u306f \u307e\u3046\u958b\uff1a\u3072\u3089\uff1a\u304b\u308c\u308b\u3067\u305b\u3046\u3002\n\u9375\uff1a\u304b\u304e\uff1a\u3092\u624b\u306b\u5165\u308c\u305f\u306e\u3067\u3059\u304b\u3089 {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"));}),_1b7=new T2(0,_1b5,_1b6),_1b8=new T2(1,_1b7,_1b4),_1b9=new T(function(){return B(unCStr("s103"));}),_1ba=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u304c\u5b58\u5728\u3059\u308b\u9650\uff1a\u304b\u304e\uff1a\u308a \u6578\u306f\u7121\uff1a\u3080\uff1a\u9650\uff1a\u3052\u3093\uff1a\u306b\u3064\u304f\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3053\u308c\u3089\u304c\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u306b\u7f6e\uff1a\u304a\uff1a\u304b\u308c\u3066\u3090\u305f\u4f4d\uff1a\u3044\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u5165\uff1a\u3044\uff1a\u308c\u66ff\uff1a\u304b\uff1a\u3078\u305f\u3089 \u4f55\uff1a\u306a\u306b\uff1a\u304b\u8d77\uff1a\u304a\uff1a\u3053\u308a\u3055\u3046\u3067\u3059 {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"));}),_1bb=new T2(0,_1b9,_1ba),_1bc=new T2(1,_1bb,_1b8),_1bd=new T(function(){return B(unCStr("s102"));}),_1be=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u3068\u3044\u3075\u5b58\u5728\u3068 \uff1c\u7121\u3044\uff1e\u3068\u3044\u3075\u5b58\u5728\u304c\u3067\u304d\u307e\u3057\u305f\u3002\n\uff1c\u5b58\u5728\uff1e\u3092 1 \u3068\u3059\u308b\u306a\u3089 \u3053\u308c\u3089\u3092\u5408\u306f\u305b\u305f\u540d\u524d\u3092\u3064\u304f\u308a\u307e\u305b\u3046 {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"));}),_1bf=new T2(0,_1bd,_1be),_1bg=new T2(1,_1bf,_1bc),_1bh=new T(function(){return B(unCStr("s1_3"));}),_1bi=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u5206\u3051\u305f\u3068\u601d\uff1a\u304a\u3082\uff1a\u306f\u306a\u3044\u306e\u3067\u3042\u308c\u3070\u3002\n\u305d\u308c\u306f \u5206\u304b\u308c\u3066\u3090\u307e\u305b\u3093"));}),_1bj=new T2(0,_1bh,_1bi),_1bk=new T2(1,_1bj,_1bg),_1bl=new T(function(){return B(unCStr("s1_2"));}),_1bm=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u4e16\u754c\u3092 \u5206\u3051\u3066\n\u300c\u5728\uff1a\u3042\uff1a\u308b\u3002\n\u300c\u7121\uff1a\u306a\uff1a\u3044\u3002\n\u3092\u3064\u304f\u308a\u307e\u3057\u305f\u3002\n\u305d\u308c\u3067\u306f \u3053\u306e \uff1c\u5728\u308b\uff1e\u3092 1 \u3068\u547c\uff1a\u3088\uff1a\u3073\u307e\u305b\u3046 {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"));}),_1bn=new T2(0,_1bl,_1bm),_1bo=new T2(1,_1bn,_1bk),_1bp=new T(function(){return B(unCStr("s101"));}),_1bq=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u3053\u308c\u3092\u53d6\uff1a\u3068\uff1a\u3063\u305f\u306e\u3067 \u305d\u308c\u306f \u307e\u3046\u3053\u3053\u306b\u3042\u308a\u307e\u305b\u3093\u3002\n\u3053\u308c\u306f \u5206\u3051\u305f\u3053\u3068\u306b\u306a\u308a\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_2.\u3044\u3044\u3048,s1_3}"));}),_1br=new T2(0,_1bp,_1bq),_1bs=new T2(1,_1br,_1bo),_1bt=new T(function(){return B(unCStr("s1_1"));}),_1bu=new T(function(){return B(unCStr("\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306b\u5206\u3051\u3089\u308c\u306a\u3044\u306e\u3067\u305b\u3046\u304b"));}),_1bv=new T2(0,_1bt,_1bu),_1bw=new T2(1,_1bv,_1bs),_1bx=new T(function(){return B(unCStr("s1_0"));}),_1by=new T(function(){return B(unCStr("\n\u3067\u306f \u5206\u3051\u3066\u304f\u3060\u3055\u3044 {ct.0.Fr}{d.b0}{e.e0.m0:s101}"));}),_1bz=new T2(0,_1bx,_1by),_1bA=new T2(1,_1bz,_1bw),_1bB=new T(function(){return B(unCStr("s100"));}),_1bC=new T(function(){return B(unCStr("\n\u3053\u308c\u306f \u5206\u3051\u3089\u308c\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_0.\u3044\u3044\u3048,s1_1}"));}),_1bD=new T2(0,_1bB,_1bC),_1bE=new T2(1,_1bD,_1bA),_1bF=new T(function(){return B(unCStr("s1"));}),_1bG=new T(function(){return B(unCStr("\n\u3082\u306e\u3092 \u304b\u305e\u3078\u308b\u306e\u304c \u6578\uff1a\u304b\u305a\uff1a\u3067\u3059\u3002\n\u3082\u3057 \u79c1\u305f\u3061\u304c \u3053\u306e\u4e16\u754c\u3092 \u5206\uff1a\u308f\uff1a\u3051\u3066\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u306a\u3044\u306a\u3089 \u6578\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3084\u3046\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u5206\u3051\u3089\u308c\u3066\u3090\u308b\u304b\u3089 \u6578\u3078\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059 {da}{e.b0.m0:s100}"));}),_1bH=new T2(0,_1bF,_1bG),_1bI=new T2(1,_1bH,_1bE),_1bJ=new T(function(){return B(unCStr("nubatama"));}),_1bK=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1bL=new T2(0,_1bJ,_1bK),_1bM=new T2(1,_1bL,_1bI),_1bN=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1bO=new T(function(){return B(unCStr("msgW"));}),_1bP=new T2(0,_1bO,_1bN),_1bQ=new T2(1,_1bP,_1bM),_1bR=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1bS=new T(function(){return B(unCStr("msgR"));}),_1bT=new T2(0,_1bS,_1bR),_1bU=new T2(1,_1bT,_1bQ),_1bV=new T2(1,_1aK,_1bU),_1bW=new T2(1,_1aH,_1bV),_1bX=new T2(1,_1aE,_1bW),_1bY=new T(function(){return B(unCStr("s0_1"));}),_1bZ=new T(function(){return B(unCStr("\n\u6578\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl1}{e.c0&s1.m1:s1}"));}),_1c0=new T2(0,_1bY,_1bZ),_1c1=new T2(1,_1c0,_1bX),_1c2=new T(function(){return B(unCStr("s0H"));}),_1c3=new T(function(){return B(unCStr("\n\u53f2\uff1a\u3075\u307f\uff1a\u306e\u90e8\u5c4b\u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_3.\u5165\u3089\u306a\u3044,s0_n}"));}),_1c4=new T2(0,_1c2,_1c3),_1c5=new T2(1,_1c4,_1c1),_1c6=new T(function(){return B(unCStr("s0S"));}),_1c7=new T(function(){return B(unCStr("\n\u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u306e\u90e8\u5c4b\u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_2.\u5165\u3089\u306a\u3044,s0_n}"));}),_1c8=new T2(0,_1c6,_1c7),_1c9=new T2(1,_1c8,_1c5),_1ca=new T(function(){return B(unCStr("s0M"));}),_1cb=new T(function(){return B(unCStr("\n\u6578\uff1a\u304b\u305a\uff1a\u306e\u90e8\u5c4b \u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_1.\u5165\u3089\u306a\u3044,s0_n}"));}),_1cc=new T2(0,_1ca,_1cb),_1cd=new T2(1,_1cc,_1c9),_1ce=new T(function(){return B(unCStr("s0"));}),_1cf=new T(function(){return B(unCStr("\n\u4e09\u3064\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u304c\u3042\u308b\u307f\u305f\u3044\u3060 {e.bM.m0:s0M}{e.bS.m0:s0S}{e.bH.m0:s0H}"));}),_1cg=new T2(0,_1ce,_1cf),_1ch=new T2(1,_1cg,_1cd),_1ci=new T(function(){return B(unCStr("initMsg"));}),_1cj=function(_1ck,_1cl){var _1cm=new T(function(){var _1cn=B(_1av(_1ck));return new T2(0,_1cn.a,_1cn.b);}),_1co=function(_1cp){var _1cq=E(_1cp);if(!_1cq._){return E(_1cm);}else{var _1cr=E(_1cq.a),_1cs=new T(function(){return B(_1co(_1cq.b));});return new T2(0,new T2(1,_1cr.a,new T(function(){return E(E(_1cs).a);})),new T2(1,_1cr.b,new T(function(){return E(E(_1cs).b);})));}},_1ct=function(_1cu,_1cv,_1cw){var _1cx=new T(function(){return B(_1co(_1cw));});return new T2(0,new T2(1,_1cu,new T(function(){return E(E(_1cx).a);})),new T2(1,_1cv,new T(function(){return E(E(_1cx).b);})));},_1cy=B(_1ct(_1ci,_1aB,_1ch)),_1cz=_1cy.a;if(!B(_4A(_qd,_1cl,_1cz))){return __Z;}else{return new F(function(){return _6Q(_1cy.b,B(_MD(_qd,_1cl,_1cz)));});}},_1cA=7,_1cB=new T2(0,_1cA,_1cA),_1cC=new T2(1,_1cB,_S),_1cD=5,_1cE=new T2(0,_1cD,_1cD),_1cF=new T2(1,_1cE,_1cC),_1cG=new T2(1,_1cE,_1cF),_1cH=new T2(1,_1cE,_1cG),_1cI=new T2(1,_1cE,_1cH),_1cJ=2,_1cK=4,_1cL=new T2(0,_1cK,_1cJ),_1cM=new T2(1,_1cL,_S),_1cN=new T2(0,_1cJ,_1cJ),_1cO=new T2(1,_1cN,_1cM),_1cP=new T2(1,_1cN,_1cO),_1cQ=new T2(1,_1cN,_1cP),_1cR=0,_1cS=new T2(0,_1cJ,_1cR),_1cT=new T2(1,_1cS,_1cQ),_1cU=new T(function(){return B(unCStr("Int"));}),_1cV=function(_1cW,_1cX,_1cY){return new F(function(){return _15y(_151,new T2(0,_1cX,_1cY),_1cW,_1cU);});},_1cZ=new T(function(){return B(unCStr("msgR"));}),_1d0=new T(function(){return B(_1cj(_S,_1cZ));}),_1d1=new T(function(){return B(unCStr("msgW"));}),_1d2=new T(function(){return B(_1cj(_S,_1d1));}),_1d3=function(_1d4){var _1d5=E(_1d4);return 0;},_1d6=new T(function(){return B(unCStr("@@@@@"));}),_1d7=new T(function(){var _1d8=E(_1d6);if(!_1d8._){return E(_ng);}else{return E(_1d8.a);}}),_1d9=new T2(0,_1cJ,_1cK),_1da=72,_1db=new T2(0,_1da,_Ef),_1dc=new T2(0,_1d9,_1db),_1dd=new T2(1,_1dc,_S),_1de=77,_1df=new T2(0,_1de,_Ef),_1dg=new T2(0,_1cL,_1df),_1dh=new T2(1,_1dg,_1dd),_1di=83,_1dj=new T2(0,_1di,_Ef),_1dk=new T2(0,_1cR,_1cJ),_1dl=new T2(0,_1dk,_1dj),_1dm=new T2(1,_1dl,_1dh),_1dn=new T(function(){return B(_19q(_1cD,5,_1dm));}),_1do=new T(function(){return B(_Lh("Check.hs:142:22-33|(ch : po)"));}),_1dp=new T(function(){return B(_e6("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1dq=48,_1dr=new T2(0,_1dq,_Ef),_1ds=new T2(0,_1cS,_1dr),_1dt=new T2(1,_1ds,_S),_1du=122,_1dv=new T2(0,_1du,_Ef),_1dw=new T2(0,_1cR,_1cR),_1dx=new T2(0,_1dw,_1dv),_1dy=61,_1dz=new T2(0,_1dy,_Ef),_1dA=1,_1dB=new T2(0,_1dA,_1cR),_1dC=new T2(0,_1dB,_1dz),_1dD=97,_1dE=new T2(0,_1dD,_E9),_1dF=new T2(0,_1cR,_1cK),_1dG=new T2(0,_1dF,_1dE),_1dH=98,_1dI=new T2(0,_1dH,_E9),_1dJ=new T2(0,_1d9,_1dI),_1dK=99,_1dL=new T2(0,_1dK,_E9),_1dM=new T2(0,_1cK,_1cK),_1dN=new T2(0,_1dM,_1dL),_1dO=new T2(1,_1dN,_S),_1dP=new T2(1,_1dJ,_1dO),_1dQ=new T2(1,_1dG,_1dP),_1dR=new T2(1,_1dC,_1dQ),_1dS=new T2(1,_1dx,_1dR),_1dT=new T2(1,_S,_S),_1dU=new T2(1,_1dS,_1dT),_1dV=new T2(1,_S,_1dU),_1dW=new T2(1,_1dt,_1dV),_1dX=new T2(1,_1dm,_1dW),_1dY=function(_1dZ){var _1e0=E(_1dZ);if(!_1e0._){return __Z;}else{var _1e1=_1e0.b,_1e2=E(_1e0.a),_1e3=_1e2.b,_1e4=E(_1e2.a),_1e5=function(_1e6){if(E(_1e4)==32){return new T2(1,_1e2,new T(function(){return B(_1dY(_1e1));}));}else{switch(E(_1e3)){case 0:return new T2(1,new T2(0,_1e4,_E9),new T(function(){return B(_1dY(_1e1));}));case 1:return new T2(1,new T2(0,_1e4,_EK),new T(function(){return B(_1dY(_1e1));}));case 2:return new T2(1,new T2(0,_1e4,_El),new T(function(){return B(_1dY(_1e1));}));case 3:return new T2(1,new T2(0,_1e4,_Er),new T(function(){return B(_1dY(_1e1));}));case 4:return new T2(1,new T2(0,_1e4,_Ex),new T(function(){return B(_1dY(_1e1));}));case 5:return new T2(1,new T2(0,_1e4,_EY),new T(function(){return B(_1dY(_1e1));}));case 6:return new T2(1,new T2(0,_1e4,_ER),new T(function(){return B(_1dY(_1e1));}));case 7:return new T2(1,new T2(0,_1e4,_EK),new T(function(){return B(_1dY(_1e1));}));default:return new T2(1,new T2(0,_1e4,_ED),new T(function(){return B(_1dY(_1e1));}));}}};if(E(_1e4)==32){return new F(function(){return _1e5(_);});}else{switch(E(_1e3)){case 0:return new T2(1,new T2(0,_1e4,_ED),new T(function(){return B(_1dY(_1e1));}));case 1:return new F(function(){return _1e5(_);});break;case 2:return new F(function(){return _1e5(_);});break;case 3:return new F(function(){return _1e5(_);});break;case 4:return new F(function(){return _1e5(_);});break;case 5:return new F(function(){return _1e5(_);});break;case 6:return new F(function(){return _1e5(_);});break;case 7:return new F(function(){return _1e5(_);});break;default:return new F(function(){return _1e5(_);});}}}},_1e7=function(_1e8){var _1e9=E(_1e8);return (_1e9._==0)?__Z:new T2(1,new T(function(){return B(_1dY(_1e9.a));}),new T(function(){return B(_1e7(_1e9.b));}));},_1ea=function(_1eb){var _1ec=E(_1eb);if(!_1ec._){return __Z;}else{var _1ed=_1ec.b,_1ee=E(_1ec.a),_1ef=_1ee.b,_1eg=E(_1ee.a),_1eh=function(_1ei){if(E(_1eg)==32){return new T2(1,_1ee,new T(function(){return B(_1ea(_1ed));}));}else{switch(E(_1ef)){case 0:return new T2(1,new T2(0,_1eg,_E9),new T(function(){return B(_1ea(_1ed));}));case 1:return new T2(1,new T2(0,_1eg,_Ef),new T(function(){return B(_1ea(_1ed));}));case 2:return new T2(1,new T2(0,_1eg,_El),new T(function(){return B(_1ea(_1ed));}));case 3:return new T2(1,new T2(0,_1eg,_Er),new T(function(){return B(_1ea(_1ed));}));case 4:return new T2(1,new T2(0,_1eg,_Ex),new T(function(){return B(_1ea(_1ed));}));case 5:return new T2(1,new T2(0,_1eg,_EY),new T(function(){return B(_1ea(_1ed));}));case 6:return new T2(1,new T2(0,_1eg,_ER),new T(function(){return B(_1ea(_1ed));}));case 7:return new T2(1,new T2(0,_1eg,_Ef),new T(function(){return B(_1ea(_1ed));}));default:return new T2(1,new T2(0,_1eg,_ED),new T(function(){return B(_1ea(_1ed));}));}}};if(E(_1eg)==32){return new F(function(){return _1eh(_);});}else{if(E(_1ef)==8){return new T2(1,new T2(0,_1eg,_E9),new T(function(){return B(_1ea(_1ed));}));}else{return new F(function(){return _1eh(_);});}}}},_1ej=function(_1ek){var _1el=E(_1ek);return (_1el._==0)?__Z:new T2(1,new T(function(){return B(_1ea(_1el.a));}),new T(function(){return B(_1ej(_1el.b));}));},_1em=function(_1en,_1eo,_1ep,_1eq,_1er,_1es,_1et,_1eu,_1ev,_1ew,_1ex,_1ey,_1ez,_1eA,_1eB,_1eC,_1eD,_1eE,_1eF,_1eG,_1eH,_1eI,_1eJ,_1eK,_1eL,_1eM,_1eN,_1eO,_1eP,_1eQ,_1eR,_1eS,_1eT,_1eU,_1eV,_1eW,_1eX,_1eY,_1eZ,_1f0){var _1f1=E(_1eo);if(!_1f1._){return E(_1dp);}else{var _1f2=_1f1.b,_1f3=E(_1f1.a),_1f4=new T(function(){var _1f5=function(_){var _1f6=B(_ms(_1eE,0))-1|0,_1f7=function(_1f8){if(_1f8>=0){var _1f9=newArr(_1f8,_14P),_1fa=_1f9,_1fb=E(_1f8);if(!_1fb){return new T4(0,E(_18j),E(_1f6),0,_1fa);}else{var _1fc=function(_1fd,_1fe,_){while(1){var _1ff=E(_1fd);if(!_1ff._){return E(_);}else{var _=_1fa[_1fe]=_1ff.a;if(_1fe!=(_1fb-1|0)){var _1fg=_1fe+1|0;_1fd=_1ff.b;_1fe=_1fg;continue;}else{return E(_);}}}},_=B(_1fc(_1eE,0,_));return new T4(0,E(_18j),E(_1f6),_1fb,_1fa);}}else{return E(_15J);}};if(0>_1f6){return new F(function(){return _1f7(0);});}else{return new F(function(){return _1f7(_1f6+1|0);});}},_1fh=B(_15K(_1f5)),_1fi=E(_1fh.a),_1fj=E(_1fh.b),_1fk=E(_1en);if(_1fi>_1fk){return B(_1cV(_1fk,_1fi,_1fj));}else{if(_1fk>_1fj){return B(_1cV(_1fk,_1fi,_1fj));}else{return E(_1fh.d[_1fk-_1fi|0]);}}});switch(E(_1f3)){case 97:var _1fl=new T(function(){var _1fm=E(_1f2);if(!_1fm._){return E(_1do);}else{return new T2(0,_1fm.a,_1fm.b);}}),_1fn=new T(function(){var _1fo=B(_1ag(E(_1fl).b));return new T2(0,_1fo.a,_1fo.b);}),_1fp=B(_Gd(B(_sy(_18i,new T(function(){return E(E(_1fn).b);})))));if(!_1fp._){return E(_18g);}else{if(!E(_1fp.b)._){var _1fq=new T(function(){var _1fr=B(_Gd(B(_sy(_18i,new T(function(){return E(E(_1fn).a);})))));if(!_1fr._){return E(_18g);}else{if(!E(_1fr.b)._){return E(_1fr.a);}else{return E(_18h);}}},1);return {_:0,a:E({_:0,a:E(_1ep),b:E(B(_KQ(_1fq,E(_1fp.a),new T(function(){return E(E(_1fl).a);}),_E9,_1eq))),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};}else{return E(_18h);}}break;case 104:return {_:0,a:E({_:0,a:E(_1ep),b:E(B(_1e7(_1eq))),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};case 106:var _1fs=E(_1f2);if(!_1fs._){return {_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l: -1,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};}else{if(E(_1fs.a)==108){var _1ft=E(_1en),_1fu=B(_Gd(B(_sy(_18i,_1fs.b))));return (_1fu._==0)?E(_18g):(E(_1fu.b)._==0)?{_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(B(_17T(_1ft,_1eD))),f:E(B(_17T(_1ft,_1eE))),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:E(_1fu.a),m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_wu),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)}:E(_18h);}else{var _1fv=B(_Gd(B(_sy(_18i,_1fs))));return (_1fv._==0)?E(_18g):(E(_1fv.b)._==0)?{_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:E(_1fv.a),m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)}:E(_18h);}}break;case 108:var _1fw=E(_1en);return {_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(B(_17T(_1fw,_1eD))),f:E(B(_17T(_1fw,_1eE))),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_wu),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};case 109:var _1fx=B(_18l(E(_1f4),_1f2)),_1fy=_1fx.c,_1fz=B(_qO(_1fy,_S));if(!E(_1fz)){var _1fA=E(_1en),_1fB=new T(function(){var _1fC=function(_){var _1fD=B(_ms(_1eD,0))-1|0,_1fE=function(_1fF){if(_1fF>=0){var _1fG=newArr(_1fF,_14P),_1fH=_1fG,_1fI=E(_1fF);if(!_1fI){return new T4(0,E(_18j),E(_1fD),0,_1fH);}else{var _1fJ=function(_1fK,_1fL,_){while(1){var _1fM=E(_1fK);if(!_1fM._){return E(_);}else{var _=_1fH[_1fL]=_1fM.a;if(_1fL!=(_1fI-1|0)){var _1fN=_1fL+1|0;_1fK=_1fM.b;_1fL=_1fN;continue;}else{return E(_);}}}},_=B(_1fJ(_1eD,0,_));return new T4(0,E(_18j),E(_1fD),_1fI,_1fH);}}else{return E(_15J);}};if(0>_1fD){return new F(function(){return _1fE(0);});}else{return new F(function(){return _1fE(_1fD+1|0);});}},_1fO=B(_15K(_1fC)),_1fP=E(_1fO.a),_1fQ=E(_1fO.b);if(_1fP>_1fA){return B(_1cV(_1fA,_1fP,_1fQ));}else{if(_1fA>_1fQ){return B(_1cV(_1fA,_1fP,_1fQ));}else{return E(E(_1fO.d[_1fA-_1fP|0]).a);}}}),_1fR=B(_18K(_1fA,new T2(0,_1fB,new T2(1,_1f3,_1fy)),_1eD));}else{var _1fR=B(_1as(_1en,_1eD));}if(!E(_1fz)){var _1fS=B(_18K(E(_1en),_1fx.a,_1eE));}else{var _1fS=B(_1as(_1en,_1eE));}return {_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(B(_1cj(_1eC,_1fx.b))),d:E(_1eC),e:E(_1fR),f:E(_1fS),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_wu),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};case 114:var _1fT=B(_6Q(_1cI,_1eu));return {_:0,a:E({_:0,a:E(B(_6Q(_1cT,_1eu))),b:E(B(_19q(_1fT.a,E(_1fT.b),new T(function(){return B(_6Q(_1dX,_1eu));})))),c:E(_1er),d:B(_6Q(_1d6,_1eu)),e:32,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1fT),c:E(_1d0),d:E(_1eC),e:E(_1eD),f:E(B(_6d(_1d3,_1eE))),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_wu),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};case 115:return {_:0,a:E({_:0,a:E(_1ep),b:E(B(_1ej(_1eq))),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};case 116:var _1fU=E(_1f4),_1fV=B(_18l(_1fU,_1f2)),_1fW=E(_1fV.a);if(!E(_1fW)){var _1fX=true;}else{var _1fX=false;}if(!E(_1fX)){var _1fY=B(_18K(E(_1en),_1fW,_1eE));}else{var _1fY=B(_18K(E(_1en),_1fU+1|0,_1eE));}if(!E(_1fX)){var _1fZ=__Z;}else{var _1fZ=E(_1fV.b);}if(!B(_qO(_1fZ,_S))){var _1g0=B(_1em(_1en,_1fZ,_1ep,_1eq,_1er,_1es,_1et,_1eu,_1ev,_1ew,_1ex,_1ey,_1ez,_1eA,_1eB,_1eC,_1eD,_1fY,_1eF,_1eG,_1eH,_1eI,_1eJ,_1eK,_1eL,_1eM,_1eN,_1eO,_1eP,_1eQ,_1eR,_1eS,_1eT,_1eU,_1eV,_1eW,_1eX,_1eY,_1eZ,_1f0)),_1g1=E(_1g0.a);return {_:0,a:E({_:0,a:E(_1g1.a),b:E(_1g1.b),c:E(_1g1.c),d:_1g1.d,e:_1g1.e,f:_1g1.f,g:E(_1g1.g),h:_1g1.h,i:E(B(_q(_1ex,_1f1))),j:E(_1g1.j),k:E(_1g1.k)}),b:E(_1g0.b),c:E(_1g0.c),d:E(_1g0.d),e:E(_1g0.e),f:E(_1g0.f),g:E(_1g0.g),h:E(_1g0.h),i:_1g0.i,j:_1g0.j,k:_1g0.k,l:_1g0.l,m:E(_1g0.m),n:_1g0.n,o:E(_1g0.o),p:E(_1g0.p),q:_1g0.q,r:E(_1g0.r),s:_1g0.s,t:E(_1g0.t),u:E(_1g0.u)};}else{return {_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1fY),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};}break;case 119:return {_:0,a:E({_:0,a:E(_1cS),b:E(_1dn),c:E(_1er),d:E(_1d7),e:32,f:0,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1cE),c:E(_1d2),d:E(_1eC),e:E(_1eD),f:E(B(_6d(_1d3,_1eE))),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_wu),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};default:return {_:0,a:E({_:0,a:E(_1ep),b:E(_1eq),c:E(_1er),d:_1es,e:_1et,f:_1eu,g:E(_1ev),h:_1ew,i:E(B(_q(_1ex,_1f1))),j:E(_1ey),k:E(_1ez)}),b:E(_1eA),c:E(_1eB),d:E(_1eC),e:E(_1eD),f:E(_1eE),g:E(_1eF),h:E(_1eG),i:_1eH,j:_1eI,k:_1eJ,l:_1eK,m:E(_1eL),n:_1eM,o:E(_1eN),p:E(_1eO),q:_1eP,r:E(_1eQ),s:_1eR,t:E({_:0,a:E(_1eS),b:E(_1eT),c:E(_1eU),d:E(_1eV),e:E(_1eW),f:E(_1eX),g:E(_1eY),h:E(_1eZ)}),u:E(_1f0)};}}},_1g2=function(_1g3,_1g4){while(1){var _1g5=E(_1g4);if(!_1g5._){return __Z;}else{var _1g6=_1g5.b,_1g7=E(_1g3);if(_1g7==1){return E(_1g6);}else{_1g3=_1g7-1|0;_1g4=_1g6;continue;}}}},_1g8=new T(function(){return B(unCStr("X"));}),_1g9=new T(function(){return B(_e6("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1ga=38,_1gb=function(_1gc,_1gd,_1ge,_1gf,_1gg,_1gh,_1gi,_1gj,_1gk,_1gl,_1gm,_1gn,_1go,_1gp,_1gq,_1gr,_1gs,_1gt,_1gu,_1gv,_1gw,_1gx,_1gy,_1gz){var _1gA=E(_1ge);if(!_1gA._){return {_:0,a:_1gf,b:_1gg,c:_1gh,d:_1gi,e:_1gj,f:_1gk,g:_1gl,h:_1gm,i:_1gn,j:_1go,k:_1gp,l:_1gq,m:_1gr,n:_1gs,o:_1gt,p:_1gu,q:_1gv,r:_1gw,s:_1gx,t:_1gy,u:_1gz};}else{var _1gB=_1gA.b,_1gC=E(_1gA.a),_1gD=_1gC.a,_1gE=_1gC.b,_1gF=function(_1gG,_1gH,_1gI){var _1gJ=function(_1gK,_1gL){if(!B(_qO(_1gK,_S))){var _1gM=E(_1gf),_1gN=E(_1gy),_1gO=B(_1em(_1gL,_1gK,_1gM.a,_1gM.b,_1gM.c,_1gM.d,_1gM.e,_1gM.f,_1gM.g,_1gM.h,_1gM.i,_1gM.j,_1gM.k,_1gg,_1gh,_1gi,_1gj,_1gk,_1gl,_1gm,_1gn,_1go,_1gp,_1gq,_1gr,_1gs,_1gt,_1gu,_1gv,_1gw,_1gx,_1gN.a,_1gN.b,_1gN.c,_1gN.d,_1gN.e,_1gN.f,_1gN.g,_1gN.h,_1gz)),_1gP=_1gO.a,_1gQ=_1gO.b,_1gR=_1gO.c,_1gS=_1gO.d,_1gT=_1gO.e,_1gU=_1gO.f,_1gV=_1gO.g,_1gW=_1gO.h,_1gX=_1gO.i,_1gY=_1gO.j,_1gZ=_1gO.k,_1h0=_1gO.l,_1h1=_1gO.m,_1h2=_1gO.n,_1h3=_1gO.o,_1h4=_1gO.p,_1h5=_1gO.q,_1h6=_1gO.r,_1h7=_1gO.s,_1h8=_1gO.t,_1h9=_1gO.u;if(B(_ms(_1gU,0))!=B(_ms(_1gk,0))){return {_:0,a:_1gP,b:_1gQ,c:_1gR,d:_1gS,e:_1gT,f:_1gU,g:_1gV,h:_1gW,i:_1gX,j:_1gY,k:_1gZ,l:_1h0,m:_1h1,n:_1h2,o:_1h3,p:_1h4,q:_1h5,r:_1h6,s:_1h7,t:_1h8,u:_1h9};}else{return new F(function(){return _1gb(new T(function(){return E(_1gc)+1|0;}),_1gd,_1gB,_1gP,_1gQ,_1gR,_1gS,_1gT,_1gU,_1gV,_1gW,_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4,_1h5,_1h6,_1h7,_1h8,_1h9);});}}else{return new F(function(){return _1gb(new T(function(){return E(_1gc)+1|0;}),_1gd,_1gB,_1gf,_1gg,_1gh,_1gi,_1gj,_1gk,_1gl,_1gm,_1gn,_1go,_1gp,_1gq,_1gr,_1gs,_1gt,_1gu,_1gv,_1gw,_1gx,_1gy,_1gz);});}},_1ha=B(_ms(_1gd,0))-B(_ms(new T2(1,_1gG,_1gH),0))|0;if(_1ha>0){var _1hb=B(_1g2(_1ha,_1gd));}else{var _1hb=E(_1gd);}if(E(B(_17B(_1gG,_1gH,_Tn)))==63){var _1hc=B(_RQ(_1gG,_1gH));}else{var _1hc=new T2(1,_1gG,_1gH);}var _1hd=function(_1he){if(!B(_4A(_h6,_1ga,_1gD))){return new T2(0,_1gE,_1gc);}else{var _1hf=function(_1hg){while(1){var _1hh=B((function(_1hi){var _1hj=E(_1hi);if(!_1hj._){return true;}else{var _1hk=_1hj.b,_1hl=E(_1hj.a);if(!_1hl._){return E(_1g9);}else{switch(E(_1hl.a)){case 99:var _1hm=E(_1gf);if(!E(_1hm.k)){return false;}else{var _1hn=function(_1ho){while(1){var _1hp=E(_1ho);if(!_1hp._){return true;}else{var _1hq=_1hp.b,_1hr=E(_1hp.a);if(!_1hr._){return E(_1g9);}else{if(E(_1hr.a)==115){var _1hs=B(_Gd(B(_sy(_18i,_1hr.b))));if(!_1hs._){return E(_18g);}else{if(!E(_1hs.b)._){if(_1hm.f!=E(_1hs.a)){return false;}else{_1ho=_1hq;continue;}}else{return E(_18h);}}}else{_1ho=_1hq;continue;}}}}};return new F(function(){return _1hn(_1hk);});}break;case 115:var _1ht=E(_1gf),_1hu=_1ht.f,_1hv=B(_Gd(B(_sy(_18i,_1hl.b))));if(!_1hv._){return E(_18g);}else{if(!E(_1hv.b)._){if(_1hu!=E(_1hv.a)){return false;}else{var _1hw=function(_1hx){while(1){var _1hy=E(_1hx);if(!_1hy._){return true;}else{var _1hz=_1hy.b,_1hA=E(_1hy.a);if(!_1hA._){return E(_1g9);}else{switch(E(_1hA.a)){case 99:if(!E(_1ht.k)){return false;}else{_1hx=_1hz;continue;}break;case 115:var _1hB=B(_Gd(B(_sy(_18i,_1hA.b))));if(!_1hB._){return E(_18g);}else{if(!E(_1hB.b)._){if(_1hu!=E(_1hB.a)){return false;}else{_1hx=_1hz;continue;}}else{return E(_18h);}}break;default:_1hx=_1hz;continue;}}}}};return new F(function(){return _1hw(_1hk);});}}else{return E(_18h);}}break;default:_1hg=_1hk;return __continue;}}}})(_1hg));if(_1hh!=__continue){return _1hh;}}};return (!B(_1hf(_1gI)))?(!B(_qO(_1hc,_1g8)))?new T2(0,_S,_1gc):new T2(0,_1gE,_1gc):new T2(0,_1gE,_1gc);}};if(E(B(_17J(_1gG,_1gH,_Tn)))==63){if(!B(_68(_1hb,_S))){var _1hC=E(_1hb);if(!_1hC._){return E(_RV);}else{if(!B(_qO(_1hc,B(_RQ(_1hC.a,_1hC.b))))){if(!B(_qO(_1hc,_1g8))){return new F(function(){return _1gJ(_S,_1gc);});}else{return new F(function(){return _1gJ(_1gE,_1gc);});}}else{var _1hD=B(_1hd(_));return new F(function(){return _1gJ(_1hD.a,_1hD.b);});}}}else{if(!B(_qO(_1hc,_1hb))){if(!B(_qO(_1hc,_1g8))){return new F(function(){return _1gJ(_S,_1gc);});}else{return new F(function(){return _1gJ(_1gE,_1gc);});}}else{var _1hE=B(_1hd(_));return new F(function(){return _1gJ(_1hE.a,_1hE.b);});}}}else{if(!B(_qO(_1hc,_1hb))){if(!B(_qO(_1hc,_1g8))){return new F(function(){return _1gJ(_S,_1gc);});}else{return new F(function(){return _1gJ(_1gE,_1gc);});}}else{var _1hF=B(_1hd(_));return new F(function(){return _1gJ(_1hF.a,_1hF.b);});}}},_1hG=E(_1gD);if(!_1hG._){return E(_Tn);}else{var _1hH=_1hG.a,_1hI=E(_1hG.b);if(!_1hI._){return new F(function(){return _1gF(_1hH,_S,_S);});}else{var _1hJ=E(_1hH),_1hK=new T(function(){var _1hL=B(_H5(38,_1hI.a,_1hI.b));return new T2(0,_1hL.a,_1hL.b);});if(E(_1hJ)==38){return E(_Tn);}else{return new F(function(){return _1gF(_1hJ,new T(function(){return E(E(_1hK).a);}),new T(function(){return E(E(_1hK).b);}));});}}}}},_1hM="]",_1hN="}",_1hO=":",_1hP=",",_1hQ=new T(function(){return eval("JSON.stringify");}),_1hR="false",_1hS="null",_1hT="[",_1hU="{",_1hV="\"",_1hW="true",_1hX=function(_1hY,_1hZ){var _1i0=E(_1hZ);switch(_1i0._){case 0:return new T2(0,new T(function(){return jsShow(_1i0.a);}),_1hY);case 1:return new T2(0,new T(function(){var _1i1=__app1(E(_1hQ),_1i0.a);return String(_1i1);}),_1hY);case 2:return (!E(_1i0.a))?new T2(0,_1hR,_1hY):new T2(0,_1hW,_1hY);case 3:var _1i2=E(_1i0.a);if(!_1i2._){return new T2(0,_1hT,new T2(1,_1hM,_1hY));}else{var _1i3=new T(function(){var _1i4=new T(function(){var _1i5=function(_1i6){var _1i7=E(_1i6);if(!_1i7._){return E(new T2(1,_1hM,_1hY));}else{var _1i8=new T(function(){var _1i9=B(_1hX(new T(function(){return B(_1i5(_1i7.b));}),_1i7.a));return new T2(1,_1i9.a,_1i9.b);});return new T2(1,_1hP,_1i8);}};return B(_1i5(_1i2.b));}),_1ia=B(_1hX(_1i4,_1i2.a));return new T2(1,_1ia.a,_1ia.b);});return new T2(0,_1hT,_1i3);}break;case 4:var _1ib=E(_1i0.a);if(!_1ib._){return new T2(0,_1hU,new T2(1,_1hN,_1hY));}else{var _1ic=E(_1ib.a),_1id=new T(function(){var _1ie=new T(function(){var _1if=function(_1ig){var _1ih=E(_1ig);if(!_1ih._){return E(new T2(1,_1hN,_1hY));}else{var _1ii=E(_1ih.a),_1ij=new T(function(){var _1ik=B(_1hX(new T(function(){return B(_1if(_1ih.b));}),_1ii.b));return new T2(1,_1ik.a,_1ik.b);});return new T2(1,_1hP,new T2(1,_1hV,new T2(1,_1ii.a,new T2(1,_1hV,new T2(1,_1hO,_1ij)))));}};return B(_1if(_1ib.b));}),_1il=B(_1hX(_1ie,_1ic.b));return new T2(1,_1il.a,_1il.b);});return new T2(0,_1hU,new T2(1,new T(function(){var _1im=__app1(E(_1hQ),E(_1ic.a));return String(_1im);}),new T2(1,_1hO,_1id)));}break;default:return new T2(0,_1hS,_1hY);}},_1in=new T(function(){return toJSStr(_S);}),_1io=function(_1ip){var _1iq=B(_1hX(_S,_1ip)),_1ir=jsCat(new T2(1,_1iq.a,_1iq.b),E(_1in));return E(_1ir);},_1is=function(_1it){var _1iu=E(_1it);if(!_1iu._){return new T2(0,_S,_S);}else{var _1iv=E(_1iu.a),_1iw=new T(function(){var _1ix=B(_1is(_1iu.b));return new T2(0,_1ix.a,_1ix.b);});return new T2(0,new T2(1,_1iv.a,new T(function(){return E(E(_1iw).a);})),new T2(1,_1iv.b,new T(function(){return E(E(_1iw).b);})));}},_1iy=new T(function(){return B(unCStr("Rk"));}),_1iz=function(_1iA,_1iB,_1iC,_1iD,_1iE,_1iF,_1iG,_1iH,_1iI,_1iJ,_1iK,_1iL,_1iM,_1iN,_1iO,_1iP,_1iQ,_1iR,_1iS,_1iT,_1iU,_1iV){while(1){var _1iW=B((function(_1iX,_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4,_1j5,_1j6,_1j7,_1j8,_1j9,_1ja,_1jb,_1jc,_1jd,_1je,_1jf,_1jg,_1jh,_1ji){var _1jj=E(_1iX);if(!_1jj._){return {_:0,a:_1iY,b:_1iZ,c:_1j0,d:_1j1,e:_1j2,f:_1j3,g:_1j4,h:_1j5,i:_1j6,j:_1j7,k:_1j8,l:_1j9,m:_1ja,n:_1jb,o:_1jc,p:_1jd,q:_1je,r:_1jf,s:_1jg,t:_1jh,u:_1ji};}else{var _1jk=_1jj.a,_1jl=B(_Se(B(unAppCStr("e.e",new T2(1,_1jk,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1jk,_1iy)));})))),_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4,_1j5,_1j6,_1j7,_1j8,_1j9,_1ja,_1jb,_1jc,_1jd,_1je,_1jf,_1jg,_1jh,_1ji));_1iA=_1jj.b;_1iB=_1jl.a;_1iC=_1jl.b;_1iD=_1jl.c;_1iE=_1jl.d;_1iF=_1jl.e;_1iG=_1jl.f;_1iH=_1jl.g;_1iI=_1jl.h;_1iJ=_1jl.i;_1iK=_1jl.j;_1iL=_1jl.k;_1iM=_1jl.l;_1iN=_1jl.m;_1iO=_1jl.n;_1iP=_1jl.o;_1iQ=_1jl.p;_1iR=_1jl.q;_1iS=_1jl.r;_1iT=_1jl.s;_1iU=_1jl.t;_1iV=_1jl.u;return __continue;}})(_1iA,_1iB,_1iC,_1iD,_1iE,_1iF,_1iG,_1iH,_1iI,_1iJ,_1iK,_1iL,_1iM,_1iN,_1iO,_1iP,_1iQ,_1iR,_1iS,_1iT,_1iU,_1iV));if(_1iW!=__continue){return _1iW;}}},_1jm=function(_1jn){var _1jo=E(_1jn);switch(_1jo){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1jo>>>0>1114111){return new F(function(){return _wE(_1jo);});}else{return _1jo;}}},_1jp=function(_1jq,_1jr,_1js){while(1){var _1jt=E(_1jr);if(!_1jt._){return (E(_1js)._==0)?true:false;}else{var _1ju=E(_1js);if(!_1ju._){return false;}else{if(!B(A3(_4y,_1jq,_1jt.a,_1ju.a))){return false;}else{_1jr=_1jt.b;_1js=_1ju.b;continue;}}}}},_1jv=function(_1jw,_1jx){return (!B(_1jp(_rl,_1jw,_1jx)))?true:false;},_1jy=function(_1jz,_1jA){return new F(function(){return _1jp(_rl,_1jz,_1jA);});},_1jB=new T2(0,_1jy,_1jv),_1jC=function(_1jD){var _1jE=E(_1jD);if(!_1jE._){return new T2(0,_S,_S);}else{var _1jF=E(_1jE.a),_1jG=new T(function(){var _1jH=B(_1jC(_1jE.b));return new T2(0,_1jH.a,_1jH.b);});return new T2(0,new T2(1,_1jF.a,new T(function(){return E(E(_1jG).a);})),new T2(1,_1jF.b,new T(function(){return E(E(_1jG).b);})));}},_1jI=function(_1jJ,_1jK){while(1){var _1jL=E(_1jK);if(!_1jL._){return __Z;}else{var _1jM=_1jL.b,_1jN=E(_1jJ);if(_1jN==1){return E(_1jM);}else{_1jJ=_1jN-1|0;_1jK=_1jM;continue;}}}},_1jO=function(_1jP,_1jQ){while(1){var _1jR=E(_1jQ);if(!_1jR._){return __Z;}else{var _1jS=_1jR.b,_1jT=E(_1jP);if(_1jT==1){return E(_1jS);}else{_1jP=_1jT-1|0;_1jQ=_1jS;continue;}}}},_1jU=function(_1jV){return new F(function(){return _Gk(_1jV,_S);});},_1jW=function(_1jX,_1jY,_1jZ,_1k0){var _1k1=new T(function(){return B(_MD(_h6,_1jY,_1jZ));}),_1k2=new T(function(){var _1k3=E(_1k1),_1k4=new T(function(){var _1k5=_1k3+1|0;if(_1k5>0){return B(_1jO(_1k5,_1jZ));}else{return E(_1jZ);}});if(0>=_1k3){return E(_1k4);}else{var _1k6=function(_1k7,_1k8){var _1k9=E(_1k7);if(!_1k9._){return E(_1k4);}else{var _1ka=_1k9.a,_1kb=E(_1k8);return (_1kb==1)?new T2(1,_1ka,_1k4):new T2(1,_1ka,new T(function(){return B(_1k6(_1k9.b,_1kb-1|0));}));}};return B(_1k6(_1jZ,_1k3));}}),_1kc=new T(function(){var _1kd=E(_1k1),_1ke=new T(function(){if(E(_1jY)==94){return B(A2(_1jX,new T(function(){return B(_6Q(_1k0,_1kd+1|0));}),new T(function(){return B(_6Q(_1k0,_1kd));})));}else{return B(A2(_1jX,new T(function(){return B(_6Q(_1k0,_1kd));}),new T(function(){return B(_6Q(_1k0,_1kd+1|0));})));}}),_1kf=new T2(1,_1ke,new T(function(){var _1kg=_1kd+2|0;if(_1kg>0){return B(_1jI(_1kg,_1k0));}else{return E(_1k0);}}));if(0>=_1kd){return E(_1kf);}else{var _1kh=function(_1ki,_1kj){var _1kk=E(_1ki);if(!_1kk._){return E(_1kf);}else{var _1kl=_1kk.a,_1km=E(_1kj);return (_1km==1)?new T2(1,_1kl,_1kf):new T2(1,_1kl,new T(function(){return B(_1kh(_1kk.b,_1km-1|0));}));}};return B(_1kh(_1k0,_1kd));}});return (E(_1jY)==94)?new T2(0,new T(function(){return B(_1jU(_1k2));}),new T(function(){return B(_1jU(_1kc));})):new T2(0,_1k2,_1kc);},_1kn=new T(function(){return B(_cm(_oL,_oK));}),_1ko=function(_1kp,_1kq,_1kr){while(1){if(!E(_1kn)){if(!B(_cm(B(_11O(_1kq,_oL)),_oK))){if(!B(_cm(_1kq,_aU))){var _1ks=B(_oe(_1kp,_1kp)),_1kt=B(_11z(B(_eN(_1kq,_aU)),_oL)),_1ku=B(_oe(_1kp,_1kr));_1kp=_1ks;_1kq=_1kt;_1kr=_1ku;continue;}else{return new F(function(){return _oe(_1kp,_1kr);});}}else{var _1ks=B(_oe(_1kp,_1kp)),_1kt=B(_11z(_1kq,_oL));_1kp=_1ks;_1kq=_1kt;continue;}}else{return E(_9T);}}},_1kv=function(_1kw,_1kx){while(1){if(!E(_1kn)){if(!B(_cm(B(_11O(_1kx,_oL)),_oK))){if(!B(_cm(_1kx,_aU))){return new F(function(){return _1ko(B(_oe(_1kw,_1kw)),B(_11z(B(_eN(_1kx,_aU)),_oL)),_1kw);});}else{return E(_1kw);}}else{var _1ky=B(_oe(_1kw,_1kw)),_1kz=B(_11z(_1kx,_oL));_1kw=_1ky;_1kx=_1kz;continue;}}else{return E(_9T);}}},_1kA=function(_1kB,_1kC){if(!B(_d6(_1kC,_oK))){if(!B(_cm(_1kC,_oK))){return new F(function(){return _1kv(_1kB,_1kC);});}else{return E(_aU);}}else{return E(_pq);}},_1kD=94,_1kE=45,_1kF=43,_1kG=42,_1kH=function(_1kI,_1kJ){while(1){var _1kK=B((function(_1kL,_1kM){var _1kN=E(_1kM);if(!_1kN._){return __Z;}else{if((B(_ms(_1kL,0))+1|0)==B(_ms(_1kN,0))){if(!B(_4A(_h6,_1kD,_1kL))){if(!B(_4A(_h6,_1kG,_1kL))){if(!B(_4A(_h6,_1kF,_1kL))){if(!B(_4A(_h6,_1kE,_1kL))){return E(_1kN);}else{var _1kO=B(_1jW(_eN,45,_1kL,_1kN));_1kI=_1kO.a;_1kJ=_1kO.b;return __continue;}}else{var _1kP=B(_1jW(_cu,43,_1kL,_1kN));_1kI=_1kP.a;_1kJ=_1kP.b;return __continue;}}else{var _1kQ=B(_1jW(_oe,42,_1kL,_1kN));_1kI=_1kQ.a;_1kJ=_1kQ.b;return __continue;}}else{var _1kR=B(_1jW(_1kA,94,new T(function(){return B(_1jU(_1kL));}),new T(function(){return B(_Gk(_1kN,_S));})));_1kI=_1kR.a;_1kJ=_1kR.b;return __continue;}}else{return __Z;}}})(_1kI,_1kJ));if(_1kK!=__continue){return _1kK;}}},_1kS=function(_1kT){var _1kU=E(_1kT);if(!_1kU._){return new T2(0,_S,_S);}else{var _1kV=E(_1kU.a),_1kW=new T(function(){var _1kX=B(_1kS(_1kU.b));return new T2(0,_1kX.a,_1kX.b);});return new T2(0,new T2(1,_1kV.a,new T(function(){return E(E(_1kW).a);})),new T2(1,_1kV.b,new T(function(){return E(E(_1kW).b);})));}},_1kY=new T(function(){return B(unCStr("0123456789+-"));}),_1kZ=function(_1l0){while(1){var _1l1=E(_1l0);if(!_1l1._){return true;}else{if(!B(_4A(_h6,_1l1.a,_1kY))){return false;}else{_1l0=_1l1.b;continue;}}}},_1l2=new T(function(){return B(err(_sr));}),_1l3=new T(function(){return B(err(_st));}),_1l4=function(_1l5,_1l6){var _1l7=function(_1l8,_1l9){var _1la=function(_1lb){return new F(function(){return A1(_1l9,new T(function(){return B(_fs(_1lb));}));});},_1lc=new T(function(){return B(_D7(function(_1ld){return new F(function(){return A3(_1l5,_1ld,_1l8,_1la);});}));}),_1le=function(_1lf){return E(_1lc);},_1lg=function(_1lh){return new F(function(){return A2(_BO,_1lh,_1le);});},_1li=new T(function(){return B(_D7(function(_1lj){var _1lk=E(_1lj);if(_1lk._==4){var _1ll=E(_1lk.a);if(!_1ll._){return new F(function(){return A3(_1l5,_1lk,_1l8,_1l9);});}else{if(E(_1ll.a)==45){if(!E(_1ll.b)._){return E(new T1(1,_1lg));}else{return new F(function(){return A3(_1l5,_1lk,_1l8,_1l9);});}}else{return new F(function(){return A3(_1l5,_1lk,_1l8,_1l9);});}}}else{return new F(function(){return A3(_1l5,_1lk,_1l8,_1l9);});}}));}),_1lm=function(_1ln){return E(_1li);};return new T1(1,function(_1lo){return new F(function(){return A2(_BO,_1lo,_1lm);});});};return new F(function(){return _DY(_1l7,_1l6);});},_1lp=function(_1lq){var _1lr=E(_1lq);if(_1lr._==5){var _1ls=B(_FW(_1lr.a));return (_1ls._==0)?E(_G1):function(_1lt,_1lu){return new F(function(){return A1(_1lu,_1ls.a);});};}else{return E(_G1);}},_1lv=new T(function(){return B(A3(_1l4,_1lp,_DE,_Fr));}),_1lw=function(_1lx,_1ly){var _1lz=E(_1ly);if(!_1lz._){return __Z;}else{var _1lA=_1lz.a,_1lB=_1lz.b,_1lC=function(_1lD){var _1lE=B(_1kS(_1lx)),_1lF=_1lE.a;return (!B(_4A(_qd,_1lA,_1lF)))?__Z:new T2(1,new T(function(){return B(_6Q(_1lE.b,B(_MD(_qd,_1lA,_1lF))));}),new T(function(){return B(_1lw(_1lx,_1lB));}));};if(!B(_68(_1lA,_S))){if(!B(_1kZ(_1lA))){return new F(function(){return _1lC(_);});}else{return new T2(1,new T(function(){var _1lG=B(_Gd(B(_sy(_1lv,_1lA))));if(!_1lG._){return E(_1l2);}else{if(!E(_1lG.b)._){return E(_1lG.a);}else{return E(_1l3);}}}),new T(function(){return B(_1lw(_1lx,_1lB));}));}}else{return new F(function(){return _1lC(_);});}}},_1lH=new T(function(){return B(unCStr("+-*^"));}),_1lI=new T(function(){return B(unCStr("0123456789"));}),_1lJ=new T(function(){return B(_Lh("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1lK=new T2(1,_S,_S),_1lL=function(_1lM){var _1lN=E(_1lM);if(!_1lN._){return new T2(0,_1lK,_S);}else{var _1lO=_1lN.a,_1lP=new T(function(){var _1lQ=B(_1lL(_1lN.b)),_1lR=E(_1lQ.a);if(!_1lR._){return E(_1lJ);}else{return new T3(0,_1lR.a,_1lR.b,_1lQ.b);}});return (!B(_4A(_h6,_1lO,_1lI)))?(!B(_4A(_h6,_1lO,_1lH)))?new T2(0,new T2(1,new T2(1,_1lO,new T(function(){return E(E(_1lP).a);})),new T(function(){return E(E(_1lP).b);})),new T(function(){return E(E(_1lP).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1lP).a);}),new T(function(){return E(E(_1lP).b);}))),new T2(1,_1lO,new T(function(){return E(E(_1lP).c);}))):new T2(0,new T2(1,new T2(1,_1lO,new T(function(){return E(E(_1lP).a);})),new T(function(){return E(E(_1lP).b);})),new T(function(){return E(E(_1lP).c);}));}},_1lS=function(_1lT,_1lU){var _1lV=new T(function(){var _1lW=B(_1lL(_1lU)),_1lX=E(_1lW.a);if(!_1lX._){return E(_1lJ);}else{return new T3(0,_1lX.a,_1lX.b,_1lW.b);}});return (!B(_4A(_h6,_1lT,_1lI)))?(!B(_4A(_h6,_1lT,_1lH)))?new T2(0,new T2(1,new T2(1,_1lT,new T(function(){return E(E(_1lV).a);})),new T(function(){return E(E(_1lV).b);})),new T(function(){return E(E(_1lV).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1lV).a);}),new T(function(){return E(E(_1lV).b);}))),new T2(1,_1lT,new T(function(){return E(E(_1lV).c);}))):new T2(0,new T2(1,new T2(1,_1lT,new T(function(){return E(E(_1lV).a);})),new T(function(){return E(E(_1lV).b);})),new T(function(){return E(E(_1lV).c);}));},_1lY=function(_1lZ,_1m0){while(1){var _1m1=E(_1lZ);if(!_1m1._){return E(_1m0);}else{_1lZ=_1m1.b;_1m0=_1m1.a;continue;}}},_1m2=function(_1m3,_1m4,_1m5){return new F(function(){return _1lY(_1m4,_1m3);});},_1m6=function(_1m7,_1m8){var _1m9=E(_1m8);if(!_1m9._){return __Z;}else{var _1ma=B(_1lS(_1m9.a,_1m9.b)),_1mb=B(_1kH(_1ma.b,B(_1lw(_1m7,_1ma.a))));if(!_1mb._){return E(_1m9);}else{return new F(function(){return _13S(0,B(_1m2(_1mb.a,_1mb.b,_Tn)),_S);});}}},_1mc=function(_1md,_1me){var _1mf=function(_1mg,_1mh){while(1){var _1mi=B((function(_1mj,_1mk){var _1ml=E(_1mk);if(!_1ml._){return (!B(_qO(_1mj,_S)))?new T2(0,_wu,_1mj):new T2(0,_wt,_S);}else{var _1mm=_1ml.b,_1mn=B(_1jC(_1ml.a)).a;if(!B(_4A(_h6,_19K,_1mn))){var _1mo=_1mj;_1mg=_1mo;_1mh=_1mm;return __continue;}else{var _1mp=B(_1ag(_1mn)),_1mq=_1mp.a,_1mr=_1mp.b;if(!B(_68(_1mr,_S))){if(!B(_qO(B(_1m6(_1md,_1mq)),B(_1m6(_1md,_1mr))))){return new T2(0,_wt,_S);}else{var _1ms=new T(function(){if(!B(_qO(_1mj,_S))){return B(_q(_1mj,new T(function(){return B(unAppCStr(" ",_1mq));},1)));}else{return E(_1mq);}});_1mg=_1ms;_1mh=_1mm;return __continue;}}else{return new T2(0,_wt,_S);}}}})(_1mg,_1mh));if(_1mi!=__continue){return _1mi;}}};return new F(function(){return _1mf(_S,_1me);});},_1mt=function(_1mu,_1mv){var _1mw=new T(function(){var _1mx=B(_Gd(B(_sy(_13I,new T(function(){return B(_pN(3,B(_A(0,imul(E(_1mv),E(_1mu)-1|0)|0,_S))));})))));if(!_1mx._){return E(_13H);}else{if(!E(_1mx.b)._){return E(_1mx.a);}else{return E(_13G);}}});return new T2(0,new T(function(){return B(_au(_1mw,_1mu));}),_1mw);},_1my=function(_1mz,_1mA){while(1){var _1mB=E(_1mA);if(!_1mB._){return __Z;}else{var _1mC=_1mB.b,_1mD=E(_1mz);if(_1mD==1){return E(_1mC);}else{_1mz=_1mD-1|0;_1mA=_1mC;continue;}}}},_1mE=function(_1mF,_1mG){while(1){var _1mH=E(_1mG);if(!_1mH._){return __Z;}else{var _1mI=_1mH.b,_1mJ=E(_1mF);if(_1mJ==1){return E(_1mI);}else{_1mF=_1mJ-1|0;_1mG=_1mI;continue;}}}},_1mK=64,_1mL=new T2(1,_1mK,_S),_1mM=function(_1mN,_1mO,_1mP,_1mQ){return (!B(_qO(_1mN,_1mP)))?true:(!B(_cm(_1mO,_1mQ)))?true:false;},_1mR=function(_1mS,_1mT){var _1mU=E(_1mS),_1mV=E(_1mT);return new F(function(){return _1mM(_1mU.a,_1mU.b,_1mV.a,_1mV.b);});},_1mW=function(_1mX,_1mY,_1mZ,_1n0){if(!B(_qO(_1mX,_1mZ))){return false;}else{return new F(function(){return _cm(_1mY,_1n0);});}},_1n1=function(_1n2,_1n3){var _1n4=E(_1n2),_1n5=E(_1n3);return new F(function(){return _1mW(_1n4.a,_1n4.b,_1n5.a,_1n5.b);});},_1n6=new T2(0,_1n1,_1mR),_1n7=function(_1n8){var _1n9=E(_1n8);if(!_1n9._){return new T2(0,_S,_S);}else{var _1na=E(_1n9.a),_1nb=new T(function(){var _1nc=B(_1n7(_1n9.b));return new T2(0,_1nc.a,_1nc.b);});return new T2(0,new T2(1,_1na.a,new T(function(){return E(E(_1nb).a);})),new T2(1,_1na.b,new T(function(){return E(E(_1nb).b);})));}},_1nd=function(_1ne){var _1nf=E(_1ne);if(!_1nf._){return new T2(0,_S,_S);}else{var _1ng=E(_1nf.a),_1nh=new T(function(){var _1ni=B(_1nd(_1nf.b));return new T2(0,_1ni.a,_1ni.b);});return new T2(0,new T2(1,_1ng.a,new T(function(){return E(E(_1nh).a);})),new T2(1,_1ng.b,new T(function(){return E(E(_1nh).b);})));}},_1nj=function(_1nk){var _1nl=E(_1nk);if(!_1nl._){return new T2(0,_S,_S);}else{var _1nm=E(_1nl.a),_1nn=new T(function(){var _1no=B(_1nj(_1nl.b));return new T2(0,_1no.a,_1no.b);});return new T2(0,new T2(1,_1nm.a,new T(function(){return E(E(_1nn).a);})),new T2(1,_1nm.b,new T(function(){return E(E(_1nn).b);})));}},_1np=function(_1nq,_1nr){return (_1nq<=_1nr)?new T2(1,_1nq,new T(function(){return B(_1np(_1nq+1|0,_1nr));})):__Z;},_1ns=new T(function(){return B(_1np(65,90));}),_1nt=function(_1nu){return (_1nu<=122)?new T2(1,_1nu,new T(function(){return B(_1nt(_1nu+1|0));})):E(_1ns);},_1nv=new T(function(){return B(_1nt(97));}),_1nw=function(_1nx){while(1){var _1ny=E(_1nx);if(!_1ny._){return true;}else{if(!B(_4A(_h6,_1ny.a,_1nv))){return false;}else{_1nx=_1ny.b;continue;}}}},_1nz=new T2(0,_S,_S),_1nA=new T(function(){return B(err(_sr));}),_1nB=new T(function(){return B(err(_st));}),_1nC=new T(function(){return B(A3(_1l4,_1lp,_DE,_Fr));}),_1nD=function(_1nE,_1nF,_1nG){while(1){var _1nH=B((function(_1nI,_1nJ,_1nK){var _1nL=E(_1nK);if(!_1nL._){return __Z;}else{var _1nM=_1nL.b,_1nN=B(_1nd(_1nJ)),_1nO=_1nN.a,_1nP=B(_1n7(_1nO)),_1nQ=_1nP.a,_1nR=new T(function(){return E(B(_1nj(_1nL.a)).a);}),_1nS=new T(function(){return B(_4A(_h6,_19K,_1nR));}),_1nT=new T(function(){if(!E(_1nS)){return E(_1nz);}else{var _1nU=B(_1ag(_1nR));return new T2(0,_1nU.a,_1nU.b);}}),_1nV=new T(function(){return E(E(_1nT).a);}),_1nW=new T(function(){return B(_MD(_qd,_1nV,_1nQ));}),_1nX=new T(function(){var _1nY=function(_){var _1nZ=B(_ms(_1nJ,0))-1|0,_1o0=function(_1o1){if(_1o1>=0){var _1o2=newArr(_1o1,_14P),_1o3=_1o2,_1o4=E(_1o1);if(!_1o4){return new T4(0,E(_18j),E(_1nZ),0,_1o3);}else{var _1o5=function(_1o6,_1o7,_){while(1){var _1o8=E(_1o6);if(!_1o8._){return E(_);}else{var _=_1o3[_1o7]=_1o8.a;if(_1o7!=(_1o4-1|0)){var _1o9=_1o7+1|0;_1o6=_1o8.b;_1o7=_1o9;continue;}else{return E(_);}}}},_=B(_1o5(_1nN.b,0,_));return new T4(0,E(_18j),E(_1nZ),_1o4,_1o3);}}else{return E(_15J);}};if(0>_1nZ){return new F(function(){return _1o0(0);});}else{return new F(function(){return _1o0(_1nZ+1|0);});}};return B(_15K(_1nY));});if(!B(_4A(_qd,_1nV,_1nQ))){var _1oa=false;}else{var _1ob=E(_1nX),_1oc=E(_1ob.a),_1od=E(_1ob.b),_1oe=E(_1nW);if(_1oc>_1oe){var _1of=B(_1cV(_1oe,_1oc,_1od));}else{if(_1oe>_1od){var _1og=B(_1cV(_1oe,_1oc,_1od));}else{var _1og=E(_1ob.d[_1oe-_1oc|0])==E(_1nI);}var _1of=_1og;}var _1oa=_1of;}var _1oh=new T(function(){return E(E(_1nT).b);}),_1oi=new T(function(){return B(_MD(_qd,_1oh,_1nQ));}),_1oj=new T(function(){if(!B(_4A(_qd,_1oh,_1nQ))){return false;}else{var _1ok=E(_1nX),_1ol=E(_1ok.a),_1om=E(_1ok.b),_1on=E(_1oi);if(_1ol>_1on){return B(_1cV(_1on,_1ol,_1om));}else{if(_1on>_1om){return B(_1cV(_1on,_1ol,_1om));}else{return E(_1ok.d[_1on-_1ol|0])==E(_1nI);}}}}),_1oo=new T(function(){var _1op=function(_){var _1oq=B(_ms(_1nO,0))-1|0,_1or=function(_1os){if(_1os>=0){var _1ot=newArr(_1os,_14P),_1ou=_1ot,_1ov=E(_1os);if(!_1ov){return new T4(0,E(_18j),E(_1oq),0,_1ou);}else{var _1ow=function(_1ox,_1oy,_){while(1){var _1oz=E(_1ox);if(!_1oz._){return E(_);}else{var _=_1ou[_1oy]=_1oz.a;if(_1oy!=(_1ov-1|0)){var _1oA=_1oy+1|0;_1ox=_1oz.b;_1oy=_1oA;continue;}else{return E(_);}}}},_=B(_1ow(_1nP.b,0,_));return new T4(0,E(_18j),E(_1oq),_1ov,_1ou);}}else{return E(_15J);}};if(0>_1oq){return new F(function(){return _1or(0);});}else{return new F(function(){return _1or(_1oq+1|0);});}};return B(_15K(_1op));}),_1oB=function(_1oC){var _1oD=function(_1oE){return (!E(_1oa))?__Z:(!E(_1oj))?__Z:new T2(1,new T2(0,_1nV,new T(function(){var _1oF=E(_1oo),_1oG=E(_1oF.a),_1oH=E(_1oF.b),_1oI=E(_1nW);if(_1oG>_1oI){return B(_1cV(_1oI,_1oG,_1oH));}else{if(_1oI>_1oH){return B(_1cV(_1oI,_1oG,_1oH));}else{return E(_1oF.d[_1oI-_1oG|0]);}}})),new T2(1,new T2(0,_1oh,new T(function(){var _1oJ=E(_1oo),_1oK=E(_1oJ.a),_1oL=E(_1oJ.b),_1oM=E(_1oi);if(_1oK>_1oM){return B(_1cV(_1oM,_1oK,_1oL));}else{if(_1oM>_1oL){return B(_1cV(_1oM,_1oK,_1oL));}else{return E(_1oJ.d[_1oM-_1oK|0]);}}})),_S));};if(!E(_1oa)){if(!E(_1oj)){return new F(function(){return _1oD(_);});}else{return new T2(1,new T2(0,_1oh,new T(function(){var _1oN=E(_1oo),_1oO=E(_1oN.a),_1oP=E(_1oN.b),_1oQ=E(_1oi);if(_1oO>_1oQ){return B(_1cV(_1oQ,_1oO,_1oP));}else{if(_1oQ>_1oP){return B(_1cV(_1oQ,_1oO,_1oP));}else{return E(_1oN.d[_1oQ-_1oO|0]);}}})),_S);}}else{return new F(function(){return _1oD(_);});}};if(!E(_1oa)){var _1oR=B(_1oB(_));}else{if(!E(_1oj)){var _1oS=new T2(1,new T2(0,_1nV,new T(function(){var _1oT=E(_1oo),_1oU=E(_1oT.a),_1oV=E(_1oT.b),_1oW=E(_1nW);if(_1oU>_1oW){return B(_1cV(_1oW,_1oU,_1oV));}else{if(_1oW>_1oV){return B(_1cV(_1oW,_1oU,_1oV));}else{return E(_1oT.d[_1oW-_1oU|0]);}}})),_S);}else{var _1oS=B(_1oB(_));}var _1oR=_1oS;}if(!B(_1jp(_1n6,_1oR,_S))){return new F(function(){return _q(_1oR,new T(function(){return B(_1nD(_1nI,_1nJ,_1nM));},1));});}else{if(!E(_1nS)){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{if(!B(_1nw(_1nV))){if(!B(_1nw(_1oh))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{if(!E(_1oa)){if(!E(_1oj)){if(!B(_68(_1nV,_S))){if(!B(_1kZ(_1nV))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{return new T2(1,new T2(0,_1oh,new T(function(){var _1oZ=B(_Gd(B(_sy(_1nC,_1nV))));if(!_1oZ._){return E(_1nA);}else{if(!E(_1oZ.b)._){return E(_1oZ.a);}else{return E(_1nB);}}})),new T(function(){return B(_1nD(_1nI,_1nJ,_1nM));}));}}else{var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}else{var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}else{var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}}else{if(!E(_1oa)){if(!E(_1oj)){if(!B(_68(_1oh,_S))){if(!B(_1kZ(_1oh))){if(!B(_1nw(_1oh))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{if(!B(_68(_1nV,_S))){if(!B(_1kZ(_1nV))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{return new T2(1,new T2(0,_1oh,new T(function(){var _1p0=B(_Gd(B(_sy(_1nC,_1nV))));if(!_1p0._){return E(_1nA);}else{if(!E(_1p0.b)._){return E(_1p0.a);}else{return E(_1nB);}}})),new T(function(){return B(_1nD(_1nI,_1nJ,_1nM));}));}}else{var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}}else{return new T2(1,new T2(0,_1nV,new T(function(){var _1p1=B(_Gd(B(_sy(_1nC,_1oh))));if(!_1p1._){return E(_1nA);}else{if(!E(_1p1.b)._){return E(_1p1.a);}else{return E(_1nB);}}})),new T(function(){return B(_1nD(_1nI,_1nJ,_1nM));}));}}else{if(!B(_1nw(_1oh))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{if(!B(_68(_1nV,_S))){if(!B(_1kZ(_1nV))){var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}else{return new T2(1,new T2(0,_1oh,new T(function(){var _1p2=B(_Gd(B(_sy(_1nC,_1nV))));if(!_1p2._){return E(_1nA);}else{if(!E(_1p2.b)._){return E(_1p2.a);}else{return E(_1nB);}}})),new T(function(){return B(_1nD(_1nI,_1nJ,_1nM));}));}}else{var _1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}}}else{var _1p3=B(_1nw(_1oh)),_1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}else{var _1p4=B(_1nw(_1oh)),_1oX=_1nI,_1oY=_1nJ;_1nE=_1oX;_1nF=_1oY;_1nG=_1nM;return __continue;}}}}}})(_1nE,_1nF,_1nG));if(_1nH!=__continue){return _1nH;}}},_1p5=102,_1p6=101,_1p7=new T(function(){return B(unCStr("=="));}),_1p8=new T(function(){return B(_e6("Action.hs:(103,17)-(107,70)|case"));}),_1p9=new T(function(){return B(_e6("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1pa=5,_1pb=117,_1pc=98,_1pd=110,_1pe=118,_1pf=function(_1pg,_1ph,_1pi,_1pj,_1pk,_1pl,_1pm,_1pn,_1po,_1pp,_1pq,_1pr,_1ps,_1pt){var _1pu=B(_6Q(B(_6Q(_1pk,_1ph)),_1pg)),_1pv=_1pu.a,_1pw=_1pu.b;if(E(_1pn)==32){if(!B(_4A(_h6,_1pv,_1mL))){var _1px=false;}else{switch(E(_1pw)){case 0:var _1py=true;break;case 1:var _1py=false;break;case 2:var _1py=false;break;case 3:var _1py=false;break;case 4:var _1py=false;break;case 5:var _1py=false;break;case 6:var _1py=false;break;case 7:var _1py=false;break;default:var _1py=false;}var _1px=_1py;}var _1pz=_1px;}else{var _1pz=false;}if(E(_1pn)==32){if(E(_1pv)==32){var _1pA=false;}else{switch(E(_1pw)){case 0:if(!E(_1pz)){var _1pB=true;}else{var _1pB=false;}var _1pC=_1pB;break;case 1:var _1pC=false;break;case 2:var _1pC=false;break;case 3:var _1pC=false;break;case 4:var _1pC=false;break;case 5:var _1pC=false;break;case 6:var _1pC=false;break;case 7:var _1pC=false;break;default:if(!E(_1pz)){var _1pD=true;}else{var _1pD=false;}var _1pC=_1pD;}var _1pA=_1pC;}var _1pE=_1pA;}else{var _1pE=false;}var _1pF=new T(function(){return B(_KQ(_1pg,_1ph,new T(function(){if(!E(_1pE)){if(!E(_1pz)){return E(_1pv);}else{return _1pm;}}else{return E(_UM);}}),_1pw,_1pk));});switch(E(_1pw)){case 3:var _1pG=true;break;case 4:if(E(_1pn)==32){var _1pH=true;}else{var _1pH=false;}var _1pG=_1pH;break;default:var _1pG=false;}if(!E(_1pG)){var _1pI=E(_1pF);}else{var _1pJ=E(_1pi),_1pK=new T(function(){return B(_6Q(_1pF,_1ph));}),_1pL=function(_1pM,_1pN){var _1pO=E(_1pM);if(_1pO==( -1)){return E(_1pF);}else{var _1pP=new T(function(){return B(_KQ(_1pg,_1ph,_UM,_E9,_1pF));}),_1pQ=E(_1pN);if(_1pQ==( -1)){var _1pR=__Z;}else{var _1pR=B(_6Q(_1pP,_1pQ));}if(E(B(_6Q(_1pR,_1pO)).a)==32){var _1pS=new T(function(){var _1pT=new T(function(){return B(_6Q(_1pK,_1pg));}),_1pU=new T2(1,new T2(0,new T(function(){return E(E(_1pT).a);}),new T(function(){return E(E(_1pT).b);})),new T(function(){var _1pV=_1pO+1|0;if(_1pV>0){return B(_1mE(_1pV,_1pR));}else{return E(_1pR);}}));if(0>=_1pO){return E(_1pU);}else{var _1pW=function(_1pX,_1pY){var _1pZ=E(_1pX);if(!_1pZ._){return E(_1pU);}else{var _1q0=_1pZ.a,_1q1=E(_1pY);return (_1q1==1)?new T2(1,_1q0,_1pU):new T2(1,_1q0,new T(function(){return B(_1pW(_1pZ.b,_1q1-1|0));}));}};return B(_1pW(_1pR,_1pO));}}),_1q2=new T2(1,_1pS,new T(function(){var _1q3=_1pN+1|0;if(_1q3>0){return B(_1my(_1q3,_1pP));}else{return E(_1pP);}}));if(0>=_1pN){return E(_1q2);}else{var _1q4=function(_1q5,_1q6){var _1q7=E(_1q5);if(!_1q7._){return E(_1q2);}else{var _1q8=_1q7.a,_1q9=E(_1q6);return (_1q9==1)?new T2(1,_1q8,_1q2):new T2(1,_1q8,new T(function(){return B(_1q4(_1q7.b,_1q9-1|0));}));}};return new F(function(){return _1q4(_1pP,_1pN);});}}else{return E(_1pF);}}};if(_1pg<=_1pJ){if(_1pJ<=_1pg){var _1qa=E(_1pj);if(_1ph<=_1qa){if(_1qa<=_1ph){var _1qb=E(_1p8);}else{var _1qc=E(_1ph);if(!_1qc){var _1qd=B(_1pL( -1, -1));}else{var _1qd=B(_1pL(_1pg,_1qc-1|0));}var _1qb=_1qd;}var _1qe=_1qb;}else{if(_1ph!=(B(_ms(_1pF,0))-1|0)){var _1qf=B(_1pL(_1pg,_1ph+1|0));}else{var _1qf=B(_1pL( -1, -1));}var _1qe=_1qf;}var _1qg=_1qe;}else{var _1qh=E(_1pg);if(!_1qh){var _1qi=B(_1pL( -1, -1));}else{var _1qi=B(_1pL(_1qh-1|0,_1ph));}var _1qg=_1qi;}var _1qj=_1qg;}else{if(_1pg!=(B(_ms(_1pK,0))-1|0)){var _1qk=B(_1pL(_1pg+1|0,_1ph));}else{var _1qk=B(_1pL( -1, -1));}var _1qj=_1qk;}var _1pI=_1qj;}if(!E(_1ps)){var _1ql=E(_1pI);}else{var _1qm=new T(function(){var _1qn=E(_1pI);if(!_1qn._){return E(_ng);}else{return B(_ms(_1qn.a,0));}}),_1qo=new T(function(){return B(_ms(_1pI,0));}),_1qp=function(_1qq,_1qr,_1qs,_1qt,_1qu,_1qv,_1qw){while(1){var _1qx=B((function(_1qy,_1qz,_1qA,_1qB,_1qC,_1qD,_1qE){var _1qF=E(_1qE);if(!_1qF._){return E(_1qB);}else{var _1qG=_1qF.b,_1qH=E(_1qF.a);if(!_1qH._){return E(_1p9);}else{var _1qI=_1qH.b,_1qJ=E(_1qH.a);if(E(_1qJ.b)==5){var _1qK=new T(function(){var _1qL=B(_1mt(_1pa,_1qy));return new T2(0,_1qL.a,_1qL.b);}),_1qM=new T(function(){var _1qN=function(_1qO,_1qP){var _1qQ=function(_1qR){return new F(function(){return _KQ(_1qz,_1qA,_UM,_E9,new T(function(){return B(_KQ(_1qO,_1qP,_1qJ.a,_EY,_1qB));}));});};if(_1qO!=_1qz){return new F(function(){return _1qQ(_);});}else{if(_1qP!=_1qA){return new F(function(){return _1qQ(_);});}else{return E(_1qB);}}};switch(E(E(_1qK).a)){case 1:var _1qS=_1qz-1|0;if(_1qS<0){return B(_1qN(_1qz,_1qA));}else{if(_1qS>=E(_1qm)){return B(_1qN(_1qz,_1qA));}else{if(_1qA<0){return B(_1qN(_1qz,_1qA));}else{if(_1qA>=E(_1qo)){return B(_1qN(_1qz,_1qA));}else{if(_1qS!=_1qC){if(E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qS)).a)==32){return B(_1qN(_1qS,_1qA));}else{return B(_1qN(_1qz,_1qA));}}else{if(_1qA!=_1qD){if(E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qS)).a)==32){return B(_1qN(_1qS,_1qA));}else{return B(_1qN(_1qz,_1qA));}}else{return B(_1qN(_1qz,_1qA));}}}}}}break;case 2:if(_1qz<0){return B(_1qN(_1qz,_1qA));}else{if(_1qz>=E(_1qm)){return B(_1qN(_1qz,_1qA));}else{var _1qT=_1qA-1|0;if(_1qT<0){return B(_1qN(_1qz,_1qA));}else{if(_1qT>=E(_1qo)){return B(_1qN(_1qz,_1qA));}else{if(_1qz!=_1qC){if(E(B(_6Q(B(_6Q(_1qB,_1qT)),_1qz)).a)==32){return B(_1qN(_1qz,_1qT));}else{return B(_1qN(_1qz,_1qA));}}else{if(_1qT!=_1qD){if(E(B(_6Q(B(_6Q(_1qB,_1qT)),_1qz)).a)==32){return B(_1qN(_1qz,_1qT));}else{return B(_1qN(_1qz,_1qA));}}else{return B(_1qN(_1qz,_1qA));}}}}}}break;case 3:var _1qU=_1qz+1|0;if(_1qU<0){return B(_1qN(_1qz,_1qA));}else{if(_1qU>=E(_1qm)){return B(_1qN(_1qz,_1qA));}else{if(_1qA<0){return B(_1qN(_1qz,_1qA));}else{if(_1qA>=E(_1qo)){return B(_1qN(_1qz,_1qA));}else{if(_1qU!=_1qC){if(E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qU)).a)==32){return B(_1qN(_1qU,_1qA));}else{return B(_1qN(_1qz,_1qA));}}else{if(_1qA!=_1qD){if(E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qU)).a)==32){return B(_1qN(_1qU,_1qA));}else{return B(_1qN(_1qz,_1qA));}}else{return B(_1qN(_1qz,_1qA));}}}}}}break;case 4:if(_1qz<0){return B(_1qN(_1qz,_1qA));}else{if(_1qz>=E(_1qm)){return B(_1qN(_1qz,_1qA));}else{var _1qV=_1qA+1|0;if(_1qV<0){return B(_1qN(_1qz,_1qA));}else{if(_1qV>=E(_1qo)){return B(_1qN(_1qz,_1qA));}else{if(_1qz!=_1qC){if(E(B(_6Q(B(_6Q(_1qB,_1qV)),_1qz)).a)==32){return B(_1qN(_1qz,_1qV));}else{return B(_1qN(_1qz,_1qA));}}else{if(_1qV!=_1qD){if(E(B(_6Q(B(_6Q(_1qB,_1qV)),_1qz)).a)==32){return B(_1qN(_1qz,_1qV));}else{return B(_1qN(_1qz,_1qA));}}else{return B(_1qN(_1qz,_1qA));}}}}}}break;default:if(_1qz<0){return B(_1qN(_1qz,_1qA));}else{if(_1qz>=E(_1qm)){return B(_1qN(_1qz,_1qA));}else{if(_1qA<0){return B(_1qN(_1qz,_1qA));}else{if(_1qA>=E(_1qo)){return B(_1qN(_1qz,_1qA));}else{if(_1qz!=_1qC){var _1qW=E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qz)).a);return B(_1qN(_1qz,_1qA));}else{if(_1qA!=_1qD){var _1qX=E(B(_6Q(B(_6Q(_1qB,_1qA)),_1qz)).a);return B(_1qN(_1qz,_1qA));}else{return B(_1qN(_1qz,_1qA));}}}}}}}}),_1qY=E(_1qI);if(!_1qY._){var _1qZ=_1qA+1|0,_1r0=_1qC,_1r1=_1qD;_1qq=new T(function(){return E(E(_1qK).b);},1);_1qr=0;_1qs=_1qZ;_1qt=_1qM;_1qu=_1r0;_1qv=_1r1;_1qw=_1qG;return __continue;}else{return new F(function(){return _1r2(new T(function(){return E(E(_1qK).b);},1),_1qz+1|0,_1qA,_1qM,_1qC,_1qD,_1qY.a,_1qY.b,_1qG);});}}else{var _1r3=E(_1qI);if(!_1r3._){var _1r4=_1qy,_1qZ=_1qA+1|0,_1r5=_1qB,_1r0=_1qC,_1r1=_1qD;_1qq=_1r4;_1qr=0;_1qs=_1qZ;_1qt=_1r5;_1qu=_1r0;_1qv=_1r1;_1qw=_1qG;return __continue;}else{return new F(function(){return _1r2(_1qy,_1qz+1|0,_1qA,_1qB,_1qC,_1qD,_1r3.a,_1r3.b,_1qG);});}}}}})(_1qq,_1qr,_1qs,_1qt,_1qu,_1qv,_1qw));if(_1qx!=__continue){return _1qx;}}},_1r2=function(_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re){while(1){var _1rf=B((function(_1rg,_1rh,_1ri,_1rj,_1rk,_1rl,_1rm,_1rn,_1ro){var _1rp=E(_1rm);if(E(_1rp.b)==5){var _1rq=new T(function(){var _1rr=B(_1mt(_1pa,_1rg));return new T2(0,_1rr.a,_1rr.b);}),_1rs=new T(function(){var _1rt=function(_1ru,_1rv){var _1rw=function(_1rx){return new F(function(){return _KQ(_1rh,_1ri,_UM,_E9,new T(function(){return B(_KQ(_1ru,_1rv,_1rp.a,_EY,_1rj));}));});};if(_1ru!=_1rh){return new F(function(){return _1rw(_);});}else{if(_1rv!=_1ri){return new F(function(){return _1rw(_);});}else{return E(_1rj);}}};switch(E(E(_1rq).a)){case 1:var _1ry=_1rh-1|0;if(_1ry<0){return B(_1rt(_1rh,_1ri));}else{if(_1ry>=E(_1qm)){return B(_1rt(_1rh,_1ri));}else{if(_1ri<0){return B(_1rt(_1rh,_1ri));}else{if(_1ri>=E(_1qo)){return B(_1rt(_1rh,_1ri));}else{if(_1ry!=_1rk){if(E(B(_6Q(B(_6Q(_1rj,_1ri)),_1ry)).a)==32){return B(_1rt(_1ry,_1ri));}else{return B(_1rt(_1rh,_1ri));}}else{if(_1ri!=_1rl){if(E(B(_6Q(B(_6Q(_1rj,_1ri)),_1ry)).a)==32){return B(_1rt(_1ry,_1ri));}else{return B(_1rt(_1rh,_1ri));}}else{return B(_1rt(_1rh,_1ri));}}}}}}break;case 2:if(_1rh<0){return B(_1rt(_1rh,_1ri));}else{if(_1rh>=E(_1qm)){return B(_1rt(_1rh,_1ri));}else{var _1rz=_1ri-1|0;if(_1rz<0){return B(_1rt(_1rh,_1ri));}else{if(_1rz>=E(_1qo)){return B(_1rt(_1rh,_1ri));}else{if(_1rh!=_1rk){if(E(B(_6Q(B(_6Q(_1rj,_1rz)),_1rh)).a)==32){return B(_1rt(_1rh,_1rz));}else{return B(_1rt(_1rh,_1ri));}}else{if(_1rz!=_1rl){if(E(B(_6Q(B(_6Q(_1rj,_1rz)),_1rh)).a)==32){return B(_1rt(_1rh,_1rz));}else{return B(_1rt(_1rh,_1ri));}}else{return B(_1rt(_1rh,_1ri));}}}}}}break;case 3:var _1rA=_1rh+1|0;if(_1rA<0){return B(_1rt(_1rh,_1ri));}else{if(_1rA>=E(_1qm)){return B(_1rt(_1rh,_1ri));}else{if(_1ri<0){return B(_1rt(_1rh,_1ri));}else{if(_1ri>=E(_1qo)){return B(_1rt(_1rh,_1ri));}else{if(_1rA!=_1rk){if(E(B(_6Q(B(_6Q(_1rj,_1ri)),_1rA)).a)==32){return B(_1rt(_1rA,_1ri));}else{return B(_1rt(_1rh,_1ri));}}else{if(_1ri!=_1rl){if(E(B(_6Q(B(_6Q(_1rj,_1ri)),_1rA)).a)==32){return B(_1rt(_1rA,_1ri));}else{return B(_1rt(_1rh,_1ri));}}else{return B(_1rt(_1rh,_1ri));}}}}}}break;case 4:if(_1rh<0){return B(_1rt(_1rh,_1ri));}else{if(_1rh>=E(_1qm)){return B(_1rt(_1rh,_1ri));}else{var _1rB=_1ri+1|0;if(_1rB<0){return B(_1rt(_1rh,_1ri));}else{if(_1rB>=E(_1qo)){return B(_1rt(_1rh,_1ri));}else{if(_1rh!=_1rk){if(E(B(_6Q(B(_6Q(_1rj,_1rB)),_1rh)).a)==32){return B(_1rt(_1rh,_1rB));}else{return B(_1rt(_1rh,_1ri));}}else{if(_1rB!=_1rl){if(E(B(_6Q(B(_6Q(_1rj,_1rB)),_1rh)).a)==32){return B(_1rt(_1rh,_1rB));}else{return B(_1rt(_1rh,_1ri));}}else{return B(_1rt(_1rh,_1ri));}}}}}}break;default:if(_1rh<0){return B(_1rt(_1rh,_1ri));}else{if(_1rh>=E(_1qm)){return B(_1rt(_1rh,_1ri));}else{if(_1ri<0){return B(_1rt(_1rh,_1ri));}else{if(_1ri>=E(_1qo)){return B(_1rt(_1rh,_1ri));}else{if(_1rh!=_1rk){var _1rC=E(B(_6Q(B(_6Q(_1rj,_1ri)),_1rh)).a);return B(_1rt(_1rh,_1ri));}else{if(_1ri!=_1rl){var _1rD=E(B(_6Q(B(_6Q(_1rj,_1ri)),_1rh)).a);return B(_1rt(_1rh,_1ri));}else{return B(_1rt(_1rh,_1ri));}}}}}}}}),_1rE=E(_1rn);if(!_1rE._){return new F(function(){return _1qp(new T(function(){return E(E(_1rq).b);},1),0,_1ri+1|0,_1rs,_1rk,_1rl,_1ro);});}else{var _1rF=_1rh+1|0,_1rG=_1ri,_1rH=_1rk,_1rI=_1rl,_1rJ=_1ro;_1r6=new T(function(){return E(E(_1rq).b);},1);_1r7=_1rF;_1r8=_1rG;_1r9=_1rs;_1ra=_1rH;_1rb=_1rI;_1rc=_1rE.a;_1rd=_1rE.b;_1re=_1rJ;return __continue;}}else{var _1rK=E(_1rn);if(!_1rK._){return new F(function(){return _1qp(_1rg,0,_1ri+1|0,_1rj,_1rk,_1rl,_1ro);});}else{var _1rL=_1rg,_1rF=_1rh+1|0,_1rG=_1ri,_1rM=_1rj,_1rH=_1rk,_1rI=_1rl,_1rJ=_1ro;_1r6=_1rL;_1r7=_1rF;_1r8=_1rG;_1r9=_1rM;_1ra=_1rH;_1rb=_1rI;_1rc=_1rK.a;_1rd=_1rK.b;_1re=_1rJ;return __continue;}}})(_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re));if(_1rf!=__continue){return _1rf;}}},_1ql=B(_1qp(_1pq,0,0,_1pI,_1pg,_1ph,_1pI));}var _1rN=function(_1rO){var _1rP=function(_1rQ){var _1rR=new T(function(){switch(E(_1pw)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1rS=new T(function(){if(!E(_1pG)){if(!E(_1rR)){return new T2(0,_1pg,_1ph);}else{return new T2(0,_1pi,_1pj);}}else{if(!B(_1jp(_1jB,_1ql,_1pF))){if(!E(_1rR)){return new T2(0,_1pg,_1ph);}else{return new T2(0,_1pi,_1pj);}}else{return new T2(0,_1pi,_1pj);}}}),_1rT=new T(function(){return E(E(_1rS).b);}),_1rU=new T(function(){return E(E(_1rS).a);});if(!E(_1pG)){var _1rV=E(_1pt);}else{var _1rV=E(B(_1mc(new T(function(){return B(_1nD(_1po,_1pp,_1ql));}),_1ql)).a);}var _1rW=new T(function(){if(!E(_1pE)){if(!E(_1pz)){var _1rX=function(_1rY){var _1rZ=function(_1s0){var _1s1=E(_1pw);if(_1s1==4){return new T2(1,_1pd,new T2(1,_1pv,_S));}else{if(!E(_1rR)){return (E(_1s1)==2)?new T2(1,_1pb,new T2(1,_1pv,_S)):__Z;}else{var _1s2=E(_1pv);return (E(_1s2)==61)?new T2(1,_1pc,new T2(1,_1s2,new T(function(){return B(_A(0,_1ph,_S));}))):new T2(1,_1pc,new T2(1,_1s2,_S));}}};if(!E(_1pG)){return new F(function(){return _1rZ(_);});}else{if(E(_1pi)!=E(_1rU)){return new T2(1,_1pe,new T2(1,_1pv,_S));}else{if(E(_1pj)!=E(_1rT)){return new T2(1,_1pe,new T2(1,_1pv,_S));}else{return new F(function(){return _1rZ(_);});}}}};if(!E(_1pG)){return B(_1rX(_));}else{if(!E(_1rV)){return B(_1rX(_));}else{return E(_1p7);}}}else{return new T2(1,_1p5,new T2(1,_1pv,_S));}}else{return new T2(1,_1p6,new T2(1,_1pv,_S));}},1);return {_:0,a:E(new T2(0,_1rU,_1rT)),b:E(_1ql),c:E(_1pl),d:_1rO,e:_1rQ,f:_1po,g:E(_1pp),h:_1pq,i:E(B(_q(_1pr,_1rW))),j:E(_1ps),k:E(_1rV)};};if(!E(_1pE)){return new F(function(){return _1rP(_1pn);});}else{return new F(function(){return _1rP(E(_1pv));});}};if(!E(_1pz)){return new F(function(){return _1rN(_1pm);});}else{return new F(function(){return _1rN(E(_1pv));});}},_1s3=new T2(1,_5U,_S),_1s4=5,_1s5=new T2(1,_1s4,_S),_1s6=function(_1s7,_1s8){while(1){var _1s9=E(_1s7);if(!_1s9._){return E(_1s8);}else{_1s7=_1s9.b;_1s8=_1s9.a;continue;}}},_1sa=57,_1sb=48,_1sc=new T2(1,_1mK,_S),_1sd=new T(function(){return B(err(_st));}),_1se=new T(function(){return B(err(_sr));}),_1sf=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_1sg=function(_1sh,_1si){if((_1si-48|0)>>>0>9){var _1sj=_1si+_1sh|0,_1sk=function(_1sl){if(!B(_4A(_h6,_1sl,_1sc))){return E(_1sl);}else{return new F(function(){return _1sg(_1sh,_1sl);});}};if(_1sj<=122){if(_1sj>=97){if(_1sj>>>0>1114111){return new F(function(){return _wE(_1sj);});}else{return new F(function(){return _1sk(_1sj);});}}else{if(_1sj<=90){if(_1sj>>>0>1114111){return new F(function(){return _wE(_1sj);});}else{return new F(function(){return _1sk(_1sj);});}}else{var _1sm=65+(_1sj-90|0)|0;if(_1sm>>>0>1114111){return new F(function(){return _wE(_1sm);});}else{return new F(function(){return _1sk(_1sm);});}}}}else{var _1sn=97+(_1sj-122|0)|0;if(_1sn>>>0>1114111){return new F(function(){return _wE(_1sn);});}else{return new F(function(){return _1sk(_1sn);});}}}else{var _1so=B(_Gd(B(_sy(_1sf,new T2(1,_1si,_S)))));if(!_1so._){return E(_1se);}else{if(!E(_1so.b)._){var _1sp=E(_1so.a)+_1sh|0;switch(_1sp){case  -1:return E(_1sb);case 10:return E(_1sa);default:return new F(function(){return _1s6(B(_A(0,_1sp,_S)),_Tn);});}}else{return E(_1sd);}}}},_1sq=function(_1sr,_1ss){if((_1sr-48|0)>>>0>9){return _1ss;}else{var _1st=B(_Gd(B(_sy(_1sf,new T2(1,_1sr,_S)))));if(!_1st._){return E(_1se);}else{if(!E(_1st.b)._){return new F(function(){return _1sg(E(_1st.a),_1ss);});}else{return E(_1sd);}}}},_1su=function(_1sv,_1sw){return new F(function(){return _1sq(E(_1sv),E(_1sw));});},_1sx=new T2(1,_1su,_S),_1sy=112,_1sz=111,_1sA=function(_1sB,_1sC,_1sD,_1sE,_1sF,_1sG,_1sH,_1sI,_1sJ,_1sK,_1sL,_1sM){var _1sN=new T(function(){return B(_6Q(B(_6Q(_1sD,_1sC)),E(_1sB)));}),_1sO=new T(function(){return E(E(_1sN).b);}),_1sP=new T(function(){if(E(_1sO)==4){return true;}else{return false;}}),_1sQ=new T(function(){return E(E(_1sN).a);});if(E(_1sG)==32){var _1sR=false;}else{if(E(_1sQ)==32){var _1sS=true;}else{var _1sS=false;}var _1sR=_1sS;}var _1sT=new T(function(){var _1sU=new T(function(){return B(A3(_6Q,_1s3,B(_MD(_h6,_1sF,_1mL)),_1sG));});if(!E(_1sR)){if(!E(_1sP)){return E(_1sQ);}else{if(!B(_4A(_3L,_1sH,_1s5))){return E(_1sQ);}else{return B(A(_6Q,[_1sx,B(_MD(_3L,_1sH,_1s5)),_1sU,_1sQ]));}}}else{return E(_1sU);}}),_1sV=B(_KQ(_1sB,_1sC,_1sT,_1sO,_1sD)),_1sW=function(_1sX){var _1sY=B(_1mc(new T(function(){return B(_1nD(_1sH,_1sI,_1sV));}),_1sV)).a;return {_:0,a:E(new T2(0,_1sB,_1sC)),b:E(_1sV),c:E(_1sE),d:_1sF,e:_1sX,f:_1sH,g:E(_1sI),h:_1sJ,i:E(B(_q(_1sK,new T(function(){if(!E(_1sY)){if(!E(_1sR)){if(!E(_1sP)){return __Z;}else{return new T2(1,_1sy,new T2(1,_1sT,_S));}}else{return new T2(1,_1sz,new T2(1,_1sT,_S));}}else{return E(_1p7);}},1)))),j:E(_1sL),k:E(_1sY)};};if(!E(_1sR)){return new F(function(){return _1sW(_1sG);});}else{return new F(function(){return _1sW(32);});}},_1sZ=4,_1t0=new T(function(){return B(_e6("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1t1=function(_1t2,_1t3){while(1){var _1t4=E(_1t3);if(!_1t4._){return false;}else{var _1t5=_1t4.b,_1t6=E(_1t2),_1t7=_1t6.a,_1t8=_1t6.b,_1t9=E(_1t4.a);if(!_1t9._){return E(_1t0);}else{var _1ta=E(_1t9.a),_1tb=_1ta.a,_1tc=_1ta.b,_1td=E(_1t9.b);if(!_1td._){var _1te=E(_1t7),_1tf=E(_1te);if(_1tf==32){switch(E(_1t8)){case 0:if(!E(_1tc)){return true;}else{_1t2=new T2(0,_1te,_E9);_1t3=_1t5;continue;}break;case 1:if(E(_1tc)==1){return true;}else{_1t2=new T2(0,_1te,_Ef);_1t3=_1t5;continue;}break;case 2:if(E(_1tc)==2){return true;}else{_1t2=new T2(0,_1te,_El);_1t3=_1t5;continue;}break;case 3:if(E(_1tc)==3){return true;}else{_1t2=new T2(0,_1te,_Er);_1t3=_1t5;continue;}break;case 4:if(E(_1tc)==4){return true;}else{_1t2=new T2(0,_1te,_Ex);_1t3=_1t5;continue;}break;case 5:if(E(_1tc)==5){return true;}else{_1t2=new T2(0,_1te,_EY);_1t3=_1t5;continue;}break;case 6:if(E(_1tc)==6){return true;}else{_1t2=new T2(0,_1te,_ER);_1t3=_1t5;continue;}break;case 7:if(E(_1tc)==7){return true;}else{_1t2=new T2(0,_1te,_EK);_1t3=_1t5;continue;}break;default:if(E(_1tc)==8){return true;}else{_1t2=new T2(0,_1te,_ED);_1t3=_1t5;continue;}}}else{if(_1tf!=E(_1tb)){_1t2=_1t6;_1t3=_1t5;continue;}else{switch(E(_1t8)){case 0:if(!E(_1tc)){return true;}else{_1t2=new T2(0,_1te,_E9);_1t3=_1t5;continue;}break;case 1:if(E(_1tc)==1){return true;}else{_1t2=new T2(0,_1te,_Ef);_1t3=_1t5;continue;}break;case 2:if(E(_1tc)==2){return true;}else{_1t2=new T2(0,_1te,_El);_1t3=_1t5;continue;}break;case 3:if(E(_1tc)==3){return true;}else{_1t2=new T2(0,_1te,_Er);_1t3=_1t5;continue;}break;case 4:if(E(_1tc)==4){return true;}else{_1t2=new T2(0,_1te,_Ex);_1t3=_1t5;continue;}break;case 5:if(E(_1tc)==5){return true;}else{_1t2=new T2(0,_1te,_EY);_1t3=_1t5;continue;}break;case 6:if(E(_1tc)==6){return true;}else{_1t2=new T2(0,_1te,_ER);_1t3=_1t5;continue;}break;case 7:if(E(_1tc)==7){return true;}else{_1t2=new T2(0,_1te,_EK);_1t3=_1t5;continue;}break;default:if(E(_1tc)==8){return true;}else{_1t2=new T2(0,_1te,_ED);_1t3=_1t5;continue;}}}}}else{var _1tg=E(_1t7),_1th=E(_1tg);if(_1th==32){switch(E(_1t8)){case 0:if(!E(_1tc)){return true;}else{_1t2=new T2(0,_1tg,_E9);_1t3=new T2(1,_1td,_1t5);continue;}break;case 1:if(E(_1tc)==1){return true;}else{_1t2=new T2(0,_1tg,_Ef);_1t3=new T2(1,_1td,_1t5);continue;}break;case 2:if(E(_1tc)==2){return true;}else{_1t2=new T2(0,_1tg,_El);_1t3=new T2(1,_1td,_1t5);continue;}break;case 3:if(E(_1tc)==3){return true;}else{_1t2=new T2(0,_1tg,_Er);_1t3=new T2(1,_1td,_1t5);continue;}break;case 4:if(E(_1tc)==4){return true;}else{_1t2=new T2(0,_1tg,_Ex);_1t3=new T2(1,_1td,_1t5);continue;}break;case 5:if(E(_1tc)==5){return true;}else{_1t2=new T2(0,_1tg,_EY);_1t3=new T2(1,_1td,_1t5);continue;}break;case 6:if(E(_1tc)==6){return true;}else{_1t2=new T2(0,_1tg,_ER);_1t3=new T2(1,_1td,_1t5);continue;}break;case 7:if(E(_1tc)==7){return true;}else{_1t2=new T2(0,_1tg,_EK);_1t3=new T2(1,_1td,_1t5);continue;}break;default:if(E(_1tc)==8){return true;}else{_1t2=new T2(0,_1tg,_ED);_1t3=new T2(1,_1td,_1t5);continue;}}}else{if(_1th!=E(_1tb)){_1t2=_1t6;_1t3=new T2(1,_1td,_1t5);continue;}else{switch(E(_1t8)){case 0:if(!E(_1tc)){return true;}else{_1t2=new T2(0,_1tg,_E9);_1t3=new T2(1,_1td,_1t5);continue;}break;case 1:if(E(_1tc)==1){return true;}else{_1t2=new T2(0,_1tg,_Ef);_1t3=new T2(1,_1td,_1t5);continue;}break;case 2:if(E(_1tc)==2){return true;}else{_1t2=new T2(0,_1tg,_El);_1t3=new T2(1,_1td,_1t5);continue;}break;case 3:if(E(_1tc)==3){return true;}else{_1t2=new T2(0,_1tg,_Er);_1t3=new T2(1,_1td,_1t5);continue;}break;case 4:if(E(_1tc)==4){return true;}else{_1t2=new T2(0,_1tg,_Ex);_1t3=new T2(1,_1td,_1t5);continue;}break;case 5:if(E(_1tc)==5){return true;}else{_1t2=new T2(0,_1tg,_EY);_1t3=new T2(1,_1td,_1t5);continue;}break;case 6:if(E(_1tc)==6){return true;}else{_1t2=new T2(0,_1tg,_ER);_1t3=new T2(1,_1td,_1t5);continue;}break;case 7:if(E(_1tc)==7){return true;}else{_1t2=new T2(0,_1tg,_EK);_1t3=new T2(1,_1td,_1t5);continue;}break;default:if(E(_1tc)==8){return true;}else{_1t2=new T2(0,_1tg,_ED);_1t3=new T2(1,_1td,_1t5);continue;}}}}}}}}},_1ti=function(_1tj,_1tk){var _1tl=E(_1tj);if(!_1tl._){return __Z;}else{var _1tm=E(_1tk);return (_1tm._==0)?__Z:new T2(1,new T(function(){return new T2(0,new T2(1,_1tm.a,_1iy),E(_1tl.a).b);}),new T(function(){return B(_1ti(_1tl.b,_1tm.b));}));}},_1tn=new T(function(){return B(unCStr("\n"));}),_1to=function(_1tp,_1tq,_){var _1tr=jsWriteHandle(E(_1tp),toJSStr(E(_1tq)));return _gD;},_1ts=function(_1tt,_1tu,_){var _1tv=E(_1tt),_1tw=jsWriteHandle(_1tv,toJSStr(E(_1tu)));return new F(function(){return _1to(_1tv,_1tn,_);});},_1tx=function(_1ty){var _1tz=E(_1ty);if(!_1tz._){return __Z;}else{return new F(function(){return _q(_1tz.a,new T(function(){return B(_1tx(_1tz.b));},1));});}},_1tA=new T(function(){return B(unCStr("removed"));}),_1tB=new T(function(){return B(unCStr("loadError"));}),_1tC=new T(function(){return B(unCStr("saved"));}),_1tD=new T(function(){var _1tE=E(_1d6);if(!_1tE._){return E(_ng);}else{return E(_1tE.a);}}),_1tF=new T(function(){return B(_19q(_1cD,5,_1dm));}),_1tG=new T(function(){return B(unCStr("Thank you for playing!"));}),_1tH=17,_1tI=2,_1tJ=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1tK=10,_1tL=3,_1tM=new T(function(){return B(unCStr("Coding : yokoP"));}),_1tN=8,_1tO=new T(function(){return B(unCStr("Congratulations!"));}),_1tP=5,_1tQ=32,_1tR=new T2(0,_1tQ,_EY),_1tS=99,_1tT=64,_1tU=new T(function(){return B(_ms(_1dX,0));}),_1tV=new T(function(){return B(unCStr("loadError"));}),_1tW=new T(function(){return B(unCStr(","));}),_1tX=new T(function(){return B(unCStr("~"));}),_1tY=new T(function(){return B(unCStr("savedata"));}),_1tZ=new T(function(){return B(unCStr("---"));}),_1u0=0,_1u1=4,_1u2=6,_1u3=new T1(0,333),_1u4=new T(function(){return B(_8r(1,2147483647));}),_1u5=new T(function(){return B(unAppCStr("[]",_S));}),_1u6=new T(function(){return B(unCStr("\""));}),_1u7=new T2(1,_S,_S),_1u8=new T(function(){return B(_6d(_Zu,_1u7));}),_1u9=new T2(1,_6C,_S),_1ua=function(_1ub,_1uc){var _1ud=E(_1uc);return (_1ud._==0)?__Z:new T2(1,_1ub,new T2(1,_1ud.a,new T(function(){return B(_1ua(_1ub,_1ud.b));})));},_1ue=new T(function(){return B(unCStr("noContent"));}),_1uf=new T(function(){return B(unCStr("noHint"));}),_1ug=new T(function(){return B(err(_st));}),_1uh=new T(function(){return B(err(_sr));}),_1ui=new T(function(){return B(A3(_FB,_G4,_DE,_Fr));}),_1uj=function(_1uk,_1ul){var _1um=E(_1ul);if(!_1um._){var _1un=B(_Gd(B(_sy(_1ui,_1uk))));return (_1un._==0)?E(_1uh):(E(_1un.b)._==0)?new T4(0,E(_1un.a),_S,_S,_S):E(_1ug);}else{var _1uo=_1um.a,_1up=E(_1um.b);if(!_1up._){var _1uq=B(_Gd(B(_sy(_1ui,_1uk))));return (_1uq._==0)?E(_1uh):(E(_1uq.b)._==0)?new T4(0,E(_1uq.a),E(_1uo),E(_1uf),E(_1ue)):E(_1ug);}else{var _1ur=_1up.a,_1us=E(_1up.b);if(!_1us._){var _1ut=B(_Gd(B(_sy(_1ui,_1uk))));return (_1ut._==0)?E(_1uh):(E(_1ut.b)._==0)?new T4(0,E(_1ut.a),E(_1uo),E(_1ur),E(_1ue)):E(_1ug);}else{if(!E(_1us.b)._){var _1uu=B(_Gd(B(_sy(_1ui,_1uk))));return (_1uu._==0)?E(_1uh):(E(_1uu.b)._==0)?new T4(0,E(_1uu.a),E(_1uo),E(_1ur),E(_1us.a)):E(_1ug);}else{return new T4(0,0,_S,_S,_S);}}}}},_1uv=function(_1uw){var _1ux=E(_1uw);if(!_1ux._){return new F(function(){return _1uj(_S,_S);});}else{var _1uy=_1ux.a,_1uz=E(_1ux.b);if(!_1uz._){return new F(function(){return _1uj(new T2(1,_1uy,_S),_S);});}else{var _1uA=E(_1uy),_1uB=new T(function(){var _1uC=B(_H5(44,_1uz.a,_1uz.b));return new T2(0,_1uC.a,_1uC.b);});if(E(_1uA)==44){return new F(function(){return _1uj(_S,new T2(1,new T(function(){return E(E(_1uB).a);}),new T(function(){return E(E(_1uB).b);})));});}else{var _1uD=E(_1uB);return new F(function(){return _1uj(new T2(1,_1uA,_1uD.a),_1uD.b);});}}}},_1uE=function(_1uF){var _1uG=B(_1uv(_1uF));return new T4(0,_1uG.a,E(_1uG.b),E(_1uG.c),E(_1uG.d));},_1uH=function(_1uI){return (E(_1uI)==10)?true:false;},_1uJ=function(_1uK){var _1uL=E(_1uK);if(!_1uL._){return __Z;}else{var _1uM=new T(function(){var _1uN=B(_19T(_1uH,_1uL));return new T2(0,_1uN.a,new T(function(){var _1uO=E(_1uN.b);if(!_1uO._){return __Z;}else{return B(_1uJ(_1uO.b));}}));});return new T2(1,new T(function(){return E(E(_1uM).a);}),new T(function(){return E(E(_1uM).b);}));}},_1uP=new T(function(){return B(unCStr("57,\u5974\u56fd\u738b\u304c\u5f8c\u6f22\u304b\u3089\u91d1\u5370,<\u5f8c\u6f22\u66f8>\u306b\u8a18\u8f09\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\u8cc0\u5cf6\u306b\u3066<\u6f22\u59d4\u5974\u570b\u738b>\u3068\u523b\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\u898b\u3055\u308c\u308b**\u5927\u548c\u671d\u5ef7\u3068\u306e\u95dc\u4fc2\u306f\u4e0d\u660e\n239,<\u5351\u5f25\u547c>\u304c\u9b4f\u306b\u9063\u4f7f,\u652f\u90a3\u306e\u6b74\u53f2\u66f8<\u9b4f\u5fd7>\u306b\u8a18\u8f09\u3055\u308c\u3066\u3090\u308b\u5deb\u5973,<\u9b4f\u5fd7>\u502d\u4eba\u4f1d\u306b\u8a18\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\u5fb3\u5929\u7687 \u7a0e\u3092\u514d\u9664,<\u53e4\u4e8b\u8a18><\u65e5\u672c\u66f8\u7d00>\u306b\u8a18\u8f09\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c<\u6c11\u306e\u304b\u307e\u3069\u3088\u308a\u7159\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\u3057\u304f\u3066\u708a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\u4e2d\u306e\u4fee\u7e55\u3092\u5f8c\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d>\u306e\u6b66\u738b \u5357\u671d\u306e\u5b8b\u3078\u9063\u4f7f,\u96c4\u7565\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\u8aac,<\u5b8b\u66f8>\u502d\u570b\u50b3\u306b\u8a18\u8f09\u304c\u3042\u308b**\u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\u6559\u516c\u4f1d,\u6b3d\u660e\u5929\u7687\u5fa1\u4ee3\u306b\u767e\u6e08\u306e\u8056\u660e\u738b\u304b\u3089\u4f1d\u6765\u3057\u305f\u3068\u306e\u6587\u732e\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\u8aac\u3042\u308b\n604,\u5341\u4e03\u6761\u61b2\u6cd5\u5236\u5b9a,\u8056\u5fb3\u592a\u5b50\u304c\u5236\u5b9a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\u3092\u4ee5\u3066\u8cb4\u3057\u3068\u70ba\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\u304d\u3092\u5b97\u3068\u305b\u3088>\n607,\u6cd5\u9686\u5bfa\u304c\u5275\u5efa\u3055\u308c\u308b,\u8056\u5fb3\u592a\u5b50\u3086\u304b\u308a\u306e\u5bfa\u9662,\u897f\u9662\u4f3d\u85cd\u306f\u73fe\u5b58\u3059\u308b\u4e16\u754c\u6700\u53e4\u306e\u6728\u9020\u5efa\u7bc9\u7269\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\u5df3\u306e\u5909,\u3053\u306e\u5f8c\u3059\u3050\u5927\u5316\u306e\u6539\u65b0\u306a\u308b,\u4e2d\u5927\u5144\u7687\u5b50(\u5f8c\u306e38\u4ee3\u5929\u667a\u5929\u7687)\u304c\u8607\u6211\u6c0f\u3092\u4ea1\u307c\u3059\n663,\u767d\u6751\u6c5f\u306e\u6226,\u5510\u3068\u65b0\u7f85\u306b\u6ec5\u307c\u3055\u308c\u305f\u767e\u6e08\u3092\u518d\u8208\u3059\u308b\u76ee\u7684,\u5510\u30fb\u65b0\u7f85\u9023\u5408\u8ecd\u306b\u6557\u308c\u308b\n672,\u58ec\u7533\u306e\u4e71,\u5929\u667a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\u7d99\u8005\u4e89\u3072,\u5f8c\u7d99\u8005\u3067\u3042\u3063\u305f\u5927\u53cb\u7687\u5b50\u306b\u53d4\u7236\u306e\u5927\u6d77\u4eba\u7687\u5b50\u304c\u53cd\u65d7\u3092\u7ffb\u3057 \u5927\u53cb\u7687\u5b50\u3092\u5012\u3057\u3066\u5929\u6b66\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b<\u82b1\u306e\u5fa1\u6240>\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075<\u4e0b\u524b\u4e0a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d <\u5929\u4e0b\u5e03\u6b66>\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b<\u9396\u56fd>\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c<\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4>\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1uQ=new T(function(){return B(_1uJ(_1uP));}),_1uR=new T(function(){return B(_6d(_1uE,_1uQ));}),_1uS=new T(function(){return B(_8O(1,2));}),_1uT=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b\u300c\u4e0d\u5e73\u7b49\u300d\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,\u300c\u6276\u6e05\u6ec5\u6d0b\u300d\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***\u300c\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287\u300d\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b\u300c\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42\u300d,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059\u300d\u30fc\u30fc\u5f8c\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059\u300d"));}),_1uU=new T(function(){return B(_1uJ(_1uT));}),_1uV=new T(function(){return B(_6d(_1uE,_1uU));}),_1uW=function(_1uX,_1uY){var _1uZ=E(_1uX);if(!_1uZ._){return __Z;}else{var _1v0=E(_1uY);return (_1v0._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1uZ.a).a;}),_1v0.a),new T(function(){return B(_1uW(_1uZ.b,_1v0.b));}));}},_1v1=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1v2=new T(function(){return B(unCStr("tail"));}),_1v3=new T(function(){return B(_nd(_1v2));}),_1v4=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1v5=new T2(1,_2t,_S),_1v6=function(_1v7,_1v8){return new T2(1,_6C,new T(function(){return B(_8j(_1v7,new T2(1,_6C,_1v8)));}));},_1v9=function(_1va){var _1vb=E(_1va);if(!_1vb._){return E(_1v5);}else{var _1vc=new T(function(){var _1vd=E(_1vb.a),_1ve=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1vf){return new F(function(){return _1v6(_1vd.a,_1vf);});},new T2(1,function(_1vg){return new F(function(){return _1v6(_1vd.b,_1vg);});},_S)),new T2(1,_y,new T(function(){return B(_1v9(_1vb.b));}))));});return new T2(1,_z,_1ve);});return new T2(1,_2s,_1vc);}},_1vh=function(_1vi){var _1vj=E(_1vi);if(!_1vj._){return E(_1v5);}else{var _1vk=new T(function(){return B(_A(0,E(_1vj.a),new T(function(){return B(_1vh(_1vj.b));})));});return new T2(1,_2s,_1vk);}},_1vl=function(_1vm){var _1vn=E(_1vm);if(!_1vn._){return E(_1v5);}else{var _1vo=new T(function(){var _1vp=E(_1vn.a),_1vq=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1vr){return new F(function(){return _1v6(_1vp.a,_1vr);});},new T2(1,function(_1vs){return new F(function(){return _1v6(_1vp.b,_1vs);});},_S)),new T2(1,_y,new T(function(){return B(_1vl(_1vn.b));}))));});return new T2(1,_z,_1vq);});return new T2(1,_2s,_1vo);}},_1vt=new T(function(){return B(unCStr("True"));}),_1vu=new T(function(){return B(unCStr("False"));}),_1vv=function(_1vw){return E(E(_1vw).b);},_1vx=function(_1vy,_1vz,_1vA){var _1vB=new T(function(){var _1vC=E(_1vA);if(!_1vC._){return __Z;}else{var _1vD=_1vC.b,_1vE=E(_1vC.a),_1vF=E(_1vE.a);if(_1vF<_1vy){var _1vG=function(_1vH){while(1){var _1vI=B((function(_1vJ){var _1vK=E(_1vJ);if(!_1vK._){return __Z;}else{var _1vL=_1vK.b,_1vM=E(_1vK.a);if(E(_1vM.a)<_1vy){_1vH=_1vL;return __continue;}else{return new T2(1,_1vM,new T(function(){return B(_1vG(_1vL));}));}}})(_1vH));if(_1vI!=__continue){return _1vI;}}};return B(_1vN(B(_1vG(_1vD))));}else{var _1vO=new T(function(){var _1vP=function(_1vQ){while(1){var _1vR=B((function(_1vS){var _1vT=E(_1vS);if(!_1vT._){return __Z;}else{var _1vU=_1vT.b,_1vV=E(_1vT.a);if(E(_1vV.a)<_1vy){_1vQ=_1vU;return __continue;}else{return new T2(1,_1vV,new T(function(){return B(_1vP(_1vU));}));}}})(_1vQ));if(_1vR!=__continue){return _1vR;}}};return B(_1vP(_1vD));});return B(_1vx(_1vF,_1vE.b,_1vO));}}}),_1vW=E(_1vA);if(!_1vW._){return new F(function(){return _q(_S,new T2(1,new T2(0,_1vy,_1vz),_1vB));});}else{var _1vX=_1vW.b,_1vY=E(_1vW.a),_1vZ=E(_1vY.a);if(_1vZ>=_1vy){var _1w0=function(_1w1){while(1){var _1w2=B((function(_1w3){var _1w4=E(_1w3);if(!_1w4._){return __Z;}else{var _1w5=_1w4.b,_1w6=E(_1w4.a);if(E(_1w6.a)>=_1vy){_1w1=_1w5;return __continue;}else{return new T2(1,_1w6,new T(function(){return B(_1w0(_1w5));}));}}})(_1w1));if(_1w2!=__continue){return _1w2;}}};return new F(function(){return _q(B(_1vN(B(_1w0(_1vX)))),new T2(1,new T2(0,_1vy,_1vz),_1vB));});}else{var _1w7=new T(function(){var _1w8=function(_1w9){while(1){var _1wa=B((function(_1wb){var _1wc=E(_1wb);if(!_1wc._){return __Z;}else{var _1wd=_1wc.b,_1we=E(_1wc.a);if(E(_1we.a)>=_1vy){_1w9=_1wd;return __continue;}else{return new T2(1,_1we,new T(function(){return B(_1w8(_1wd));}));}}})(_1w9));if(_1wa!=__continue){return _1wa;}}};return B(_1w8(_1vX));});return new F(function(){return _q(B(_1vx(_1vZ,_1vY.b,_1w7)),new T2(1,new T2(0,_1vy,_1vz),_1vB));});}}},_1vN=function(_1wf){var _1wg=E(_1wf);if(!_1wg._){return __Z;}else{var _1wh=_1wg.b,_1wi=E(_1wg.a),_1wj=_1wi.a,_1wk=new T(function(){var _1wl=E(_1wh);if(!_1wl._){return __Z;}else{var _1wm=_1wl.b,_1wn=E(_1wl.a),_1wo=E(_1wn.a),_1wp=E(_1wj);if(_1wo<_1wp){var _1wq=function(_1wr){while(1){var _1ws=B((function(_1wt){var _1wu=E(_1wt);if(!_1wu._){return __Z;}else{var _1wv=_1wu.b,_1ww=E(_1wu.a);if(E(_1ww.a)<_1wp){_1wr=_1wv;return __continue;}else{return new T2(1,_1ww,new T(function(){return B(_1wq(_1wv));}));}}})(_1wr));if(_1ws!=__continue){return _1ws;}}};return B(_1vN(B(_1wq(_1wm))));}else{var _1wx=new T(function(){var _1wy=function(_1wz){while(1){var _1wA=B((function(_1wB){var _1wC=E(_1wB);if(!_1wC._){return __Z;}else{var _1wD=_1wC.b,_1wE=E(_1wC.a);if(E(_1wE.a)<_1wp){_1wz=_1wD;return __continue;}else{return new T2(1,_1wE,new T(function(){return B(_1wy(_1wD));}));}}})(_1wz));if(_1wA!=__continue){return _1wA;}}};return B(_1wy(_1wm));});return B(_1vx(_1wo,_1wn.b,_1wx));}}}),_1wF=E(_1wh);if(!_1wF._){return new F(function(){return _q(_S,new T2(1,_1wi,_1wk));});}else{var _1wG=_1wF.b,_1wH=E(_1wF.a),_1wI=E(_1wH.a),_1wJ=E(_1wj);if(_1wI>=_1wJ){var _1wK=function(_1wL){while(1){var _1wM=B((function(_1wN){var _1wO=E(_1wN);if(!_1wO._){return __Z;}else{var _1wP=_1wO.b,_1wQ=E(_1wO.a);if(E(_1wQ.a)>=_1wJ){_1wL=_1wP;return __continue;}else{return new T2(1,_1wQ,new T(function(){return B(_1wK(_1wP));}));}}})(_1wL));if(_1wM!=__continue){return _1wM;}}};return new F(function(){return _q(B(_1vN(B(_1wK(_1wG)))),new T2(1,_1wi,_1wk));});}else{var _1wR=new T(function(){var _1wS=function(_1wT){while(1){var _1wU=B((function(_1wV){var _1wW=E(_1wV);if(!_1wW._){return __Z;}else{var _1wX=_1wW.b,_1wY=E(_1wW.a);if(E(_1wY.a)>=_1wJ){_1wT=_1wX;return __continue;}else{return new T2(1,_1wY,new T(function(){return B(_1wS(_1wX));}));}}})(_1wT));if(_1wU!=__continue){return _1wU;}}};return B(_1wS(_1wG));});return new F(function(){return _q(B(_1vx(_1wI,_1wH.b,_1wR)),new T2(1,_1wi,_1wk));});}}}},_1wZ=function(_){return new F(function(){return jsMkStdout();});},_1x0=new T(function(){return B(_36(_1wZ));}),_1x1=new T(function(){return B(_Lh("Browser.hs:82:24-56|(Right j)"));}),_1x2=function(_1x3){var _1x4=jsParseJSON(toJSStr(E(_1x3)));return (_1x4._==0)?E(_1x1):E(_1x4.a);},_1x5=function(_1x6,_1x7,_1x8,_1x9,_1xa,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xm,_1xn,_1xo,_1xp,_1xq,_1xr,_1xs,_1xt,_1xu,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_1xB,_1xC,_1xD,_1xE,_1xF,_1xG,_1xH,_1xI,_1xJ,_1xK,_1xL,_1xM,_1xN,_1xO,_1xP,_){var _1xQ={_:0,a:E(_1xH),b:E(_1xI),c:E(_1xJ),d:E(_1xK),e:E(_1xL),f:E(_1xM),g:E(_1xN),h:E(_1xO)},_1xR=new T2(0,_1xE,_1xF),_1xS=new T2(0,_1xt,_1xu),_1xT=new T2(0,_1xm,_1xn),_1xU={_:0,a:E(_1xb),b:E(_1xc),c:E(_1xd),d:_1xe,e:_1xf,f:_1xg,g:E(_1xh),h:_1xi,i:E(_1xj),j:E(_1xk),k:E(_1xl)},_1xV={_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:_1xA,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)};if(!E(_1xM)){var _1xW=function(_1xX){if(!E(_1xK)){if(!E(_1xO)){return _1xV;}else{var _1xY=function(_,_1xZ,_1y0,_1y1,_1y2,_1y3,_1y4,_1y5,_1y6,_1y7,_1y8,_1y9,_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yg,_1yh,_1yi,_1yj,_1yk,_1yl,_1ym,_1yn,_1yo,_1yp,_1yq,_1yr,_1ys,_1yt,_1yu){var _1yv=function(_){var _1yw=function(_){var _1yx=function(_){var _1yy=B(_1ts(_1x0,new T2(1,_6C,new T(function(){return B(_8j(_1y7,_1u9));})),_)),_1yz=function(_){var _1yA=B(_1ts(_1x0,B(_A(0,_1xy,_S)),_)),_1yB=B(_14s(_1tP,_1y6,_)),_1yC=_1yB,_1yD=E(_1x6),_1yE=_1yD.a,_1yF=_1yD.b,_1yG=new T(function(){return B(_1jm(E(_1xa)));}),_1yH=new T(function(){var _1yI=E(_1yG),_1yJ=E(_1xZ),_1yK=_1yJ.a,_1yL=_1yJ.b,_1yM=function(_1yN,_1yO){var _1yP=E(_1yN),_1yQ=E(_1yO),_1yR=E(_1yK);if(_1yP<=_1yR){if(_1yR<=_1yP){var _1yS=E(_1yL);if(_1yQ<=_1yS){if(_1yS<=_1yQ){var _1yT=4;}else{var _1yT=0;}var _1yU=_1yT;}else{var _1yU=1;}var _1yV=_1yU;}else{var _1yV=2;}var _1yW=_1yV;}else{var _1yW=3;}var _1yX=function(_1yY,_1yZ,_1z0,_1z1,_1z2,_1z3,_1z4,_1z5,_1z6,_1z7){switch(E(_1yW)){case 0:if(!E(_1y1)){var _1z8=new T2(0,_1yq,_1yr);}else{var _1z8=new T2(0,_1yq,_1tI);}var _1z9=_1z8;break;case 1:if(E(_1y1)==1){var _1za=new T2(0,_1yq,_1yr);}else{var _1za=new T2(0,_1yq,_1u0);}var _1z9=_1za;break;case 2:if(E(_1y1)==2){var _1zb=new T2(0,_1yq,_1yr);}else{var _1zb=new T2(0,_1yq,_1u2);}var _1z9=_1zb;break;case 3:if(E(_1y1)==3){var _1zc=new T2(0,_1yq,_1yr);}else{var _1zc=new T2(0,_1yq,_1u1);}var _1z9=_1zc;break;default:if(E(_1y1)==4){var _1zd=new T2(0,_1yq,_1yr);}else{var _1zd=new T2(0,_1yq,_1u0);}var _1z9=_1zd;}var _1ze=B(_1gb(_1u0,_1z5,_1yd,{_:0,a:E(_1yY),b:E(_1yZ),c:E(_1z0),d:_1z1,e:_1z2,f:_1z3,g:E(_1z4),h:E(E(_1yC).b),i:E(_1z5),j:E(_1z6),k:E(_1z7)},_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yg,_1yh,_1yi,_1yj,_1yk,_1yl,_1ym,_1yn,_1yo,_1yp,_1z9,_1ys,_1yt,_1yu));return {_:0,a:E(_1ze.a),b:E(_1ze.b),c:E(_1ze.c),d:E(_1ze.d),e:E(_1ze.e),f:E(_1ze.f),g:E(_1ze.g),h:E(_1ze.h),i:_1ze.i,j:_1ze.j,k:_1ze.k,l:_1ze.l,m:E(_1ze.m),n:_1ze.n,o:E(_1ze.o),p:E(_1ze.p),q:_1ze.q,r:E(_1ze.r),s:_1ze.s,t:E(_1ze.t),u:E(_1ze.u)};};if(E(_1yI)==32){var _1zf=B(_1pf(_1yP,_1yQ,_1yR,_1yL,_1y0,_1yW,_1y2,_1y3,_1y4,_1y5,_1y6,_1y7,_1y8,_1y9)),_1zg=E(_1zf.a),_1zh=B(_1sA(_1zg.a,E(_1zg.b),_1zf.b,_1zf.c,_1zf.d,_1zf.e,_1zf.f,_1zf.g,_1zf.h,_1zf.i,_1zf.j,_1zf.k));return new F(function(){return _1yX(_1zh.a,_1zh.b,_1zh.c,_1zh.d,_1zh.e,_1zh.f,_1zh.g,_1zh.i,_1zh.j,_1zh.k);});}else{var _1zi=B(_1pf(_1yP,_1yQ,_1yR,_1yL,_1y0,_1yW,_1y2,_1y3,_1y4,_1y5,_1y6,_1y7,_1y8,_1y9));return new F(function(){return _1yX(_1zi.a,_1zi.b,_1zi.c,_1zi.d,_1zi.e,_1zi.f,_1zi.g,_1zi.i,_1zi.j,_1zi.k);});}};switch(E(_1yI)){case 72:var _1zj=E(_1yL);if(0<=(_1zj-1|0)){return B(_1yM(_1yK,_1zj-1|0));}else{return B(_1yM(_1yK,_1zj));}break;case 75:var _1zk=E(_1yK);if(0<=(_1zk-1|0)){return B(_1yM(_1zk-1|0,_1yL));}else{return B(_1yM(_1zk,_1yL));}break;case 77:var _1zl=E(_1yK);if(E(_1xm)!=(_1zl+1|0)){return B(_1yM(_1zl+1|0,_1yL));}else{return B(_1yM(_1zl,_1yL));}break;case 80:var _1zm=E(_1yL);if(E(_1xn)!=(_1zm+1|0)){return B(_1yM(_1yK,_1zm+1|0));}else{return B(_1yM(_1yK,_1zm));}break;case 104:var _1zn=E(_1yK);if(0<=(_1zn-1|0)){return B(_1yM(_1zn-1|0,_1yL));}else{return B(_1yM(_1zn,_1yL));}break;case 106:var _1zo=E(_1yL);if(E(_1xn)!=(_1zo+1|0)){return B(_1yM(_1yK,_1zo+1|0));}else{return B(_1yM(_1yK,_1zo));}break;case 107:var _1zp=E(_1yL);if(0<=(_1zp-1|0)){return B(_1yM(_1yK,_1zp-1|0));}else{return B(_1yM(_1yK,_1zp));}break;case 108:var _1zq=E(_1yK);if(E(_1xm)!=(_1zq+1|0)){return B(_1yM(_1zq+1|0,_1yL));}else{return B(_1yM(_1zq,_1yL));}break;default:return B(_1yM(_1yK,_1yL));}}),_1zr=B(_16V(_1yE,_1yF,_1x7,_1x8,_1x9,_1yH,_)),_1zs=_1zr,_1zt=E(_1yG),_1zu=function(_,_1zv){var _1zw=function(_1zx){var _1zy=B(_1ts(_1x0,B(_8p(_1zv)),_)),_1zz=E(_1zs),_1zA=_1zz.d,_1zB=_1zz.e,_1zC=_1zz.f,_1zD=_1zz.g,_1zE=_1zz.i,_1zF=_1zz.j,_1zG=_1zz.k,_1zH=_1zz.l,_1zI=_1zz.m,_1zJ=_1zz.n,_1zK=_1zz.o,_1zL=_1zz.p,_1zM=_1zz.q,_1zN=_1zz.s,_1zO=_1zz.u,_1zP=E(_1zz.t),_1zQ=_1zP.a,_1zR=_1zP.d,_1zS=_1zP.e,_1zT=_1zP.f,_1zU=_1zP.g,_1zV=_1zP.h,_1zW=E(_1zz.a),_1zX=_1zW.c,_1zY=_1zW.f,_1zZ=_1zW.g,_1A0=_1zW.h,_1A1=E(_1zz.h),_1A2=E(_1zz.r),_1A3=function(_1A4){var _1A5=function(_1A6){if(_1A6!=E(_1tU)){var _1A7=B(_6Q(_1cI,_1A6)),_1A8=_1A7.a,_1A9=E(_1A7.b),_1Aa=B(_19q(_1A8,_1A9,new T(function(){return B(_6Q(_1dX,_1A6));})));return new F(function(){return _1x5(_1yD,_1x7,_1x8,_1x9,_1tT,B(_6Q(_1cT,_1A6)),_1Aa,_1zX,B(_6Q(_1d6,_1A6)),32,_1A6,_1zZ,_1A0,B(_q(_1zW.i,new T2(1,_1tS,new T(function(){return B(_A(0,_1zY,_S));})))),B(_1t1(_1tR,_1Aa)),_wt,_1A8,_1A9,_S,_1zA,_1zB,_1zC,_1zD,_1A1.a,_1A1.b,_1zE,_1zF,_1zG, -1,_1zI,_1zJ,_1zK,_1zL,_1zM,_1A2.a,_1A2.b,_1zN,_wt,_wt,_wt,_1zR,_1zS,_1zT,_1zU,_1zV,_1zO,_);});}else{var _1Ab=__app1(E(_nh),_1yF),_1Ac=B(A2(_ni,_1yE,_)),_1Ad=B(A(_mN,[_1yE,_j2,_1tI,_1tP,_1tO,_])),_1Ae=B(A(_mN,[_1yE,_j2,_1tL,_1tN,_1tM,_])),_1Af=B(A(_mN,[_1yE,_j2,_1tL,_1tK,_1tJ,_])),_1Ag=B(A(_mN,[_1yE,_j2,_1tI,_1tH,_1tG,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1cS),b:E(_1tF),c:E(_1zX),d:E(_1tD),e:32,f:0,g:E(_1zZ),h:_1A0,i:E(_S),j:E(_1zW.j),k:E(_wt)}),b:E(_1cE),c:E(_1zz.c),d:E(_1zA),e:E(_1zB),f:E(_1zC),g:E(_1zD),h:E(_1A1),i:_1zE,j:_1zF,k:_1zG,l:_1zH,m:E(_1zI),n:_1zJ,o:E(_1zK),p:E(_1zL),q:_1zM,r:E(_1A2),s:_1zN,t:E({_:0,a:E(_1zQ),b:E(_wt),c:E(_wt),d:E(_1zR),e:E(_1zS),f:E(_1zT),g:E(_1zU),h:E(_1zV)}),u:E(_1zO)};});}};if(_1zH>=0){return new F(function(){return _1A5(_1zH);});}else{return new F(function(){return _1A5(_1zY+1|0);});}};if(!E(_1zQ)){if(E(_1zt)==110){return new F(function(){return _1A3(_);});}else{return _1zz;}}else{return new F(function(){return _1A3(_);});}};if(E(_1zt)==114){if(!B(_68(_1zv,_1tV))){var _1Ah=E(_1zv);if(!_1Ah._){return _1zs;}else{var _1Ai=_1Ah.b;return new T(function(){var _1Aj=E(_1zs),_1Ak=E(_1Aj.a),_1Al=E(_1Ah.a),_1Am=E(_1Al);if(_1Am==34){var _1An=B(_RQ(_1Al,_1Ai));if(!_1An._){var _1Ao=E(_1v3);}else{var _1Ap=E(_1An.b);if(!_1Ap._){var _1Aq=E(_1u7);}else{var _1Ar=_1Ap.a,_1As=E(_1Ap.b);if(!_1As._){var _1At=new T2(1,new T2(1,_1Ar,_S),_S);}else{var _1Au=E(_1Ar),_1Av=new T(function(){var _1Aw=B(_H5(126,_1As.a,_1As.b));return new T2(0,_1Aw.a,_1Aw.b);});if(E(_1Au)==126){var _1Ax=new T2(1,_S,new T2(1,new T(function(){return E(E(_1Av).a);}),new T(function(){return E(E(_1Av).b);})));}else{var _1Ax=new T2(1,new T2(1,_1Au,new T(function(){return E(E(_1Av).a);})),new T(function(){return E(E(_1Av).b);}));}var _1At=_1Ax;}var _1Aq=_1At;}var _1Ao=_1Aq;}var _1Ay=_1Ao;}else{var _1Az=E(_1Ai);if(!_1Az._){var _1AA=new T2(1,new T2(1,_1Al,_S),_S);}else{var _1AB=new T(function(){var _1AC=B(_H5(126,_1Az.a,_1Az.b));return new T2(0,_1AC.a,_1AC.b);});if(E(_1Am)==126){var _1AD=new T2(1,_S,new T2(1,new T(function(){return E(E(_1AB).a);}),new T(function(){return E(E(_1AB).b);})));}else{var _1AD=new T2(1,new T2(1,_1Al,new T(function(){return E(E(_1AB).a);})),new T(function(){return E(E(_1AB).b);}));}var _1AA=_1AD;}var _1Ay=_1AA;}var _1AE=B(_Gd(B(_sy(_Zt,new T(function(){return B(_Jh(_1Ay));})))));if(!_1AE._){return E(_Zr);}else{if(!E(_1AE.b)._){var _1AF=E(_1AE.a),_1AG=B(_6Q(_1cI,_1AF)),_1AH=B(_6Q(_1Ay,1));if(!_1AH._){var _1AI=__Z;}else{var _1AJ=E(_1AH.b);if(!_1AJ._){var _1AK=__Z;}else{var _1AL=E(_1AH.a),_1AM=new T(function(){var _1AN=B(_H5(44,_1AJ.a,_1AJ.b));return new T2(0,_1AN.a,_1AN.b);});if(E(_1AL)==44){var _1AO=B(_Zj(_S,new T(function(){return E(E(_1AM).a);}),new T(function(){return E(E(_1AM).b);})));}else{var _1AO=B(_Zn(new T2(1,_1AL,new T(function(){return E(E(_1AM).a);})),new T(function(){return E(E(_1AM).b);})));}var _1AK=_1AO;}var _1AI=_1AK;}var _1AP=B(_6Q(_1Ay,2));if(!_1AP._){var _1AQ=E(_1u8);}else{var _1AR=_1AP.a,_1AS=E(_1AP.b);if(!_1AS._){var _1AT=B(_6d(_Zu,new T2(1,new T2(1,_1AR,_S),_S)));}else{var _1AU=E(_1AR),_1AV=new T(function(){var _1AW=B(_H5(44,_1AS.a,_1AS.b));return new T2(0,_1AW.a,_1AW.b);});if(E(_1AU)==44){var _1AX=B(_6d(_Zu,new T2(1,_S,new T2(1,new T(function(){return E(E(_1AV).a);}),new T(function(){return E(E(_1AV).b);})))));}else{var _1AX=B(_6d(_Zu,new T2(1,new T2(1,_1AU,new T(function(){return E(E(_1AV).a);})),new T(function(){return E(E(_1AV).b);}))));}var _1AT=_1AX;}var _1AQ=_1AT;}return {_:0,a:E({_:0,a:E(B(_6Q(_1cT,_1AF))),b:E(B(_19q(_1AG.a,E(_1AG.b),new T(function(){return B(_6Q(_1dX,_1AF));})))),c:E(_1Ak.c),d:B(_6Q(_1d6,_1AF)),e:32,f:_1AF,g:E(_1Ak.g),h:_1Ak.h,i:E(_1Ak.i),j:E(_1Ak.j),k:E(_1Ak.k)}),b:E(_1AG),c:E(_1Aj.c),d:E(_1Aj.d),e:E(_1AI),f:E(_1AQ),g:E(_1Aj.g),h:E(_1Aj.h),i:_1Aj.i,j:_1Aj.j,k:_1Aj.k,l:_1Aj.l,m:E(_1Aj.m),n:_1Aj.n,o:E(_1Aj.o),p:E(_1Aj.p),q:_1Aj.q,r:E(_1Aj.r),s:_1Aj.s,t:E(_1Aj.t),u:E(_1Aj.u)};}else{return E(_Zs);}}});}}else{return new F(function(){return _1zw(_);});}}else{return new F(function(){return _1zw(_);});}};switch(E(_1zt)){case 100:var _1AY=__app1(E(_1v1),toJSStr(E(_1tY)));return new F(function(){return _1zu(_,_1tA);});break;case 114:var _1AZ=B(_ZE(_6v,toJSStr(E(_1tY)),_));return new F(function(){return _1zu(_,new T(function(){var _1B0=E(_1AZ);if(!_1B0._){return E(_1tB);}else{return fromJSStr(B(_1io(_1B0.a)));}}));});break;case 115:var _1B1=new T(function(){var _1B2=new T(function(){var _1B3=new T(function(){var _1B4=B(_6d(_6A,_1xr));if(!_1B4._){return __Z;}else{return B(_1tx(new T2(1,_1B4.a,new T(function(){return B(_1ua(_1tW,_1B4.b));}))));}}),_1B5=new T(function(){var _1B6=function(_1B7){var _1B8=E(_1B7);if(!_1B8._){return __Z;}else{var _1B9=E(_1B8.a);return new T2(1,_1B9.a,new T2(1,_1B9.b,new T(function(){return B(_1B6(_1B8.b));})));}},_1Ba=B(_1B6(_1xq));if(!_1Ba._){return __Z;}else{return B(_1tx(new T2(1,_1Ba.a,new T(function(){return B(_1ua(_1tW,_1Ba.b));}))));}});return B(_1ua(_1tX,new T2(1,_1B5,new T2(1,_1B3,_S))));});return B(_q(B(_1tx(new T2(1,new T(function(){return B(_A(0,_1xg,_S));}),_1B2))),_1u6));}),_1Bb=__app2(E(_1v4),toJSStr(E(_1tY)),B(_1io(B(_1x2(B(unAppCStr("\"",_1B1)))))));return new F(function(){return _1zu(_,_1tC);});break;default:return new F(function(){return _1zu(_,_1tZ);});}};if(!E(_1y9)){var _1Bc=B(_1ts(_1x0,_1vu,_));return new F(function(){return _1yz(_);});}else{var _1Bd=B(_1ts(_1x0,_1vt,_));return new F(function(){return _1yz(_);});}},_1Be=E(_1xs);if(!_1Be._){var _1Bf=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1yx(_);});}else{var _1Bg=new T(function(){var _1Bh=E(_1Be.a),_1Bi=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1Bj){return new F(function(){return _1v6(_1Bh.a,_1Bj);});},new T2(1,function(_1Bk){return new F(function(){return _1v6(_1Bh.b,_1Bk);});},_S)),new T2(1,_y,new T(function(){return B(_1v9(_1Be.b));}))));});return new T2(1,_z,_1Bi);}),_1Bl=B(_1ts(_1x0,new T2(1,_2u,_1Bg),_));return new F(function(){return _1yx(_);});}},_1Bm=E(_1xr);if(!_1Bm._){var _1Bn=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1yw(_);});}else{var _1Bo=new T(function(){return B(_A(0,E(_1Bm.a),new T(function(){return B(_1vh(_1Bm.b));})));}),_1Bp=B(_1ts(_1x0,new T2(1,_2u,_1Bo),_));return new F(function(){return _1yw(_);});}},_1Bq=E(_1xq);if(!_1Bq._){var _1Br=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1yv(_);});}else{var _1Bs=new T(function(){var _1Bt=E(_1Bq.a),_1Bu=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1Bv){return new F(function(){return _1v6(_1Bt.a,_1Bv);});},new T2(1,function(_1Bw){return new F(function(){return _1v6(_1Bt.b,_1Bw);});},_S)),new T2(1,_y,new T(function(){return B(_1vl(_1Bq.b));}))));});return new T2(1,_z,_1Bu);}),_1Bx=B(_1ts(_1x0,new T2(1,_2u,_1Bs),_));return new F(function(){return _1yv(_);});}},_1By=E(_1xB);if(!_1By._){return new F(function(){return _1xY(_,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xT,_1xo,_1xp,_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,_1xC,_1xD,_1xE,_1xF,_1xG,_1xQ,_1xP);});}else{var _1Bz=E(_1By.b);if(!_1Bz._){return new F(function(){return _1xY(_,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xT,_1xo,_1xp,_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,_1xC,_1xD,_1xE,_1xF,_1xG,_1xQ,_1xP);});}else{var _1BA=E(_1Bz.b);if(!_1BA._){return new F(function(){return _1xY(_,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xT,_1xo,_1xp,_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,_1xC,_1xD,_1xE,_1xF,_1xG,_1xQ,_1xP);});}else{var _1BB=_1BA.a,_1BC=E(_1BA.b);if(!_1BC._){return new F(function(){return _1xY(_,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xT,_1xo,_1xp,_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,_1xC,_1xD,_1xE,_1xF,_1xG,_1xQ,_1xP);});}else{if(!E(_1BC.b)._){var _1BD=B(_15N(B(_ms(_1BB,0)),_1xi,new T(function(){var _1BE=B(_Gd(B(_sy(_Zt,_1By.a))));if(!_1BE._){return E(_1uR);}else{if(!E(_1BE.b)._){if(E(_1BE.a)==2){return E(_1uV);}else{return E(_1uR);}}else{return E(_1uR);}}}),_)),_1BF=E(_1BD),_1BG=_1BF.a,_1BH=new T(function(){var _1BI=new T(function(){return B(_6d(function(_1BJ){var _1BK=B(_sl(_3L,_1BJ,B(_Gp(_1u4,_1BB))));return (_1BK._==0)?E(_1tQ):E(_1BK.a);},B(_6d(_1vv,B(_1vN(B(_1uW(_1BG,_1uS))))))));}),_1BL=B(_Se(B(unAppCStr("e.==.m1:",_1BC.a)),{_:0,a:E(_1xb),b:E(_1xc),c:E(_1xd),d:_1xe,e:_1xf,f:_1xg,g:E(B(_q(_1xh,new T2(1,new T2(0,new T2(0,_1Bz.a,_1u3),_1xg),new T2(1,new T2(0,new T2(0,_1BI,_1u3),_1xg),_S))))),h:E(_1BF.b),i:E(_1xj),j:E(_1xk),k:E(_1xl)},_1xT,_1xo,B(_q(_1xp,new T(function(){return B(_1ti(_1BG,_1BB));},1))),_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,E(_1BG),0,_1xR,_1xG,_1xQ,_1xP)),_1BM=B(_1iz(_1BB,_1BL.a,_1BL.b,_1BL.c,_1BL.d,_1BL.e,_1BL.f,_1BL.g,_1BL.h,_1BL.i,_1BL.j,_1BL.k,_1BL.l,_1BL.m,_1BL.n,_1BL.o,_1BL.p,_1BL.q,_1BL.r,_1BL.s,_1BL.t,_1BL.u));return {_:0,a:E(_1BM.a),b:E(_1BM.b),c:E(_1BM.c),d:E(_1BM.d),e:E(_1BM.e),f:E(_1BM.f),g:E(_1BM.g),h:E(_1BM.h),i:_1BM.i,j:_1BM.j,k:_1BM.k,l:_1BM.l,m:E(_1BM.m),n:_1BM.n,o:E(_1BM.o),p:E(_1BM.p),q:_1BM.q,r:E(_1BM.r),s:_1BM.s,t:E(_1BM.t),u:E(_1BM.u)};}),_1BN=function(_){var _1BO=function(_){var _1BP=function(_){var _1BQ=new T(function(){var _1BR=E(E(_1BH).a);return new T5(0,_1BR,_1BR.a,_1BR.h,_1BR.i,_1BR.k);}),_1BS=B(_1ts(_1x0,new T2(1,_6C,new T(function(){return B(_8j(E(_1BQ).d,_1u9));})),_)),_1BT=E(_1BQ),_1BU=_1BT.a,_1BV=function(_){var _1BW=B(_1ts(_1x0,B(_A(0,_1xy,_S)),_)),_1BX=B(_14s(_1tP,_1BT.c,_)),_1BY=E(_1BX).b,_1BZ=E(_1x6),_1C0=_1BZ.a,_1C1=_1BZ.b,_1C2=new T(function(){return B(_1jm(E(_1xa)));}),_1C3=new T(function(){var _1C4=E(_1BH),_1C5=_1C4.b,_1C6=_1C4.c,_1C7=_1C4.d,_1C8=_1C4.e,_1C9=_1C4.f,_1Ca=_1C4.g,_1Cb=_1C4.h,_1Cc=_1C4.i,_1Cd=_1C4.j,_1Ce=_1C4.k,_1Cf=_1C4.l,_1Cg=_1C4.m,_1Ch=_1C4.n,_1Ci=_1C4.o,_1Cj=_1C4.p,_1Ck=_1C4.q,_1Cl=_1C4.s,_1Cm=_1C4.t,_1Cn=_1C4.u,_1Co=E(_1C4.r),_1Cp=_1Co.a,_1Cq=_1Co.b,_1Cr=E(_1C2),_1Cs=E(_1BT.b),_1Ct=_1Cs.a,_1Cu=_1Cs.b,_1Cv=function(_1Cw,_1Cx){var _1Cy=E(_1Cw),_1Cz=E(_1Ct);if(_1Cy<=_1Cz){if(_1Cz<=_1Cy){var _1CA=E(_1Cu);if(_1Cx<=_1CA){if(_1CA<=_1Cx){var _1CB=4;}else{var _1CB=0;}var _1CC=_1CB;}else{var _1CC=1;}var _1CD=_1CC;}else{var _1CD=2;}var _1CE=_1CD;}else{var _1CE=3;}var _1CF=function(_1CG,_1CH,_1CI,_1CJ,_1CK,_1CL,_1CM,_1CN,_1CO,_1CP){switch(E(_1CE)){case 0:if(!E(E(_1BU).c)){var _1CQ=new T2(0,_1Cp,_1Cq);}else{var _1CQ=new T2(0,_1Cp,_1tI);}var _1CR=_1CQ;break;case 1:if(E(E(_1BU).c)==1){var _1CS=new T2(0,_1Cp,_1Cq);}else{var _1CS=new T2(0,_1Cp,_1u0);}var _1CR=_1CS;break;case 2:if(E(E(_1BU).c)==2){var _1CT=new T2(0,_1Cp,_1Cq);}else{var _1CT=new T2(0,_1Cp,_1u2);}var _1CR=_1CT;break;case 3:if(E(E(_1BU).c)==3){var _1CU=new T2(0,_1Cp,_1Cq);}else{var _1CU=new T2(0,_1Cp,_1u1);}var _1CR=_1CU;break;default:if(E(E(_1BU).c)==4){var _1CV=new T2(0,_1Cp,_1Cq);}else{var _1CV=new T2(0,_1Cp,_1u0);}var _1CR=_1CV;}var _1CW=B(_1gb(_1u0,_1CN,_1C8,{_:0,a:E(_1CG),b:E(_1CH),c:E(_1CI),d:_1CJ,e:_1CK,f:_1CL,g:E(_1CM),h:E(_1BY),i:E(_1CN),j:E(_1CO),k:E(_1CP)},_1C5,_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg,_1Ch,_1Ci,_1Cj,_1Ck,_1CR,_1Cl,_1Cm,_1Cn));return {_:0,a:E(_1CW.a),b:E(_1CW.b),c:E(_1CW.c),d:E(_1CW.d),e:E(_1CW.e),f:E(_1CW.f),g:E(_1CW.g),h:E(_1CW.h),i:_1CW.i,j:_1CW.j,k:_1CW.k,l:_1CW.l,m:E(_1CW.m),n:_1CW.n,o:E(_1CW.o),p:E(_1CW.p),q:_1CW.q,r:E(_1CW.r),s:_1CW.s,t:E(_1CW.t),u:E(_1CW.u)};};if(E(_1Cr)==32){var _1CX=E(_1BU),_1CY=E(_1CX.a),_1CZ=B(_1pf(_1Cy,_1Cx,_1CY.a,_1CY.b,_1CX.b,_1CE,_1CX.d,_1CX.e,_1CX.f,_1CX.g,_1CX.h,_1CX.i,_1CX.j,_1CX.k)),_1D0=E(_1CZ.a),_1D1=B(_1sA(_1D0.a,E(_1D0.b),_1CZ.b,_1CZ.c,_1CZ.d,_1CZ.e,_1CZ.f,_1CZ.g,_1CZ.h,_1CZ.i,_1CZ.j,_1CZ.k));return new F(function(){return _1CF(_1D1.a,_1D1.b,_1D1.c,_1D1.d,_1D1.e,_1D1.f,_1D1.g,_1D1.i,_1D1.j,_1D1.k);});}else{var _1D2=E(_1BU),_1D3=E(_1D2.a),_1D4=B(_1pf(_1Cy,_1Cx,_1D3.a,_1D3.b,_1D2.b,_1CE,_1D2.d,_1D2.e,_1D2.f,_1D2.g,_1D2.h,_1D2.i,_1D2.j,_1D2.k));return new F(function(){return _1CF(_1D4.a,_1D4.b,_1D4.c,_1D4.d,_1D4.e,_1D4.f,_1D4.g,_1D4.i,_1D4.j,_1D4.k);});}},_1D5=function(_1D6,_1D7){var _1D8=E(_1D7),_1D9=E(_1Ct);if(_1D6<=_1D9){if(_1D9<=_1D6){var _1Da=E(_1Cu);if(_1D8<=_1Da){if(_1Da<=_1D8){var _1Db=4;}else{var _1Db=0;}var _1Dc=_1Db;}else{var _1Dc=1;}var _1Dd=_1Dc;}else{var _1Dd=2;}var _1De=_1Dd;}else{var _1De=3;}var _1Df=function(_1Dg,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1Dm,_1Dn,_1Do,_1Dp){switch(E(_1De)){case 0:if(!E(E(_1BU).c)){var _1Dq=new T2(0,_1Cp,_1Cq);}else{var _1Dq=new T2(0,_1Cp,_1tI);}var _1Dr=_1Dq;break;case 1:if(E(E(_1BU).c)==1){var _1Ds=new T2(0,_1Cp,_1Cq);}else{var _1Ds=new T2(0,_1Cp,_1u0);}var _1Dr=_1Ds;break;case 2:if(E(E(_1BU).c)==2){var _1Dt=new T2(0,_1Cp,_1Cq);}else{var _1Dt=new T2(0,_1Cp,_1u2);}var _1Dr=_1Dt;break;case 3:if(E(E(_1BU).c)==3){var _1Du=new T2(0,_1Cp,_1Cq);}else{var _1Du=new T2(0,_1Cp,_1u1);}var _1Dr=_1Du;break;default:if(E(E(_1BU).c)==4){var _1Dv=new T2(0,_1Cp,_1Cq);}else{var _1Dv=new T2(0,_1Cp,_1u0);}var _1Dr=_1Dv;}var _1Dw=B(_1gb(_1u0,_1Dn,_1C8,{_:0,a:E(_1Dg),b:E(_1Dh),c:E(_1Di),d:_1Dj,e:_1Dk,f:_1Dl,g:E(_1Dm),h:E(_1BY),i:E(_1Dn),j:E(_1Do),k:E(_1Dp)},_1C5,_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg,_1Ch,_1Ci,_1Cj,_1Ck,_1Dr,_1Cl,_1Cm,_1Cn));return {_:0,a:E(_1Dw.a),b:E(_1Dw.b),c:E(_1Dw.c),d:E(_1Dw.d),e:E(_1Dw.e),f:E(_1Dw.f),g:E(_1Dw.g),h:E(_1Dw.h),i:_1Dw.i,j:_1Dw.j,k:_1Dw.k,l:_1Dw.l,m:E(_1Dw.m),n:_1Dw.n,o:E(_1Dw.o),p:E(_1Dw.p),q:_1Dw.q,r:E(_1Dw.r),s:_1Dw.s,t:E(_1Dw.t),u:E(_1Dw.u)};};if(E(_1Cr)==32){var _1Dx=E(_1BU),_1Dy=E(_1Dx.a),_1Dz=B(_1pf(_1D6,_1D8,_1Dy.a,_1Dy.b,_1Dx.b,_1De,_1Dx.d,_1Dx.e,_1Dx.f,_1Dx.g,_1Dx.h,_1Dx.i,_1Dx.j,_1Dx.k)),_1DA=E(_1Dz.a),_1DB=B(_1sA(_1DA.a,E(_1DA.b),_1Dz.b,_1Dz.c,_1Dz.d,_1Dz.e,_1Dz.f,_1Dz.g,_1Dz.h,_1Dz.i,_1Dz.j,_1Dz.k));return new F(function(){return _1Df(_1DB.a,_1DB.b,_1DB.c,_1DB.d,_1DB.e,_1DB.f,_1DB.g,_1DB.i,_1DB.j,_1DB.k);});}else{var _1DC=E(_1BU),_1DD=E(_1DC.a),_1DE=B(_1pf(_1D6,_1D8,_1DD.a,_1DD.b,_1DC.b,_1De,_1DC.d,_1DC.e,_1DC.f,_1DC.g,_1DC.h,_1DC.i,_1DC.j,_1DC.k));return new F(function(){return _1Df(_1DE.a,_1DE.b,_1DE.c,_1DE.d,_1DE.e,_1DE.f,_1DE.g,_1DE.i,_1DE.j,_1DE.k);});}},_1DF=E(_1Cr);switch(_1DF){case 72:var _1DG=E(_1Cu);if(0<=(_1DG-1|0)){return B(_1Cv(_1Ct,_1DG-1|0));}else{return B(_1Cv(_1Ct,_1DG));}break;case 75:var _1DH=E(_1Ct);if(0<=(_1DH-1|0)){return B(_1D5(_1DH-1|0,_1Cu));}else{return B(_1D5(_1DH,_1Cu));}break;case 77:var _1DI=E(_1Ct);if(E(_1xm)!=(_1DI+1|0)){return B(_1D5(_1DI+1|0,_1Cu));}else{return B(_1D5(_1DI,_1Cu));}break;case 80:var _1DJ=E(_1Cu);if(E(_1xn)!=(_1DJ+1|0)){return B(_1Cv(_1Ct,_1DJ+1|0));}else{return B(_1Cv(_1Ct,_1DJ));}break;case 104:var _1DK=E(_1Ct);if(0<=(_1DK-1|0)){return B(_1D5(_1DK-1|0,_1Cu));}else{return B(_1D5(_1DK,_1Cu));}break;case 106:var _1DL=E(_1Cu);if(E(_1xn)!=(_1DL+1|0)){return B(_1Cv(_1Ct,_1DL+1|0));}else{return B(_1Cv(_1Ct,_1DL));}break;case 107:var _1DM=E(_1Cu);if(0<=(_1DM-1|0)){return B(_1Cv(_1Ct,_1DM-1|0));}else{return B(_1Cv(_1Ct,_1DM));}break;case 108:var _1DN=E(_1Ct);if(E(_1xm)!=(_1DN+1|0)){return B(_1D5(_1DN+1|0,_1Cu));}else{return B(_1D5(_1DN,_1Cu));}break;default:var _1DO=E(_1Ct),_1DP=E(_1Cu),_1DQ=function(_1DR,_1DS,_1DT,_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0){if(E(E(_1BU).c)==4){var _1E1=new T2(0,_1Cp,_1Cq);}else{var _1E1=new T2(0,_1Cp,_1u0);}var _1E2=B(_1gb(_1u0,_1DY,_1C8,{_:0,a:E(_1DR),b:E(_1DS),c:E(_1DT),d:_1DU,e:_1DV,f:_1DW,g:E(_1DX),h:E(_1BY),i:E(_1DY),j:E(_1DZ),k:E(_1E0)},_1C5,_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg,_1Ch,_1Ci,_1Cj,_1Ck,_1E1,_1Cl,_1Cm,_1Cn));return {_:0,a:E(_1E2.a),b:E(_1E2.b),c:E(_1E2.c),d:E(_1E2.d),e:E(_1E2.e),f:E(_1E2.f),g:E(_1E2.g),h:E(_1E2.h),i:_1E2.i,j:_1E2.j,k:_1E2.k,l:_1E2.l,m:E(_1E2.m),n:_1E2.n,o:E(_1E2.o),p:E(_1E2.p),q:_1E2.q,r:E(_1E2.r),s:_1E2.s,t:E(_1E2.t),u:E(_1E2.u)};};if(E(_1DF)==32){var _1E3=E(_1BU),_1E4=E(_1E3.a),_1E5=B(_1pf(_1DO,_1DP,_1E4.a,_1E4.b,_1E3.b,_1sZ,_1E3.d,_1E3.e,_1E3.f,_1E3.g,_1E3.h,_1E3.i,_1E3.j,_1E3.k)),_1E6=E(_1E5.a),_1E7=B(_1sA(_1E6.a,E(_1E6.b),_1E5.b,_1E5.c,_1E5.d,_1E5.e,_1E5.f,_1E5.g,_1E5.h,_1E5.i,_1E5.j,_1E5.k));return B(_1DQ(_1E7.a,_1E7.b,_1E7.c,_1E7.d,_1E7.e,_1E7.f,_1E7.g,_1E7.i,_1E7.j,_1E7.k));}else{var _1E8=E(_1BU),_1E9=E(_1E8.a),_1Ea=B(_1pf(_1DO,_1DP,_1E9.a,_1E9.b,_1E8.b,_1sZ,_1E8.d,_1E8.e,_1E8.f,_1E8.g,_1E8.h,_1E8.i,_1E8.j,_1E8.k));return B(_1DQ(_1Ea.a,_1Ea.b,_1Ea.c,_1Ea.d,_1Ea.e,_1Ea.f,_1Ea.g,_1Ea.i,_1Ea.j,_1Ea.k));}}}),_1Eb=B(_16V(_1C0,_1C1,_1x7,_1x8,_1x9,_1C3,_)),_1Ec=_1Eb,_1Ed=E(_1C2),_1Ee=function(_,_1Ef){var _1Eg=function(_1Eh){var _1Ei=B(_1ts(_1x0,B(_8p(_1Ef)),_)),_1Ej=E(_1Ec),_1Ek=_1Ej.d,_1El=_1Ej.e,_1Em=_1Ej.f,_1En=_1Ej.g,_1Eo=_1Ej.i,_1Ep=_1Ej.j,_1Eq=_1Ej.k,_1Er=_1Ej.l,_1Es=_1Ej.m,_1Et=_1Ej.n,_1Eu=_1Ej.o,_1Ev=_1Ej.p,_1Ew=_1Ej.q,_1Ex=_1Ej.s,_1Ey=_1Ej.u,_1Ez=E(_1Ej.t),_1EA=_1Ez.a,_1EB=_1Ez.d,_1EC=_1Ez.e,_1ED=_1Ez.f,_1EE=_1Ez.g,_1EF=_1Ez.h,_1EG=E(_1Ej.a),_1EH=_1EG.c,_1EI=_1EG.f,_1EJ=_1EG.g,_1EK=_1EG.h,_1EL=E(_1Ej.h),_1EM=E(_1Ej.r),_1EN=function(_1EO){var _1EP=function(_1EQ){if(_1EQ!=E(_1tU)){var _1ER=B(_6Q(_1cI,_1EQ)),_1ES=_1ER.a,_1ET=E(_1ER.b),_1EU=B(_19q(_1ES,_1ET,new T(function(){return B(_6Q(_1dX,_1EQ));})));return new F(function(){return _1x5(_1BZ,_1x7,_1x8,_1x9,_1tT,B(_6Q(_1cT,_1EQ)),_1EU,_1EH,B(_6Q(_1d6,_1EQ)),32,_1EQ,_1EJ,_1EK,B(_q(_1EG.i,new T2(1,_1tS,new T(function(){return B(_A(0,_1EI,_S));})))),B(_1t1(_1tR,_1EU)),_wt,_1ES,_1ET,_S,_1Ek,_1El,_1Em,_1En,_1EL.a,_1EL.b,_1Eo,_1Ep,_1Eq, -1,_1Es,_1Et,_1Eu,_1Ev,_1Ew,_1EM.a,_1EM.b,_1Ex,_wt,_wt,_wt,_1EB,_1EC,_1ED,_1EE,_1EF,_1Ey,_);});}else{var _1EV=__app1(E(_nh),_1C1),_1EW=B(A2(_ni,_1C0,_)),_1EX=B(A(_mN,[_1C0,_j2,_1tI,_1tP,_1tO,_])),_1EY=B(A(_mN,[_1C0,_j2,_1tL,_1tN,_1tM,_])),_1EZ=B(A(_mN,[_1C0,_j2,_1tL,_1tK,_1tJ,_])),_1F0=B(A(_mN,[_1C0,_j2,_1tI,_1tH,_1tG,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1cS),b:E(_1tF),c:E(_1EH),d:E(_1tD),e:32,f:0,g:E(_1EJ),h:_1EK,i:E(_S),j:E(_1EG.j),k:E(_wt)}),b:E(_1cE),c:E(_1Ej.c),d:E(_1Ek),e:E(_1El),f:E(_1Em),g:E(_1En),h:E(_1EL),i:_1Eo,j:_1Ep,k:_1Eq,l:_1Er,m:E(_1Es),n:_1Et,o:E(_1Eu),p:E(_1Ev),q:_1Ew,r:E(_1EM),s:_1Ex,t:E({_:0,a:E(_1EA),b:E(_wt),c:E(_wt),d:E(_1EB),e:E(_1EC),f:E(_1ED),g:E(_1EE),h:E(_1EF)}),u:E(_1Ey)};});}};if(_1Er>=0){return new F(function(){return _1EP(_1Er);});}else{return new F(function(){return _1EP(_1EI+1|0);});}};if(!E(_1EA)){if(E(_1Ed)==110){return new F(function(){return _1EN(_);});}else{return _1Ej;}}else{return new F(function(){return _1EN(_);});}};if(E(_1Ed)==114){if(!B(_68(_1Ef,_1tV))){var _1F1=E(_1Ef);if(!_1F1._){return _1Ec;}else{var _1F2=_1F1.b;return new T(function(){var _1F3=E(_1Ec),_1F4=E(_1F3.a),_1F5=E(_1F1.a),_1F6=E(_1F5);if(_1F6==34){var _1F7=B(_RQ(_1F5,_1F2));if(!_1F7._){var _1F8=E(_1v3);}else{var _1F9=E(_1F7.b);if(!_1F9._){var _1Fa=E(_1u7);}else{var _1Fb=_1F9.a,_1Fc=E(_1F9.b);if(!_1Fc._){var _1Fd=new T2(1,new T2(1,_1Fb,_S),_S);}else{var _1Fe=E(_1Fb),_1Ff=new T(function(){var _1Fg=B(_H5(126,_1Fc.a,_1Fc.b));return new T2(0,_1Fg.a,_1Fg.b);});if(E(_1Fe)==126){var _1Fh=new T2(1,_S,new T2(1,new T(function(){return E(E(_1Ff).a);}),new T(function(){return E(E(_1Ff).b);})));}else{var _1Fh=new T2(1,new T2(1,_1Fe,new T(function(){return E(E(_1Ff).a);})),new T(function(){return E(E(_1Ff).b);}));}var _1Fd=_1Fh;}var _1Fa=_1Fd;}var _1F8=_1Fa;}var _1Fi=_1F8;}else{var _1Fj=E(_1F2);if(!_1Fj._){var _1Fk=new T2(1,new T2(1,_1F5,_S),_S);}else{var _1Fl=new T(function(){var _1Fm=B(_H5(126,_1Fj.a,_1Fj.b));return new T2(0,_1Fm.a,_1Fm.b);});if(E(_1F6)==126){var _1Fn=new T2(1,_S,new T2(1,new T(function(){return E(E(_1Fl).a);}),new T(function(){return E(E(_1Fl).b);})));}else{var _1Fn=new T2(1,new T2(1,_1F5,new T(function(){return E(E(_1Fl).a);})),new T(function(){return E(E(_1Fl).b);}));}var _1Fk=_1Fn;}var _1Fi=_1Fk;}var _1Fo=B(_Gd(B(_sy(_Zt,new T(function(){return B(_Jh(_1Fi));})))));if(!_1Fo._){return E(_Zr);}else{if(!E(_1Fo.b)._){var _1Fp=E(_1Fo.a),_1Fq=B(_6Q(_1cI,_1Fp)),_1Fr=B(_6Q(_1Fi,1));if(!_1Fr._){var _1Fs=__Z;}else{var _1Ft=E(_1Fr.b);if(!_1Ft._){var _1Fu=__Z;}else{var _1Fv=E(_1Fr.a),_1Fw=new T(function(){var _1Fx=B(_H5(44,_1Ft.a,_1Ft.b));return new T2(0,_1Fx.a,_1Fx.b);});if(E(_1Fv)==44){var _1Fy=B(_Zj(_S,new T(function(){return E(E(_1Fw).a);}),new T(function(){return E(E(_1Fw).b);})));}else{var _1Fy=B(_Zn(new T2(1,_1Fv,new T(function(){return E(E(_1Fw).a);})),new T(function(){return E(E(_1Fw).b);})));}var _1Fu=_1Fy;}var _1Fs=_1Fu;}var _1Fz=B(_6Q(_1Fi,2));if(!_1Fz._){var _1FA=E(_1u8);}else{var _1FB=_1Fz.a,_1FC=E(_1Fz.b);if(!_1FC._){var _1FD=B(_6d(_Zu,new T2(1,new T2(1,_1FB,_S),_S)));}else{var _1FE=E(_1FB),_1FF=new T(function(){var _1FG=B(_H5(44,_1FC.a,_1FC.b));return new T2(0,_1FG.a,_1FG.b);});if(E(_1FE)==44){var _1FH=B(_6d(_Zu,new T2(1,_S,new T2(1,new T(function(){return E(E(_1FF).a);}),new T(function(){return E(E(_1FF).b);})))));}else{var _1FH=B(_6d(_Zu,new T2(1,new T2(1,_1FE,new T(function(){return E(E(_1FF).a);})),new T(function(){return E(E(_1FF).b);}))));}var _1FD=_1FH;}var _1FA=_1FD;}return {_:0,a:E({_:0,a:E(B(_6Q(_1cT,_1Fp))),b:E(B(_19q(_1Fq.a,E(_1Fq.b),new T(function(){return B(_6Q(_1dX,_1Fp));})))),c:E(_1F4.c),d:B(_6Q(_1d6,_1Fp)),e:32,f:_1Fp,g:E(_1F4.g),h:_1F4.h,i:E(_1F4.i),j:E(_1F4.j),k:E(_1F4.k)}),b:E(_1Fq),c:E(_1F3.c),d:E(_1F3.d),e:E(_1Fs),f:E(_1FA),g:E(_1F3.g),h:E(_1F3.h),i:_1F3.i,j:_1F3.j,k:_1F3.k,l:_1F3.l,m:E(_1F3.m),n:_1F3.n,o:E(_1F3.o),p:E(_1F3.p),q:_1F3.q,r:E(_1F3.r),s:_1F3.s,t:E(_1F3.t),u:E(_1F3.u)};}else{return E(_Zs);}}});}}else{return new F(function(){return _1Eg(_);});}}else{return new F(function(){return _1Eg(_);});}};switch(E(_1Ed)){case 100:var _1FI=__app1(E(_1v1),toJSStr(E(_1tY)));return new F(function(){return _1Ee(_,_1tA);});break;case 114:var _1FJ=B(_ZE(_6v,toJSStr(E(_1tY)),_));return new F(function(){return _1Ee(_,new T(function(){var _1FK=E(_1FJ);if(!_1FK._){return E(_1tB);}else{return fromJSStr(B(_1io(_1FK.a)));}}));});break;case 115:var _1FL=new T(function(){var _1FM=new T(function(){var _1FN=new T(function(){var _1FO=B(_6d(_6A,_1xr));if(!_1FO._){return __Z;}else{return B(_1tx(new T2(1,_1FO.a,new T(function(){return B(_1ua(_1tW,_1FO.b));}))));}}),_1FP=new T(function(){var _1FQ=function(_1FR){var _1FS=E(_1FR);if(!_1FS._){return __Z;}else{var _1FT=E(_1FS.a);return new T2(1,_1FT.a,new T2(1,_1FT.b,new T(function(){return B(_1FQ(_1FS.b));})));}},_1FU=B(_1FQ(_1xq));if(!_1FU._){return __Z;}else{return B(_1tx(new T2(1,_1FU.a,new T(function(){return B(_1ua(_1tW,_1FU.b));}))));}});return B(_1ua(_1tX,new T2(1,_1FP,new T2(1,_1FN,_S))));});return B(_q(B(_1tx(new T2(1,new T(function(){return B(_A(0,_1xg,_S));}),_1FM))),_1u6));}),_1FV=__app2(E(_1v4),toJSStr(E(_1tY)),B(_1io(B(_1x2(B(unAppCStr("\"",_1FL)))))));return new F(function(){return _1Ee(_,_1tC);});break;default:return new F(function(){return _1Ee(_,_1tZ);});}};if(!E(_1BT.e)){var _1FW=B(_1ts(_1x0,_1vu,_));return new F(function(){return _1BV(_);});}else{var _1FX=B(_1ts(_1x0,_1vt,_));return new F(function(){return _1BV(_);});}},_1FY=E(_1xs);if(!_1FY._){var _1FZ=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1BP(_);});}else{var _1G0=new T(function(){var _1G1=E(_1FY.a),_1G2=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1G3){return new F(function(){return _1v6(_1G1.a,_1G3);});},new T2(1,function(_1G4){return new F(function(){return _1v6(_1G1.b,_1G4);});},_S)),new T2(1,_y,new T(function(){return B(_1v9(_1FY.b));}))));});return new T2(1,_z,_1G2);}),_1G5=B(_1ts(_1x0,new T2(1,_2u,_1G0),_));return new F(function(){return _1BP(_);});}},_1G6=E(_1xr);if(!_1G6._){var _1G7=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1BO(_);});}else{var _1G8=new T(function(){return B(_A(0,E(_1G6.a),new T(function(){return B(_1vh(_1G6.b));})));}),_1G9=B(_1ts(_1x0,new T2(1,_2u,_1G8),_));return new F(function(){return _1BO(_);});}},_1Ga=E(_1xq);if(!_1Ga._){var _1Gb=B(_1ts(_1x0,_1u5,_));return new F(function(){return _1BN(_);});}else{var _1Gc=new T(function(){var _1Gd=E(_1Ga.a),_1Ge=new T(function(){return B(A3(_sd,_6w,new T2(1,function(_1Gf){return new F(function(){return _1v6(_1Gd.a,_1Gf);});},new T2(1,function(_1Gg){return new F(function(){return _1v6(_1Gd.b,_1Gg);});},_S)),new T2(1,_y,new T(function(){return B(_1vl(_1Ga.b));}))));});return new T2(1,_z,_1Ge);}),_1Gh=B(_1ts(_1x0,new T2(1,_2u,_1Gc),_));return new F(function(){return _1BN(_);});}}else{return new F(function(){return _1xY(_,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xT,_1xo,_1xp,_1xq,_1xr,_1xs,_1xS,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_S,_1xC,_1xD,_1xE,_1xF,_1xG,_1xQ,_1xP);});}}}}}}}else{if(!E(_1xN)){return {_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:_1xA,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E({_:0,a:E(_1xH),b:E(_1xI),c:E(_1xJ),d:E(_wt),e:E(_1xL),f:E(_wt),g:E(_wt),h:E(_1xO)}),u:E(_1xP)};}else{var _1Gi=new T(function(){var _1Gj=B(_1is(_1xz));return new T2(0,_1Gj.a,_1Gj.b);}),_1Gk=new T(function(){return B(_ms(E(_1Gi).a,0))-1|0;}),_1Gl=function(_1Gm){var _1Gn=E(_1Gm);switch(_1Gn){case  -2:var _1Go=E(_1x6);return new F(function(){return _16V(_1Go.a,_1Go.b,_1x7,_1x8,_1x9,_1xV,_);});break;case  -1:var _1Gp=E(_1x6),_1Gq=new T(function(){return {_:0,a:E(_1xU),b:E(_1xT),c:E(B(_1cj(_S,new T(function(){return B(_6Q(E(_1Gi).b,_1xA));})))),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:_1xA,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E({_:0,a:E(_1xH),b:E(_1xI),c:E(_wu),d:E(_wt),e:E(_1xL),f:E(_wt),g:E(_wt),h:E(_1xO)}),u:E(_1xP)};});return new F(function(){return _16V(_1Gp.a,_1Gp.b,_1x7,_1x8,_1x9,_1Gq,_);});break;default:var _1Gr=E(_1x6);return new F(function(){return _16V(_1Gr.a,_1Gr.b,_1x7,_1x8,_1x9,{_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:_1Gn,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)},_);});}};switch(E(B(_1jm(E(_1xa))))){case 32:var _1Gs=E(_1x6),_1Gt=new T(function(){return {_:0,a:E(_1xU),b:E(_1xT),c:E(B(_1cj(_S,new T(function(){return B(_6Q(E(_1Gi).b,_1xA));})))),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:_1xA,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E({_:0,a:E(_1xH),b:E(_1xI),c:E(_wu),d:E(_wt),e:E(_1xL),f:E(_wt),g:E(_wt),h:E(_1xO)}),u:E(_1xP)};});return new F(function(){return _16V(_1Gs.a,_1Gs.b,_1x7,_1x8,_1x9,_1Gt,_);});break;case 72:var _1Gu=E(_1xA);if(!_1Gu){return new F(function(){return _1Gl(E(_1Gk));});}else{return new F(function(){return _1Gl(_1Gu-1|0);});}break;case 75:if(_1xA!=E(_1Gk)){return new F(function(){return _1Gl(_1xA+1|0);});}else{var _1Gv=E(_1x6);return new F(function(){return _16V(_1Gv.a,_1Gv.b,_1x7,_1x8,_1x9,{_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:0,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)},_);});}break;case 77:var _1Gw=E(_1xA);if(!_1Gw){return new F(function(){return _1Gl(E(_1Gk));});}else{return new F(function(){return _1Gl(_1Gw-1|0);});}break;case 80:if(_1xA!=E(_1Gk)){return new F(function(){return _1Gl(_1xA+1|0);});}else{var _1Gx=E(_1x6);return new F(function(){return _16V(_1Gx.a,_1Gx.b,_1x7,_1x8,_1x9,{_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:0,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)},_);});}break;case 104:if(_1xA!=E(_1Gk)){return new F(function(){return _1Gl(_1xA+1|0);});}else{var _1Gy=E(_1x6);return new F(function(){return _16V(_1Gy.a,_1Gy.b,_1x7,_1x8,_1x9,{_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:0,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)},_);});}break;case 106:if(_1xA!=E(_1Gk)){return new F(function(){return _1Gl(_1xA+1|0);});}else{var _1Gz=E(_1x6);return new F(function(){return _16V(_1Gz.a,_1Gz.b,_1x7,_1x8,_1x9,{_:0,a:E(_1xU),b:E(_1xT),c:E(_1xo),d:E(_1xp),e:E(_1xq),f:E(_1xr),g:E(_1xs),h:E(_1xS),i:_1xv,j:_1xw,k:_1xx,l:_1xy,m:E(_1xz),n:0,o:E(_1xB),p:E(_1xC),q:_1xD,r:E(_1xR),s:_1xG,t:E(_1xQ),u:E(_1xP)},_);});}break;case 107:var _1GA=E(_1xA);if(!_1GA){return new F(function(){return _1Gl(E(_1Gk));});}else{return new F(function(){return _1Gl(_1GA-1|0);});}break;case 108:var _1GB=E(_1xA);if(!_1GB){return new F(function(){return _1Gl(E(_1Gk));});}else{return new F(function(){return _1Gl(_1GB-1|0);});}break;default:var _1GC=E(_1x6);return new F(function(){return _16V(_1GC.a,_1GC.b,_1x7,_1x8,_1x9,_1xV,_);});}}}};if(!E(_1xJ)){return new F(function(){return _1xW(_);});}else{if(!E(_1xK)){return new F(function(){return _Y5(_1x6,_1x7,_1x8,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xm,_1xn,_1xo,_1xp,_1xq,_1xr,_1xs,_1xt,_1xu,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_1xB,_1xC,_1xD,_1xR,_1xG,_1xH,_1xI,_wt,_1xL,_wu,_1xN,_1xO,_1xP,_);});}else{return new F(function(){return _1xW(_);});}}}else{return _1xV;}},_1GD=function(_1GE,_1GF,_1GG,_1GH,_1GI,_1GJ,_1GK,_1GL,_1GM,_1GN,_1GO,_1GP,_1GQ,_1GR,_1GS,_1GT,_1GU,_1GV,_1GW,_1GX,_1GY,_1GZ,_1H0,_1H1,_1H2,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_){var _1Ha=function(_1Hb){var _1Hc=new T(function(){var _1Hd=E(_1GX);if(!_1Hd._){return {_:0,a:E(_1GI),b:E(_1GJ),c:E(_1GK),d:E(_1GL),e:E(_1GM),f:E(_1GN),g:E(_1GO),h:E(_1GP),i:_1GQ,j:_1GR,k:_1GS,l:_1GT,m:E(_1GU),n:_1GV,o:E(_1GW),p:E(_S),q:_1GY,r:E(_1GZ),s:_1Hb,t:E({_:0,a:E(_1H1),b:E(_1H2),c:E(_1H3),d:E(_1H4),e:E(_1H5),f:E(_1H6),g:E(_1H7),h:E(_1H8)}),u:E(_1H9)};}else{if(!B(_an(_1Hb,20))){return {_:0,a:E(_1GI),b:E(_1GJ),c:E(_1GK),d:E(_1GL),e:E(_1GM),f:E(_1GN),g:E(_1GO),h:E(_1GP),i:_1GQ,j:_1GR,k:_1GS,l:_1GT,m:E(_1GU),n:_1GV,o:E(_1GW),p:E(_1Hd),q:_1GY+1|0,r:E(_1GZ),s:_1Hb,t:E({_:0,a:E(_1H1),b:E(_1H2),c:E(_1H3),d:E(_1H4),e:E(_1H5),f:E(_1H6),g:E(_1H7),h:E(_1H8)}),u:E(_1H9)};}else{return {_:0,a:E(_1GI),b:E(_1GJ),c:E(_1GK),d:E(_1GL),e:E(_1GM),f:E(_1GN),g:E(_1GO),h:E(_1GP),i:_1GQ,j:_1GR,k:_1GS,l:_1GT,m:E(_1GU),n:_1GV,o:E(_1GW),p:E(_1Hd),q:_1GY,r:E(_1GZ),s:_1Hb,t:E({_:0,a:E(_1H1),b:E(_1H2),c:E(_1H3),d:E(_1H4),e:E(_1H5),f:E(_1H6),g:E(_1H7),h:E(_1H8)}),u:E(_1H9)};}}});if(!E(_1H8)){var _1He=E(_1Hc),_1Hf=E(_1He.a),_1Hg=E(_1He.b),_1Hh=E(_1He.h),_1Hi=E(_1He.t);return new F(function(){return _VG(_1GE,_1GF,_1GG,_1Hf.a,_1Hf.b,_1Hf.c,_1Hf.d,_1Hf.e,_1Hf.f,_1Hf.g,_1Hf.h,_1Hf.i,_1Hf.j,_1Hf.k,_1Hg.a,_1Hg.b,_1He.c,_1He.d,_1He.e,_1He.f,_1He.g,_1Hh.a,_1Hh.b,_1He.i,_1He.j,_1He.k,_1He.l,_1He.m,_1He.n,_1He.o,_1He.p,_1He.q,_1He.r,_1He.s,_1Hi.a,_1Hi.b,_1Hi.c,_1Hi.d,_1Hi.e,_1Hi.f,_1Hi.g,_1Hi.h,_1He.u,_);});}else{if(!B(_an(_1Hb,10))){if(!E(_1H3)){var _1Hj=E(_1GE);return new F(function(){return _16V(_1Hj.a,_1Hj.b,_1GF,_1GG,_1GH,_1Hc,_);});}else{var _1Hk=E(_1Hc),_1Hl=E(_1Hk.a),_1Hm=E(_1Hk.b),_1Hn=E(_1Hk.h),_1Ho=E(_1Hk.t);return new F(function(){return _VG(_1GE,_1GF,_1GG,_1Hl.a,_1Hl.b,_1Hl.c,_1Hl.d,_1Hl.e,_1Hl.f,_1Hl.g,_1Hl.h,_1Hl.i,_1Hl.j,_1Hl.k,_1Hm.a,_1Hm.b,_1Hk.c,_1Hk.d,_1Hk.e,_1Hk.f,_1Hk.g,_1Hn.a,_1Hn.b,_1Hk.i,_1Hk.j,_1Hk.k,_1Hk.l,_1Hk.m,_1Hk.n,_1Hk.o,_1Hk.p,_1Hk.q,_1Hk.r,_1Hk.s,_1Ho.a,_1Ho.b,_1Ho.c,_1Ho.d,_1Ho.e,_1Ho.f,_1Ho.g,_1Ho.h,_1Hk.u,_);});}}else{var _1Hp=E(_1Hc),_1Hq=E(_1Hp.a),_1Hr=E(_1Hp.b),_1Hs=E(_1Hp.h),_1Ht=E(_1Hp.t);return new F(function(){return _VG(_1GE,_1GF,_1GG,_1Hq.a,_1Hq.b,_1Hq.c,_1Hq.d,_1Hq.e,_1Hq.f,_1Hq.g,_1Hq.h,_1Hq.i,_1Hq.j,_1Hq.k,_1Hr.a,_1Hr.b,_1Hp.c,_1Hp.d,_1Hp.e,_1Hp.f,_1Hp.g,_1Hs.a,_1Hs.b,_1Hp.i,_1Hp.j,_1Hp.k,_1Hp.l,_1Hp.m,_1Hp.n,_1Hp.o,_1Hp.p,_1Hp.q,_1Hp.r,_1Hp.s,_1Ht.a,_1Ht.b,_1Ht.c,_1Ht.d,_1Ht.e,_1Ht.f,_1Ht.g,_1Ht.h,_1Hp.u,_);});}}};if(_1H0<=298){return new F(function(){return _1Ha(_1H0+1|0);});}else{return new F(function(){return _1Ha(0);});}},_1Hu=function(_1Hv,_1Hw,_1Hx){var _1Hy=E(_1Hx);if(!_1Hy._){return 0;}else{var _1Hz=_1Hy.b,_1HA=E(_1Hy.a),_1HB=_1HA.a,_1HC=_1HA.b;return (_1Hv<=_1HB)?1+B(_1Hu(_1Hv,_1Hw,_1Hz))|0:(_1Hv>=_1HB+_1HA.c)?1+B(_1Hu(_1Hv,_1Hw,_1Hz))|0:(_1Hw<=_1HC)?1+B(_1Hu(_1Hv,_1Hw,_1Hz))|0:(_1Hw>=_1HC+_1HA.d)?1+B(_1Hu(_1Hv,_1Hw,_1Hz))|0:1;}},_1HD=function(_1HE,_1HF,_1HG){var _1HH=E(_1HG);if(!_1HH._){return 0;}else{var _1HI=_1HH.b,_1HJ=E(_1HH.a),_1HK=_1HJ.a,_1HL=_1HJ.b;if(_1HE<=_1HK){return 1+B(_1HD(_1HE,_1HF,_1HI))|0;}else{if(_1HE>=_1HK+_1HJ.c){return 1+B(_1HD(_1HE,_1HF,_1HI))|0;}else{var _1HM=E(_1HF);return (_1HM<=_1HL)?1+B(_1Hu(_1HE,_1HM,_1HI))|0:(_1HM>=_1HL+_1HJ.d)?1+B(_1Hu(_1HE,_1HM,_1HI))|0:1;}}}},_1HN=function(_1HO,_1HP,_1HQ){var _1HR=E(_1HQ);if(!_1HR._){return 0;}else{var _1HS=_1HR.b,_1HT=E(_1HR.a),_1HU=_1HT.a,_1HV=_1HT.b,_1HW=E(_1HO);if(_1HW<=_1HU){return 1+B(_1HD(_1HW,_1HP,_1HS))|0;}else{if(_1HW>=_1HU+_1HT.c){return 1+B(_1HD(_1HW,_1HP,_1HS))|0;}else{var _1HX=E(_1HP);return (_1HX<=_1HV)?1+B(_1Hu(_1HW,_1HX,_1HS))|0:(_1HX>=_1HV+_1HT.d)?1+B(_1Hu(_1HW,_1HX,_1HS))|0:1;}}}},_1HY=function(_1HZ,_1I0){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1I0)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1I0)-100,E(_1HZ),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1HZ),100);}),new T2(1,new T(function(){return new T4(0,E(_1HZ)-100,100,100,E(_1I0)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1HZ)-200,E(_1I0)-200);}),_S)))));},_1I1=32,_1I2=76,_1I3=75,_1I4=74,_1I5=72,_1I6=64,_1I7=function(_1I8,_1I9,_1Ia,_1Ib,_1Ic){var _1Id=new T(function(){var _1Ie=E(_1I9),_1If=E(_1Ie.a),_1Ig=_1If.a,_1Ih=_1If.b,_1Ii=B(_1HY(_1Ig,_1Ih)),_1Ij=new T(function(){var _1Ik=E(_1Ie.b);return new T2(0,new T(function(){return B(_g7(_1Ig,_1Ik.a));}),new T(function(){return B(_g7(_1Ih,_1Ik.b));}));});switch(B(_1HN(new T(function(){return E(_1Ib)*E(E(_1Ij).a);},1),new T(function(){return E(_1Ic)*E(E(_1Ij).b);},1),new T2(1,_1Ii.a,_1Ii.b)))){case 1:return E(_1I5);break;case 2:return E(_1I4);break;case 3:return E(_1I3);break;case 4:return E(_1I2);break;case 5:return E(_1I1);break;default:return E(_1I6);}});return function(_1Il,_){var _1Im=E(E(_1I9).a),_1In=E(_1Il),_1Io=E(_1In.a),_1Ip=E(_1In.b),_1Iq=E(_1In.h),_1Ir=E(_1In.r),_1Is=E(_1In.t);return new F(function(){return _1x5(_1I8,_1Im.a,_1Im.b,_1Ia,_1Id,_1Io.a,_1Io.b,_1Io.c,_1Io.d,_1Io.e,_1Io.f,_1Io.g,_1Io.h,_1Io.i,_1Io.j,_1Io.k,_1Ip.a,_1Ip.b,_1In.c,_1In.d,_1In.e,_1In.f,_1In.g,_1Iq.a,_1Iq.b,_1In.i,_1In.j,_1In.k,_1In.l,_1In.m,_1In.n,_1In.o,_1In.p,_1In.q,_1Ir.a,_1Ir.b,_1In.s,_1Is.a,_1Is.b,_1Is.c,_1Is.d,_1Is.e,_1Is.f,_1Is.g,_1Is.h,_1In.u,_);});};},_1It=0,_1Iu=2,_1Iv=2,_1Iw=0,_1Ix=new T(function(){return eval("document");}),_1Iy=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Iz=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1IA=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1IB=function(_1IC){return E(E(_1IC).b);},_1ID=function(_1IE,_1IF){return new F(function(){return A2(_1IB,_1IE,function(_){var _1IG=E(_1IF),_1IH=__app1(E(_1IA),_1IG);if(!_1IH){return _2N;}else{var _1II=__app1(E(_1Iz),_1IG);return new T1(1,new T2(0,_1II,_1IG));}});});},_1IJ=1,_1IK=new T(function(){var _1IL=E(_1d6);if(!_1IL._){return E(_ng);}else{return {_:0,a:E(_1cS),b:E(B(_19q(_1cD,5,_1dm))),c:E(_1IJ),d:E(_1IL.a),e:32,f:0,g:E(_S),h:0,i:E(_S),j:E(_wt),k:E(_wt)};}}),_1IM=0,_1IN=4,_1IO=new T2(0,_1IN,_1IM),_1IP=new T2(0,_1IM,_1IM),_1IQ={_:0,a:E(_wt),b:E(_wt),c:E(_wu),d:E(_wt),e:E(_wt),f:E(_wt),g:E(_wt),h:E(_wt)},_1IR=new T(function(){return {_:0,a:E(_1IK),b:E(_1cE),c:E(_1aB),d:E(_S),e:E(_S),f:E(_S),g:E(_S),h:E(_1IP),i:0,j:0,k:0,l: -1,m:E(_S),n:0,o:E(_S),p:E(_S),q:0,r:E(_1IO),s:0,t:E(_1IQ),u:E(_S)};}),_1IS=new T1(0,100),_1IT=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1IU=new T6(0,_2N,_2O,_S,_1IT,_2N,_2N),_1IV=new T(function(){return B(_2L(_1IU));}),_1IW=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1IX=new T6(0,_2N,_2O,_S,_1IW,_2N,_2N),_1IY=new T(function(){return B(_2L(_1IX));}),_1IZ=new T1(1,50),_1J0=function(_1J1){return E(E(_1J1).a);},_1J2=function(_1J3){return E(E(_1J3).a);},_1J4=function(_1J5){return E(E(_1J5).b);},_1J6=function(_1J7){return E(E(_1J7).b);},_1J8=function(_1J9){return E(E(_1J9).a);},_1Ja=function(_){return new F(function(){return nMV(_2N);});},_1Jb=new T(function(){return B(_36(_1Ja));}),_1Jc=function(_1Jd){return E(E(_1Jd).b);},_1Je=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Jf=function(_1Jg){return E(E(_1Jg).d);},_1Jh=function(_1Ji,_1Jj,_1Jk,_1Jl,_1Jm,_1Jn){var _1Jo=B(_1J0(_1Ji)),_1Jp=B(_1J2(_1Jo)),_1Jq=new T(function(){return B(_1IB(_1Jo));}),_1Jr=new T(function(){return B(_1Jf(_1Jp));}),_1Js=new T(function(){return B(A1(_1Jj,_1Jl));}),_1Jt=new T(function(){return B(A2(_1J8,_1Jk,_1Jm));}),_1Ju=function(_1Jv){return new F(function(){return A1(_1Jr,new T3(0,_1Jt,_1Js,_1Jv));});},_1Jw=function(_1Jx){var _1Jy=new T(function(){var _1Jz=new T(function(){var _1JA=__createJSFunc(2,function(_1JB,_){var _1JC=B(A2(E(_1Jx),_1JB,_));return _3a;}),_1JD=_1JA;return function(_){return new F(function(){return __app3(E(_1Je),E(_1Js),E(_1Jt),_1JD);});};});return B(A1(_1Jq,_1Jz));});return new F(function(){return A3(_1J4,_1Jp,_1Jy,_1Ju);});},_1JE=new T(function(){var _1JF=new T(function(){return B(_1IB(_1Jo));}),_1JG=function(_1JH){var _1JI=new T(function(){return B(A1(_1JF,function(_){var _=wMV(E(_1Jb),new T1(1,_1JH));return new F(function(){return A(_1J6,[_1Jk,_1Jm,_1JH,_]);});}));});return new F(function(){return A3(_1J4,_1Jp,_1JI,_1Jn);});};return B(A2(_1Jc,_1Ji,_1JG));});return new F(function(){return A3(_1J4,_1Jp,_1JE,_1Jw);});},_1JJ=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1JK=function(_){var _1JL=rMV(E(_1Jb)),_1JM=E(_1JL);if(!_1JM._){var _1JN=__app1(E(_1JJ),E(_3a));return new F(function(){return _gE(_);});}else{var _1JO=__app1(E(_1JJ),E(_1JM.a));return new F(function(){return _gE(_);});}},_1JP="src",_1JQ=new T(function(){return B(unCStr("img"));}),_1JR=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1JS=function(_1JT,_1JU){return new F(function(){return A2(_1IB,_1JT,function(_){var _1JV=__app1(E(_1JR),toJSStr(E(_1JQ))),_1JW=__app3(E(_i0),_1JV,E(_1JP),E(_1JU));return _1JV;});});},_1JX=new T(function(){return B(unCStr(".png"));}),_1JY=function(_1JZ,_1K0){var _1K1=E(_1JZ);if(_1K1==( -1)){return __Z;}else{var _1K2=new T(function(){var _1K3=new T(function(){return toJSStr(B(_q(_1K0,new T(function(){return B(_q(B(_A(0,_1K1,_S)),_1JX));},1))));});return B(_1JS(_5W,_1K3));});return new F(function(){return _q(B(_1JY(_1K1-1|0,_1K0)),new T2(1,_1K2,_S));});}},_1K4=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1K5=new T(function(){return B(_1JY(120,_1K4));}),_1K6=function(_1K7,_){var _1K8=E(_1K7);if(!_1K8._){return _S;}else{var _1K9=B(A1(_1K8.a,_)),_1Ka=B(_1K6(_1K8.b,_));return new T2(1,_1K9,_1Ka);}},_1Kb=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1Kc=new T(function(){return B(_1JY(56,_1Kb));}),_1Kd=function(_1Ke,_){var _1Kf=E(_1Ke);if(!_1Kf._){return _S;}else{var _1Kg=B(A1(_1Kf.a,_)),_1Kh=B(_1Kd(_1Kf.b,_));return new T2(1,_1Kg,_1Kh);}},_1Ki=new T(function(){return B(unCStr("Images/img"));}),_1Kj=new T(function(){return B(_1JY(5,_1Ki));}),_1Kk=function(_1Kl,_){var _1Km=E(_1Kl);if(!_1Km._){return _S;}else{var _1Kn=B(A1(_1Km.a,_)),_1Ko=B(_1Kk(_1Km.b,_));return new T2(1,_1Kn,_1Ko);}},_1Kp=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1Kq=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1Kr=function(_1Ks,_1Kt,_1Ku){var _1Kv=B(_1J0(_1Ks)),_1Kw=new T(function(){return B(_1IB(_1Kv));}),_1Kx=function(_1Ky){var _1Kz=function(_){var _1KA=E(_1Kt);if(!_1KA._){var _1KB=B(A1(_1Ky,_gD)),_1KC=__createJSFunc(0,function(_){var _1KD=B(A1(_1KB,_));return _3a;}),_1KE=__app2(E(_1Kq),_1KA.a,_1KC);return new T(function(){var _1KF=Number(_1KE),_1KG=jsTrunc(_1KF);return new T2(0,_1KG,E(_1KA));});}else{var _1KH=B(A1(_1Ky,_gD)),_1KI=__createJSFunc(0,function(_){var _1KJ=B(A1(_1KH,_));return _3a;}),_1KK=__app2(E(_1Kp),_1KA.a,_1KI);return new T(function(){var _1KL=Number(_1KK),_1KM=jsTrunc(_1KL);return new T2(0,_1KM,E(_1KA));});}};return new F(function(){return A1(_1Kw,_1Kz);});},_1KN=new T(function(){return B(A2(_1Jc,_1Ks,function(_1KO){return E(_1Ku);}));});return new F(function(){return A3(_1J4,B(_1J2(_1Kv)),_1KN,_1Kx);});},_1KP=function(_){var _1KQ=B(_1Kk(_1Kj,_)),_1KR=B(_1Kd(_1Kc,_)),_1KS=B(_1K6(_1K5,_)),_1KT=__app1(E(_1Iy),"canvas"),_1KU=__eq(_1KT,E(_3a));if(!E(_1KU)){var _1KV=__isUndef(_1KT);if(!E(_1KV)){var _1KW=B(A3(_1ID,_5W,_1KT,_)),_1KX=E(_1KW);if(!_1KX._){return new F(function(){return die(_1IY);});}else{var _1KY=E(_1KX.a),_1KZ=B(_62(_1KY.b,_)),_1L0=_1KZ,_1L1=nMV(_1IR),_1L2=_1L1,_1L3=new T3(0,_1KQ,_1KR,_1KS),_1L4=B(A(_1Jh,[_5X,_3D,_m,_1Ix,_1Iu,function(_1L5,_){var _1L6=B(_1JK(_)),_1L7=rMV(_1L2),_1L8=E(E(_1L0).a),_1L9=E(_1L7),_1La=E(_1L9.a),_1Lb=E(_1L9.b),_1Lc=E(_1L9.h),_1Ld=E(_1L9.r),_1Le=E(_1L9.t),_1Lf=B(_1x5(_1KY,_1L8.a,_1L8.b,_1L3,E(_1L5).a,_1La.a,_1La.b,_1La.c,_1La.d,_1La.e,_1La.f,_1La.g,_1La.h,_1La.i,_1La.j,_1La.k,_1Lb.a,_1Lb.b,_1L9.c,_1L9.d,_1L9.e,_1L9.f,_1L9.g,_1Lc.a,_1Lc.b,_1L9.i,_1L9.j,_1L9.k,_1L9.l,_1L9.m,_1L9.n,_1L9.o,_1L9.p,_1L9.q,_1Ld.a,_1Ld.b,_1L9.s,_1Le.a,_1Le.b,_1Le.c,_1Le.d,_1Le.e,_1Le.f,_1Le.g,_1Le.h,_1L9.u,_)),_=wMV(_1L2,_1Lf);return _gD;},_])),_1Lg=B(A(_1Jh,[_5X,_3D,_3C,_1KT,_1It,function(_1Lh,_){var _1Li=E(E(_1Lh).a),_1Lj=rMV(_1L2),_1Lk=B(A(_1I7,[_1KY,_1L0,_1L3,_1Li.a,_1Li.b,_1Lj,_])),_=wMV(_1L2,_1Lk);return _gD;},_])),_1Ll=B(A(_1Jh,[_5X,_3D,_5c,_1KT,_1Iw,function(_1Lm,_){var _1Ln=E(_1Lm),_1Lo=rMV(_1L2),_1Lp=E(_1Lo);if(!E(E(_1Lp.t).e)){var _=wMV(_1L2,_1Lp);return _gD;}else{var _1Lq=B(_1JK(_)),_=wMV(_1L2,_1Lp);return _gD;}},_])),_1Lr=function(_){var _1Ls=rMV(_1L2),_=wMV(_1L2,new T(function(){var _1Lt=E(_1Ls),_1Lu=E(_1Lt.t);return {_:0,a:E(_1Lt.a),b:E(_1Lt.b),c:E(_1Lt.c),d:E(_1Lt.d),e:E(_1Lt.e),f:E(_1Lt.f),g:E(_1Lt.g),h:E(_1Lt.h),i:_1Lt.i,j:_1Lt.j,k:_1Lt.k,l:_1Lt.l,m:E(_1Lt.m),n:_1Lt.n,o:E(_1Lt.o),p:E(_1Lt.p),q:_1Lt.q,r:E(_1Lt.r),s:_1Lt.s,t:E({_:0,a:E(_1Lu.a),b:E(_1Lu.b),c:E(_1Lu.c),d:E(_1Lu.d),e:E(_wt),f:E(_1Lu.f),g:E(_1Lu.g),h:E(_1Lu.h)}),u:E(_1Lt.u)};}));return _gD;},_1Lv=function(_1Lw,_){var _1Lx=E(_1Lw),_1Ly=rMV(_1L2),_=wMV(_1L2,new T(function(){var _1Lz=E(_1Ly),_1LA=E(_1Lz.t);return {_:0,a:E(_1Lz.a),b:E(_1Lz.b),c:E(_1Lz.c),d:E(_1Lz.d),e:E(_1Lz.e),f:E(_1Lz.f),g:E(_1Lz.g),h:E(_1Lz.h),i:_1Lz.i,j:_1Lz.j,k:_1Lz.k,l:_1Lz.l,m:E(_1Lz.m),n:_1Lz.n,o:E(_1Lz.o),p:E(_1Lz.p),q:_1Lz.q,r:E(_1Lz.r),s:_1Lz.s,t:E({_:0,a:E(_1LA.a),b:E(_1LA.b),c:E(_1LA.c),d:E(_1LA.d),e:E(_wu),f:E(_1LA.f),g:E(_1LA.g),h:E(_1LA.h)}),u:E(_1Lz.u)};})),_1LB=B(A(_1Kr,[_5X,_1IS,_1Lr,_]));return _gD;},_1LC=B(A(_1Jh,[_5X,_3D,_5c,_1KT,_1Iv,_1Lv,_])),_1LD=B(A(_1Kr,[_5X,_1IZ,function(_){var _1LE=rMV(_1L2),_1LF=E(E(_1L0).a),_1LG=E(_1LE),_1LH=E(_1LG.t),_1LI=B(_1GD(_1KY,_1LF.a,_1LF.b,_1L3,_1LG.a,_1LG.b,_1LG.c,_1LG.d,_1LG.e,_1LG.f,_1LG.g,_1LG.h,_1LG.i,_1LG.j,_1LG.k,_1LG.l,_1LG.m,_1LG.n,_1LG.o,_1LG.p,_1LG.q,_1LG.r,_1LG.s,_1LH.a,_1LH.b,_1LH.c,_1LH.d,_1LH.e,_1LH.f,_1LH.g,_1LH.h,_1LG.u,_)),_=wMV(_1L2,_1LI);return _gD;},_]));return _gD;}}else{return new F(function(){return die(_1IV);});}}else{return new F(function(){return die(_1IV);});}},_1LJ=function(_){return new F(function(){return _1KP(_);});};
var hasteMain = function() {B(A(_1LJ, [0]));};window.onload = hasteMain;