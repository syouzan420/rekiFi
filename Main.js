"use strict";
var __haste_prog_id = '9df7585a6656de291aa38ca7d64de5cacaab634c02519f4796297235c9a98438';
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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n="deltaZ",_o="deltaY",_p="deltaX",_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v,_w){var _x=jsShowI(_v);return new F(function(){return _q(fromJSStr(_x),_w);});},_y=41,_z=40,_A=function(_B,_C,_D){if(_C>=0){return new F(function(){return _u(_C,_D);});}else{if(_B<=6){return new F(function(){return _u(_C,_D);});}else{return new T2(1,_z,new T(function(){var _E=jsShowI(_C);return B(_q(fromJSStr(_E),new T2(1,_y,_D)));}));}}},_F=new T(function(){return B(unCStr(")"));}),_G=new T(function(){return B(_A(0,2,_F));}),_H=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_G));}),_I=function(_J){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_A(0,_J,_H));}))));});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L)),_N=jsTrunc(_M);if(_N<0){return B(_I(_N));}else{if(_N>2){return B(_I(_N));}else{return _N;}}});},_O=0,_P=new T3(0,_O,_O,_O),_Q="button",_R=new T(function(){return eval("jsGetMouseCoords");}),_S=__Z,_T=function(_U,_){var _V=E(_U);if(!_V._){return _S;}else{var _W=B(_T(_V.b,_));return new T2(1,new T(function(){var _X=Number(E(_V.a));return jsTrunc(_X);}),_W);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _T(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return new T(function(){var _15=Number(E(_14));return jsTrunc(_15);});},_16=new T2(0,_13,_11),_17=function(_18,_){var _19=E(_18);if(!_19._){return _S;}else{var _1a=B(_17(_19.b,_));return new T2(1,_19.a,_1a);}},_1b=new T(function(){return B(unCStr("base"));}),_1c=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1d=new T(function(){return B(unCStr("IOException"));}),_1e=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1b,_1c,_1d),_1f=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1e,_S,_S),_1g=function(_1h){return E(_1f);},_1i=function(_1j){return E(E(_1j).a);},_1k=function(_1l,_1m,_1n){var _1o=B(A1(_1l,_)),_1p=B(A1(_1m,_)),_1q=hs_eqWord64(_1o.a,_1p.a);if(!_1q){return __Z;}else{var _1r=hs_eqWord64(_1o.b,_1p.b);return (!_1r)?__Z:new T1(1,_1n);}},_1s=function(_1t){var _1u=E(_1t);return new F(function(){return _1k(B(_1i(_1u.a)),_1g,_1u.b);});},_1v=new T(function(){return B(unCStr(": "));}),_1w=new T(function(){return B(unCStr(")"));}),_1x=new T(function(){return B(unCStr(" ("));}),_1y=new T(function(){return B(unCStr("interrupted"));}),_1z=new T(function(){return B(unCStr("system error"));}),_1A=new T(function(){return B(unCStr("unsatisified constraints"));}),_1B=new T(function(){return B(unCStr("user error"));}),_1C=new T(function(){return B(unCStr("permission denied"));}),_1D=new T(function(){return B(unCStr("illegal operation"));}),_1E=new T(function(){return B(unCStr("end of file"));}),_1F=new T(function(){return B(unCStr("resource exhausted"));}),_1G=new T(function(){return B(unCStr("resource busy"));}),_1H=new T(function(){return B(unCStr("does not exist"));}),_1I=new T(function(){return B(unCStr("already exists"));}),_1J=new T(function(){return B(unCStr("resource vanished"));}),_1K=new T(function(){return B(unCStr("timeout"));}),_1L=new T(function(){return B(unCStr("unsupported operation"));}),_1M=new T(function(){return B(unCStr("hardware fault"));}),_1N=new T(function(){return B(unCStr("inappropriate type"));}),_1O=new T(function(){return B(unCStr("invalid argument"));}),_1P=new T(function(){return B(unCStr("failed"));}),_1Q=new T(function(){return B(unCStr("protocol error"));}),_1R=function(_1S,_1T){switch(E(_1S)){case 0:return new F(function(){return _q(_1I,_1T);});break;case 1:return new F(function(){return _q(_1H,_1T);});break;case 2:return new F(function(){return _q(_1G,_1T);});break;case 3:return new F(function(){return _q(_1F,_1T);});break;case 4:return new F(function(){return _q(_1E,_1T);});break;case 5:return new F(function(){return _q(_1D,_1T);});break;case 6:return new F(function(){return _q(_1C,_1T);});break;case 7:return new F(function(){return _q(_1B,_1T);});break;case 8:return new F(function(){return _q(_1A,_1T);});break;case 9:return new F(function(){return _q(_1z,_1T);});break;case 10:return new F(function(){return _q(_1Q,_1T);});break;case 11:return new F(function(){return _q(_1P,_1T);});break;case 12:return new F(function(){return _q(_1O,_1T);});break;case 13:return new F(function(){return _q(_1N,_1T);});break;case 14:return new F(function(){return _q(_1M,_1T);});break;case 15:return new F(function(){return _q(_1L,_1T);});break;case 16:return new F(function(){return _q(_1K,_1T);});break;case 17:return new F(function(){return _q(_1J,_1T);});break;default:return new F(function(){return _q(_1y,_1T);});}},_1U=new T(function(){return B(unCStr("}"));}),_1V=new T(function(){return B(unCStr("{handle: "));}),_1W=function(_1X,_1Y,_1Z,_20,_21,_22){var _23=new T(function(){var _24=new T(function(){var _25=new T(function(){var _26=E(_20);if(!_26._){return E(_22);}else{var _27=new T(function(){return B(_q(_26,new T(function(){return B(_q(_1w,_22));},1)));},1);return B(_q(_1x,_27));}},1);return B(_1R(_1Y,_25));}),_28=E(_1Z);if(!_28._){return E(_24);}else{return B(_q(_28,new T(function(){return B(_q(_1v,_24));},1)));}}),_29=E(_21);if(!_29._){var _2a=E(_1X);if(!_2a._){return E(_23);}else{var _2b=E(_2a.a);if(!_2b._){var _2c=new T(function(){var _2d=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2d));},1);return new F(function(){return _q(_1V,_2c);});}else{var _2e=new T(function(){var _2f=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2f));},1);return new F(function(){return _q(_1V,_2e);});}}}else{return new F(function(){return _q(_29.a,new T(function(){return B(_q(_1v,_23));},1));});}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _1W(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_S);});},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1W(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1W(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2g,_2G),_2K=new T(function(){return new T5(0,_1g,_2J,_2L,_1s,_2g);}),_2L=function(_2M){return new T2(0,_2K,_2M);},_2N=__Z,_2O=7,_2P=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2Q=new T6(0,_2N,_2O,_S,_2P,_2N,_2N),_2R=new T(function(){return B(_2L(_2Q));}),_2S=function(_){return new F(function(){return die(_2R);});},_2T=function(_2U){return E(E(_2U).a);},_2V=function(_2W,_2X,_2Y,_){var _2Z=__arr2lst(0,_2Y),_30=B(_17(_2Z,_)),_31=E(_30);if(!_31._){return new F(function(){return _2S(_);});}else{var _32=E(_31.b);if(!_32._){return new F(function(){return _2S(_);});}else{if(!E(_32.b)._){var _33=B(A3(_2T,_2W,_31.a,_)),_34=B(A3(_2T,_2X,_32.a,_));return new T2(0,_33,_34);}else{return new F(function(){return _2S(_);});}}}},_35=function(_){return new F(function(){return __jsNull();});},_36=function(_37){var _38=B(A1(_37,_));return E(_38);},_39=new T(function(){return B(_36(_35));}),_3a=new T(function(){return E(_39);}),_3b=function(_3c,_3d,_){if(E(_3c)==7){var _3e=__app1(E(_R),_3d),_3f=B(_2V(_16,_16,_3e,_)),_3g=__get(_3d,E(_p)),_3h=__get(_3d,E(_o)),_3i=__get(_3d,E(_n));return new T(function(){return new T3(0,E(_3f),E(_2N),E(new T3(0,_3g,_3h,_3i)));});}else{var _3j=__app1(E(_R),_3d),_3k=B(_2V(_16,_16,_3j,_)),_3l=__get(_3d,E(_Q)),_3m=__eq(_3l,E(_3a));if(!E(_3m)){var _3n=__isUndef(_3l);if(!E(_3n)){var _3o=B(_K(_3l,_));return new T(function(){return new T3(0,E(_3k),E(new T1(1,_3o)),E(_P));});}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}},_3p=function(_3q,_3r,_){return new F(function(){return _3b(_3q,E(_3r),_);});},_3s="mouseout",_3t="mouseover",_3u="mousemove",_3v="mouseup",_3w="mousedown",_3x="dblclick",_3y="click",_3z="wheel",_3A=function(_3B){switch(E(_3B)){case 0:return E(_3y);case 1:return E(_3x);case 2:return E(_3w);case 3:return E(_3v);case 4:return E(_3u);case 5:return E(_3t);case 6:return E(_3s);default:return E(_3z);}},_3C=new T2(0,_3A,_3p),_3D=function(_3E){return E(_3E);},_3F=function(_3G,_3H){return E(_3G)==E(_3H);},_3I=function(_3J,_3K){return E(_3J)!=E(_3K);},_3L=new T2(0,_3F,_3I),_3M="screenY",_3N="screenX",_3O="clientY",_3P="clientX",_3Q="pageY",_3R="pageX",_3S="target",_3T="identifier",_3U=function(_3V,_){var _3W=__get(_3V,E(_3T)),_3X=__get(_3V,E(_3S)),_3Y=__get(_3V,E(_3R)),_3Z=__get(_3V,E(_3Q)),_40=__get(_3V,E(_3P)),_41=__get(_3V,E(_3O)),_42=__get(_3V,E(_3N)),_43=__get(_3V,E(_3M));return new T(function(){var _44=Number(_3W),_45=jsTrunc(_44);return new T5(0,_45,_3X,E(new T2(0,new T(function(){var _46=Number(_3Y);return jsTrunc(_46);}),new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}))),E(new T2(0,new T(function(){var _48=Number(_40);return jsTrunc(_48);}),new T(function(){var _49=Number(_41);return jsTrunc(_49);}))),E(new T2(0,new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}),new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}))));});},_4c=function(_4d,_){var _4e=E(_4d);if(!_4e._){return _S;}else{var _4f=B(_3U(E(_4e.a),_)),_4g=B(_4c(_4e.b,_));return new T2(1,_4f,_4g);}},_4h="touches",_4i=function(_4j){return E(E(_4j).b);},_4k=function(_4l,_4m,_){var _4n=__arr2lst(0,_4m),_4o=new T(function(){return B(_4i(_4l));}),_4p=function(_4q,_){var _4r=E(_4q);if(!_4r._){return _S;}else{var _4s=B(A2(_4o,_4r.a,_)),_4t=B(_4p(_4r.b,_));return new T2(1,_4s,_4t);}};return new F(function(){return _4p(_4n,_);});},_4u=function(_4v,_){return new F(function(){return _4k(_16,E(_4v),_);});},_4w=new T2(0,_11,_4u),_4x=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4y=function(_4z){return E(E(_4z).a);},_4A=function(_4B,_4C,_4D){while(1){var _4E=E(_4D);if(!_4E._){return false;}else{if(!B(A3(_4y,_4B,_4C,_4E.a))){_4D=_4E.b;continue;}else{return true;}}}},_4F=function(_4G,_4H){while(1){var _4I=B((function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return __Z;}else{var _4M=_4L.a,_4N=_4L.b;if(!B(A1(_4J,_4M))){var _4O=_4J;_4G=_4O;_4H=_4N;return __continue;}else{return new T2(1,_4M,new T(function(){return B(_4F(_4J,_4N));}));}}})(_4G,_4H));if(_4I!=__continue){return _4I;}}},_4P=function(_4Q,_){var _4R=__get(_4Q,E(_4h)),_4S=__arr2lst(0,_4R),_4T=B(_4c(_4S,_)),_4U=__app1(E(_4x),_4Q),_4V=B(_2V(_4w,_4w,_4U,_)),_4W=E(_4V),_4X=new T(function(){var _4Y=function(_4Z){return new F(function(){return _4A(_3L,new T(function(){return E(_4Z).a;}),_4W.a);});};return B(_4F(_4Y,_4T));}),_50=new T(function(){var _51=function(_52){return new F(function(){return _4A(_3L,new T(function(){return E(_52).a;}),_4W.b);});};return B(_4F(_51,_4T));});return new T3(0,_4T,_50,_4X);},_53=function(_54,_55,_){return new F(function(){return _4P(E(_55),_);});},_56="touchcancel",_57="touchend",_58="touchmove",_59="touchstart",_5a=function(_5b){switch(E(_5b)){case 0:return E(_59);case 1:return E(_58);case 2:return E(_57);default:return E(_56);}},_5c=new T2(0,_5a,_53),_5d=function(_5e,_5f,_){var _5g=B(A1(_5e,_)),_5h=B(A1(_5f,_));return _5g;},_5i=function(_5j,_5k,_){var _5l=B(A1(_5j,_)),_5m=B(A1(_5k,_));return new T(function(){return B(A1(_5l,_5m));});},_5n=function(_5o,_5p,_){var _5q=B(A1(_5p,_));return _5o;},_5r=function(_5s,_5t,_){var _5u=B(A1(_5t,_));return new T(function(){return B(A1(_5s,_5u));});},_5v=new T2(0,_5r,_5n),_5w=function(_5x,_){return _5x;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5z,_));return new F(function(){return A1(_5A,_);});},_5C=new T5(0,_5v,_5w,_5i,_5y,_5d),_5D=new T(function(){return E(_2K);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H){return new T6(0,_2N,_2O,_S,_5H,_2N,_2N);},_5I=function(_5J,_){var _5K=new T(function(){return B(A2(_5E,_5D,new T(function(){return B(A1(_5G,_5J));})));});return new F(function(){return die(_5K);});},_5L=function(_5M,_){return new F(function(){return _5I(_5M,_);});},_5N=function(_5O){return new F(function(){return A1(_5L,_5O);});},_5P=function(_5Q,_5R,_){var _5S=B(A1(_5Q,_));return new F(function(){return A2(_5R,_5S,_);});},_5T=new T5(0,_5C,_5P,_5y,_5w,_5N),_5U=function(_5V){return E(_5V);},_5W=new T2(0,_5T,_5U),_5X=new T2(0,_5W,_5w),_5Y=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_60=new T(function(){return eval("(function(cv){return cv.height})");}),_61=new T(function(){return eval("(function(cv){return cv.width})");}),_62=function(_63,_){var _64=__app1(E(_61),_63),_65=__app1(E(_60),_63),_66=__app1(E(_5Z),_63),_67=__app1(E(_5Y),_63);return new T2(0,new T2(0,_64,_65),new T2(0,_66,_67));},_68=function(_69,_6a){while(1){var _6b=B((function(_6c,_6d){var _6e=E(_6d);if(!_6e._){_69=new T2(1,new T2(0,_6e.b,_6e.c),new T(function(){return B(_68(_6c,_6e.e));}));_6a=_6e.d;return __continue;}else{return E(_6c);}})(_69,_6a));if(_6b!=__continue){return _6b;}}},_6f=function(_6g,_6h){while(1){var _6i=E(_6g);if(!_6i._){return (E(_6h)._==0)?true:false;}else{var _6j=E(_6h);if(!_6j._){return false;}else{if(E(_6i.a)!=E(_6j.a)){return false;}else{_6g=_6i.b;_6h=_6j.b;continue;}}}}},_6k=function(_6l,_6m){var _6n=E(_6m);return (_6n._==0)?__Z:new T2(1,new T(function(){return B(A1(_6l,_6n.a));}),new T(function(){return B(_6k(_6l,_6n.b));}));},_6o=function(_6p){return new T1(3,E(B(_6k(_5U,_6p))));},_6q="Tried to deserialie a non-array to a list!",_6r=new T1(0,_6q),_6s=new T1(1,_S),_6t=function(_6u){var _6v=E(_6u);if(!_6v._){return E(_6s);}else{var _6w=B(_6t(_6v.b));return (_6w._==0)?new T1(0,_6w.a):new T1(1,new T2(1,_6v.a,_6w.a));}},_6x=function(_6y){var _6z=E(_6y);if(_6z._==3){return new F(function(){return _6t(_6z.a);});}else{return E(_6r);}},_6A=function(_6B){return new T1(1,_6B);},_6C=new T4(0,_5U,_6o,_6A,_6x),_6D=function(_6E,_6F,_6G){return new F(function(){return A1(_6E,new T2(1,_2s,new T(function(){return B(A1(_6F,_6G));})));});},_6H=function(_6I){return new F(function(){return _A(0,E(_6I),_S);});},_6J=34,_6K=new T2(1,_6J,_S),_6L=new T(function(){return B(unCStr("!!: negative index"));}),_6M=new T(function(){return B(unCStr("Prelude."));}),_6N=new T(function(){return B(_q(_6M,_6L));}),_6O=new T(function(){return B(err(_6N));}),_6P=new T(function(){return B(unCStr("!!: index too large"));}),_6Q=new T(function(){return B(_q(_6M,_6P));}),_6R=new T(function(){return B(err(_6Q));}),_6S=function(_6T,_6U){while(1){var _6V=E(_6T);if(!_6V._){return E(_6R);}else{var _6W=E(_6U);if(!_6W){return E(_6V.a);}else{_6T=_6V.b;_6U=_6W-1|0;continue;}}}},_6X=function(_6Y,_6Z){if(_6Z>=0){return new F(function(){return _6S(_6Y,_6Z);});}else{return E(_6O);}},_70=new T(function(){return B(unCStr("ACK"));}),_71=new T(function(){return B(unCStr("BEL"));}),_72=new T(function(){return B(unCStr("BS"));}),_73=new T(function(){return B(unCStr("SP"));}),_74=new T2(1,_73,_S),_75=new T(function(){return B(unCStr("US"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("RS"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("GS"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("FS"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("ESC"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("SUB"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("EM"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("CAN"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("ETB"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("SYN"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("NAK"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("DC4"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DC3"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("DC2"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("DC1"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("DLE"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("SI"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("SO"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("CR"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("FF"));}),_7I=new T2(1,_7H,_7G),_7J=new T(function(){return B(unCStr("VT"));}),_7K=new T2(1,_7J,_7I),_7L=new T(function(){return B(unCStr("LF"));}),_7M=new T2(1,_7L,_7K),_7N=new T(function(){return B(unCStr("HT"));}),_7O=new T2(1,_7N,_7M),_7P=new T2(1,_72,_7O),_7Q=new T2(1,_71,_7P),_7R=new T2(1,_70,_7Q),_7S=new T(function(){return B(unCStr("ENQ"));}),_7T=new T2(1,_7S,_7R),_7U=new T(function(){return B(unCStr("EOT"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("ETX"));}),_7X=new T2(1,_7W,_7V),_7Y=new T(function(){return B(unCStr("STX"));}),_7Z=new T2(1,_7Y,_7X),_80=new T(function(){return B(unCStr("SOH"));}),_81=new T2(1,_80,_7Z),_82=new T(function(){return B(unCStr("NUL"));}),_83=new T2(1,_82,_81),_84=92,_85=new T(function(){return B(unCStr("\\DEL"));}),_86=new T(function(){return B(unCStr("\\a"));}),_87=new T(function(){return B(unCStr("\\\\"));}),_88=new T(function(){return B(unCStr("\\SO"));}),_89=new T(function(){return B(unCStr("\\r"));}),_8a=new T(function(){return B(unCStr("\\f"));}),_8b=new T(function(){return B(unCStr("\\v"));}),_8c=new T(function(){return B(unCStr("\\n"));}),_8d=new T(function(){return B(unCStr("\\t"));}),_8e=new T(function(){return B(unCStr("\\b"));}),_8f=function(_8g,_8h){if(_8g<=127){var _8i=E(_8g);switch(_8i){case 92:return new F(function(){return _q(_87,_8h);});break;case 127:return new F(function(){return _q(_85,_8h);});break;default:if(_8i<32){var _8j=E(_8i);switch(_8j){case 7:return new F(function(){return _q(_86,_8h);});break;case 8:return new F(function(){return _q(_8e,_8h);});break;case 9:return new F(function(){return _q(_8d,_8h);});break;case 10:return new F(function(){return _q(_8c,_8h);});break;case 11:return new F(function(){return _q(_8b,_8h);});break;case 12:return new F(function(){return _q(_8a,_8h);});break;case 13:return new F(function(){return _q(_89,_8h);});break;case 14:return new F(function(){return _q(_88,new T(function(){var _8k=E(_8h);if(!_8k._){return __Z;}else{if(E(_8k.a)==72){return B(unAppCStr("\\&",_8k));}else{return E(_8k);}}},1));});break;default:return new F(function(){return _q(new T2(1,_84,new T(function(){return B(_6X(_83,_8j));})),_8h);});}}else{return new T2(1,_8i,_8h);}}}else{var _8l=new T(function(){var _8m=jsShowI(_8g);return B(_q(fromJSStr(_8m),new T(function(){var _8n=E(_8h);if(!_8n._){return __Z;}else{var _8o=E(_8n.a);if(_8o<48){return E(_8n);}else{if(_8o>57){return E(_8n);}else{return B(unAppCStr("\\&",_8n));}}}},1)));});return new T2(1,_84,_8l);}},_8p=new T(function(){return B(unCStr("\\\""));}),_8q=function(_8r,_8s){var _8t=E(_8r);if(!_8t._){return E(_8s);}else{var _8u=_8t.b,_8v=E(_8t.a);if(_8v==34){return new F(function(){return _q(_8p,new T(function(){return B(_8q(_8u,_8s));},1));});}else{return new F(function(){return _8f(_8v,new T(function(){return B(_8q(_8u,_8s));}));});}}},_8w=function(_8x){return new T2(1,_6J,new T(function(){return B(_8q(_8x,_6K));}));},_8y=function(_8z,_8A){if(_8z<=_8A){var _8B=function(_8C){return new T2(1,_8C,new T(function(){if(_8C!=_8A){return B(_8B(_8C+1|0));}else{return __Z;}}));};return new F(function(){return _8B(_8z);});}else{return __Z;}},_8D=function(_8E){return new F(function(){return _8y(E(_8E),2147483647);});},_8F=function(_8G,_8H,_8I){if(_8I<=_8H){var _8J=new T(function(){var _8K=_8H-_8G|0,_8L=function(_8M){return (_8M>=(_8I-_8K|0))?new T2(1,_8M,new T(function(){return B(_8L(_8M+_8K|0));})):new T2(1,_8M,_S);};return B(_8L(_8H));});return new T2(1,_8G,_8J);}else{return (_8I<=_8G)?new T2(1,_8G,_S):__Z;}},_8N=function(_8O,_8P,_8Q){if(_8Q>=_8P){var _8R=new T(function(){var _8S=_8P-_8O|0,_8T=function(_8U){return (_8U<=(_8Q-_8S|0))?new T2(1,_8U,new T(function(){return B(_8T(_8U+_8S|0));})):new T2(1,_8U,_S);};return B(_8T(_8P));});return new T2(1,_8O,_8R);}else{return (_8Q>=_8O)?new T2(1,_8O,_S):__Z;}},_8V=function(_8W,_8X){if(_8X<_8W){return new F(function(){return _8F(_8W,_8X, -2147483648);});}else{return new F(function(){return _8N(_8W,_8X,2147483647);});}},_8Y=function(_8Z,_90){return new F(function(){return _8V(E(_8Z),E(_90));});},_91=function(_92,_93,_94){if(_93<_92){return new F(function(){return _8F(_92,_93,_94);});}else{return new F(function(){return _8N(_92,_93,_94);});}},_95=function(_96,_97,_98){return new F(function(){return _91(E(_96),E(_97),E(_98));});},_99=function(_9a,_9b){return new F(function(){return _8y(E(_9a),E(_9b));});},_9c=function(_9d){return E(_9d);},_9e=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_9f=new T(function(){return B(err(_9e));}),_9g=function(_9h){var _9i=E(_9h);return (_9i==( -2147483648))?E(_9f):_9i-1|0;},_9j=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9k=new T(function(){return B(err(_9j));}),_9l=function(_9m){var _9n=E(_9m);return (_9n==2147483647)?E(_9k):_9n+1|0;},_9o={_:0,a:_9l,b:_9g,c:_9c,d:_9c,e:_8D,f:_8Y,g:_99,h:_95},_9p=function(_9q,_9r){if(_9q<=0){if(_9q>=0){return new F(function(){return quot(_9q,_9r);});}else{if(_9r<=0){return new F(function(){return quot(_9q,_9r);});}else{return quot(_9q+1|0,_9r)-1|0;}}}else{if(_9r>=0){if(_9q>=0){return new F(function(){return quot(_9q,_9r);});}else{if(_9r<=0){return new F(function(){return quot(_9q,_9r);});}else{return quot(_9q+1|0,_9r)-1|0;}}}else{return quot(_9q-1|0,_9r)-1|0;}}},_9s=new T(function(){return B(unCStr("base"));}),_9t=new T(function(){return B(unCStr("GHC.Exception"));}),_9u=new T(function(){return B(unCStr("ArithException"));}),_9v=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9s,_9t,_9u),_9w=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9v,_S,_S),_9x=function(_9y){return E(_9w);},_9z=function(_9A){var _9B=E(_9A);return new F(function(){return _1k(B(_1i(_9B.a)),_9x,_9B.b);});},_9C=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9D=new T(function(){return B(unCStr("denormal"));}),_9E=new T(function(){return B(unCStr("divide by zero"));}),_9F=new T(function(){return B(unCStr("loss of precision"));}),_9G=new T(function(){return B(unCStr("arithmetic underflow"));}),_9H=new T(function(){return B(unCStr("arithmetic overflow"));}),_9I=function(_9J,_9K){switch(E(_9J)){case 0:return new F(function(){return _q(_9H,_9K);});break;case 1:return new F(function(){return _q(_9G,_9K);});break;case 2:return new F(function(){return _q(_9F,_9K);});break;case 3:return new F(function(){return _q(_9E,_9K);});break;case 4:return new F(function(){return _q(_9D,_9K);});break;default:return new F(function(){return _q(_9C,_9K);});}},_9L=function(_9M){return new F(function(){return _9I(_9M,_S);});},_9N=function(_9O,_9P,_9Q){return new F(function(){return _9I(_9P,_9Q);});},_9R=function(_9S,_9T){return new F(function(){return _2v(_9I,_9S,_9T);});},_9U=new T3(0,_9N,_9L,_9R),_9V=new T(function(){return new T5(0,_9x,_9U,_9W,_9z,_9L);}),_9W=function(_9X){return new T2(0,_9V,_9X);},_9Y=3,_9Z=new T(function(){return B(_9W(_9Y));}),_a0=new T(function(){return die(_9Z);}),_a1=0,_a2=new T(function(){return B(_9W(_a1));}),_a3=new T(function(){return die(_a2);}),_a4=function(_a5,_a6){var _a7=E(_a6);switch(_a7){case  -1:var _a8=E(_a5);if(_a8==( -2147483648)){return E(_a3);}else{return new F(function(){return _9p(_a8, -1);});}break;case 0:return E(_a0);default:return new F(function(){return _9p(_a5,_a7);});}},_a9=function(_aa,_ab){return new F(function(){return _a4(E(_aa),E(_ab));});},_ac=0,_ad=new T2(0,_a3,_ac),_ae=function(_af,_ag){var _ah=E(_af),_ai=E(_ag);switch(_ai){case  -1:var _aj=E(_ah);if(_aj==( -2147483648)){return E(_ad);}else{if(_aj<=0){if(_aj>=0){var _ak=quotRemI(_aj, -1);return new T2(0,_ak.a,_ak.b);}else{var _al=quotRemI(_aj, -1);return new T2(0,_al.a,_al.b);}}else{var _am=quotRemI(_aj-1|0, -1);return new T2(0,_am.a-1|0,(_am.b+( -1)|0)+1|0);}}break;case 0:return E(_a0);default:if(_ah<=0){if(_ah>=0){var _an=quotRemI(_ah,_ai);return new T2(0,_an.a,_an.b);}else{if(_ai<=0){var _ao=quotRemI(_ah,_ai);return new T2(0,_ao.a,_ao.b);}else{var _ap=quotRemI(_ah+1|0,_ai);return new T2(0,_ap.a-1|0,(_ap.b+_ai|0)-1|0);}}}else{if(_ai>=0){if(_ah>=0){var _aq=quotRemI(_ah,_ai);return new T2(0,_aq.a,_aq.b);}else{if(_ai<=0){var _ar=quotRemI(_ah,_ai);return new T2(0,_ar.a,_ar.b);}else{var _as=quotRemI(_ah+1|0,_ai);return new T2(0,_as.a-1|0,(_as.b+_ai|0)-1|0);}}}else{var _at=quotRemI(_ah-1|0,_ai);return new T2(0,_at.a-1|0,(_at.b+_ai|0)+1|0);}}}},_au=function(_av,_aw){var _ax=_av%_aw;if(_av<=0){if(_av>=0){return E(_ax);}else{if(_aw<=0){return E(_ax);}else{var _ay=E(_ax);return (_ay==0)?0:_ay+_aw|0;}}}else{if(_aw>=0){if(_av>=0){return E(_ax);}else{if(_aw<=0){return E(_ax);}else{var _az=E(_ax);return (_az==0)?0:_az+_aw|0;}}}else{var _aA=E(_ax);return (_aA==0)?0:_aA+_aw|0;}}},_aB=function(_aC,_aD){var _aE=E(_aD);switch(_aE){case  -1:return E(_ac);case 0:return E(_a0);default:return new F(function(){return _au(E(_aC),_aE);});}},_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=E(_aH);switch(_aJ){case  -1:var _aK=E(_aI);if(_aK==( -2147483648)){return E(_a3);}else{return new F(function(){return quot(_aK, -1);});}break;case 0:return E(_a0);default:return new F(function(){return quot(_aI,_aJ);});}},_aL=function(_aM,_aN){var _aO=E(_aM),_aP=E(_aN);switch(_aP){case  -1:var _aQ=E(_aO);if(_aQ==( -2147483648)){return E(_ad);}else{var _aR=quotRemI(_aQ, -1);return new T2(0,_aR.a,_aR.b);}break;case 0:return E(_a0);default:var _aS=quotRemI(_aO,_aP);return new T2(0,_aS.a,_aS.b);}},_aT=function(_aU,_aV){var _aW=E(_aV);switch(_aW){case  -1:return E(_ac);case 0:return E(_a0);default:return E(_aU)%_aW;}},_aX=function(_aY){return new T1(0,_aY);},_aZ=function(_b0){return new F(function(){return _aX(E(_b0));});},_b1=new T1(0,1),_b2=function(_b3){return new T2(0,E(B(_aX(E(_b3)))),E(_b1));},_b4=function(_b5,_b6){return imul(E(_b5),E(_b6))|0;},_b7=function(_b8,_b9){return E(_b8)+E(_b9)|0;},_ba=function(_bb,_bc){return E(_bb)-E(_bc)|0;},_bd=function(_be){var _bf=E(_be);return (_bf<0)? -_bf:E(_bf);},_bg=function(_bh){var _bi=E(_bh);if(!_bi._){return E(_bi.a);}else{return new F(function(){return I_toInt(_bi.a);});}},_bj=function(_bk){return new F(function(){return _bg(_bk);});},_bl=function(_bm){return  -E(_bm);},_bn= -1,_bo=0,_bp=1,_bq=function(_br){var _bs=E(_br);return (_bs>=0)?(E(_bs)==0)?E(_bo):E(_bp):E(_bn);},_bt={_:0,a:_b7,b:_ba,c:_b4,d:_bl,e:_bd,f:_bq,g:_bj},_bu=function(_bv,_bw){var _bx=E(_bv),_by=E(_bw);return (_bx>_by)?E(_bx):E(_by);},_bz=function(_bA,_bB){var _bC=E(_bA),_bD=E(_bB);return (_bC>_bD)?E(_bD):E(_bC);},_bE=function(_bF,_bG){return (_bF>=_bG)?(_bF!=_bG)?2:1:0;},_bH=function(_bI,_bJ){return new F(function(){return _bE(E(_bI),E(_bJ));});},_bK=function(_bL,_bM){return E(_bL)>=E(_bM);},_bN=function(_bO,_bP){return E(_bO)>E(_bP);},_bQ=function(_bR,_bS){return E(_bR)<=E(_bS);},_bT=function(_bU,_bV){return E(_bU)<E(_bV);},_bW={_:0,a:_3L,b:_bH,c:_bT,d:_bQ,e:_bN,f:_bK,g:_bu,h:_bz},_bX=new T3(0,_bt,_bW,_b2),_bY={_:0,a:_bX,b:_9o,c:_aF,d:_aT,e:_a9,f:_aB,g:_aL,h:_ae,i:_aZ},_bZ=function(_c0){var _c1=E(_c0);return new F(function(){return Math.log(_c1+(_c1+1)*Math.sqrt((_c1-1)/(_c1+1)));});},_c2=function(_c3){var _c4=E(_c3);return new F(function(){return Math.log(_c4+Math.sqrt(1+_c4*_c4));});},_c5=function(_c6){var _c7=E(_c6);return 0.5*Math.log((1+_c7)/(1-_c7));},_c8=function(_c9,_ca){return Math.log(E(_ca))/Math.log(E(_c9));},_cb=3.141592653589793,_cc=new T1(0,1),_cd=function(_ce,_cf){var _cg=E(_ce);if(!_cg._){var _ch=_cg.a,_ci=E(_cf);if(!_ci._){var _cj=_ci.a;return (_ch!=_cj)?(_ch>_cj)?2:0:1;}else{var _ck=I_compareInt(_ci.a,_ch);return (_ck<=0)?(_ck>=0)?1:2:0;}}else{var _cl=_cg.a,_cm=E(_cf);if(!_cm._){var _cn=I_compareInt(_cl,_cm.a);return (_cn>=0)?(_cn<=0)?1:2:0;}else{var _co=I_compare(_cl,_cm.a);return (_co>=0)?(_co<=0)?1:2:0;}}},_cp=function(_cq,_cr){var _cs=E(_cq);return (_cs._==0)?_cs.a*Math.pow(2,_cr):I_toNumber(_cs.a)*Math.pow(2,_cr);},_ct=function(_cu,_cv){var _cw=E(_cu);if(!_cw._){var _cx=_cw.a,_cy=E(_cv);return (_cy._==0)?_cx==_cy.a:(I_compareInt(_cy.a,_cx)==0)?true:false;}else{var _cz=_cw.a,_cA=E(_cv);return (_cA._==0)?(I_compareInt(_cz,_cA.a)==0)?true:false:(I_compare(_cz,_cA.a)==0)?true:false;}},_cB=function(_cC,_cD){while(1){var _cE=E(_cC);if(!_cE._){var _cF=_cE.a,_cG=E(_cD);if(!_cG._){var _cH=_cG.a,_cI=addC(_cF,_cH);if(!E(_cI.b)){return new T1(0,_cI.a);}else{_cC=new T1(1,I_fromInt(_cF));_cD=new T1(1,I_fromInt(_cH));continue;}}else{_cC=new T1(1,I_fromInt(_cF));_cD=_cG;continue;}}else{var _cJ=E(_cD);if(!_cJ._){_cC=_cE;_cD=new T1(1,I_fromInt(_cJ.a));continue;}else{return new T1(1,I_add(_cE.a,_cJ.a));}}}},_cK=function(_cL,_cM){while(1){var _cN=E(_cL);if(!_cN._){var _cO=E(_cN.a);if(_cO==( -2147483648)){_cL=new T1(1,I_fromInt( -2147483648));continue;}else{var _cP=E(_cM);if(!_cP._){var _cQ=_cP.a;return new T2(0,new T1(0,quot(_cO,_cQ)),new T1(0,_cO%_cQ));}else{_cL=new T1(1,I_fromInt(_cO));_cM=_cP;continue;}}}else{var _cR=E(_cM);if(!_cR._){_cL=_cN;_cM=new T1(1,I_fromInt(_cR.a));continue;}else{var _cS=I_quotRem(_cN.a,_cR.a);return new T2(0,new T1(1,_cS.a),new T1(1,_cS.b));}}}},_cT=new T1(0,0),_cU=function(_cV,_cW){while(1){var _cX=E(_cV);if(!_cX._){_cV=new T1(1,I_fromInt(_cX.a));continue;}else{return new T1(1,I_shiftLeft(_cX.a,_cW));}}},_cY=function(_cZ,_d0,_d1){if(!B(_ct(_d1,_cT))){var _d2=B(_cK(_d0,_d1)),_d3=_d2.a;switch(B(_cd(B(_cU(_d2.b,1)),_d1))){case 0:return new F(function(){return _cp(_d3,_cZ);});break;case 1:if(!(B(_bg(_d3))&1)){return new F(function(){return _cp(_d3,_cZ);});}else{return new F(function(){return _cp(B(_cB(_d3,_cc)),_cZ);});}break;default:return new F(function(){return _cp(B(_cB(_d3,_cc)),_cZ);});}}else{return E(_a0);}},_d4=function(_d5,_d6){var _d7=E(_d5);if(!_d7._){var _d8=_d7.a,_d9=E(_d6);return (_d9._==0)?_d8>_d9.a:I_compareInt(_d9.a,_d8)<0;}else{var _da=_d7.a,_db=E(_d6);return (_db._==0)?I_compareInt(_da,_db.a)>0:I_compare(_da,_db.a)>0;}},_dc=new T1(0,1),_dd=function(_de,_df){var _dg=E(_de);if(!_dg._){var _dh=_dg.a,_di=E(_df);return (_di._==0)?_dh<_di.a:I_compareInt(_di.a,_dh)>0;}else{var _dj=_dg.a,_dk=E(_df);return (_dk._==0)?I_compareInt(_dj,_dk.a)<0:I_compare(_dj,_dk.a)<0;}},_dl=new T(function(){return B(unCStr("base"));}),_dm=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dn=new T(function(){return B(unCStr("PatternMatchFail"));}),_do=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dl,_dm,_dn),_dp=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_do,_S,_S),_dq=function(_dr){return E(_dp);},_ds=function(_dt){var _du=E(_dt);return new F(function(){return _1k(B(_1i(_du.a)),_dq,_du.b);});},_dv=function(_dw){return E(E(_dw).a);},_dx=function(_dy){return new T2(0,_dz,_dy);},_dA=function(_dB,_dC){return new F(function(){return _q(E(_dB).a,_dC);});},_dD=function(_dE,_dF){return new F(function(){return _2v(_dA,_dE,_dF);});},_dG=function(_dH,_dI,_dJ){return new F(function(){return _q(E(_dI).a,_dJ);});},_dK=new T3(0,_dG,_dv,_dD),_dz=new T(function(){return new T5(0,_dq,_dK,_dx,_ds,_dv);}),_dL=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dM=function(_dN,_dO){return new F(function(){return die(new T(function(){return B(A2(_5E,_dO,_dN));}));});},_dP=function(_dQ,_9X){return new F(function(){return _dM(_dQ,_9X);});},_dR=function(_dS,_dT){var _dU=E(_dT);if(!_dU._){return new T2(0,_S,_S);}else{var _dV=_dU.a;if(!B(A1(_dS,_dV))){return new T2(0,_S,_dU);}else{var _dW=new T(function(){var _dX=B(_dR(_dS,_dU.b));return new T2(0,_dX.a,_dX.b);});return new T2(0,new T2(1,_dV,new T(function(){return E(E(_dW).a);})),new T(function(){return E(E(_dW).b);}));}}},_dY=32,_dZ=new T(function(){return B(unCStr("\n"));}),_e0=function(_e1){return (E(_e1)==124)?false:true;},_e2=function(_e3,_e4){var _e5=B(_dR(_e0,B(unCStr(_e3)))),_e6=_e5.a,_e7=function(_e8,_e9){var _ea=new T(function(){var _eb=new T(function(){return B(_q(_e4,new T(function(){return B(_q(_e9,_dZ));},1)));});return B(unAppCStr(": ",_eb));},1);return new F(function(){return _q(_e8,_ea);});},_ec=E(_e5.b);if(!_ec._){return new F(function(){return _e7(_e6,_S);});}else{if(E(_ec.a)==124){return new F(function(){return _e7(_e6,new T2(1,_dY,_ec.b));});}else{return new F(function(){return _e7(_e6,_S);});}}},_ed=function(_ee){return new F(function(){return _dP(new T1(0,new T(function(){return B(_e2(_ee,_dL));})),_dz);});},_ef=function(_eg){var _eh=function(_ei,_ej){while(1){if(!B(_dd(_ei,_eg))){if(!B(_d4(_ei,_eg))){if(!B(_ct(_ei,_eg))){return new F(function(){return _ed("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ej);}}else{return _ej-1|0;}}else{var _ek=B(_cU(_ei,1)),_el=_ej+1|0;_ei=_ek;_ej=_el;continue;}}};return new F(function(){return _eh(_dc,0);});},_em=function(_en){var _eo=E(_en);if(!_eo._){var _ep=_eo.a>>>0;if(!_ep){return  -1;}else{var _eq=function(_er,_es){while(1){if(_er>=_ep){if(_er<=_ep){if(_er!=_ep){return new F(function(){return _ed("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_es);}}else{return _es-1|0;}}else{var _et=imul(_er,2)>>>0,_eu=_es+1|0;_er=_et;_es=_eu;continue;}}};return new F(function(){return _eq(1,0);});}}else{return new F(function(){return _ef(_eo);});}},_ev=function(_ew){var _ex=E(_ew);if(!_ex._){var _ey=_ex.a>>>0;if(!_ey){return new T2(0, -1,0);}else{var _ez=function(_eA,_eB){while(1){if(_eA>=_ey){if(_eA<=_ey){if(_eA!=_ey){return new F(function(){return _ed("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_eB);}}else{return _eB-1|0;}}else{var _eC=imul(_eA,2)>>>0,_eD=_eB+1|0;_eA=_eC;_eB=_eD;continue;}}};return new T2(0,B(_ez(1,0)),(_ey&_ey-1>>>0)>>>0&4294967295);}}else{var _eE=_ex.a;return new T2(0,B(_em(_ex)),I_compareInt(I_and(_eE,I_sub(_eE,I_fromInt(1))),0));}},_eF=function(_eG,_eH){var _eI=E(_eG);if(!_eI._){var _eJ=_eI.a,_eK=E(_eH);return (_eK._==0)?_eJ<=_eK.a:I_compareInt(_eK.a,_eJ)>=0;}else{var _eL=_eI.a,_eM=E(_eH);return (_eM._==0)?I_compareInt(_eL,_eM.a)<=0:I_compare(_eL,_eM.a)<=0;}},_eN=function(_eO,_eP){while(1){var _eQ=E(_eO);if(!_eQ._){var _eR=_eQ.a,_eS=E(_eP);if(!_eS._){return new T1(0,(_eR>>>0&_eS.a>>>0)>>>0&4294967295);}else{_eO=new T1(1,I_fromInt(_eR));_eP=_eS;continue;}}else{var _eT=E(_eP);if(!_eT._){_eO=_eQ;_eP=new T1(1,I_fromInt(_eT.a));continue;}else{return new T1(1,I_and(_eQ.a,_eT.a));}}}},_eU=function(_eV,_eW){while(1){var _eX=E(_eV);if(!_eX._){var _eY=_eX.a,_eZ=E(_eW);if(!_eZ._){var _f0=_eZ.a,_f1=subC(_eY,_f0);if(!E(_f1.b)){return new T1(0,_f1.a);}else{_eV=new T1(1,I_fromInt(_eY));_eW=new T1(1,I_fromInt(_f0));continue;}}else{_eV=new T1(1,I_fromInt(_eY));_eW=_eZ;continue;}}else{var _f2=E(_eW);if(!_f2._){_eV=_eX;_eW=new T1(1,I_fromInt(_f2.a));continue;}else{return new T1(1,I_sub(_eX.a,_f2.a));}}}},_f3=new T1(0,2),_f4=function(_f5,_f6){var _f7=E(_f5);if(!_f7._){var _f8=(_f7.a>>>0&(2<<_f6>>>0)-1>>>0)>>>0,_f9=1<<_f6>>>0;return (_f9<=_f8)?(_f9>=_f8)?1:2:0;}else{var _fa=B(_eN(_f7,B(_eU(B(_cU(_f3,_f6)),_dc)))),_fb=B(_cU(_dc,_f6));return (!B(_d4(_fb,_fa)))?(!B(_dd(_fb,_fa)))?1:2:0;}},_fc=function(_fd,_fe){while(1){var _ff=E(_fd);if(!_ff._){_fd=new T1(1,I_fromInt(_ff.a));continue;}else{return new T1(1,I_shiftRight(_ff.a,_fe));}}},_fg=function(_fh,_fi,_fj,_fk){var _fl=B(_ev(_fk)),_fm=_fl.a;if(!E(_fl.b)){var _fn=B(_em(_fj));if(_fn<((_fm+_fh|0)-1|0)){var _fo=_fm+(_fh-_fi|0)|0;if(_fo>0){if(_fo>_fn){if(_fo<=(_fn+1|0)){if(!E(B(_ev(_fj)).b)){return 0;}else{return new F(function(){return _cp(_cc,_fh-_fi|0);});}}else{return 0;}}else{var _fp=B(_fc(_fj,_fo));switch(B(_f4(_fj,_fo-1|0))){case 0:return new F(function(){return _cp(_fp,_fh-_fi|0);});break;case 1:if(!(B(_bg(_fp))&1)){return new F(function(){return _cp(_fp,_fh-_fi|0);});}else{return new F(function(){return _cp(B(_cB(_fp,_cc)),_fh-_fi|0);});}break;default:return new F(function(){return _cp(B(_cB(_fp,_cc)),_fh-_fi|0);});}}}else{return new F(function(){return _cp(_fj,(_fh-_fi|0)-_fo|0);});}}else{if(_fn>=_fi){var _fq=B(_fc(_fj,(_fn+1|0)-_fi|0));switch(B(_f4(_fj,_fn-_fi|0))){case 0:return new F(function(){return _cp(_fq,((_fn-_fm|0)+1|0)-_fi|0);});break;case 2:return new F(function(){return _cp(B(_cB(_fq,_cc)),((_fn-_fm|0)+1|0)-_fi|0);});break;default:if(!(B(_bg(_fq))&1)){return new F(function(){return _cp(_fq,((_fn-_fm|0)+1|0)-_fi|0);});}else{return new F(function(){return _cp(B(_cB(_fq,_cc)),((_fn-_fm|0)+1|0)-_fi|0);});}}}else{return new F(function(){return _cp(_fj, -_fm);});}}}else{var _fr=B(_em(_fj))-_fm|0,_fs=function(_ft){var _fu=function(_fv,_fw){if(!B(_eF(B(_cU(_fw,_fi)),_fv))){return new F(function(){return _cY(_ft-_fi|0,_fv,_fw);});}else{return new F(function(){return _cY((_ft-_fi|0)+1|0,_fv,B(_cU(_fw,1)));});}};if(_ft>=_fi){if(_ft!=_fi){return new F(function(){return _fu(_fj,new T(function(){return B(_cU(_fk,_ft-_fi|0));}));});}else{return new F(function(){return _fu(_fj,_fk);});}}else{return new F(function(){return _fu(new T(function(){return B(_cU(_fj,_fi-_ft|0));}),_fk);});}};if(_fh>_fr){return new F(function(){return _fs(_fh);});}else{return new F(function(){return _fs(_fr);});}}},_fx=new T1(0,2147483647),_fy=new T(function(){return B(_cB(_fx,_dc));}),_fz=function(_fA){var _fB=E(_fA);if(!_fB._){var _fC=E(_fB.a);return (_fC==( -2147483648))?E(_fy):new T1(0, -_fC);}else{return new T1(1,I_negate(_fB.a));}},_fD=new T(function(){return 0/0;}),_fE=new T(function(){return  -1/0;}),_fF=new T(function(){return 1/0;}),_fG=0,_fH=function(_fI,_fJ){if(!B(_ct(_fJ,_cT))){if(!B(_ct(_fI,_cT))){if(!B(_dd(_fI,_cT))){return new F(function(){return _fg( -1021,53,_fI,_fJ);});}else{return  -B(_fg( -1021,53,B(_fz(_fI)),_fJ));}}else{return E(_fG);}}else{return (!B(_ct(_fI,_cT)))?(!B(_dd(_fI,_cT)))?E(_fF):E(_fE):E(_fD);}},_fK=function(_fL){var _fM=E(_fL);return new F(function(){return _fH(_fM.a,_fM.b);});},_fN=function(_fO){return 1/E(_fO);},_fP=function(_fQ){var _fR=E(_fQ);return (_fR!=0)?(_fR<=0)? -_fR:E(_fR):E(_fG);},_fS=function(_fT){var _fU=E(_fT);if(!_fU._){return _fU.a;}else{return new F(function(){return I_toNumber(_fU.a);});}},_fV=function(_fW){return new F(function(){return _fS(_fW);});},_fX=1,_fY= -1,_fZ=function(_g0){var _g1=E(_g0);return (_g1<=0)?(_g1>=0)?E(_g1):E(_fY):E(_fX);},_g2=function(_g3,_g4){return E(_g3)-E(_g4);},_g5=function(_g6){return  -E(_g6);},_g7=function(_g8,_g9){return E(_g8)+E(_g9);},_ga=function(_gb,_gc){return E(_gb)*E(_gc);},_gd={_:0,a:_g7,b:_g2,c:_ga,d:_g5,e:_fP,f:_fZ,g:_fV},_ge=function(_gf,_gg){return E(_gf)/E(_gg);},_gh=new T4(0,_gd,_ge,_fN,_fK),_gi=function(_gj){return new F(function(){return Math.acos(E(_gj));});},_gk=function(_gl){return new F(function(){return Math.asin(E(_gl));});},_gm=function(_gn){return new F(function(){return Math.atan(E(_gn));});},_go=function(_gp){return new F(function(){return Math.cos(E(_gp));});},_gq=function(_gr){return new F(function(){return cosh(E(_gr));});},_gs=function(_gt){return new F(function(){return Math.exp(E(_gt));});},_gu=function(_gv){return new F(function(){return Math.log(E(_gv));});},_gw=function(_gx,_gy){return new F(function(){return Math.pow(E(_gx),E(_gy));});},_gz=function(_gA){return new F(function(){return Math.sin(E(_gA));});},_gB=function(_gC){return new F(function(){return sinh(E(_gC));});},_gD=function(_gE){return new F(function(){return Math.sqrt(E(_gE));});},_gF=function(_gG){return new F(function(){return Math.tan(E(_gG));});},_gH=function(_gI){return new F(function(){return tanh(E(_gI));});},_gJ={_:0,a:_gh,b:_cb,c:_gs,d:_gu,e:_gD,f:_gw,g:_c8,h:_gz,i:_go,j:_gF,k:_gk,l:_gi,m:_gm,n:_gB,o:_gq,p:_gH,q:_c2,r:_bZ,s:_c5},_gK=0,_gL=function(_){return _gK;},_gM=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gN=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gO=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gP=function(_gQ,_gR,_gS,_){var _gT=__app1(E(_gN),_gS),_gU=__app2(E(_gO),_gS,E(_gQ)),_gV=B(A2(_gR,_gS,_)),_gW=__app1(E(_gM),_gS);return new F(function(){return _gL(_);});},_gX=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gY=function(_gZ,_h0,_h1,_h2,_){var _h3=__app1(E(_gN),_h2),_h4=__app3(E(_gX),_h2,E(_gZ),E(_h0)),_h5=B(A2(_h1,_h2,_)),_h6=__app1(E(_gM),_h2);return new F(function(){return _gL(_);});},_h7=function(_h8,_h9){return E(_h8)!=E(_h9);},_ha=function(_hb,_hc){return E(_hb)==E(_hc);},_hd=new T2(0,_ha,_h7),_he=function(_hf){return E(E(_hf).a);},_hg=function(_hh){return E(E(_hh).a);},_hi=function(_hj){return E(E(_hj).b);},_hk=function(_hl){return E(E(_hl).g);},_hm=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hn=0,_ho=3.3333333333333335,_hp=16.666666666666668,_hq=function(_hr){return E(E(_hr).b);},_hs=new T1(0,0),_ht=new T1(0,2),_hu=function(_hv){return E(E(_hv).i);},_hw=function(_hx,_hy,_hz,_hA,_hB,_hC,_hD,_hE){var _hF=new T(function(){var _hG=E(_hE);if(_hG<=31){return B(_4A(_hd,_hG,_hm));}else{if(_hG>=128){return B(_4A(_hd,_hG,_hm));}else{return true;}}}),_hH=new T(function(){if(E(_hA)==8){return new T2(0,new T(function(){return B(_fS(B(A2(_hu,_hy,_hC))))*28+20;}),new T(function(){return B(_fS(B(A2(_hu,_hz,_hD))))*20+8*(E(_hB)-1);}));}else{return new T2(0,new T(function(){return B(_fS(B(A2(_hu,_hy,_hC))))*28;}),new T(function(){return B(_fS(B(A2(_hu,_hz,_hD))))*20;}));}}),_hI=new T(function(){var _hJ=B(_he(_hx));if(!E(_hF)){return B(A2(_hk,B(_hg(_hJ)),_hs));}else{return B(A3(_hi,_hJ,new T(function(){return B(_hq(_hx));}),new T(function(){return B(A2(_hk,B(_hg(_hJ)),_ht));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hH).a);}),new T(function(){return E(E(_hH).b);})),new T2(0,new T(function(){if(!E(_hF)){return E(_hn);}else{return E(_ho);}}),new T(function(){if(!E(_hF)){return E(_hn);}else{return E(_hp);}})),_hI);},_hK=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hL=function(_hM,_hN,_hO){var _hP=new T(function(){return toJSStr(E(_hO));});return function(_hQ,_){var _hR=__app4(E(_hK),E(_hQ),E(_hP),E(_hM),E(_hN));return new F(function(){return _gL(_);});};},_hS=0,_hT=",",_hU="rgba(",_hV=new T(function(){return toJSStr(_S);}),_hW="rgb(",_hX=")",_hY=new T2(1,_hX,_S),_hZ=function(_i0){var _i1=E(_i0);if(!_i1._){var _i2=jsCat(new T2(1,_hW,new T2(1,new T(function(){return String(_i1.a);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.b);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.c);}),_hY)))))),E(_hV));return E(_i2);}else{var _i3=jsCat(new T2(1,_hU,new T2(1,new T(function(){return String(_i1.a);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.b);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.c);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.d);}),_hY)))))))),E(_hV));return E(_i3);}},_i4="strokeStyle",_i5="fillStyle",_i6=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i7=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i8=function(_i9,_ia){var _ib=new T(function(){return B(_hZ(_i9));});return function(_ic,_){var _id=E(_ic),_ie=E(_i5),_if=E(_i6),_ig=__app2(_if,_id,_ie),_ih=E(_i4),_ii=__app2(_if,_id,_ih),_ij=E(_ib),_ik=E(_i7),_il=__app3(_ik,_id,_ie,_ij),_im=__app3(_ik,_id,_ih,_ij),_in=B(A2(_ia,_id,_)),_io=String(_ig),_ip=__app3(_ik,_id,_ie,_io),_iq=String(_ii),_ir=__app3(_ik,_id,_ih,_iq);return new F(function(){return _gL(_);});};},_is="font",_it=function(_iu,_iv){var _iw=new T(function(){return toJSStr(E(_iu));});return function(_ix,_){var _iy=E(_ix),_iz=E(_is),_iA=__app2(E(_i6),_iy,_iz),_iB=E(_i7),_iC=__app3(_iB,_iy,_iz,E(_iw)),_iD=B(A2(_iv,_iy,_)),_iE=String(_iA),_iF=__app3(_iB,_iy,_iz,_iE);return new F(function(){return _gL(_);});};},_iG=new T(function(){return B(unCStr("px IPAGothic"));}),_iH=function(_iI,_iJ,_iK,_iL,_iM,_iN,_iO,_){var _iP=new T(function(){var _iQ=new T(function(){var _iR=B(_hw(_gJ,_bY,_bY,_iK,_iL,_iM,_iN,_iO)),_iS=E(_iR.a),_iT=E(_iR.b);return new T5(0,_iS.a,_iS.b,_iT.a,_iT.b,_iR.c);}),_iU=new T(function(){var _iV=E(_iQ);return E(_iV.a)+E(_iV.c);}),_iW=new T(function(){var _iX=E(_iQ);return E(_iX.b)-E(_iX.d);}),_iY=new T(function(){return E(E(_iQ).e);}),_iZ=new T(function(){return B(_hL(_hS,_hS,new T2(1,_iO,_S)));}),_j0=function(_j1,_){return new F(function(){return _gP(_iY,_iZ,E(_j1),_);});};return B(_it(new T(function(){return B(_q(B(_A(0,E(_iK),_S)),_iG));},1),function(_j2,_){return new F(function(){return _gY(_iU,_iW,_j0,E(_j2),_);});}));});return new F(function(){return A(_i8,[_iJ,_iP,_iI,_]);});},_j3=new T3(0,153,255,255),_j4=new T2(1,_j3,_S),_j5=new T3(0,255,153,204),_j6=new T2(1,_j5,_j4),_j7=new T3(0,255,204,153),_j8=new T2(1,_j7,_j6),_j9=new T3(0,200,255,200),_ja=new T2(1,_j9,_j8),_jb=20,_jc=64,_jd=1,_je=2,_jf=8,_jg=function(_jh,_ji,_jj,_jk,_jl,_jm,_jn,_){while(1){var _jo=B((function(_jp,_jq,_jr,_js,_jt,_ju,_jv,_){var _jw=E(_jv);if(!_jw._){return _gK;}else{var _jx=_jw.b,_jy=E(_jw.a),_jz=E(_jy);switch(_jz){case 10:var _jA=_jp,_jB=_jq,_jC=_js,_jD=_js;_jh=_jA;_ji=_jB;_jj=0;_jk=_jC;_jl=new T(function(){return E(_jt)-1|0;});_jm=_jD;_jn=_jx;return __continue;case 123:return new F(function(){return _jE(_jp,_jq,_jr,_js,_jt,_ju,_jx,_);});break;case 65306:var _jF=new T(function(){return B(_6X(_ja,_jr));}),_jG=function(_jH,_jI,_jJ,_jK,_jL,_jM,_){while(1){var _jN=B((function(_jO,_jP,_jQ,_jR,_jS,_jT,_){var _jU=E(_jT);if(!_jU._){return _gK;}else{var _jV=_jU.b,_jW=E(_jU.a);if(E(_jW)==65306){var _jX=new T(function(){var _jY=E(_jS);if((_jY+1)*20<=E(_jq)-10){return new T2(0,_jR,_jY+1|0);}else{return new T2(0,new T(function(){return E(_jR)-1|0;}),_jP);}});return new F(function(){return _jg(_jO,_jq,_jr,_jP,new T(function(){return E(E(_jX).a);}),new T(function(){return E(E(_jX).b);}),_jV,_);});}else{var _jZ=E(_jO),_k0=B(_iH(_jZ.a,_jF,_jf,_jQ,_jR,_jS,_jW,_)),_k1=_jP,_k2=_jQ+1,_k3=_jR,_k4=_jS;_jH=_jZ;_jI=_k1;_jJ=_k2;_jK=_k3;_jL=_k4;_jM=_jV;return __continue;}}})(_jH,_jI,_jJ,_jK,_jL,_jM,_));if(_jN!=__continue){return _jN;}}};return new F(function(){return _jG(_jp,_js,0,new T(function(){if(E(_js)!=E(_ju)){return E(_jt);}else{return E(_jt)+1|0;}}),new T(function(){var _k5=E(_ju);if(E(_js)!=_k5){return _k5-1|0;}else{var _k6=(E(_jq)-10)/20,_k7=_k6&4294967295;if(_k6>=_k7){return _k7;}else{return _k7-1|0;}}}),_jx,_);});break;default:var _k8=function(_k9,_ka){var _kb=new T(function(){switch(E(_jz)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return _jr;}}),_kc=new T(function(){var _kd=E(_ju);if((_kd+1)*20<=E(_jq)-10){return new T2(0,_jt,_kd+1|0);}else{return new T2(0,new T(function(){return E(_jt)-1|0;}),_js);}});if(E(_k9)==64){return new F(function(){return _ke(_jp,_jq,_kb,_js,new T(function(){return E(E(_kc).a);}),new T(function(){return E(E(_kc).b);}),_jx,_);});}else{var _kf=E(_jp),_kg=B(_iH(_kf.a,new T(function(){return B(_6X(_ja,E(_kb)));},1),_jb,_hS,_jt,_ju,_ka,_));return new F(function(){return _ke(_kf,_jq,_kb,_js,new T(function(){return E(E(_kc).a);}),new T(function(){return E(E(_kc).b);}),_jx,_);});}},_kh=E(_jz);switch(_kh){case 42:return new F(function(){return _k8(64,_jc);});break;case 12289:return new F(function(){return _k8(64,_jc);});break;case 12290:return new F(function(){return _k8(64,_jc);});break;default:return new F(function(){return _k8(_kh,_jy);});}}}})(_jh,_ji,_jj,_jk,_jl,_jm,_jn,_));if(_jo!=__continue){return _jo;}}},_ke=function(_ki,_kj,_kk,_kl,_km,_kn,_ko,_){var _kp=E(_ko);if(!_kp._){return _gK;}else{var _kq=_kp.b,_kr=E(_kp.a),_ks=E(_kr);switch(_ks){case 10:return new F(function(){return _jg(_ki,_kj,0,_kl,new T(function(){return E(_km)-1|0;}),_kl,_kq,_);});break;case 123:return new F(function(){return _jE(_ki,_kj,_kk,_kl,_km,_kn,_kq,_);});break;case 65306:var _kt=new T(function(){return B(_6X(_ja,E(_kk)));}),_ku=function(_kv,_kw,_kx,_ky,_kz,_kA,_){while(1){var _kB=B((function(_kC,_kD,_kE,_kF,_kG,_kH,_){var _kI=E(_kH);if(!_kI._){return _gK;}else{var _kJ=_kI.b,_kK=E(_kI.a);if(E(_kK)==65306){var _kL=new T(function(){var _kM=E(_kG);if((_kM+1)*20<=E(_kj)-10){return new T2(0,_kF,_kM+1|0);}else{return new T2(0,new T(function(){return E(_kF)-1|0;}),_kD);}});return new F(function(){return _ke(_kC,_kj,_kk,_kD,new T(function(){return E(E(_kL).a);}),new T(function(){return E(E(_kL).b);}),_kJ,_);});}else{var _kN=E(_kC),_kO=B(_iH(_kN.a,_kt,_jf,_kE,_kF,_kG,_kK,_)),_kP=_kD,_kQ=_kE+1,_kR=_kF,_kS=_kG;_kv=_kN;_kw=_kP;_kx=_kQ;_ky=_kR;_kz=_kS;_kA=_kJ;return __continue;}}})(_kv,_kw,_kx,_ky,_kz,_kA,_));if(_kB!=__continue){return _kB;}}};return new F(function(){return _ku(_ki,_kl,0,new T(function(){if(E(_kl)!=E(_kn)){return E(_km);}else{return E(_km)+1|0;}}),new T(function(){var _kT=E(_kn);if(E(_kl)!=_kT){return _kT-1|0;}else{var _kU=(E(_kj)-10)/20,_kV=_kU&4294967295;if(_kU>=_kV){return _kV;}else{return _kV-1|0;}}}),_kq,_);});break;default:var _kW=function(_kX,_kY){var _kZ=new T(function(){switch(E(_ks)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return E(_kk);}}),_l0=new T(function(){var _l1=E(_kn);if((_l1+1)*20<=E(_kj)-10){return new T2(0,_km,_l1+1|0);}else{return new T2(0,new T(function(){return E(_km)-1|0;}),_kl);}});if(E(_kX)==64){return new F(function(){return _ke(_ki,_kj,_kZ,_kl,new T(function(){return E(E(_l0).a);}),new T(function(){return E(E(_l0).b);}),_kq,_);});}else{var _l2=E(_ki),_l3=B(_iH(_l2.a,new T(function(){return B(_6X(_ja,E(_kZ)));},1),_jb,_hS,_km,_kn,_kY,_));return new F(function(){return _ke(_l2,_kj,_kZ,_kl,new T(function(){return E(E(_l0).a);}),new T(function(){return E(E(_l0).b);}),_kq,_);});}},_l4=E(_ks);switch(_l4){case 42:return new F(function(){return _kW(64,_jc);});break;case 12289:return new F(function(){return _kW(64,_jc);});break;case 12290:return new F(function(){return _kW(64,_jc);});break;default:return new F(function(){return _kW(_l4,_kr);});}}}},_jE=function(_l5,_l6,_l7,_l8,_l9,_la,_lb,_){while(1){var _lc=B((function(_ld,_le,_lf,_lg,_lh,_li,_lj,_){var _lk=E(_lj);if(!_lk._){return _gK;}else{var _ll=_lk.b;if(E(_lk.a)==125){var _lm=new T(function(){var _ln=E(_li);if((_ln+1)*20<=E(_le)-10){return new T2(0,_lh,_ln+1|0);}else{return new T2(0,new T(function(){return E(_lh)-1|0;}),_lg);}});return new F(function(){return _ke(_ld,_le,_lf,_lg,new T(function(){return E(E(_lm).a);}),new T(function(){return E(E(_lm).b);}),_ll,_);});}else{var _lo=_ld,_lp=_le,_lq=_lf,_lr=_lg,_ls=_lh,_lt=_li;_l5=_lo;_l6=_lp;_l7=_lq;_l8=_lr;_l9=_ls;_la=_lt;_lb=_ll;return __continue;}}})(_l5,_l6,_l7,_l8,_l9,_la,_lb,_));if(_lc!=__continue){return _lc;}}},_lu=function(_lv,_lw,_lx,_ly,_lz,_lA,_lB,_lC,_){while(1){var _lD=B((function(_lE,_lF,_lG,_lH,_lI,_lJ,_lK,_lL,_){var _lM=E(_lL);if(!_lM._){return _gK;}else{var _lN=_lM.b,_lO=E(_lM.a),_lP=E(_lO);switch(_lP){case 10:var _lQ=_lE,_lR=_lF,_lS=_lG,_lT=_lI,_lU=_lI;_lv=_lQ;_lw=_lR;_lx=_lS;_ly=0;_lz=_lT;_lA=new T(function(){return E(_lJ)-1|0;});_lB=_lU;_lC=_lN;return __continue;case 123:return new F(function(){return _jE(new T2(0,_lE,_lF),_lG,_lH,_lI,_lJ,_lK,_lN,_);});break;case 65306:var _lV=new T(function(){return B(_6X(_ja,_lH));}),_lW=function(_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_){while(1){var _m4=B((function(_m5,_m6,_m7,_m8,_m9,_ma,_mb,_){var _mc=E(_mb);if(!_mc._){return _gK;}else{var _md=_mc.b,_me=E(_mc.a);if(E(_me)==65306){var _mf=new T(function(){var _mg=E(_ma);if((_mg+1)*20<=E(_lG)-10){return new T2(0,_m9,_mg+1|0);}else{return new T2(0,new T(function(){return E(_m9)-1|0;}),_m7);}});return new F(function(){return _lu(_m5,_m6,_lG,_lH,_m7,new T(function(){return E(E(_mf).a);}),new T(function(){return E(E(_mf).b);}),_md,_);});}else{var _mh=B(_iH(_m5,_lV,_jf,_m8,_m9,_ma,_me,_)),_mi=_m5,_mj=_m6,_mk=_m7,_ml=_m8+1,_mm=_m9,_mn=_ma;_lX=_mi;_lY=_mj;_lZ=_mk;_m0=_ml;_m1=_mm;_m2=_mn;_m3=_md;return __continue;}}})(_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_));if(_m4!=__continue){return _m4;}}};return new F(function(){return _lW(_lE,_lF,_lI,0,new T(function(){if(E(_lI)!=E(_lK)){return E(_lJ);}else{return E(_lJ)+1|0;}}),new T(function(){var _mo=E(_lK);if(E(_lI)!=_mo){return _mo-1|0;}else{var _mp=(E(_lG)-10)/20,_mq=_mp&4294967295;if(_mp>=_mq){return _mq;}else{return _mq-1|0;}}}),_lN,_);});break;default:var _mr=function(_ms,_mt){var _mu=new T(function(){switch(E(_lP)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return _lH;}}),_mv=new T(function(){var _mw=E(_lK);if((_mw+1)*20<=E(_lG)-10){return new T2(0,_lJ,_mw+1|0);}else{return new T2(0,new T(function(){return E(_lJ)-1|0;}),_lI);}});if(E(_ms)==64){return new F(function(){return _ke(new T2(0,_lE,_lF),_lG,_mu,_lI,new T(function(){return E(E(_mv).a);}),new T(function(){return E(E(_mv).b);}),_lN,_);});}else{var _mx=B(_iH(_lE,new T(function(){return B(_6X(_ja,E(_mu)));},1),_jb,_hS,_lJ,_lK,_mt,_));return new F(function(){return _ke(new T2(0,_lE,_lF),_lG,_mu,_lI,new T(function(){return E(E(_mv).a);}),new T(function(){return E(E(_mv).b);}),_lN,_);});}},_my=E(_lP);switch(_my){case 42:return new F(function(){return _mr(64,_jc);});break;case 12289:return new F(function(){return _mr(64,_jc);});break;case 12290:return new F(function(){return _mr(64,_jc);});break;default:return new F(function(){return _mr(_my,_lO);});}}}})(_lv,_lw,_lx,_ly,_lz,_lA,_lB,_lC,_));if(_lD!=__continue){return _lD;}}},_mz=function(_mA,_mB){while(1){var _mC=E(_mA);if(!_mC._){return E(_mB);}else{var _mD=_mB+1|0;_mA=_mC.b;_mB=_mD;continue;}}},_mE=function(_mF){return E(E(_mF).a);},_mG=function(_mH,_mI){var _mJ=E(_mI),_mK=new T(function(){var _mL=B(_hg(_mH)),_mM=B(_mG(_mH,B(A3(_mE,_mL,_mJ,new T(function(){return B(A2(_hk,_mL,_b1));})))));return new T2(1,_mM.a,_mM.b);});return new T2(0,_mJ,_mK);},_mN=new T(function(){var _mO=B(_mG(_gh,_hS));return new T2(1,_mO.a,_mO.b);}),_mP=new T(function(){return B(unCStr("px Courier"));}),_mQ=new T(function(){return B(_A(0,20,_S));}),_mR=new T(function(){return B(_q(_mQ,_mP));}),_mS=function(_mT,_){return _gK;},_mU=function(_mV,_mW,_mX,_mY,_mZ){var _n0=new T(function(){return E(_mX)*16;}),_n1=new T(function(){return E(_mY)*20;}),_n2=function(_n3,_n4){var _n5=E(_n3);if(!_n5._){return E(_mS);}else{var _n6=E(_n4);if(!_n6._){return E(_mS);}else{var _n7=new T(function(){return B(_n2(_n5.b,_n6.b));}),_n8=new T(function(){var _n9=new T(function(){var _na=new T(function(){return B(_hL(new T(function(){return E(_n0)+16*E(_n6.a);}),_n1,new T2(1,_n5.a,_S)));});return B(_it(_mR,_na));});return B(_i8(_mW,_n9));});return function(_nb,_){var _nc=B(A2(_n8,_nb,_));return new F(function(){return A2(_n7,_nb,_);});};}}};return new F(function(){return A3(_n2,_mZ,_mN,_mV);});},_nd=45,_ne=new T(function(){return B(unCStr("-"));}),_nf=new T2(1,_nd,_ne),_ng=function(_nh){var _ni=E(_nh);return (_ni==1)?E(_nf):new T2(1,_nd,new T(function(){return B(_ng(_ni-1|0));}));},_nj=new T(function(){return B(unCStr(": empty list"));}),_nk=function(_nl){return new F(function(){return err(B(_q(_6M,new T(function(){return B(_q(_nl,_nj));},1))));});},_nm=new T(function(){return B(unCStr("head"));}),_nn=new T(function(){return B(_nk(_nm));}),_no=new T(function(){return eval("(function(e){e.width = e.width;})");}),_np=new T(function(){return B(_hL(_hS,_hS,_S));}),_nq=32,_nr=new T(function(){return B(unCStr("|"));}),_ns=function(_nt){var _nu=E(_nt);return (_nu._==0)?E(_nr):new T2(1,new T(function(){var _nv=E(_nu.a);switch(E(_nv.b)){case 7:return E(_nq);break;case 8:return E(_nq);break;default:return E(_nv.a);}}),new T(function(){return B(_ns(_nu.b));}));},_nw=function(_nx,_ny,_nz,_nA,_nB,_){var _nC=__app1(E(_no),_ny),_nD=B(A2(_np,_nx,_)),_nE=B(unAppCStr("-",new T(function(){var _nF=E(_nB);if(!_nF._){return E(_nn);}else{var _nG=B(_mz(_nF.a,0));if(0>=_nG){return E(_ne);}else{return B(_ng(_nG));}}}))),_nH=B(A(_mU,[_nx,_j9,_nz,_nA,_nE,_])),_nI=function(_nJ,_nK,_nL,_){while(1){var _nM=B((function(_nN,_nO,_nP,_){var _nQ=E(_nP);if(!_nQ._){return new F(function(){return A(_mU,[_nx,_j9,_nN,_nO,_nE,_]);});}else{var _nR=B(A(_mU,[_nx,_j9,_nN,_nO,B(unAppCStr("|",new T(function(){return B(_ns(_nQ.a));}))),_])),_nS=_nN;_nJ=_nS;_nK=new T(function(){return E(_nO)+1|0;});_nL=_nQ.b;return __continue;}})(_nJ,_nK,_nL,_));if(_nM!=__continue){return _nM;}}};return new F(function(){return _nI(_nz,new T(function(){return E(_nA)+1|0;}),_nB,_);});},_nT=new T(function(){return B(_6X(_ja,1));}),_nU=new T(function(){return B(_6X(_ja,2));}),_nV=2,_nW=function(_nX,_nY,_nZ,_o0,_){var _o1=__app1(E(_no),_nY),_o2=B(A2(_np,_nX,_)),_o3=E(_o0),_o4=E(_o3.b).a,_o5=E(_o3.a),_o6=_o5.a;if(!E(E(_o3.t).h)){return _gK;}else{var _o7=B(_nw(_nX,_nY,new T(function(){return E(_nZ)-E(_o4)|0;}),_nV,_o5.b,_));return new F(function(){return A(_mU,[_nX,new T(function(){if(E(_o5.e)==32){return E(_nT);}else{return E(_nU);}}),new T(function(){return ((E(E(_o6).a)+1|0)+E(_nZ)|0)-E(_o4)|0;},1),new T(function(){return (E(E(_o6).b)+2|0)+1|0;},1),new T2(1,_o5.d,_S),_]);});}},_o8=function(_o9){return E(E(_o9).a);},_oa=function(_ob){return E(E(_ob).a);},_oc=function(_od,_oe){while(1){var _of=E(_od);if(!_of._){return E(_oe);}else{_od=_of.b;_oe=_of.a;continue;}}},_og=function(_oh,_oi,_oj){return new F(function(){return _oc(_oi,_oh);});},_ok=new T1(0,2),_ol=function(_om,_on){while(1){var _oo=E(_om);if(!_oo._){var _op=_oo.a,_oq=E(_on);if(!_oq._){var _or=_oq.a;if(!(imul(_op,_or)|0)){return new T1(0,imul(_op,_or)|0);}else{_om=new T1(1,I_fromInt(_op));_on=new T1(1,I_fromInt(_or));continue;}}else{_om=new T1(1,I_fromInt(_op));_on=_oq;continue;}}else{var _os=E(_on);if(!_os._){_om=_oo;_on=new T1(1,I_fromInt(_os.a));continue;}else{return new T1(1,I_mul(_oo.a,_os.a));}}}},_ot=function(_ou,_ov,_ow){while(1){if(!(_ov%2)){var _ox=B(_ol(_ou,_ou)),_oy=quot(_ov,2);_ou=_ox;_ov=_oy;continue;}else{var _oz=E(_ov);if(_oz==1){return new F(function(){return _ol(_ou,_ow);});}else{var _ox=B(_ol(_ou,_ou)),_oA=B(_ol(_ou,_ow));_ou=_ox;_ov=quot(_oz-1|0,2);_ow=_oA;continue;}}}},_oB=function(_oC,_oD){while(1){if(!(_oD%2)){var _oE=B(_ol(_oC,_oC)),_oF=quot(_oD,2);_oC=_oE;_oD=_oF;continue;}else{var _oG=E(_oD);if(_oG==1){return E(_oC);}else{return new F(function(){return _ot(B(_ol(_oC,_oC)),quot(_oG-1|0,2),_oC);});}}}},_oH=function(_oI){return E(E(_oI).c);},_oJ=function(_oK){return E(E(_oK).a);},_oL=function(_oM){return E(E(_oM).b);},_oN=function(_oO){return E(E(_oO).b);},_oP=function(_oQ){return E(E(_oQ).c);},_oR=new T1(0,0),_oS=new T1(0,2),_oT=function(_oU){return E(E(_oU).d);},_oV=function(_oW,_oX){var _oY=B(_o8(_oW)),_oZ=new T(function(){return B(_oa(_oY));}),_p0=new T(function(){return B(A3(_oT,_oW,_oX,new T(function(){return B(A2(_hk,_oZ,_oS));})));});return new F(function(){return A3(_4y,B(_oJ(B(_oL(_oY)))),_p0,new T(function(){return B(A2(_hk,_oZ,_oR));}));});},_p1=new T(function(){return B(unCStr("Negative exponent"));}),_p2=new T(function(){return B(err(_p1));}),_p3=function(_p4){return E(E(_p4).c);},_p5=function(_p6,_p7,_p8,_p9){var _pa=B(_o8(_p7)),_pb=new T(function(){return B(_oa(_pa));}),_pc=B(_oL(_pa));if(!B(A3(_oP,_pc,_p9,new T(function(){return B(A2(_hk,_pb,_oR));})))){if(!B(A3(_4y,B(_oJ(_pc)),_p9,new T(function(){return B(A2(_hk,_pb,_oR));})))){var _pd=new T(function(){return B(A2(_hk,_pb,_oS));}),_pe=new T(function(){return B(A2(_hk,_pb,_b1));}),_pf=B(_oJ(_pc)),_pg=function(_ph,_pi,_pj){while(1){var _pk=B((function(_pl,_pm,_pn){if(!B(_oV(_p7,_pm))){if(!B(A3(_4y,_pf,_pm,_pe))){var _po=new T(function(){return B(A3(_p3,_p7,new T(function(){return B(A3(_oN,_pb,_pm,_pe));}),_pd));});_ph=new T(function(){return B(A3(_oH,_p6,_pl,_pl));});_pi=_po;_pj=new T(function(){return B(A3(_oH,_p6,_pl,_pn));});return __continue;}else{return new F(function(){return A3(_oH,_p6,_pl,_pn);});}}else{var _pp=_pn;_ph=new T(function(){return B(A3(_oH,_p6,_pl,_pl));});_pi=new T(function(){return B(A3(_p3,_p7,_pm,_pd));});_pj=_pp;return __continue;}})(_ph,_pi,_pj));if(_pk!=__continue){return _pk;}}},_pq=function(_pr,_ps){while(1){var _pt=B((function(_pu,_pv){if(!B(_oV(_p7,_pv))){if(!B(A3(_4y,_pf,_pv,_pe))){var _pw=new T(function(){return B(A3(_p3,_p7,new T(function(){return B(A3(_oN,_pb,_pv,_pe));}),_pd));});return new F(function(){return _pg(new T(function(){return B(A3(_oH,_p6,_pu,_pu));}),_pw,_pu);});}else{return E(_pu);}}else{_pr=new T(function(){return B(A3(_oH,_p6,_pu,_pu));});_ps=new T(function(){return B(A3(_p3,_p7,_pv,_pd));});return __continue;}})(_pr,_ps));if(_pt!=__continue){return _pt;}}};return new F(function(){return _pq(_p8,_p9);});}else{return new F(function(){return A2(_hk,_p6,_b1);});}}else{return E(_p2);}},_px=new T(function(){return B(err(_p1));}),_py=function(_pz){var _pA=I_decodeDouble(_pz);return new T2(0,new T1(1,_pA.b),_pA.a);},_pB=function(_pC,_pD){var _pE=B(_py(_pD)),_pF=_pE.a,_pG=_pE.b,_pH=new T(function(){return B(_oa(new T(function(){return B(_o8(_pC));})));});if(_pG<0){var _pI= -_pG;if(_pI>=0){var _pJ=E(_pI);if(!_pJ){var _pK=E(_b1);}else{var _pK=B(_oB(_ok,_pJ));}if(!B(_ct(_pK,_cT))){var _pL=B(_cK(_pF,_pK));return new T2(0,new T(function(){return B(A2(_hk,_pH,_pL.a));}),new T(function(){return B(_cp(_pL.b,_pG));}));}else{return E(_a0);}}else{return E(_px);}}else{var _pM=new T(function(){var _pN=new T(function(){return B(_p5(_pH,_bY,new T(function(){return B(A2(_hk,_pH,_ok));}),_pG));});return B(A3(_oH,_pH,new T(function(){return B(A2(_hk,_pH,_pF));}),_pN));});return new T2(0,_pM,_fG);}},_pO=function(_pP,_pQ){while(1){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.b,_pT=E(_pP);if(_pT==1){return E(_pS);}else{_pP=_pT-1|0;_pQ=_pS;continue;}}}},_pU=function(_pV,_pW){var _pX=E(_pW);if(!_pX._){return __Z;}else{var _pY=_pX.a,_pZ=E(_pV);return (_pZ==1)?new T2(1,_pY,_S):new T2(1,_pY,new T(function(){return B(_pU(_pZ-1|0,_pX.b));}));}},_q0=function(_q1,_q2,_q3,_q4){while(1){if(B(_6X(new T2(1,_q3,_q4),_q2))!=_q1){var _q5=_q2+1|0;_q2=_q5;continue;}else{if(0>=_q2){return __Z;}else{return new F(function(){return _pU(_q2,new T2(1,_q3,_q4));});}}}},_q6=function(_q7,_q8,_q9){var _qa=E(_q9);if(!_qa._){return __Z;}else{var _qb=E(_q7);if(B(_6X(_qa,_q8))!=_qb){return new F(function(){return _q0(_qb,_q8+1|0,_qa.a,_qa.b);});}else{if(0>=_q8){return __Z;}else{return new F(function(){return _pU(_q8,_qa);});}}}},_qc=function(_qd,_qe,_qf){var _qg=_qe+1|0;if(_qg>0){return new F(function(){return _pO(_qg,B(_q6(_qd,_qg,_qf)));});}else{return new F(function(){return _q6(_qd,_qg,_qf);});}},_qh=function(_qi,_qj){return (!B(_6f(_qi,_qj)))?true:false;},_qk=new T2(0,_6f,_qh),_ql=new T(function(){return B(_ed("Event.hs:(65,1)-(66,68)|function addEvent"));}),_qm=0,_qn=function(_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF,_qG,_qH,_qI,_qJ){while(1){var _qK=E(_qo);if(!_qK._){return {_:0,a:_qp,b:_qq,c:_qr,d:_qs,e:_qt,f:_qu,g:_qv,h:_qw,i:_qx,j:_qy,k:_qz,l:_qA,m:_qB,n:_qC,o:_qD,p:_qE,q:_qF,r:_qG,s:_qH,t:_qI,u:_qJ};}else{var _qL=E(_qK.b);if(!_qL._){return E(_ql);}else{var _qM=new T2(1,new T2(0,_qK.a,_qL.a),_qt),_qN=new T2(1,_qm,_qu);_qo=_qL.b;_qt=_qM;_qu=_qN;continue;}}}},_qO=function(_qP,_qQ,_qR){var _qS=E(_qR);if(!_qS._){return __Z;}else{var _qT=_qS.a,_qU=_qS.b;return (!B(A2(_qP,_qQ,_qT)))?new T2(1,_qT,new T(function(){return B(_qO(_qP,_qQ,_qU));})):E(_qU);}},_qV=function(_qW,_qX){while(1){var _qY=E(_qW);if(!_qY._){return (E(_qX)._==0)?true:false;}else{var _qZ=E(_qX);if(!_qZ._){return false;}else{if(E(_qY.a)!=E(_qZ.a)){return false;}else{_qW=_qY.b;_qX=_qZ.b;continue;}}}}},_r0=function(_r1,_r2){while(1){var _r3=E(_r1);if(!_r3._){return (E(_r2)._==0)?true:false;}else{var _r4=E(_r2);if(!_r4._){return false;}else{if(!B(_6f(_r3.a,_r4.a))){return false;}else{_r1=_r3.b;_r2=_r4.b;continue;}}}}},_r5=function(_r6,_r7){switch(E(_r6)){case 0:return (E(_r7)==0)?true:false;case 1:return (E(_r7)==1)?true:false;case 2:return (E(_r7)==2)?true:false;case 3:return (E(_r7)==3)?true:false;case 4:return (E(_r7)==4)?true:false;case 5:return (E(_r7)==5)?true:false;case 6:return (E(_r7)==6)?true:false;case 7:return (E(_r7)==7)?true:false;default:return (E(_r7)==8)?true:false;}},_r8=function(_r9,_ra,_rb,_rc){if(_r9!=_rb){return false;}else{return new F(function(){return _r5(_ra,_rc);});}},_rd=function(_re,_rf){var _rg=E(_re),_rh=E(_rf);return new F(function(){return _r8(E(_rg.a),_rg.b,E(_rh.a),_rh.b);});},_ri=function(_rj,_rk,_rl,_rm){if(_rj!=_rl){return true;}else{switch(E(_rk)){case 0:return (E(_rm)==0)?false:true;case 1:return (E(_rm)==1)?false:true;case 2:return (E(_rm)==2)?false:true;case 3:return (E(_rm)==3)?false:true;case 4:return (E(_rm)==4)?false:true;case 5:return (E(_rm)==5)?false:true;case 6:return (E(_rm)==6)?false:true;case 7:return (E(_rm)==7)?false:true;default:return (E(_rm)==8)?false:true;}}},_rn=function(_ro,_rp){var _rq=E(_ro),_rr=E(_rp);return new F(function(){return _ri(E(_rq.a),_rq.b,E(_rr.a),_rr.b);});},_rs=new T2(0,_rd,_rn),_rt=0,_ru=function(_rv,_rw){var _rx=E(_rw);if(!_rx._){return 0;}else{var _ry=_rx.b,_rz=E(_rv),_rA=E(_rx.a),_rB=_rA.b;if(E(_rz.a)!=E(_rA.a)){return 1+B(_ru(_rz,_ry))|0;}else{switch(E(_rz.b)){case 0:return (E(_rB)==0)?0:1+B(_ru(_rz,_ry))|0;case 1:return (E(_rB)==1)?0:1+B(_ru(_rz,_ry))|0;case 2:return (E(_rB)==2)?0:1+B(_ru(_rz,_ry))|0;case 3:return (E(_rB)==3)?0:1+B(_ru(_rz,_ry))|0;case 4:return (E(_rB)==4)?0:1+B(_ru(_rz,_ry))|0;case 5:return (E(_rB)==5)?0:1+B(_ru(_rz,_ry))|0;case 6:return (E(_rB)==6)?0:1+B(_ru(_rz,_ry))|0;case 7:return (E(_rB)==7)?0:1+B(_ru(_rz,_ry))|0;default:return (E(_rB)==8)?0:1+B(_ru(_rz,_ry))|0;}}}},_rC=function(_rD,_rE){return new F(function(){return _ru(_rD,_rE);});},_rF=function(_rG,_rH){var _rI=E(_rH);if(!_rI._){return new T2(0,_rt,_rt);}else{var _rJ=_rI.a,_rK=_rI.b;return (!B(_4A(_rs,_rG,_rJ)))?new T2(0,new T(function(){return E(B(_rF(_rG,_rK)).a);}),new T(function(){return 1+E(B(_rF(_rG,_rK)).b)|0;})):new T2(0,new T(function(){return B(_rC(_rG,_rJ));}),_rt);}},_rL=function(_rM,_rN){while(1){var _rO=E(_rN);if(!_rO._){return __Z;}else{var _rP=_rO.b,_rQ=E(_rM);if(_rQ==1){return E(_rP);}else{_rM=_rQ-1|0;_rN=_rP;continue;}}}},_rR=new T(function(){return B(unCStr("getch"));}),_rS=new T(function(){return B(unCStr("=="));}),_rT=new T(function(){return B(unCStr("&&"));}),_rU=new T(function(){return B(unCStr("||"));}),_rV=new T(function(){return B(unCStr("getpos"));}),_rW=new T(function(){return B(unCStr("ch"));}),_rX=new T(function(){return B(unCStr("tp"));}),_rY=new T2(1,_rX,_S),_rZ=new T2(1,_rW,_rY),_s0=new T2(0,_rV,_rZ),_s1=new T(function(){return B(unCStr("a"));}),_s2=new T(function(){return B(unCStr("b"));}),_s3=new T2(1,_s2,_S),_s4=new T2(1,_s1,_s3),_s5=new T2(0,_rS,_s4),_s6=new T2(0,_rT,_s4),_s7=new T2(0,_rU,_s4),_s8=new T2(1,_s7,_S),_s9=new T2(1,_s6,_s8),_sa=new T2(1,_s5,_s9),_sb=new T2(1,_s0,_sa),_sc=new T(function(){return B(unCStr("p"));}),_sd=new T(function(){return B(unCStr("q"));}),_se=new T2(1,_sd,_S),_sf=new T2(1,_sc,_se),_sg=new T2(0,_rR,_sf),_sh=new T2(1,_sg,_sb),_si=new T(function(){return B(unCStr("foldr1"));}),_sj=new T(function(){return B(_nk(_si));}),_sk=function(_sl,_sm){var _sn=E(_sm);if(!_sn._){return E(_sj);}else{var _so=_sn.a,_sp=E(_sn.b);if(!_sp._){return E(_so);}else{return new F(function(){return A2(_sl,_so,new T(function(){return B(_sk(_sl,_sp));}));});}}},_sq=function(_sr){return E(E(_sr).a);},_ss=function(_st,_su,_sv){while(1){var _sw=E(_sv);if(!_sw._){return __Z;}else{var _sx=E(_sw.a);if(!B(A3(_4y,_st,_su,_sx.a))){_sv=_sw.b;continue;}else{return new T1(1,_sx.b);}}}},_sy=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sz=new T(function(){return B(err(_sy));}),_sA=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_sB=new T(function(){return B(err(_sA));}),_sC=new T(function(){return B(unCStr("T"));}),_sD=new T(function(){return B(unCStr("F"));}),_sE=new T(function(){return B(_ed("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sF=function(_sG,_sH){while(1){var _sI=B((function(_sJ,_sK){var _sL=E(_sJ);switch(_sL._){case 0:var _sM=E(_sK);if(!_sM._){return __Z;}else{_sG=B(A1(_sL.a,_sM.a));_sH=_sM.b;return __continue;}break;case 1:var _sN=B(A1(_sL.a,_sK)),_sO=_sK;_sG=_sN;_sH=_sO;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sL.a,_sK),new T(function(){return B(_sF(_sL.b,_sK));}));default:return E(_sL.a);}})(_sG,_sH));if(_sI!=__continue){return _sI;}}},_sP=function(_sQ,_sR){var _sS=function(_sT){var _sU=E(_sR);if(_sU._==3){return new T2(3,_sU.a,new T(function(){return B(_sP(_sQ,_sU.b));}));}else{var _sV=E(_sQ);if(_sV._==2){return E(_sU);}else{var _sW=E(_sU);if(_sW._==2){return E(_sV);}else{var _sX=function(_sY){var _sZ=E(_sW);if(_sZ._==4){var _t0=function(_t1){return new T1(4,new T(function(){return B(_q(B(_sF(_sV,_t1)),_sZ.a));}));};return new T1(1,_t0);}else{var _t2=E(_sV);if(_t2._==1){var _t3=_t2.a,_t4=E(_sZ);if(!_t4._){return new T1(1,function(_t5){return new F(function(){return _sP(B(A1(_t3,_t5)),_t4);});});}else{var _t6=function(_t7){return new F(function(){return _sP(B(A1(_t3,_t7)),new T(function(){return B(A1(_t4.a,_t7));}));});};return new T1(1,_t6);}}else{var _t8=E(_sZ);if(!_t8._){return E(_sE);}else{var _t9=function(_ta){return new F(function(){return _sP(_t2,new T(function(){return B(A1(_t8.a,_ta));}));});};return new T1(1,_t9);}}}},_tb=E(_sV);switch(_tb._){case 1:var _tc=E(_sW);if(_tc._==4){var _td=function(_te){return new T1(4,new T(function(){return B(_q(B(_sF(B(A1(_tb.a,_te)),_te)),_tc.a));}));};return new T1(1,_td);}else{return new F(function(){return _sX(_);});}break;case 4:var _tf=_tb.a,_tg=E(_sW);switch(_tg._){case 0:var _th=function(_ti){var _tj=new T(function(){return B(_q(_tf,new T(function(){return B(_sF(_tg,_ti));},1)));});return new T1(4,_tj);};return new T1(1,_th);case 1:var _tk=function(_tl){var _tm=new T(function(){return B(_q(_tf,new T(function(){return B(_sF(B(A1(_tg.a,_tl)),_tl));},1)));});return new T1(4,_tm);};return new T1(1,_tk);default:return new T1(4,new T(function(){return B(_q(_tf,_tg.a));}));}break;default:return new F(function(){return _sX(_);});}}}}},_tn=E(_sQ);switch(_tn._){case 0:var _to=E(_sR);if(!_to._){var _tp=function(_tq){return new F(function(){return _sP(B(A1(_tn.a,_tq)),new T(function(){return B(A1(_to.a,_tq));}));});};return new T1(0,_tp);}else{return new F(function(){return _sS(_);});}break;case 3:return new T2(3,_tn.a,new T(function(){return B(_sP(_tn.b,_sR));}));default:return new F(function(){return _sS(_);});}},_tr=new T(function(){return B(unCStr("("));}),_ts=new T(function(){return B(unCStr(")"));}),_tt=function(_tu,_tv){var _tw=E(_tu);switch(_tw._){case 0:return new T1(0,function(_tx){return new F(function(){return _tt(B(A1(_tw.a,_tx)),_tv);});});case 1:return new T1(1,function(_ty){return new F(function(){return _tt(B(A1(_tw.a,_ty)),_tv);});});case 2:return new T0(2);case 3:return new F(function(){return _sP(B(A1(_tv,_tw.a)),new T(function(){return B(_tt(_tw.b,_tv));}));});break;default:var _tz=function(_tA){var _tB=E(_tA);if(!_tB._){return __Z;}else{var _tC=E(_tB.a);return new F(function(){return _q(B(_sF(B(A1(_tv,_tC.a)),_tC.b)),new T(function(){return B(_tz(_tB.b));},1));});}},_tD=B(_tz(_tw.a));return (_tD._==0)?new T0(2):new T1(4,_tD);}},_tE=new T0(2),_tF=function(_tG){return new T2(3,_tG,_tE);},_tH=function(_tI,_tJ){var _tK=E(_tI);if(!_tK){return new F(function(){return A1(_tJ,_gK);});}else{var _tL=new T(function(){return B(_tH(_tK-1|0,_tJ));});return new T1(0,function(_tM){return E(_tL);});}},_tN=function(_tO,_tP,_tQ){var _tR=new T(function(){return B(A1(_tO,_tF));}),_tS=function(_tT,_tU,_tV,_tW){while(1){var _tX=B((function(_tY,_tZ,_u0,_u1){var _u2=E(_tY);switch(_u2._){case 0:var _u3=E(_tZ);if(!_u3._){return new F(function(){return A1(_tP,_u1);});}else{var _u4=_u0+1|0,_u5=_u1;_tT=B(A1(_u2.a,_u3.a));_tU=_u3.b;_tV=_u4;_tW=_u5;return __continue;}break;case 1:var _u6=B(A1(_u2.a,_tZ)),_u7=_tZ,_u4=_u0,_u5=_u1;_tT=_u6;_tU=_u7;_tV=_u4;_tW=_u5;return __continue;case 2:return new F(function(){return A1(_tP,_u1);});break;case 3:var _u8=new T(function(){return B(_tt(_u2,_u1));});return new F(function(){return _tH(_u0,function(_u9){return E(_u8);});});break;default:return new F(function(){return _tt(_u2,_u1);});}})(_tT,_tU,_tV,_tW));if(_tX!=__continue){return _tX;}}};return function(_ua){return new F(function(){return _tS(_tR,_ua,0,_tQ);});};},_ub=function(_uc){return new F(function(){return A1(_uc,_S);});},_ud=function(_ue,_uf){var _ug=function(_uh){var _ui=E(_uh);if(!_ui._){return E(_ub);}else{var _uj=_ui.a;if(!B(A1(_ue,_uj))){return E(_ub);}else{var _uk=new T(function(){return B(_ug(_ui.b));}),_ul=function(_um){var _un=new T(function(){return B(A1(_uk,function(_uo){return new F(function(){return A1(_um,new T2(1,_uj,_uo));});}));});return new T1(0,function(_up){return E(_un);});};return E(_ul);}}};return function(_uq){return new F(function(){return A2(_ug,_uq,_uf);});};},_ur=new T0(6),_us=new T(function(){return B(unCStr("valDig: Bad base"));}),_ut=new T(function(){return B(err(_us));}),_uu=function(_uv,_uw){var _ux=function(_uy,_uz){var _uA=E(_uy);if(!_uA._){var _uB=new T(function(){return B(A1(_uz,_S));});return function(_uC){return new F(function(){return A1(_uC,_uB);});};}else{var _uD=E(_uA.a),_uE=function(_uF){var _uG=new T(function(){return B(_ux(_uA.b,function(_uH){return new F(function(){return A1(_uz,new T2(1,_uF,_uH));});}));}),_uI=function(_uJ){var _uK=new T(function(){return B(A1(_uG,_uJ));});return new T1(0,function(_uL){return E(_uK);});};return E(_uI);};switch(E(_uv)){case 8:if(48>_uD){var _uM=new T(function(){return B(A1(_uz,_S));});return function(_uN){return new F(function(){return A1(_uN,_uM);});};}else{if(_uD>55){var _uO=new T(function(){return B(A1(_uz,_S));});return function(_uP){return new F(function(){return A1(_uP,_uO);});};}else{return new F(function(){return _uE(_uD-48|0);});}}break;case 10:if(48>_uD){var _uQ=new T(function(){return B(A1(_uz,_S));});return function(_uR){return new F(function(){return A1(_uR,_uQ);});};}else{if(_uD>57){var _uS=new T(function(){return B(A1(_uz,_S));});return function(_uT){return new F(function(){return A1(_uT,_uS);});};}else{return new F(function(){return _uE(_uD-48|0);});}}break;case 16:if(48>_uD){if(97>_uD){if(65>_uD){var _uU=new T(function(){return B(A1(_uz,_S));});return function(_uV){return new F(function(){return A1(_uV,_uU);});};}else{if(_uD>70){var _uW=new T(function(){return B(A1(_uz,_S));});return function(_uX){return new F(function(){return A1(_uX,_uW);});};}else{return new F(function(){return _uE((_uD-65|0)+10|0);});}}}else{if(_uD>102){if(65>_uD){var _uY=new T(function(){return B(A1(_uz,_S));});return function(_uZ){return new F(function(){return A1(_uZ,_uY);});};}else{if(_uD>70){var _v0=new T(function(){return B(A1(_uz,_S));});return function(_v1){return new F(function(){return A1(_v1,_v0);});};}else{return new F(function(){return _uE((_uD-65|0)+10|0);});}}}else{return new F(function(){return _uE((_uD-97|0)+10|0);});}}}else{if(_uD>57){if(97>_uD){if(65>_uD){var _v2=new T(function(){return B(A1(_uz,_S));});return function(_v3){return new F(function(){return A1(_v3,_v2);});};}else{if(_uD>70){var _v4=new T(function(){return B(A1(_uz,_S));});return function(_v5){return new F(function(){return A1(_v5,_v4);});};}else{return new F(function(){return _uE((_uD-65|0)+10|0);});}}}else{if(_uD>102){if(65>_uD){var _v6=new T(function(){return B(A1(_uz,_S));});return function(_v7){return new F(function(){return A1(_v7,_v6);});};}else{if(_uD>70){var _v8=new T(function(){return B(A1(_uz,_S));});return function(_v9){return new F(function(){return A1(_v9,_v8);});};}else{return new F(function(){return _uE((_uD-65|0)+10|0);});}}}else{return new F(function(){return _uE((_uD-97|0)+10|0);});}}}else{return new F(function(){return _uE(_uD-48|0);});}}break;default:return E(_ut);}}},_va=function(_vb){var _vc=E(_vb);if(!_vc._){return new T0(2);}else{return new F(function(){return A1(_uw,_vc);});}};return function(_vd){return new F(function(){return A3(_ux,_vd,_5U,_va);});};},_ve=16,_vf=8,_vg=function(_vh){var _vi=function(_vj){return new F(function(){return A1(_vh,new T1(5,new T2(0,_vf,_vj)));});},_vk=function(_vl){return new F(function(){return A1(_vh,new T1(5,new T2(0,_ve,_vl)));});},_vm=function(_vn){switch(E(_vn)){case 79:return new T1(1,B(_uu(_vf,_vi)));case 88:return new T1(1,B(_uu(_ve,_vk)));case 111:return new T1(1,B(_uu(_vf,_vi)));case 120:return new T1(1,B(_uu(_ve,_vk)));default:return new T0(2);}};return function(_vo){return (E(_vo)==48)?E(new T1(0,_vm)):new T0(2);};},_vp=function(_vq){return new T1(0,B(_vg(_vq)));},_vr=function(_vs){return new F(function(){return A1(_vs,_2N);});},_vt=function(_vu){return new F(function(){return A1(_vu,_2N);});},_vv=10,_vw=new T1(0,10),_vx=function(_vy){return new F(function(){return _aX(E(_vy));});},_vz=new T(function(){return B(unCStr("this should not happen"));}),_vA=new T(function(){return B(err(_vz));}),_vB=function(_vC,_vD){var _vE=E(_vD);if(!_vE._){return __Z;}else{var _vF=E(_vE.b);return (_vF._==0)?E(_vA):new T2(1,B(_cB(B(_ol(_vE.a,_vC)),_vF.a)),new T(function(){return B(_vB(_vC,_vF.b));}));}},_vG=new T1(0,0),_vH=function(_vI,_vJ,_vK){while(1){var _vL=B((function(_vM,_vN,_vO){var _vP=E(_vO);if(!_vP._){return E(_vG);}else{if(!E(_vP.b)._){return E(_vP.a);}else{var _vQ=E(_vN);if(_vQ<=40){var _vR=function(_vS,_vT){while(1){var _vU=E(_vT);if(!_vU._){return E(_vS);}else{var _vV=B(_cB(B(_ol(_vS,_vM)),_vU.a));_vS=_vV;_vT=_vU.b;continue;}}};return new F(function(){return _vR(_vG,_vP);});}else{var _vW=B(_ol(_vM,_vM));if(!(_vQ%2)){var _vX=B(_vB(_vM,_vP));_vI=_vW;_vJ=quot(_vQ+1|0,2);_vK=_vX;return __continue;}else{var _vX=B(_vB(_vM,new T2(1,_vG,_vP)));_vI=_vW;_vJ=quot(_vQ+1|0,2);_vK=_vX;return __continue;}}}}})(_vI,_vJ,_vK));if(_vL!=__continue){return _vL;}}},_vY=function(_vZ,_w0){return new F(function(){return _vH(_vZ,new T(function(){return B(_mz(_w0,0));},1),B(_6k(_vx,_w0)));});},_w1=function(_w2){var _w3=new T(function(){var _w4=new T(function(){var _w5=function(_w6){return new F(function(){return A1(_w2,new T1(1,new T(function(){return B(_vY(_vw,_w6));})));});};return new T1(1,B(_uu(_vv,_w5)));}),_w7=function(_w8){if(E(_w8)==43){var _w9=function(_wa){return new F(function(){return A1(_w2,new T1(1,new T(function(){return B(_vY(_vw,_wa));})));});};return new T1(1,B(_uu(_vv,_w9)));}else{return new T0(2);}},_wb=function(_wc){if(E(_wc)==45){var _wd=function(_we){return new F(function(){return A1(_w2,new T1(1,new T(function(){return B(_fz(B(_vY(_vw,_we))));})));});};return new T1(1,B(_uu(_vv,_wd)));}else{return new T0(2);}};return B(_sP(B(_sP(new T1(0,_wb),new T1(0,_w7))),_w4));});return new F(function(){return _sP(new T1(0,function(_wf){return (E(_wf)==101)?E(_w3):new T0(2);}),new T1(0,function(_wg){return (E(_wg)==69)?E(_w3):new T0(2);}));});},_wh=function(_wi){var _wj=function(_wk){return new F(function(){return A1(_wi,new T1(1,_wk));});};return function(_wl){return (E(_wl)==46)?new T1(1,B(_uu(_vv,_wj))):new T0(2);};},_wm=function(_wn){return new T1(0,B(_wh(_wn)));},_wo=function(_wp){var _wq=function(_wr){var _ws=function(_wt){return new T1(1,B(_tN(_w1,_vr,function(_wu){return new F(function(){return A1(_wp,new T1(5,new T3(1,_wr,_wt,_wu)));});})));};return new T1(1,B(_tN(_wm,_vt,_ws)));};return new F(function(){return _uu(_vv,_wq);});},_wv=function(_ww){return new T1(1,B(_wo(_ww)));},_wx=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wy=function(_wz){return new F(function(){return _4A(_hd,_wz,_wx);});},_wA=false,_wB=true,_wC=function(_wD){var _wE=new T(function(){return B(A1(_wD,_vf));}),_wF=new T(function(){return B(A1(_wD,_ve));});return function(_wG){switch(E(_wG)){case 79:return E(_wE);case 88:return E(_wF);case 111:return E(_wE);case 120:return E(_wF);default:return new T0(2);}};},_wH=function(_wI){return new T1(0,B(_wC(_wI)));},_wJ=function(_wK){return new F(function(){return A1(_wK,_vv);});},_wL=function(_wM){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_A(9,_wM,_S));}))));});},_wN=function(_wO){return new T0(2);},_wP=function(_wQ){var _wR=E(_wQ);if(!_wR._){return E(_wN);}else{var _wS=_wR.a,_wT=E(_wR.b);if(!_wT._){return E(_wS);}else{var _wU=new T(function(){return B(_wP(_wT));}),_wV=function(_wW){return new F(function(){return _sP(B(A1(_wS,_wW)),new T(function(){return B(A1(_wU,_wW));}));});};return E(_wV);}}},_wX=function(_wY,_wZ){var _x0=function(_x1,_x2,_x3){var _x4=E(_x1);if(!_x4._){return new F(function(){return A1(_x3,_wY);});}else{var _x5=E(_x2);if(!_x5._){return new T0(2);}else{if(E(_x4.a)!=E(_x5.a)){return new T0(2);}else{var _x6=new T(function(){return B(_x0(_x4.b,_x5.b,_x3));});return new T1(0,function(_x7){return E(_x6);});}}}};return function(_x8){return new F(function(){return _x0(_wY,_x8,_wZ);});};},_x9=new T(function(){return B(unCStr("SO"));}),_xa=14,_xb=function(_xc){var _xd=new T(function(){return B(A1(_xc,_xa));});return new T1(1,B(_wX(_x9,function(_xe){return E(_xd);})));},_xf=new T(function(){return B(unCStr("SOH"));}),_xg=1,_xh=function(_xi){var _xj=new T(function(){return B(A1(_xi,_xg));});return new T1(1,B(_wX(_xf,function(_xk){return E(_xj);})));},_xl=function(_xm){return new T1(1,B(_tN(_xh,_xb,_xm)));},_xn=new T(function(){return B(unCStr("NUL"));}),_xo=0,_xp=function(_xq){var _xr=new T(function(){return B(A1(_xq,_xo));});return new T1(1,B(_wX(_xn,function(_xs){return E(_xr);})));},_xt=new T(function(){return B(unCStr("STX"));}),_xu=2,_xv=function(_xw){var _xx=new T(function(){return B(A1(_xw,_xu));});return new T1(1,B(_wX(_xt,function(_xy){return E(_xx);})));},_xz=new T(function(){return B(unCStr("ETX"));}),_xA=3,_xB=function(_xC){var _xD=new T(function(){return B(A1(_xC,_xA));});return new T1(1,B(_wX(_xz,function(_xE){return E(_xD);})));},_xF=new T(function(){return B(unCStr("EOT"));}),_xG=4,_xH=function(_xI){var _xJ=new T(function(){return B(A1(_xI,_xG));});return new T1(1,B(_wX(_xF,function(_xK){return E(_xJ);})));},_xL=new T(function(){return B(unCStr("ENQ"));}),_xM=5,_xN=function(_xO){var _xP=new T(function(){return B(A1(_xO,_xM));});return new T1(1,B(_wX(_xL,function(_xQ){return E(_xP);})));},_xR=new T(function(){return B(unCStr("ACK"));}),_xS=6,_xT=function(_xU){var _xV=new T(function(){return B(A1(_xU,_xS));});return new T1(1,B(_wX(_xR,function(_xW){return E(_xV);})));},_xX=new T(function(){return B(unCStr("BEL"));}),_xY=7,_xZ=function(_y0){var _y1=new T(function(){return B(A1(_y0,_xY));});return new T1(1,B(_wX(_xX,function(_y2){return E(_y1);})));},_y3=new T(function(){return B(unCStr("BS"));}),_y4=8,_y5=function(_y6){var _y7=new T(function(){return B(A1(_y6,_y4));});return new T1(1,B(_wX(_y3,function(_y8){return E(_y7);})));},_y9=new T(function(){return B(unCStr("HT"));}),_ya=9,_yb=function(_yc){var _yd=new T(function(){return B(A1(_yc,_ya));});return new T1(1,B(_wX(_y9,function(_ye){return E(_yd);})));},_yf=new T(function(){return B(unCStr("LF"));}),_yg=10,_yh=function(_yi){var _yj=new T(function(){return B(A1(_yi,_yg));});return new T1(1,B(_wX(_yf,function(_yk){return E(_yj);})));},_yl=new T(function(){return B(unCStr("VT"));}),_ym=11,_yn=function(_yo){var _yp=new T(function(){return B(A1(_yo,_ym));});return new T1(1,B(_wX(_yl,function(_yq){return E(_yp);})));},_yr=new T(function(){return B(unCStr("FF"));}),_ys=12,_yt=function(_yu){var _yv=new T(function(){return B(A1(_yu,_ys));});return new T1(1,B(_wX(_yr,function(_yw){return E(_yv);})));},_yx=new T(function(){return B(unCStr("CR"));}),_yy=13,_yz=function(_yA){var _yB=new T(function(){return B(A1(_yA,_yy));});return new T1(1,B(_wX(_yx,function(_yC){return E(_yB);})));},_yD=new T(function(){return B(unCStr("SI"));}),_yE=15,_yF=function(_yG){var _yH=new T(function(){return B(A1(_yG,_yE));});return new T1(1,B(_wX(_yD,function(_yI){return E(_yH);})));},_yJ=new T(function(){return B(unCStr("DLE"));}),_yK=16,_yL=function(_yM){var _yN=new T(function(){return B(A1(_yM,_yK));});return new T1(1,B(_wX(_yJ,function(_yO){return E(_yN);})));},_yP=new T(function(){return B(unCStr("DC1"));}),_yQ=17,_yR=function(_yS){var _yT=new T(function(){return B(A1(_yS,_yQ));});return new T1(1,B(_wX(_yP,function(_yU){return E(_yT);})));},_yV=new T(function(){return B(unCStr("DC2"));}),_yW=18,_yX=function(_yY){var _yZ=new T(function(){return B(A1(_yY,_yW));});return new T1(1,B(_wX(_yV,function(_z0){return E(_yZ);})));},_z1=new T(function(){return B(unCStr("DC3"));}),_z2=19,_z3=function(_z4){var _z5=new T(function(){return B(A1(_z4,_z2));});return new T1(1,B(_wX(_z1,function(_z6){return E(_z5);})));},_z7=new T(function(){return B(unCStr("DC4"));}),_z8=20,_z9=function(_za){var _zb=new T(function(){return B(A1(_za,_z8));});return new T1(1,B(_wX(_z7,function(_zc){return E(_zb);})));},_zd=new T(function(){return B(unCStr("NAK"));}),_ze=21,_zf=function(_zg){var _zh=new T(function(){return B(A1(_zg,_ze));});return new T1(1,B(_wX(_zd,function(_zi){return E(_zh);})));},_zj=new T(function(){return B(unCStr("SYN"));}),_zk=22,_zl=function(_zm){var _zn=new T(function(){return B(A1(_zm,_zk));});return new T1(1,B(_wX(_zj,function(_zo){return E(_zn);})));},_zp=new T(function(){return B(unCStr("ETB"));}),_zq=23,_zr=function(_zs){var _zt=new T(function(){return B(A1(_zs,_zq));});return new T1(1,B(_wX(_zp,function(_zu){return E(_zt);})));},_zv=new T(function(){return B(unCStr("CAN"));}),_zw=24,_zx=function(_zy){var _zz=new T(function(){return B(A1(_zy,_zw));});return new T1(1,B(_wX(_zv,function(_zA){return E(_zz);})));},_zB=new T(function(){return B(unCStr("EM"));}),_zC=25,_zD=function(_zE){var _zF=new T(function(){return B(A1(_zE,_zC));});return new T1(1,B(_wX(_zB,function(_zG){return E(_zF);})));},_zH=new T(function(){return B(unCStr("SUB"));}),_zI=26,_zJ=function(_zK){var _zL=new T(function(){return B(A1(_zK,_zI));});return new T1(1,B(_wX(_zH,function(_zM){return E(_zL);})));},_zN=new T(function(){return B(unCStr("ESC"));}),_zO=27,_zP=function(_zQ){var _zR=new T(function(){return B(A1(_zQ,_zO));});return new T1(1,B(_wX(_zN,function(_zS){return E(_zR);})));},_zT=new T(function(){return B(unCStr("FS"));}),_zU=28,_zV=function(_zW){var _zX=new T(function(){return B(A1(_zW,_zU));});return new T1(1,B(_wX(_zT,function(_zY){return E(_zX);})));},_zZ=new T(function(){return B(unCStr("GS"));}),_A0=29,_A1=function(_A2){var _A3=new T(function(){return B(A1(_A2,_A0));});return new T1(1,B(_wX(_zZ,function(_A4){return E(_A3);})));},_A5=new T(function(){return B(unCStr("RS"));}),_A6=30,_A7=function(_A8){var _A9=new T(function(){return B(A1(_A8,_A6));});return new T1(1,B(_wX(_A5,function(_Aa){return E(_A9);})));},_Ab=new T(function(){return B(unCStr("US"));}),_Ac=31,_Ad=function(_Ae){var _Af=new T(function(){return B(A1(_Ae,_Ac));});return new T1(1,B(_wX(_Ab,function(_Ag){return E(_Af);})));},_Ah=new T(function(){return B(unCStr("SP"));}),_Ai=32,_Aj=function(_Ak){var _Al=new T(function(){return B(A1(_Ak,_Ai));});return new T1(1,B(_wX(_Ah,function(_Am){return E(_Al);})));},_An=new T(function(){return B(unCStr("DEL"));}),_Ao=127,_Ap=function(_Aq){var _Ar=new T(function(){return B(A1(_Aq,_Ao));});return new T1(1,B(_wX(_An,function(_As){return E(_Ar);})));},_At=new T2(1,_Ap,_S),_Au=new T2(1,_Aj,_At),_Av=new T2(1,_Ad,_Au),_Aw=new T2(1,_A7,_Av),_Ax=new T2(1,_A1,_Aw),_Ay=new T2(1,_zV,_Ax),_Az=new T2(1,_zP,_Ay),_AA=new T2(1,_zJ,_Az),_AB=new T2(1,_zD,_AA),_AC=new T2(1,_zx,_AB),_AD=new T2(1,_zr,_AC),_AE=new T2(1,_zl,_AD),_AF=new T2(1,_zf,_AE),_AG=new T2(1,_z9,_AF),_AH=new T2(1,_z3,_AG),_AI=new T2(1,_yX,_AH),_AJ=new T2(1,_yR,_AI),_AK=new T2(1,_yL,_AJ),_AL=new T2(1,_yF,_AK),_AM=new T2(1,_yz,_AL),_AN=new T2(1,_yt,_AM),_AO=new T2(1,_yn,_AN),_AP=new T2(1,_yh,_AO),_AQ=new T2(1,_yb,_AP),_AR=new T2(1,_y5,_AQ),_AS=new T2(1,_xZ,_AR),_AT=new T2(1,_xT,_AS),_AU=new T2(1,_xN,_AT),_AV=new T2(1,_xH,_AU),_AW=new T2(1,_xB,_AV),_AX=new T2(1,_xv,_AW),_AY=new T2(1,_xp,_AX),_AZ=new T2(1,_xl,_AY),_B0=new T(function(){return B(_wP(_AZ));}),_B1=34,_B2=new T1(0,1114111),_B3=92,_B4=39,_B5=function(_B6){var _B7=new T(function(){return B(A1(_B6,_xY));}),_B8=new T(function(){return B(A1(_B6,_y4));}),_B9=new T(function(){return B(A1(_B6,_ya));}),_Ba=new T(function(){return B(A1(_B6,_yg));}),_Bb=new T(function(){return B(A1(_B6,_ym));}),_Bc=new T(function(){return B(A1(_B6,_ys));}),_Bd=new T(function(){return B(A1(_B6,_yy));}),_Be=new T(function(){return B(A1(_B6,_B3));}),_Bf=new T(function(){return B(A1(_B6,_B4));}),_Bg=new T(function(){return B(A1(_B6,_B1));}),_Bh=new T(function(){var _Bi=function(_Bj){var _Bk=new T(function(){return B(_aX(E(_Bj)));}),_Bl=function(_Bm){var _Bn=B(_vY(_Bk,_Bm));if(!B(_eF(_Bn,_B2))){return new T0(2);}else{return new F(function(){return A1(_B6,new T(function(){var _Bo=B(_bg(_Bn));if(_Bo>>>0>1114111){return B(_wL(_Bo));}else{return _Bo;}}));});}};return new T1(1,B(_uu(_Bj,_Bl)));},_Bp=new T(function(){var _Bq=new T(function(){return B(A1(_B6,_Ac));}),_Br=new T(function(){return B(A1(_B6,_A6));}),_Bs=new T(function(){return B(A1(_B6,_A0));}),_Bt=new T(function(){return B(A1(_B6,_zU));}),_Bu=new T(function(){return B(A1(_B6,_zO));}),_Bv=new T(function(){return B(A1(_B6,_zI));}),_Bw=new T(function(){return B(A1(_B6,_zC));}),_Bx=new T(function(){return B(A1(_B6,_zw));}),_By=new T(function(){return B(A1(_B6,_zq));}),_Bz=new T(function(){return B(A1(_B6,_zk));}),_BA=new T(function(){return B(A1(_B6,_ze));}),_BB=new T(function(){return B(A1(_B6,_z8));}),_BC=new T(function(){return B(A1(_B6,_z2));}),_BD=new T(function(){return B(A1(_B6,_yW));}),_BE=new T(function(){return B(A1(_B6,_yQ));}),_BF=new T(function(){return B(A1(_B6,_yK));}),_BG=new T(function(){return B(A1(_B6,_yE));}),_BH=new T(function(){return B(A1(_B6,_xa));}),_BI=new T(function(){return B(A1(_B6,_xS));}),_BJ=new T(function(){return B(A1(_B6,_xM));}),_BK=new T(function(){return B(A1(_B6,_xG));}),_BL=new T(function(){return B(A1(_B6,_xA));}),_BM=new T(function(){return B(A1(_B6,_xu));}),_BN=new T(function(){return B(A1(_B6,_xg));}),_BO=new T(function(){return B(A1(_B6,_xo));}),_BP=function(_BQ){switch(E(_BQ)){case 64:return E(_BO);case 65:return E(_BN);case 66:return E(_BM);case 67:return E(_BL);case 68:return E(_BK);case 69:return E(_BJ);case 70:return E(_BI);case 71:return E(_B7);case 72:return E(_B8);case 73:return E(_B9);case 74:return E(_Ba);case 75:return E(_Bb);case 76:return E(_Bc);case 77:return E(_Bd);case 78:return E(_BH);case 79:return E(_BG);case 80:return E(_BF);case 81:return E(_BE);case 82:return E(_BD);case 83:return E(_BC);case 84:return E(_BB);case 85:return E(_BA);case 86:return E(_Bz);case 87:return E(_By);case 88:return E(_Bx);case 89:return E(_Bw);case 90:return E(_Bv);case 91:return E(_Bu);case 92:return E(_Bt);case 93:return E(_Bs);case 94:return E(_Br);case 95:return E(_Bq);default:return new T0(2);}};return B(_sP(new T1(0,function(_BR){return (E(_BR)==94)?E(new T1(0,_BP)):new T0(2);}),new T(function(){return B(A1(_B0,_B6));})));});return B(_sP(new T1(1,B(_tN(_wH,_wJ,_Bi))),_Bp));});return new F(function(){return _sP(new T1(0,function(_BS){switch(E(_BS)){case 34:return E(_Bg);case 39:return E(_Bf);case 92:return E(_Be);case 97:return E(_B7);case 98:return E(_B8);case 102:return E(_Bc);case 110:return E(_Ba);case 114:return E(_Bd);case 116:return E(_B9);case 118:return E(_Bb);default:return new T0(2);}}),_Bh);});},_BT=function(_BU){return new F(function(){return A1(_BU,_gK);});},_BV=function(_BW){var _BX=E(_BW);if(!_BX._){return E(_BT);}else{var _BY=E(_BX.a),_BZ=_BY>>>0,_C0=new T(function(){return B(_BV(_BX.b));});if(_BZ>887){var _C1=u_iswspace(_BY);if(!E(_C1)){return E(_BT);}else{var _C2=function(_C3){var _C4=new T(function(){return B(A1(_C0,_C3));});return new T1(0,function(_C5){return E(_C4);});};return E(_C2);}}else{var _C6=E(_BZ);if(_C6==32){var _C7=function(_C8){var _C9=new T(function(){return B(A1(_C0,_C8));});return new T1(0,function(_Ca){return E(_C9);});};return E(_C7);}else{if(_C6-9>>>0>4){if(E(_C6)==160){var _Cb=function(_Cc){var _Cd=new T(function(){return B(A1(_C0,_Cc));});return new T1(0,function(_Ce){return E(_Cd);});};return E(_Cb);}else{return E(_BT);}}else{var _Cf=function(_Cg){var _Ch=new T(function(){return B(A1(_C0,_Cg));});return new T1(0,function(_Ci){return E(_Ch);});};return E(_Cf);}}}}},_Cj=function(_Ck){var _Cl=new T(function(){return B(_Cj(_Ck));}),_Cm=function(_Cn){return (E(_Cn)==92)?E(_Cl):new T0(2);},_Co=function(_Cp){return E(new T1(0,_Cm));},_Cq=new T1(1,function(_Cr){return new F(function(){return A2(_BV,_Cr,_Co);});}),_Cs=new T(function(){return B(_B5(function(_Ct){return new F(function(){return A1(_Ck,new T2(0,_Ct,_wB));});}));}),_Cu=function(_Cv){var _Cw=E(_Cv);if(_Cw==38){return E(_Cl);}else{var _Cx=_Cw>>>0;if(_Cx>887){var _Cy=u_iswspace(_Cw);return (E(_Cy)==0)?new T0(2):E(_Cq);}else{var _Cz=E(_Cx);return (_Cz==32)?E(_Cq):(_Cz-9>>>0>4)?(E(_Cz)==160)?E(_Cq):new T0(2):E(_Cq);}}};return new F(function(){return _sP(new T1(0,function(_CA){return (E(_CA)==92)?E(new T1(0,_Cu)):new T0(2);}),new T1(0,function(_CB){var _CC=E(_CB);if(E(_CC)==92){return E(_Cs);}else{return new F(function(){return A1(_Ck,new T2(0,_CC,_wA));});}}));});},_CD=function(_CE,_CF){var _CG=new T(function(){return B(A1(_CF,new T1(1,new T(function(){return B(A1(_CE,_S));}))));}),_CH=function(_CI){var _CJ=E(_CI),_CK=E(_CJ.a);if(E(_CK)==34){if(!E(_CJ.b)){return E(_CG);}else{return new F(function(){return _CD(function(_CL){return new F(function(){return A1(_CE,new T2(1,_CK,_CL));});},_CF);});}}else{return new F(function(){return _CD(function(_CM){return new F(function(){return A1(_CE,new T2(1,_CK,_CM));});},_CF);});}};return new F(function(){return _Cj(_CH);});},_CN=new T(function(){return B(unCStr("_\'"));}),_CO=function(_CP){var _CQ=u_iswalnum(_CP);if(!E(_CQ)){return new F(function(){return _4A(_hd,_CP,_CN);});}else{return true;}},_CR=function(_CS){return new F(function(){return _CO(E(_CS));});},_CT=new T(function(){return B(unCStr(",;()[]{}`"));}),_CU=new T(function(){return B(unCStr("=>"));}),_CV=new T2(1,_CU,_S),_CW=new T(function(){return B(unCStr("~"));}),_CX=new T2(1,_CW,_CV),_CY=new T(function(){return B(unCStr("@"));}),_CZ=new T2(1,_CY,_CX),_D0=new T(function(){return B(unCStr("->"));}),_D1=new T2(1,_D0,_CZ),_D2=new T(function(){return B(unCStr("<-"));}),_D3=new T2(1,_D2,_D1),_D4=new T(function(){return B(unCStr("|"));}),_D5=new T2(1,_D4,_D3),_D6=new T(function(){return B(unCStr("\\"));}),_D7=new T2(1,_D6,_D5),_D8=new T(function(){return B(unCStr("="));}),_D9=new T2(1,_D8,_D7),_Da=new T(function(){return B(unCStr("::"));}),_Db=new T2(1,_Da,_D9),_Dc=new T(function(){return B(unCStr(".."));}),_Dd=new T2(1,_Dc,_Db),_De=function(_Df){var _Dg=new T(function(){return B(A1(_Df,_ur));}),_Dh=new T(function(){var _Di=new T(function(){var _Dj=function(_Dk){var _Dl=new T(function(){return B(A1(_Df,new T1(0,_Dk)));});return new T1(0,function(_Dm){return (E(_Dm)==39)?E(_Dl):new T0(2);});};return B(_B5(_Dj));}),_Dn=function(_Do){var _Dp=E(_Do);switch(E(_Dp)){case 39:return new T0(2);case 92:return E(_Di);default:var _Dq=new T(function(){return B(A1(_Df,new T1(0,_Dp)));});return new T1(0,function(_Dr){return (E(_Dr)==39)?E(_Dq):new T0(2);});}},_Ds=new T(function(){var _Dt=new T(function(){return B(_CD(_5U,_Df));}),_Du=new T(function(){var _Dv=new T(function(){var _Dw=new T(function(){var _Dx=function(_Dy){var _Dz=E(_Dy),_DA=u_iswalpha(_Dz);return (E(_DA)==0)?(E(_Dz)==95)?new T1(1,B(_ud(_CR,function(_DB){return new F(function(){return A1(_Df,new T1(3,new T2(1,_Dz,_DB)));});}))):new T0(2):new T1(1,B(_ud(_CR,function(_DC){return new F(function(){return A1(_Df,new T1(3,new T2(1,_Dz,_DC)));});})));};return B(_sP(new T1(0,_Dx),new T(function(){return new T1(1,B(_tN(_vp,_wv,_Df)));})));}),_DD=function(_DE){return (!B(_4A(_hd,_DE,_wx)))?new T0(2):new T1(1,B(_ud(_wy,function(_DF){var _DG=new T2(1,_DE,_DF);if(!B(_4A(_qk,_DG,_Dd))){return new F(function(){return A1(_Df,new T1(4,_DG));});}else{return new F(function(){return A1(_Df,new T1(2,_DG));});}})));};return B(_sP(new T1(0,_DD),_Dw));});return B(_sP(new T1(0,function(_DH){if(!B(_4A(_hd,_DH,_CT))){return new T0(2);}else{return new F(function(){return A1(_Df,new T1(2,new T2(1,_DH,_S)));});}}),_Dv));});return B(_sP(new T1(0,function(_DI){return (E(_DI)==34)?E(_Dt):new T0(2);}),_Du));});return B(_sP(new T1(0,function(_DJ){return (E(_DJ)==39)?E(new T1(0,_Dn)):new T0(2);}),_Ds));});return new F(function(){return _sP(new T1(1,function(_DK){return (E(_DK)._==0)?E(_Dg):new T0(2);}),_Dh);});},_DL=0,_DM=function(_DN,_DO){var _DP=new T(function(){var _DQ=new T(function(){var _DR=function(_DS){var _DT=new T(function(){var _DU=new T(function(){return B(A1(_DO,_DS));});return B(_De(function(_DV){var _DW=E(_DV);return (_DW._==2)?(!B(_qV(_DW.a,_ts)))?new T0(2):E(_DU):new T0(2);}));}),_DX=function(_DY){return E(_DT);};return new T1(1,function(_DZ){return new F(function(){return A2(_BV,_DZ,_DX);});});};return B(A2(_DN,_DL,_DR));});return B(_De(function(_E0){var _E1=E(_E0);return (_E1._==2)?(!B(_qV(_E1.a,_tr)))?new T0(2):E(_DQ):new T0(2);}));}),_E2=function(_E3){return E(_DP);};return function(_E4){return new F(function(){return A2(_BV,_E4,_E2);});};},_E5=function(_E6,_E7){var _E8=function(_E9){var _Ea=new T(function(){return B(A1(_E6,_E9));}),_Eb=function(_Ec){return new F(function(){return _sP(B(A1(_Ea,_Ec)),new T(function(){return new T1(1,B(_DM(_E8,_Ec)));}));});};return E(_Eb);},_Ed=new T(function(){return B(A1(_E6,_E7));}),_Ee=function(_Ef){return new F(function(){return _sP(B(A1(_Ed,_Ef)),new T(function(){return new T1(1,B(_DM(_E8,_Ef)));}));});};return E(_Ee);},_Eg=0,_Eh=function(_Ei,_Ej){return new F(function(){return A1(_Ej,_Eg);});},_Ek=new T(function(){return B(unCStr("Fr"));}),_El=new T2(0,_Ek,_Eh),_Em=1,_En=function(_Eo,_Ep){return new F(function(){return A1(_Ep,_Em);});},_Eq=new T(function(){return B(unCStr("Bl"));}),_Er=new T2(0,_Eq,_En),_Es=2,_Et=function(_Eu,_Ev){return new F(function(){return A1(_Ev,_Es);});},_Ew=new T(function(){return B(unCStr("Ex"));}),_Ex=new T2(0,_Ew,_Et),_Ey=3,_Ez=function(_EA,_EB){return new F(function(){return A1(_EB,_Ey);});},_EC=new T(function(){return B(unCStr("Mv"));}),_ED=new T2(0,_EC,_Ez),_EE=4,_EF=function(_EG,_EH){return new F(function(){return A1(_EH,_EE);});},_EI=new T(function(){return B(unCStr("Pn"));}),_EJ=new T2(0,_EI,_EF),_EK=8,_EL=function(_EM,_EN){return new F(function(){return A1(_EN,_EK);});},_EO=new T(function(){return B(unCStr("DF"));}),_EP=new T2(0,_EO,_EL),_EQ=new T2(1,_EP,_S),_ER=7,_ES=function(_ET,_EU){return new F(function(){return A1(_EU,_ER);});},_EV=new T(function(){return B(unCStr("DB"));}),_EW=new T2(0,_EV,_ES),_EX=new T2(1,_EW,_EQ),_EY=6,_EZ=function(_F0,_F1){return new F(function(){return A1(_F1,_EY);});},_F2=new T(function(){return B(unCStr("Cm"));}),_F3=new T2(0,_F2,_EZ),_F4=new T2(1,_F3,_EX),_F5=5,_F6=function(_F7,_F8){return new F(function(){return A1(_F8,_F5);});},_F9=new T(function(){return B(unCStr("Wn"));}),_Fa=new T2(0,_F9,_F6),_Fb=new T2(1,_Fa,_F4),_Fc=new T2(1,_EJ,_Fb),_Fd=new T2(1,_ED,_Fc),_Fe=new T2(1,_Ex,_Fd),_Ff=new T2(1,_Er,_Fe),_Fg=new T2(1,_El,_Ff),_Fh=function(_Fi,_Fj,_Fk){var _Fl=E(_Fi);if(!_Fl._){return new T0(2);}else{var _Fm=E(_Fl.a),_Fn=_Fm.a,_Fo=new T(function(){return B(A2(_Fm.b,_Fj,_Fk));}),_Fp=new T(function(){return B(_De(function(_Fq){var _Fr=E(_Fq);switch(_Fr._){case 3:return (!B(_qV(_Fn,_Fr.a)))?new T0(2):E(_Fo);case 4:return (!B(_qV(_Fn,_Fr.a)))?new T0(2):E(_Fo);default:return new T0(2);}}));}),_Fs=function(_Ft){return E(_Fp);};return new F(function(){return _sP(new T1(1,function(_Fu){return new F(function(){return A2(_BV,_Fu,_Fs);});}),new T(function(){return B(_Fh(_Fl.b,_Fj,_Fk));}));});}},_Fv=function(_Fw,_Fx){return new F(function(){return _Fh(_Fg,_Fw,_Fx);});},_Fy=function(_Fz){var _FA=function(_FB){return E(new T2(3,_Fz,_tE));};return new T1(1,function(_FC){return new F(function(){return A2(_BV,_FC,_FA);});});},_FD=new T(function(){return B(A3(_E5,_Fv,_DL,_Fy));}),_FE=new T(function(){return B(unCStr("empty"));}),_FF=new T2(1,_FE,_S),_FG=new T(function(){return B(err(_sy));}),_FH=new T(function(){return B(err(_sA));}),_FI=function(_FJ,_FK){var _FL=function(_FM,_FN){var _FO=function(_FP){return new F(function(){return A1(_FN,new T(function(){return  -E(_FP);}));});},_FQ=new T(function(){return B(_De(function(_FR){return new F(function(){return A3(_FJ,_FR,_FM,_FO);});}));}),_FS=function(_FT){return E(_FQ);},_FU=function(_FV){return new F(function(){return A2(_BV,_FV,_FS);});},_FW=new T(function(){return B(_De(function(_FX){var _FY=E(_FX);if(_FY._==4){var _FZ=E(_FY.a);if(!_FZ._){return new F(function(){return A3(_FJ,_FY,_FM,_FN);});}else{if(E(_FZ.a)==45){if(!E(_FZ.b)._){return E(new T1(1,_FU));}else{return new F(function(){return A3(_FJ,_FY,_FM,_FN);});}}else{return new F(function(){return A3(_FJ,_FY,_FM,_FN);});}}}else{return new F(function(){return A3(_FJ,_FY,_FM,_FN);});}}));}),_G0=function(_G1){return E(_FW);};return new T1(1,function(_G2){return new F(function(){return A2(_BV,_G2,_G0);});});};return new F(function(){return _E5(_FL,_FK);});},_G3=function(_G4){var _G5=E(_G4);if(!_G5._){var _G6=_G5.b,_G7=new T(function(){return B(_vH(new T(function(){return B(_aX(E(_G5.a)));}),new T(function(){return B(_mz(_G6,0));},1),B(_6k(_vx,_G6))));});return new T1(1,_G7);}else{return (E(_G5.b)._==0)?(E(_G5.c)._==0)?new T1(1,new T(function(){return B(_vY(_vw,_G5.a));})):__Z:__Z;}},_G8=function(_G9,_Ga){return new T0(2);},_Gb=function(_Gc){var _Gd=E(_Gc);if(_Gd._==5){var _Ge=B(_G3(_Gd.a));if(!_Ge._){return E(_G8);}else{var _Gf=new T(function(){return B(_bg(_Ge.a));});return function(_Gg,_Gh){return new F(function(){return A1(_Gh,_Gf);});};}}else{return E(_G8);}},_Gi=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_Gj=new T2(1,_y,_S),_Gk=function(_Gl){while(1){var _Gm=B((function(_Gn){var _Go=E(_Gn);if(!_Go._){return __Z;}else{var _Gp=_Go.b,_Gq=E(_Go.a);if(!E(_Gq.b)._){return new T2(1,_Gq.a,new T(function(){return B(_Gk(_Gp));}));}else{_Gl=_Gp;return __continue;}}})(_Gl));if(_Gm!=__continue){return _Gm;}}},_Gr=function(_Gs,_Gt){while(1){var _Gu=E(_Gs);if(!_Gu._){return E(_Gt);}else{var _Gv=new T2(1,_Gu.a,_Gt);_Gs=_Gu.b;_Gt=_Gv;continue;}}},_Gw=function(_Gx,_Gy){var _Gz=E(_Gx);if(!_Gz._){return __Z;}else{var _GA=E(_Gy);return (_GA._==0)?__Z:new T2(1,new T2(0,_Gz.a,_GA.a),new T(function(){return B(_Gw(_Gz.b,_GA.b));}));}},_GB=function(_GC,_GD,_GE){while(1){var _GF=B((function(_GG,_GH,_GI){var _GJ=E(_GI);if(!_GJ._){return E(_GH);}else{var _GK=_GJ.a,_GL=_GJ.b,_GM=B(_ss(_qk,_GK,_sh));if(!_GM._){var _GN=E(_FF);}else{var _GN=E(_GM.a);}if(!B(_r0(_GN,_FF))){var _GO=B(_Gr(B(_Gw(B(_Gr(_GH,_S)),new T(function(){return B(_Gr(_GN,_S));},1))),_S)),_GP=B(_mz(_GO,0)),_GQ=new T(function(){var _GR=B(_6k(_sq,_GO));if(!_GR._){return __Z;}else{var _GS=_GR.a,_GT=E(_GR.b);if(!_GT._){return __Z;}else{var _GU=_GT.a;if(!E(_GT.b)._){if(!B(_qV(_GK,_rT))){if(!B(_qV(_GK,_rS))){if(!B(_qV(_GK,_rR))){if(!B(_qV(_GK,_rV))){if(!B(_qV(_GK,_rU))){return __Z;}else{if(!B(_qV(_GS,_sC))){if(!B(_qV(_GU,_sC))){return E(_sD);}else{return E(_sC);}}else{return E(_sC);}}}else{var _GV=B(_rF(new T2(0,new T(function(){var _GW=E(_GS);if(!_GW._){return E(_nn);}else{return E(_GW.a);}}),new T(function(){var _GX=B(_Gk(B(_sF(_FD,_GU))));if(!_GX._){return E(_sz);}else{if(!E(_GX.b)._){return E(_GX.a);}else{return E(_sB);}}})),E(E(_GG).a).b)),_GY=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_GZ){return new F(function(){return _A(0,E(_GV.a),_GZ);});},new T2(1,function(_H0){return new F(function(){return _A(0,E(_GV.b),_H0);});},_S)),_Gj));});return new T2(1,_z,_GY);}}else{return new T2(1,new T(function(){var _H1=B(_Gk(B(_sF(_Gi,_GS))));if(!_H1._){return E(_FG);}else{if(!E(_H1.b)._){var _H2=B(_Gk(B(_sF(_Gi,_GU))));if(!_H2._){return E(_FG);}else{if(!E(_H2.b)._){return E(B(_6X(B(_6X(E(E(_GG).a).b,E(_H2.a))),E(_H1.a))).a);}else{return E(_FH);}}}else{return E(_FH);}}}),_S);}}else{if(!B(_qV(_GS,_GU))){return E(_sD);}else{return E(_sC);}}}else{if(!B(_qV(_GS,_sC))){return E(_sD);}else{if(!B(_qV(_GU,_sC))){return E(_sD);}else{return E(_sC);}}}}else{return __Z;}}}});if(_GP>0){var _H3=_GG,_H4=B(_q(B(_Gr(B(_rL(_GP,B(_Gr(_GH,_S)))),_S)),new T2(1,_GQ,_S)));_GC=_H3;_GD=_H4;_GE=_GL;return __continue;}else{var _H3=_GG,_H4=B(_q(B(_Gr(B(_Gr(_GH,_S)),_S)),new T2(1,_GQ,_S)));_GC=_H3;_GD=_H4;_GE=_GL;return __continue;}}else{var _H3=_GG,_H4=B(_q(_GH,new T2(1,_GK,_S)));_GC=_H3;_GD=_H4;_GE=_GL;return __continue;}}})(_GC,_GD,_GE));if(_GF!=__continue){return _GF;}}},_H5=new T(function(){return B(_ed("Event.hs:(86,1)-(90,73)|function addMemory"));}),_H6=function(_H7,_H8){var _H9=E(_H7),_Ha=E(_H8);if(!B(_qV(_H9.a,_Ha.a))){return false;}else{return new F(function(){return _qV(_H9.b,_Ha.b);});}},_Hb=new T2(1,_S,_S),_Hc=function(_Hd,_He,_Hf){var _Hg=E(_Hf);if(!_Hg._){return new T2(0,new T2(1,_He,_S),_S);}else{var _Hh=E(_He),_Hi=new T(function(){var _Hj=B(_Hc(_Hd,_Hg.a,_Hg.b));return new T2(0,_Hj.a,_Hj.b);});return (_Hd!=_Hh)?new T2(0,new T2(1,_Hh,new T(function(){return E(E(_Hi).a);})),new T(function(){return E(E(_Hi).b);})):new T2(0,_S,new T2(1,new T(function(){return E(E(_Hi).a);}),new T(function(){return E(E(_Hi).b);})));}},_Hk=32,_Hl=function(_Hm){var _Hn=E(_Hm);if(!_Hn._){return __Z;}else{var _Ho=new T(function(){return B(_q(_Hn.a,new T(function(){return B(_Hl(_Hn.b));},1)));});return new T2(1,_Hk,_Ho);}},_Hp=function(_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL){while(1){var _HM=B((function(_HN,_HO,_HP,_HQ,_HR,_HS,_HT,_HU,_HV,_HW,_HX,_HY,_HZ,_I0,_I1,_I2,_I3,_I4,_I5,_I6,_I7,_I8){var _I9=E(_HN);if(!_I9._){return {_:0,a:_HO,b:_HP,c:_HQ,d:_HR,e:_HS,f:_HT,g:_HU,h:_HV,i:_HW,j:_HX,k:_HY,l:_HZ,m:_I0,n:_I1,o:_I2,p:_I3,q:_I4,r:_I5,s:_I6,t:_I7,u:_I8};}else{var _Ia=_I9.a,_Ib=E(_I9.b);if(!_Ib._){return E(_H5);}else{var _Ic=new T(function(){var _Id=E(_Ib.a);if(!_Id._){var _Ie=B(_GB({_:0,a:E(_HO),b:E(_HP),c:E(_HQ),d:E(_HR),e:E(_HS),f:E(_HT),g:E(_HU),h:E(_HV),i:_HW,j:_HX,k:_HY,l:_HZ,m:E(_I0),n:_I1,o:E(_I2),p:E(_I3),q:_I4,r:E(_I5),s:_I6,t:E(_I7),u:E(_I8)},_S,_Hb));if(!_Ie._){return __Z;}else{return B(_q(_Ie.a,new T(function(){return B(_Hl(_Ie.b));},1)));}}else{var _If=_Id.a,_Ig=E(_Id.b);if(!_Ig._){var _Ih=B(_GB({_:0,a:E(_HO),b:E(_HP),c:E(_HQ),d:E(_HR),e:E(_HS),f:E(_HT),g:E(_HU),h:E(_HV),i:_HW,j:_HX,k:_HY,l:_HZ,m:E(_I0),n:_I1,o:E(_I2),p:E(_I3),q:_I4,r:E(_I5),s:_I6,t:E(_I7),u:E(_I8)},_S,new T2(1,new T2(1,_If,_S),_S)));if(!_Ih._){return __Z;}else{return B(_q(_Ih.a,new T(function(){return B(_Hl(_Ih.b));},1)));}}else{var _Ii=E(_If),_Ij=new T(function(){var _Ik=B(_Hc(95,_Ig.a,_Ig.b));return new T2(0,_Ik.a,_Ik.b);});if(E(_Ii)==95){var _Il=B(_GB({_:0,a:E(_HO),b:E(_HP),c:E(_HQ),d:E(_HR),e:E(_HS),f:E(_HT),g:E(_HU),h:E(_HV),i:_HW,j:_HX,k:_HY,l:_HZ,m:E(_I0),n:_I1,o:E(_I2),p:E(_I3),q:_I4,r:E(_I5),s:_I6,t:E(_I7),u:E(_I8)},_S,new T2(1,_S,new T2(1,new T(function(){return E(E(_Ij).a);}),new T(function(){return E(E(_Ij).b);})))));if(!_Il._){return __Z;}else{return B(_q(_Il.a,new T(function(){return B(_Hl(_Il.b));},1)));}}else{var _Im=B(_GB({_:0,a:E(_HO),b:E(_HP),c:E(_HQ),d:E(_HR),e:E(_HS),f:E(_HT),g:E(_HU),h:E(_HV),i:_HW,j:_HX,k:_HY,l:_HZ,m:E(_I0),n:_I1,o:E(_I2),p:E(_I3),q:_I4,r:E(_I5),s:_I6,t:E(_I7),u:E(_I8)},_S,new T2(1,new T2(1,_Ii,new T(function(){return E(E(_Ij).a);})),new T(function(){return E(E(_Ij).b);}))));if(!_Im._){return __Z;}else{return B(_q(_Im.a,new T(function(){return B(_Hl(_Im.b));},1)));}}}}}),_In=_HO,_Io=_HP,_Ip=_HQ,_Iq=_HR,_Ir=_HS,_Is=_HT,_It=_HV,_Iu=_HW,_Iv=_HX,_Iw=_HY,_Ix=_HZ,_Iy=_I0,_Iz=_I1,_IA=_I2,_IB=_I3,_IC=_I4,_ID=_I5,_IE=_I6,_IF=_I7,_IG=_I8;_Hq=_Ib.b;_Hr=_In;_Hs=_Io;_Ht=_Ip;_Hu=_Iq;_Hv=_Ir;_Hw=_Is;_Hx=new T2(1,new T2(0,_Ia,_Ic),new T(function(){var _IH=B(_ss(_qk,_Ia,_HU));if(!_IH._){var _II=__Z;}else{var _II=E(_IH.a);}if(!B(_qV(_II,_S))){return B(_qO(_H6,new T2(0,_Ia,_II),_HU));}else{return E(_HU);}}));_Hy=_It;_Hz=_Iu;_HA=_Iv;_HB=_Iw;_HC=_Ix;_HD=_Iy;_HE=_Iz;_HF=_IA;_HG=_IB;_HH=_IC;_HI=_ID;_HJ=_IE;_HK=_IF;_HL=_IG;return __continue;}}})(_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL));if(_HM!=__continue){return _HM;}}},_IJ=function(_IK){var _IL=E(_IK);if(!_IL._){return new T2(0,_S,_S);}else{var _IM=E(_IL.a),_IN=new T(function(){var _IO=B(_IJ(_IL.b));return new T2(0,_IO.a,_IO.b);});return new T2(0,new T2(1,_IM.a,new T(function(){return E(E(_IN).a);})),new T2(1,_IM.b,new T(function(){return E(E(_IN).b);})));}},_IP=function(_IQ,_IR,_IS){while(1){var _IT=B((function(_IU,_IV,_IW){var _IX=E(_IW);if(!_IX._){return __Z;}else{var _IY=_IX.b;if(_IV!=E(_IX.a)){var _IZ=_IU+1|0,_J0=_IV;_IQ=_IZ;_IR=_J0;_IS=_IY;return __continue;}else{return new T2(1,_IU,new T(function(){return B(_IP(_IU+1|0,_IV,_IY));}));}}})(_IQ,_IR,_IS));if(_IT!=__continue){return _IT;}}},_J1=function(_J2,_J3,_J4){var _J5=E(_J4);if(!_J5._){return __Z;}else{var _J6=_J5.b,_J7=E(_J3);if(_J7!=E(_J5.a)){return new F(function(){return _IP(_J2+1|0,_J7,_J6);});}else{return new T2(1,_J2,new T(function(){return B(_IP(_J2+1|0,_J7,_J6));}));}}},_J8=function(_J9,_Ja,_Jb,_Jc){var _Jd=E(_Jc);if(!_Jd._){return __Z;}else{var _Je=_Jd.b;return (!B(_4A(_3L,_J9,_Jb)))?new T2(1,_Jd.a,new T(function(){return B(_J8(_J9+1|0,_Ja,_Jb,_Je));})):new T2(1,_Ja,new T(function(){return B(_J8(_J9+1|0,_Ja,_Jb,_Je));}));}},_Jf=function(_Jg,_Jh,_Ji){var _Jj=E(_Ji);if(!_Jj._){return __Z;}else{var _Jk=new T(function(){var _Jl=B(_IJ(_Jj.a)),_Jm=_Jl.a,_Jn=new T(function(){return B(_J8(0,_Jh,new T(function(){return B(_J1(0,_Jg,_Jm));}),_Jl.b));},1);return B(_Gw(_Jm,_Jn));});return new T2(1,_Jk,new T(function(){return B(_Jf(_Jg,_Jh,_Jj.b));}));}},_Jo=function(_Jp){var _Jq=E(_Jp);return (_Jq._==0)?E(_nn):E(_Jq.a);},_Jr=new T(function(){return B(_ed("Event.hs:(59,1)-(62,93)|function changeType"));}),_Js=new T(function(){return B(_ed("Event.hs:56:16-116|case"));}),_Jt=new T(function(){return B(unCStr("Wn"));}),_Ju=new T(function(){return B(unCStr("Pn"));}),_Jv=new T(function(){return B(unCStr("Mv"));}),_Jw=new T(function(){return B(unCStr("Fr"));}),_Jx=new T(function(){return B(unCStr("Ex"));}),_Jy=new T(function(){return B(unCStr("DF"));}),_Jz=new T(function(){return B(unCStr("DB"));}),_JA=new T(function(){return B(unCStr("Cm"));}),_JB=new T(function(){return B(unCStr("Bl"));}),_JC=function(_JD){return (!B(_qV(_JD,_JB)))?(!B(_qV(_JD,_JA)))?(!B(_qV(_JD,_Jz)))?(!B(_qV(_JD,_Jy)))?(!B(_qV(_JD,_Jx)))?(!B(_qV(_JD,_Jw)))?(!B(_qV(_JD,_Jv)))?(!B(_qV(_JD,_Ju)))?(!B(_qV(_JD,_Jt)))?E(_Js):5:4:3:0:2:8:7:6:1;},_JE=function(_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0){while(1){var _K1=B((function(_K2,_K3,_K4,_K5,_K6,_K7,_K8,_K9,_Ka,_Kb,_Kc,_Kd,_Ke,_Kf,_Kg,_Kh,_Ki,_Kj,_Kk,_Kl,_Km,_Kn){var _Ko=E(_K2);if(!_Ko._){return {_:0,a:_K3,b:_K4,c:_K5,d:_K6,e:_K7,f:_K8,g:_K9,h:_Ka,i:_Kb,j:_Kc,k:_Kd,l:_Ke,m:_Kf,n:_Kg,o:_Kh,p:_Ki,q:_Kj,r:_Kk,s:_Kl,t:_Km,u:_Kn};}else{var _Kp=E(_Ko.b);if(!_Kp._){return E(_Jr);}else{var _Kq=E(_K3),_Kr=_K4,_Ks=_K5,_Kt=_K6,_Ku=_K7,_Kv=_K8,_Kw=_K9,_Kx=_Ka,_Ky=_Kb,_Kz=_Kc,_KA=_Kd,_KB=_Ke,_KC=_Kf,_KD=_Kg,_KE=_Kh,_KF=_Ki,_KG=_Kj,_KH=_Kk,_KI=_Kl,_KJ=_Km,_KK=_Kn;_JF=_Kp.b;_JG={_:0,a:E(_Kq.a),b:E(B(_Jf(new T(function(){return B(_Jo(_Ko.a));}),new T(function(){return B(_JC(_Kp.a));}),_Kq.b))),c:E(_Kq.c),d:_Kq.d,e:_Kq.e,f:_Kq.f,g:E(_Kq.g),h:_Kq.h,i:E(_Kq.i),j:E(_Kq.j),k:E(_Kq.k)};_JH=_Kr;_JI=_Ks;_JJ=_Kt;_JK=_Ku;_JL=_Kv;_JM=_Kw;_JN=_Kx;_JO=_Ky;_JP=_Kz;_JQ=_KA;_JR=_KB;_JS=_KC;_JT=_KD;_JU=_KE;_JV=_KF;_JW=_KG;_JX=_KH;_JY=_KI;_JZ=_KJ;_K0=_KK;return __continue;}}})(_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0));if(_K1!=__continue){return _K1;}}},_KL=function(_KM,_KN){while(1){var _KO=E(_KN);if(!_KO._){return __Z;}else{var _KP=_KO.b,_KQ=E(_KM);if(_KQ==1){return E(_KP);}else{_KM=_KQ-1|0;_KN=_KP;continue;}}}},_KR=function(_KS,_KT){while(1){var _KU=E(_KT);if(!_KU._){return __Z;}else{var _KV=_KU.b,_KW=E(_KS);if(_KW==1){return E(_KV);}else{_KS=_KW-1|0;_KT=_KV;continue;}}}},_KX=function(_KY,_KZ,_L0,_L1,_L2){var _L3=new T(function(){var _L4=E(_KY),_L5=new T(function(){return B(_6X(_L2,_KZ));}),_L6=new T2(1,new T2(0,_L0,_L1),new T(function(){var _L7=_L4+1|0;if(_L7>0){return B(_KR(_L7,_L5));}else{return E(_L5);}}));if(0>=_L4){return E(_L6);}else{var _L8=function(_L9,_La){var _Lb=E(_L9);if(!_Lb._){return E(_L6);}else{var _Lc=_Lb.a,_Ld=E(_La);return (_Ld==1)?new T2(1,_Lc,_L6):new T2(1,_Lc,new T(function(){return B(_L8(_Lb.b,_Ld-1|0));}));}};return B(_L8(_L5,_L4));}}),_Le=new T2(1,_L3,new T(function(){var _Lf=_KZ+1|0;if(_Lf>0){return B(_KL(_Lf,_L2));}else{return E(_L2);}}));if(0>=_KZ){return E(_Le);}else{var _Lg=function(_Lh,_Li){var _Lj=E(_Lh);if(!_Lj._){return E(_Le);}else{var _Lk=_Lj.a,_Ll=E(_Li);return (_Ll==1)?new T2(1,_Lk,_Le):new T2(1,_Lk,new T(function(){return B(_Lg(_Lj.b,_Ll-1|0));}));}};return new F(function(){return _Lg(_L2,_KZ);});}},_Lm=32,_Ln=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Lo=function(_Lp){return new F(function(){return _dP(new T1(0,new T(function(){return B(_e2(_Lp,_Ln));})),_dz);});},_Lq=function(_Lr){return new F(function(){return _Lo("Event.hs:42:27-53|(x\' : y\' : _)");});},_Ls=new T(function(){return B(_Lq(_));}),_Lt=function(_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO,_LP){while(1){var _LQ=B((function(_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc){var _Md=E(_LR);if(!_Md._){return {_:0,a:_LS,b:_LT,c:_LU,d:_LV,e:_LW,f:_LX,g:_LY,h:_LZ,i:_M0,j:_M1,k:_M2,l:_M3,m:_M4,n:_M5,o:_M6,p:_M7,q:_M8,r:_M9,s:_Ma,t:_Mb,u:_Mc};}else{var _Me=E(_LS),_Mf=new T(function(){var _Mg=E(_Md.a);if(!_Mg._){return E(_Ls);}else{var _Mh=E(_Mg.b);if(!_Mh._){return E(_Ls);}else{var _Mi=_Mh.a,_Mj=_Mh.b,_Mk=E(_Mg.a);if(E(_Mk)==44){return new T2(0,_S,new T(function(){return E(B(_Hc(44,_Mi,_Mj)).a);}));}else{var _Ml=B(_Hc(44,_Mi,_Mj)),_Mm=E(_Ml.b);if(!_Mm._){return E(_Ls);}else{return new T2(0,new T2(1,_Mk,_Ml.a),_Mm.a);}}}}}),_Mn=B(_Gk(B(_sF(_Gi,new T(function(){return E(E(_Mf).b);})))));if(!_Mn._){return E(_FG);}else{if(!E(_Mn.b)._){var _Mo=new T(function(){var _Mp=B(_Gk(B(_sF(_Gi,new T(function(){return E(E(_Mf).a);})))));if(!_Mp._){return E(_FG);}else{if(!E(_Mp.b)._){return E(_Mp.a);}else{return E(_FH);}}},1),_Mq=_LT,_Mr=_LU,_Ms=_LV,_Mt=_LW,_Mu=_LX,_Mv=_LY,_Mw=_LZ,_Mx=_M0,_My=_M1,_Mz=_M2,_MA=_M3,_MB=_M4,_MC=_M5,_MD=_M6,_ME=_M7,_MF=_M8,_MG=_M9,_MH=_Ma,_MI=_Mb,_MJ=_Mc;_Lu=_Md.b;_Lv={_:0,a:E(_Me.a),b:E(B(_KX(_Mo,E(_Mn.a),_Lm,_Eg,_Me.b))),c:E(_Me.c),d:_Me.d,e:_Me.e,f:_Me.f,g:E(_Me.g),h:_Me.h,i:E(_Me.i),j:E(_Me.j),k:E(_Me.k)};_Lw=_Mq;_Lx=_Mr;_Ly=_Ms;_Lz=_Mt;_LA=_Mu;_LB=_Mv;_LC=_Mw;_LD=_Mx;_LE=_My;_LF=_Mz;_LG=_MA;_LH=_MB;_LI=_MC;_LJ=_MD;_LK=_ME;_LL=_MF;_LM=_MG;_LN=_MH;_LO=_MI;_LP=_MJ;return __continue;}else{return E(_FH);}}}})(_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO,_LP));if(_LQ!=__continue){return _LQ;}}},_MK=function(_ML,_MM,_MN){var _MO=E(_MN);return (_MO._==0)?0:(!B(A3(_4y,_ML,_MM,_MO.a)))?1+B(_MK(_ML,_MM,_MO.b))|0:0;},_MP=function(_MQ,_MR){while(1){var _MS=E(_MR);if(!_MS._){return __Z;}else{var _MT=_MS.b,_MU=E(_MQ);if(_MU==1){return E(_MT);}else{_MQ=_MU-1|0;_MR=_MT;continue;}}}},_MV=function(_MW,_MX){var _MY=new T(function(){var _MZ=_MW+1|0;if(_MZ>0){return B(_MP(_MZ,_MX));}else{return E(_MX);}});if(0>=_MW){return E(_MY);}else{var _N0=function(_N1,_N2){var _N3=E(_N1);if(!_N3._){return E(_MY);}else{var _N4=_N3.a,_N5=E(_N2);return (_N5==1)?new T2(1,_N4,_MY):new T2(1,_N4,new T(function(){return B(_N0(_N3.b,_N5-1|0));}));}};return new F(function(){return _N0(_MX,_MW);});}},_N6=function(_N7,_N8){return new F(function(){return _MV(E(_N7),_N8);});},_N9= -1,_Na=function(_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw){while(1){var _Nx=B((function(_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT){var _NU=E(_Ny);if(!_NU._){return {_:0,a:_Nz,b:_NA,c:_NB,d:_NC,e:_ND,f:_NE,g:_NF,h:_NG,i:_NH,j:_NI,k:_NJ,l:_NK,m:_NL,n:_NM,o:_NN,p:_NO,q:_NP,r:_NQ,s:_NR,t:_NS,u:_NT};}else{var _NV=_NU.a,_NW=B(_6k(_sq,_ND)),_NX=B(_4A(_qk,_NV,_NW)),_NY=new T(function(){if(!E(_NX)){return E(_N9);}else{return B(_MK(_qk,_NV,_NW));}});if(!E(_NX)){var _NZ=E(_ND);}else{var _NZ=B(_N6(_NY,_ND));}if(!E(_NX)){var _O0=E(_NE);}else{var _O0=B(_N6(_NY,_NE));}var _O1=_Nz,_O2=_NA,_O3=_NB,_O4=_NC,_O5=_NF,_O6=_NG,_O7=_NH,_O8=_NI,_O9=_NJ,_Oa=_NK,_Ob=_NL,_Oc=_NM,_Od=_NN,_Oe=_NO,_Of=_NP,_Og=_NQ,_Oh=_NR,_Oi=_NS,_Oj=_NT;_Nb=_NU.b;_Nc=_O1;_Nd=_O2;_Ne=_O3;_Nf=_O4;_Ng=_NZ;_Nh=_O0;_Ni=_O5;_Nj=_O6;_Nk=_O7;_Nl=_O8;_Nm=_O9;_Nn=_Oa;_No=_Ob;_Np=_Oc;_Nq=_Od;_Nr=_Oe;_Ns=_Of;_Nt=_Og;_Nu=_Oh;_Nv=_Oi;_Nw=_Oj;return __continue;}})(_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw));if(_Nx!=__continue){return _Nx;}}},_Ok=function(_Ol){var _Om=E(_Ol);if(!_Om._){return new T2(0,_S,_S);}else{var _On=E(_Om.a),_Oo=new T(function(){var _Op=B(_Ok(_Om.b));return new T2(0,_Op.a,_Op.b);});return new T2(0,new T2(1,_On.a,new T(function(){return E(E(_Oo).a);})),new T2(1,_On.b,new T(function(){return E(E(_Oo).b);})));}},_Oq=function(_Or){return new F(function(){return _Lo("Event.hs:103:28-52|(c : d : _)");});},_Os=new T(function(){return B(_Oq(_));}),_Ot=function(_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW){while(1){var _OX=B((function(_OY,_OZ,_P0,_P1,_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb,_Pc,_Pd,_Pe,_Pf,_Pg,_Ph,_Pi,_Pj,_Pk,_Pl,_Pm,_Pn,_Po,_Pp,_Pq){var _Pr=E(_OY);if(!_Pr._){return {_:0,a:E(_OZ),b:E(_P0),c:E(_P1),d:E(_P2),e:E(_P3),f:E(_P4),g:E(_P5),h:E(_P6),i:_P7,j:_P8,k:_P9,l:_Pa,m:E(_Pb),n:_Pc,o:E(_Pd),p:E(_Pe),q:_Pf,r:E(_Pg),s:_Ph,t:E({_:0,a:E(_Pi),b:E(_Pj),c:E(_Pk),d:E(_wB),e:E(_Pm),f:E(_Pn),g:E(_wB),h:E(_Pp)}),u:E(_Pq)};}else{var _Ps=new T(function(){var _Pt=E(_Pr.a);if(!_Pt._){return E(_Os);}else{var _Pu=E(_Pt.b);if(!_Pu._){return E(_Os);}else{var _Pv=_Pu.a,_Pw=_Pu.b,_Px=E(_Pt.a);if(E(_Px)==44){return new T2(0,_S,new T(function(){return E(B(_Hc(44,_Pv,_Pw)).a);}));}else{var _Py=B(_Hc(44,_Pv,_Pw)),_Pz=E(_Py.b);if(!_Pz._){return E(_Os);}else{return new T2(0,new T2(1,_Px,_Py.a),_Pz.a);}}}}}),_PA=_OZ,_PB=_P0,_PC=_P1,_PD=_P2,_PE=_P3,_PF=_P4,_PG=_P5,_PH=_P6,_PI=_P7,_PJ=_P8,_PK=_P9,_PL=_Pa,_PM=B(_q(_Pb,new T2(1,new T2(0,new T(function(){return E(E(_Ps).a);}),new T(function(){return E(E(_Ps).b);})),_S))),_PN=_Pc,_PO=_Pd,_PP=_Pe,_PQ=_Pf,_PR=_Pg,_PS=_Ph,_PT=_Pi,_PU=_Pj,_PV=_Pk,_PW=_Pl,_PX=_Pm,_PY=_Pn,_PZ=_Po,_Q0=_Pp,_Q1=_Pq;_Ou=_Pr.b;_Ov=_PA;_Ow=_PB;_Ox=_PC;_Oy=_PD;_Oz=_PE;_OA=_PF;_OB=_PG;_OC=_PH;_OD=_PI;_OE=_PJ;_OF=_PK;_OG=_PL;_OH=_PM;_OI=_PN;_OJ=_PO;_OK=_PP;_OL=_PQ;_OM=_PR;_ON=_PS;_OO=_PT;_OP=_PU;_OQ=_PV;_OR=_PW;_OS=_PX;_OT=_PY;_OU=_PZ;_OV=_Q0;_OW=_Q1;return __continue;}})(_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW));if(_OX!=__continue){return _OX;}}},_Q2=function(_Q3){return new F(function(){return _Lo("Event.hs:49:27-53|(x\' : y\' : _)");});},_Q4=new T(function(){return B(_Q2(_));}),_Q5=function(_Q6){return new F(function(){return _Lo("Event.hs:50:27-55|(chs : tps : _)");});},_Q7=new T(function(){return B(_Q5(_));}),_Q8=new T(function(){return B(_ed("Event.hs:(47,1)-(53,83)|function putCell"));}),_Q9=function(_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv){while(1){var _Qw=B((function(_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH,_QI,_QJ,_QK,_QL,_QM,_QN,_QO,_QP,_QQ,_QR,_QS){var _QT=E(_Qx);if(!_QT._){return {_:0,a:_Qy,b:_Qz,c:_QA,d:_QB,e:_QC,f:_QD,g:_QE,h:_QF,i:_QG,j:_QH,k:_QI,l:_QJ,m:_QK,n:_QL,o:_QM,p:_QN,q:_QO,r:_QP,s:_QQ,t:_QR,u:_QS};}else{var _QU=E(_QT.b);if(!_QU._){return E(_Q8);}else{var _QV=E(_Qy),_QW=new T(function(){var _QX=E(_QT.a);if(!_QX._){return E(_Q4);}else{var _QY=E(_QX.b);if(!_QY._){return E(_Q4);}else{var _QZ=_QY.a,_R0=_QY.b,_R1=E(_QX.a);if(E(_R1)==44){return new T2(0,_S,new T(function(){return E(B(_Hc(44,_QZ,_R0)).a);}));}else{var _R2=B(_Hc(44,_QZ,_R0)),_R3=E(_R2.b);if(!_R3._){return E(_Q4);}else{return new T2(0,new T2(1,_R1,_R2.a),_R3.a);}}}}}),_R4=B(_Gk(B(_sF(_Gi,new T(function(){return E(E(_QW).b);})))));if(!_R4._){return E(_FG);}else{if(!E(_R4.b)._){var _R5=new T(function(){var _R6=E(_QU.a);if(!_R6._){return E(_Q7);}else{var _R7=E(_R6.b);if(!_R7._){return E(_Q7);}else{var _R8=_R7.a,_R9=_R7.b,_Ra=E(_R6.a);if(E(_Ra)==44){return new T2(0,_S,new T(function(){return E(B(_Hc(44,_R8,_R9)).a);}));}else{var _Rb=B(_Hc(44,_R8,_R9)),_Rc=E(_Rb.b);if(!_Rc._){return E(_Q7);}else{return new T2(0,new T2(1,_Ra,_Rb.a),_Rc.a);}}}}}),_Rd=new T(function(){var _Re=B(_Gk(B(_sF(_Gi,new T(function(){return E(E(_QW).a);})))));if(!_Re._){return E(_FG);}else{if(!E(_Re.b)._){return E(_Re.a);}else{return E(_FH);}}},1),_Rf=_Qz,_Rg=_QA,_Rh=_QB,_Ri=_QC,_Rj=_QD,_Rk=_QE,_Rl=_QF,_Rm=_QG,_Rn=_QH,_Ro=_QI,_Rp=_QJ,_Rq=_QK,_Rr=_QL,_Rs=_QM,_Rt=_QN,_Ru=_QO,_Rv=_QP,_Rw=_QQ,_Rx=_QR,_Ry=_QS;_Qa=_QU.b;_Qb={_:0,a:E(_QV.a),b:E(B(_KX(_Rd,E(_R4.a),new T(function(){return B(_Jo(E(_R5).a));}),new T(function(){return B(_JC(E(_R5).b));}),_QV.b))),c:E(_QV.c),d:_QV.d,e:_QV.e,f:_QV.f,g:E(_QV.g),h:_QV.h,i:E(_QV.i),j:E(_QV.j),k:E(_QV.k)};_Qc=_Rf;_Qd=_Rg;_Qe=_Rh;_Qf=_Ri;_Qg=_Rj;_Qh=_Rk;_Qi=_Rl;_Qj=_Rm;_Qk=_Rn;_Ql=_Ro;_Qm=_Rp;_Qn=_Rq;_Qo=_Rr;_Qp=_Rs;_Qq=_Rt;_Qr=_Ru;_Qs=_Rv;_Qt=_Rw;_Qu=_Rx;_Qv=_Ry;return __continue;}else{return E(_FH);}}}}})(_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv));if(_Qw!=__continue){return _Qw;}}},_Rz=function(_RA){var _RB=E(_RA);if(!_RB._){return new T2(0,_S,_S);}else{var _RC=E(_RB.a),_RD=new T(function(){var _RE=B(_Rz(_RB.b));return new T2(0,_RE.a,_RE.b);});return new T2(0,new T2(1,_RC.a,new T(function(){return E(E(_RD).a);})),new T2(1,_RC.b,new T(function(){return E(E(_RD).b);})));}},_RF=32,_RG=function(_RH,_RI,_RJ,_RK){var _RL=E(_RK);if(!_RL._){return __Z;}else{var _RM=_RL.b;if(!B(_4A(_3L,_RH,_RJ))){var _RN=new T(function(){return B(_RG(new T(function(){return E(_RH)+1|0;}),_RI,_RJ,_RM));});return new T2(1,_RL.a,_RN);}else{var _RO=new T(function(){return B(_RG(new T(function(){return E(_RH)+1|0;}),_RI,_RJ,_RM));});return new T2(1,_RI,_RO);}}},_RP=function(_RQ,_RR){var _RS=E(_RR);if(!_RS._){return __Z;}else{var _RT=new T(function(){var _RU=B(_Rz(_RS.a)),_RV=_RU.a,_RW=new T(function(){return B(_J1(0,_RQ,_RV));});return B(_Gw(B(_RG(_rt,_RF,_RW,_RV)),new T(function(){return B(_J8(0,_Eg,_RW,_RU.b));},1)));});return new T2(1,_RT,new T(function(){return B(_RP(_RQ,_RS.b));}));}},_RX=function(_RY,_RZ){var _S0=E(_RZ);return (_S0._==0)?__Z:new T2(1,_RY,new T(function(){return B(_RX(_S0.a,_S0.b));}));},_S1=new T(function(){return B(unCStr("init"));}),_S2=new T(function(){return B(_nk(_S1));}),_S3=function(_S4,_S5){var _S6=function(_S7){var _S8=E(_S7);if(!_S8._){return __Z;}else{var _S9=new T(function(){return B(_q(new T2(1,_S4,_S),new T(function(){return B(_S6(_S8.b));},1)));},1);return new F(function(){return _q(_S8.a,_S9);});}},_Sa=B(_S6(_S5));if(!_Sa._){return E(_S2);}else{return new F(function(){return _RX(_Sa.a,_Sa.b);});}},_Sb=61,_Sc=46,_Sd=new T(function(){return B(_ed("Event.hs:(93,1)-(99,61)|function makeDecision"));}),_Se=new T(function(){return B(unCStr("sm"));}),_Sf=new T(function(){return B(unCStr("rk"));}),_Sg=new T(function(){return B(unCStr("if"));}),_Sh=new T(function(){return B(unCStr("hm"));}),_Si=new T(function(){return B(unCStr("cleq"));}),_Sj=new T(function(){return B(unCStr("da"));}),_Sk=new T(function(){return B(unCStr("ct"));}),_Sl=function(_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH){var _SI=function(_SJ,_SK){var _SL=function(_SM){if(!B(_qV(_SJ,_Sk))){if(!B(_qV(_SJ,_Sj))){var _SN=function(_SO){if(!B(_qV(_SJ,_Si))){var _SP=function(_SQ){if(!B(_qV(_SJ,_rW))){if(!B(_qV(_SJ,_Sh))){if(!B(_qV(_SJ,_Sg))){if(!B(_qV(_SJ,_Sf))){if(!B(_qV(_SJ,_Se))){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{var _SR=E(_SG);return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E({_:0,a:E(_SR.a),b:E(_SR.b),c:E(_SR.c),d:E(_SR.d),e:E(_SR.e),f:E(_SR.f),g:E(_SR.g),h:E(_wB)}),u:E(_SH)};}}else{return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SK),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}}else{var _SS=E(_SK);if(!_SS._){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{var _ST=_SS.a,_SU=E(_SS.b);if(!_SU._){return E(_Sd);}else{var _SV=_SU.a,_SW=B(_Ok(_St)),_SX=_SW.a,_SY=_SW.b,_SZ=function(_T0){if(!B(_4A(_qk,_ST,_SX))){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{if(!B(_qV(_SV,B(_6X(_SY,B(_MK(_qk,_ST,_SX))))))){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{return new F(function(){return _Sl(_T0,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}}},_T1=B(_S3(_Sc,_SU.b));if(!_T1._){return new F(function(){return _SZ(_S);});}else{var _T2=_T1.a,_T3=E(_T1.b);if(!_T3._){return new F(function(){return _SZ(new T2(1,_T2,_S));});}else{var _T4=_T3.a,_T5=_T3.b,_T6=E(_T2);if(E(_T6)==47){if(!B(_4A(_qk,_ST,_SX))){return new F(function(){return _Sl(B(_Hc(47,_T4,_T5)).a,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}else{if(!B(_qV(_SV,B(_6X(_SY,B(_MK(_qk,_ST,_SX))))))){return new F(function(){return _Sl(B(_Hc(47,_T4,_T5)).a,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}else{return new F(function(){return _Sl(_S,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}}}else{if(!B(_4A(_qk,_ST,_SX))){var _T7=E(B(_Hc(47,_T4,_T5)).b);if(!_T7._){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{return new F(function(){return _Sl(_T7.a,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}}else{if(!B(_qV(_SV,B(_6X(_SY,B(_MK(_qk,_ST,_SX))))))){var _T8=E(B(_Hc(47,_T4,_T5)).b);if(!_T8._){return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}else{return new F(function(){return _Sl(_T8.a,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}}else{return new F(function(){return _Sl(new T2(1,_T6,new T(function(){return E(B(_Hc(47,_T4,_T5)).a);})),_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH);});}}}}}}}}}else{var _T9=E(_SG);return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E({_:0,a:E(_T9.a),b:E(_T9.b),c:E(_T9.c),d:E(_T9.d),e:E(_T9.e),f:E(_T9.f),g:E(_T9.g),h:E(_wA)}),u:E(_SH)};}}else{var _Ta=E(_SG);return new F(function(){return _Ot(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_S,_SA,_SB,_SC,_SD,_SE,_SF,_Ta.a,_Ta.b,_Ta.c,_Ta.d,_Ta.e,_Ta.f,_Ta.g,_Ta.h,_SH);});}},_Tb=E(_SJ);if(!_Tb._){return new F(function(){return _SP(_);});}else{if(E(_Tb.a)==109){if(!E(_Tb.b)._){var _Tc=B(_Hp(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Tc.a),b:E(_Tc.b),c:E(_Tc.c),d:E(_Tc.d),e:E(_Tc.e),f:E(_Tc.f),g:E(_Tc.g),h:E(_Tc.h),i:_Tc.i,j:_Tc.j,k:_Tc.k,l:_Tc.l,m:E(_Tc.m),n:_Tc.n,o:E(_Tc.o),p:E(_Tc.p),q:_Tc.q,r:E(_Tc.r),s:_Tc.s,t:E(_Tc.t),u:E(_Tc.u)};}else{return new F(function(){return _SP(_);});}}else{return new F(function(){return _SP(_);});}}}else{var _Td=E(_Sn);return {_:0,a:E({_:0,a:E(_Td.a),b:E(B(_RP(_Sb,_Td.b))),c:E(_Td.c),d:_Td.d,e:_Td.e,f:_Td.f,g:E(_Td.g),h:_Td.h,i:E(_Td.i),j:E(_Td.j),k:E(_Td.k)}),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_Sr),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}},_Te=E(_SJ);if(!_Te._){return new F(function(){return _SN(_);});}else{var _Tf=_Te.b;switch(E(_Te.a)){case 99:if(!E(_Tf)._){var _Tg=B(_Lt(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Tg.a),b:E(_Tg.b),c:E(_Tg.c),d:E(_Tg.d),e:E(_Tg.e),f:E(_Tg.f),g:E(_Tg.g),h:E(_Tg.h),i:_Tg.i,j:_Tg.j,k:_Tg.k,l:_Tg.l,m:E(_Tg.m),n:_Tg.n,o:E(_Tg.o),p:E(_Tg.p),q:_Tg.q,r:E(_Tg.r),s:_Tg.s,t:E(_Tg.t),u:E(_Tg.u)};}else{return new F(function(){return _SN(_);});}break;case 112:if(!E(_Tf)._){var _Th=B(_Q9(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Th.a),b:E(_Th.b),c:E(_Th.c),d:E(_Th.d),e:E(_Th.e),f:E(_Th.f),g:E(_Th.g),h:E(_Th.h),i:_Th.i,j:_Th.j,k:_Th.k,l:_Th.l,m:E(_Th.m),n:_Th.n,o:E(_Th.o),p:E(_Th.p),q:_Th.q,r:E(_Th.r),s:_Th.s,t:E(_Th.t),u:E(_Th.u)};}else{return new F(function(){return _SN(_);});}break;default:return new F(function(){return _SN(_);});}}}else{return {_:0,a:E(_Sn),b:E(_So),c:E(_Sp),d:E(_Sq),e:E(_S),f:E(_Ss),g:E(_St),h:E(_Su),i:_Sv,j:_Sw,k:_Sx,l:_Sy,m:E(_Sz),n:_SA,o:E(_SB),p:E(_SC),q:_SD,r:E(_SE),s:_SF,t:E(_SG),u:E(_SH)};}}else{var _Ti=B(_JE(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Ti.a),b:E(_Ti.b),c:E(_Ti.c),d:E(_Ti.d),e:E(_Ti.e),f:E(_Ti.f),g:E(_Ti.g),h:E(_Ti.h),i:_Ti.i,j:_Ti.j,k:_Ti.k,l:_Ti.l,m:E(_Ti.m),n:_Ti.n,o:E(_Ti.o),p:E(_Ti.p),q:_Ti.q,r:E(_Ti.r),s:_Ti.s,t:E(_Ti.t),u:E(_Ti.u)};}},_Tj=E(_SJ);if(!_Tj._){return new F(function(){return _SL(_);});}else{var _Tk=_Tj.b;switch(E(_Tj.a)){case 100:if(!E(_Tk)._){var _Tl=B(_Na(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Tl.a),b:E(_Tl.b),c:E(_Tl.c),d:E(_Tl.d),e:E(_Tl.e),f:E(_Tl.f),g:E(_Tl.g),h:E(_Tl.h),i:_Tl.i,j:_Tl.j,k:_Tl.k,l:_Tl.l,m:E(_Tl.m),n:_Tl.n,o:E(_Tl.o),p:E(_Tl.p),q:_Tl.q,r:E(_Tl.r),s:_Tl.s,t:E(_Tl.t),u:E(_Tl.u)};}else{return new F(function(){return _SL(_);});}break;case 101:if(!E(_Tk)._){var _Tm=B(_qn(_SK,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC,_SD,_SE,_SF,_SG,_SH));return {_:0,a:E(_Tm.a),b:E(_Tm.b),c:E(_Tm.c),d:E(_Tm.d),e:E(_Tm.e),f:E(_Tm.f),g:E(_Tm.g),h:E(_Tm.h),i:_Tm.i,j:_Tm.j,k:_Tm.k,l:_Tm.l,m:E(_Tm.m),n:_Tm.n,o:E(_Tm.o),p:E(_Tm.p),q:_Tm.q,r:E(_Tm.r),s:_Tm.s,t:E(_Tm.t),u:E(_Tm.u)};}else{return new F(function(){return _SL(_);});}break;default:return new F(function(){return _SL(_);});}}},_Tn=E(_Sm);if(!_Tn._){return new F(function(){return _SI(_S,_S);});}else{var _To=_Tn.a,_Tp=E(_Tn.b);if(!_Tp._){return new F(function(){return _SI(new T2(1,_To,_S),_S);});}else{var _Tq=E(_To),_Tr=new T(function(){var _Ts=B(_Hc(46,_Tp.a,_Tp.b));return new T2(0,_Ts.a,_Ts.b);});if(E(_Tq)==46){return new F(function(){return _SI(_S,new T2(1,new T(function(){return E(E(_Tr).a);}),new T(function(){return E(E(_Tr).b);})));});}else{return new F(function(){return _SI(new T2(1,_Tq,new T(function(){return E(E(_Tr).a);})),new T(function(){return E(E(_Tr).b);}));});}}}},_Tt=new T(function(){return B(unCStr("last"));}),_Tu=new T(function(){return B(_nk(_Tt));}),_Tv=32,_Tw=0,_Tx=65306,_Ty=125,_Tz=new T1(0,1),_TA=function(_TB,_TC,_TD,_TE,_TF){var _TG=new T(function(){return E(_TF).i;}),_TH=new T(function(){return E(E(_TF).c);}),_TI=new T(function(){var _TJ=E(_TG)+1|0;if(0>=_TJ){return E(_Tv);}else{var _TK=B(_pU(_TJ,_TH));if(!_TK._){return E(_Tv);}else{return B(_og(_TK.a,_TK.b,_Tu));}}}),_TL=new T(function(){var _TM=E(_TI);switch(E(_TM)){case 125:return E(_Tv);break;case 12289:return E(_Tv);break;case 12290:return E(_Tv);break;default:return E(_TM);}}),_TN=new T(function(){if(E(_TL)==10){return true;}else{return false;}}),_TO=new T(function(){if(!E(_TN)){if(E(_TL)==12300){return E(_jd);}else{return E(_TF).j;}}else{return E(_Tw);}}),_TP=new T(function(){var _TQ=E(_TC)/28,_TR=_TQ&4294967295;if(_TQ>=_TR){return _TR-1|0;}else{return (_TR-1|0)-1|0;}}),_TS=new T(function(){if(!E(E(_TE).h)){return E(_je);}else{return 2+(E(E(E(_TF).b).b)+3|0)|0;}}),_TT=new T(function(){if(!E(_TG)){return new T2(0,_TP,_TS);}else{return E(E(_TF).h);}}),_TU=new T(function(){return E(E(_TT).b);}),_TV=new T(function(){return E(E(_TT).a);}),_TW=new T(function(){if(E(_TL)==65306){return true;}else{return false;}}),_TX=new T(function(){if(!E(_TW)){if(!E(_TN)){var _TY=E(_TU);if((_TY+1)*20<=E(_TD)-10){return new T2(0,_TV,_TY+1|0);}else{return new T2(0,new T(function(){return E(_TV)-1|0;}),_TS);}}else{return new T2(0,new T(function(){return E(_TV)-1|0;}),_TS);}}else{return new T2(0,_TV,_TU);}}),_TZ=new T(function(){if(E(E(_TX).a)==1){if(E(_TV)==1){return false;}else{return true;}}else{return false;}}),_U0=new T(function(){if(!E(_TW)){return __Z;}else{return B(_qc(_Tx,E(_TG),_TH));}}),_U1=new T(function(){if(E(_TL)==123){return true;}else{return false;}}),_U2=new T(function(){if(!E(_U1)){return __Z;}else{return B(_qc(_Ty,E(_TG),_TH));}}),_U3=new T(function(){if(!E(_U1)){var _U4=E(_TF),_U5=E(_TE);if(E(_TI)==12290){var _U6=true;}else{var _U6=false;}return {_:0,a:E(_U4.a),b:E(_U4.b),c:E(_U4.c),d:E(_U4.d),e:E(_U4.e),f:E(_U4.f),g:E(_U4.g),h:E(_U4.h),i:_U4.i,j:_U4.j,k:_U4.k,l:_U4.l,m:E(_U4.m),n:_U4.n,o:E(_U4.o),p:E(_U4.p),q:_U4.q,r:E(_U4.r),s:_U4.s,t:E({_:0,a:E(_U5.a),b:E(_U5.b),c:E(_U5.c),d:E(_U6),e:E(_U5.e),f:E(_U5.f),g:E(_U5.g),h:E(_U5.h)}),u:E(_U4.u)};}else{var _U7=E(_TF),_U8=E(_TE);if(E(_TI)==12290){var _U9=true;}else{var _U9=false;}return B(_Sl(_U2,_U7.a,_U7.b,_U7.c,_U7.d,_U7.e,_U7.f,_U7.g,_U7.h,_U7.i,_U7.j,_U7.k,_U7.l,_U7.m,_U7.n,_U7.o,_U7.p,_U7.q,_U7.r,_U7.s,{_:0,a:E(_U8.a),b:E(_U8.b),c:E(_U8.c),d:E(_U9),e:E(_U8.e),f:E(_U8.f),g:E(_U8.g),h:E(_U8.h)},_U7.u));}}),_Ua=new T(function(){return E(E(_U3).t);}),_Ub=new T(function(){if(!E(_TG)){return E(_Tw);}else{return E(_U3).k;}}),_Uc=new T(function(){var _Ud=E(_U3),_Ue=_Ud.a,_Uf=_Ud.b,_Ug=_Ud.c,_Uh=_Ud.d,_Ui=_Ud.e,_Uj=_Ud.f,_Uk=_Ud.g,_Ul=_Ud.l,_Um=_Ud.m,_Un=_Ud.n,_Uo=_Ud.o,_Up=_Ud.p,_Uq=_Ud.q,_Ur=_Ud.r,_Us=_Ud.s,_Ut=_Ud.u;if(!E(_TZ)){var _Uu=E(_TX);}else{var _Uu=new T2(0,_TV,_TS);}var _Uv=E(_TG),_Uw=function(_Ux){var _Uy=B(_mz(_TH,0))-1|0,_Uz=function(_UA){var _UB=E(_TO);if(!E(_TZ)){var _UC=E(_Ua);return {_:0,a:E(_Ue),b:E(_Uf),c:E(_Ug),d:E(_Uh),e:E(_Ui),f:E(_Uj),g:E(_Uk),h:E(_Uu),i:_UA,j:_UB,k:E(_Ub),l:_Ul,m:E(_Um),n:_Un,o:E(_Uo),p:E(_Up),q:_Uq,r:E(_Ur),s:_Us,t:E({_:0,a:E(_UC.a),b:E(_UC.b),c:(_Uv+_Ux|0)<=_Uy,d:E(_UC.d),e:E(_UC.e),f:E(_UC.f),g:E(_UC.g),h:E(_UC.h)}),u:E(_Ut)};}else{var _UD=E(_Ua);return {_:0,a:E(_Ue),b:E(_Uf),c:E(_Ug),d:E(_Uh),e:E(_Ui),f:E(_Uj),g:E(_Uk),h:E(_Uu),i:_UA,j:_UB,k:E(_Ub)+1|0,l:_Ul,m:E(_Um),n:_Un,o:E(_Uo),p:E(_Up),q:_Uq,r:E(_Ur),s:_Us,t:E({_:0,a:E(_UD.a),b:E(_UD.b),c:(_Uv+_Ux|0)<=_Uy,d:E(_UD.d),e:E(_UD.e),f:E(_UD.f),g:E(_UD.g),h:E(_UD.h)}),u:E(_Ut)};}};if((_Uv+_Ux|0)<=_Uy){return new F(function(){return _Uz(_Uv+_Ux|0);});}else{return new F(function(){return _Uz(0);});}};if(!E(_TW)){if(!E(_U1)){return B(_Uw(1));}else{return B(_Uw(B(_mz(_U2,0))+2|0));}}else{return B(_Uw(B(_mz(_U0,0))+2|0));}}),_UE=new T(function(){var _UF=B(_oa(B(_o8(_TB)))),_UG=new T(function(){var _UH=B(_pB(_TB,E(_TC)/16)),_UI=_UH.a;if(E(_UH.b)>=0){return E(_UI);}else{return B(A3(_oN,_UF,_UI,new T(function(){return B(A2(_hk,_UF,_Tz));})));}});return B(A3(_oN,_UF,_UG,new T(function(){return B(A2(_hk,_UF,_ht));})));});return {_:0,a:_TL,b:_TV,c:_TU,d:new T(function(){if(E(_TS)!=E(_TU)){return E(_TV);}else{return E(_TV)+1|0;}}),e:new T(function(){var _UJ=E(_TU);if(E(_TS)!=_UJ){return _UJ-1|0;}else{var _UK=(E(_TD)-10)/20,_UL=_UK&4294967295;if(_UK>=_UL){return _UL;}else{return _UL-1|0;}}}),f:_TS,g:_TG,h:_TH,i:new T(function(){return B(_6X(_ja,E(_TO)));}),j:_U0,k:_TP,l:_UE,m:_Ub,n:_jf,o:_TW,p:_U1,q:_TZ,r:_Ua,s:_U3,t:_Uc};},_UM=function(_UN){var _UO=E(_UN);if(!_UO._){return new T2(0,_S,_S);}else{var _UP=E(_UO.a),_UQ=new T(function(){var _UR=B(_UM(_UO.b));return new T2(0,_UR.a,_UR.b);});return new T2(0,new T2(1,_UP.a,new T(function(){return E(E(_UQ).a);})),new T2(1,_UP.b,new T(function(){return E(E(_UQ).b);})));}},_US=42,_UT=32,_UU=function(_UV,_UW,_UX){var _UY=E(_UV);if(!_UY._){return __Z;}else{var _UZ=_UY.a,_V0=_UY.b;if(_UW!=_UX){var _V1=E(_UZ);return (_V1._==0)?E(_nn):(E(_V1.a)==42)?new T2(1,new T2(1,_UT,_V1.b),new T(function(){return B(_UU(_V0,_UW,_UX+1|0));})):new T2(1,new T2(1,_UT,_V1),new T(function(){return B(_UU(_V0,_UW,_UX+1|0));}));}else{var _V2=E(_UZ);return (_V2._==0)?E(_nn):(E(_V2.a)==42)?new T2(1,new T2(1,_UT,_V2),new T(function(){return B(_UU(_V0,_UW,_UX+1|0));})):new T2(1,new T2(1,_US,_V2),new T(function(){return B(_UU(_V0,_UW,_UX+1|0));}));}}},_V3=new T(function(){return B(unCStr("\n\n"));}),_V4=function(_V5){var _V6=E(_V5);if(!_V6._){return __Z;}else{var _V7=new T(function(){return B(_q(_V3,new T(function(){return B(_V4(_V6.b));},1)));},1);return new F(function(){return _q(_V6.a,_V7);});}},_V8=function(_V9,_Va,_Vb){var _Vc=new T(function(){var _Vd=new T(function(){var _Ve=E(_Va);if(!_Ve._){return B(_V4(_S));}else{var _Vf=_Ve.a,_Vg=_Ve.b,_Vh=E(_Vb);if(!_Vh){var _Vi=E(_Vf);if(!_Vi._){return E(_nn);}else{if(E(_Vi.a)==42){return B(_V4(new T2(1,new T2(1,_UT,_Vi),new T(function(){return B(_UU(_Vg,0,1));}))));}else{return B(_V4(new T2(1,new T2(1,_US,_Vi),new T(function(){return B(_UU(_Vg,0,1));}))));}}}else{var _Vj=E(_Vf);if(!_Vj._){return E(_nn);}else{if(E(_Vj.a)==42){return B(_V4(new T2(1,new T2(1,_UT,_Vj.b),new T(function(){return B(_UU(_Vg,_Vh,1));}))));}else{return B(_V4(new T2(1,new T2(1,_UT,_Vj),new T(function(){return B(_UU(_Vg,_Vh,1));}))));}}}}});return B(unAppCStr("\n\n",_Vd));},1);return new F(function(){return _q(_V9,_Vc);});},_Vk=function(_Vl){return E(E(_Vl).c);},_Vm=function(_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv){var _Vw=new T(function(){if(!E(_Vo)){return E(_Vp);}else{return false;}}),_Vx=new T(function(){if(!E(_Vo)){return false;}else{return E(E(_Vu).g);}}),_Vy=new T(function(){if(!E(_Vx)){if(!E(_Vw)){return B(A2(_hk,_Vn,_hs));}else{return B(A3(_mE,_Vn,new T(function(){return B(A3(_mE,_Vn,_Vs,_Vt));}),new T(function(){return B(A2(_hk,_Vn,_Tz));})));}}else{return B(A3(_mE,_Vn,_Vs,_Vt));}}),_Vz=new T(function(){if(!E(_Vx)){if(!E(_Vw)){return __Z;}else{var _VA=E(_Vq)+1|0;if(0>=_VA){return __Z;}else{return B(_pU(_VA,_Vr));}}}else{return B(_V8(B(_Vk(_Vv)),new T(function(){return E(B(_UM(E(_Vv).m)).a);},1),new T(function(){return E(_Vv).n;},1)));}});return new T4(0,_Vx,_Vw,_Vz,_Vy);},_VB=function(_VC,_VD,_VE){var _VF=E(_VD),_VG=E(_VE),_VH=new T(function(){var _VI=B(_hg(_VC)),_VJ=B(_VB(_VC,_VG,B(A3(_oN,_VI,new T(function(){return B(A3(_mE,_VI,_VG,_VG));}),_VF))));return new T2(1,_VJ.a,_VJ.b);});return new T2(0,_VF,_VH);},_VK=1,_VL=new T(function(){var _VM=B(_VB(_gh,_hS,_VK));return new T2(1,_VM.a,_VM.b);}),_VN=function(_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd,_We,_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_){var _Wv={_:0,a:E(_Wm),b:E(_Wn),c:E(_Wo),d:E(_Wp),e:E(_Wq),f:E(_Wr),g:E(_Ws),h:E(_Wt)};if(!E(_Wo)){return {_:0,a:E({_:0,a:E(_VR),b:E(_VS),c:E(_VT),d:_VU,e:_VV,f:_VW,g:E(_VX),h:_VY,i:E(_VZ),j:E(_W0),k:E(_W1)}),b:E(new T2(0,_W2,_W3)),c:E(_W4),d:E(_W5),e:E(_W6),f:E(_W7),g:E(_W8),h:E(new T2(0,_W9,_Wa)),i:_Wb,j:_Wc,k:_Wd,l:_We,m:E(_Wf),n:_Wg,o:E(_Wh),p:E(_Wi),q:_Wj,r:E(_Wk),s:_Wl,t:E(_Wv),u:E(_Wu)};}else{if(!E(_Wp)){var _Ww=B(_TA(_bY,_VP,_VQ,_Wv,{_:0,a:E({_:0,a:E(_VR),b:E(_VS),c:E(_VT),d:_VU,e:_VV,f:_VW,g:E(_VX),h:_VY,i:E(_VZ),j:E(_W0),k:E(_W1)}),b:E(new T2(0,_W2,_W3)),c:E(_W4),d:E(_W5),e:E(_W6),f:E(_W7),g:E(_W8),h:E(new T2(0,_W9,_Wa)),i:_Wb,j:_Wc,k:_Wd,l:_We,m:E(_Wf),n:_Wg,o:E(_Wh),p:E(_Wi),q:_Wj,r:E(_Wk),s:_Wl,t:E(_Wv),u:E(_Wu)})),_Wx=_Ww.d,_Wy=_Ww.e,_Wz=_Ww.f,_WA=_Ww.i,_WB=_Ww.n,_WC=_Ww.p,_WD=_Ww.q,_WE=_Ww.s,_WF=_Ww.t;if(!E(_Ww.o)){var _WG=B(_Vm(_bt,_WC,_WD,_Ww.g,_Ww.h,_Ww.k,_Ww.m,_Ww.r,_WE)),_WH=_WG.c,_WI=_WG.d,_WJ=function(_){var _WK=function(_){if(!E(_WC)){if(!E(_WD)){var _WL=B(_iH(E(_VO).a,_WA,_jb,_hS,_Ww.b,_Ww.c,_Ww.a,_));return _WF;}else{return _WF;}}else{return _WF;}};if(!E(_WG.b)){return new F(function(){return _WK(_);});}else{var _WM=E(_VO),_WN=_WM.a,_WO=_WM.b,_WP=B(_nW(_WN,_WO,_Ww.l,_WE,_)),_WQ=B(_lu(_WN,_WO,_VQ,0,_Wz,_WI,_Wz,_WH,_));return new F(function(){return _WK(_);});}};if(!E(_WG.a)){return new F(function(){return _WJ(_);});}else{var _WR=B(_jg(_VO,_VQ,0,_Wz,_WI,_Wz,_WH,_));return new F(function(){return _WJ(_);});}}else{var _WS=E(_Ww.j);if(!_WS._){return _WF;}else{var _WT=E(_VL);if(!_WT._){return _WF;}else{var _WU=E(_VO).a,_WV=B(_iH(_WU,_WA,_WB,_WT.a,_Wx,_Wy,_WS.a,_)),_WW=function(_WX,_WY,_){while(1){var _WZ=E(_WX);if(!_WZ._){return _gK;}else{var _X0=E(_WY);if(!_X0._){return _gK;}else{var _X1=B(_iH(_WU,_WA,_WB,_X0.a,_Wx,_Wy,_WZ.a,_));_WX=_WZ.b;_WY=_X0.b;continue;}}}},_X2=B(_WW(_WS.b,_WT.b,_));return _WF;}}}}else{return {_:0,a:E({_:0,a:E(_VR),b:E(_VS),c:E(_VT),d:_VU,e:_VV,f:_VW,g:E(_VX),h:_VY,i:E(_VZ),j:E(_W0),k:E(_W1)}),b:E(new T2(0,_W2,_W3)),c:E(_W4),d:E(_W5),e:E(_W6),f:E(_W7),g:E(_W8),h:E(new T2(0,_W9,_Wa)),i:_Wb,j:_Wc,k:_Wd,l:_We,m:E(_Wf),n:_Wg,o:E(_Wh),p:E(_Wi),q:_Wj,r:E(_Wk),s:_Wl,t:E(_Wv),u:E(_Wu)};}}},_X3=function(_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_XC,_XD,_XE,_XF,_XG,_XH,_XI,_XJ,_XK,_){while(1){var _XL=B(_VN(_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_Xd,_Xe,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_XC,_XD,_XE,_XF,_XG,_XH,_XI,_XJ,_XK,_)),_XM=E(_XL),_XN=_XM.c,_XO=_XM.d,_XP=_XM.e,_XQ=_XM.f,_XR=_XM.g,_XS=_XM.i,_XT=_XM.j,_XU=_XM.k,_XV=_XM.l,_XW=_XM.m,_XX=_XM.n,_XY=_XM.o,_XZ=_XM.p,_Y0=_XM.q,_Y1=_XM.r,_Y2=_XM.s,_Y3=_XM.u,_Y4=E(_XM.t),_Y5=_Y4.a,_Y6=_Y4.b,_Y7=_Y4.c,_Y8=_Y4.e,_Y9=_Y4.g,_Ya=_Y4.h,_Yb=E(_XM.a),_Yc=E(_XM.b),_Yd=E(_XM.h);if(!E(_Y4.d)){if(!E(_XE)){return {_:0,a:E(_Yb),b:E(_Yc),c:E(_XN),d:E(_XO),e:E(_XP),f:E(_XQ),g:E(_XR),h:E(_Yd),i:_XS,j:_XT,k:_XU,l:_XV,m:E(_XW),n:_XX,o:E(_XY),p:E(_XZ),q:_Y0,r:E(_Y1),s:_Y2,t:E({_:0,a:E(_Y5),b:E(_Y6),c:E(_Y7),d:E(_wA),e:E(_Y8),f:E(_wA),g:E(_Y9),h:E(_Ya)}),u:E(_Y3)};}else{_X7=_Yb.a;_X8=_Yb.b;_X9=_Yb.c;_Xa=_Yb.d;_Xb=_Yb.e;_Xc=_Yb.f;_Xd=_Yb.g;_Xe=_Yb.h;_Xf=_Yb.i;_Xg=_Yb.j;_Xh=_Yb.k;_Xi=_Yc.a;_Xj=_Yc.b;_Xk=_XN;_Xl=_XO;_Xm=_XP;_Xn=_XQ;_Xo=_XR;_Xp=_Yd.a;_Xq=_Yd.b;_Xr=_XS;_Xs=_XT;_Xt=_XU;_Xu=_XV;_Xv=_XW;_Xw=_XX;_Xx=_XY;_Xy=_XZ;_Xz=_Y0;_XA=_Y1;_XB=_Y2;_XC=_Y5;_XD=_Y6;_XE=_Y7;_XF=_wA;_XG=_Y8;_XH=_Y4.f;_XI=_Y9;_XJ=_Ya;_XK=_Y3;continue;}}else{return {_:0,a:E(_Yb),b:E(_Yc),c:E(_XN),d:E(_XO),e:E(_XP),f:E(_XQ),g:E(_XR),h:E(_Yd),i:_XS,j:_XT,k:_XU,l:_XV,m:E(_XW),n:_XX,o:E(_XY),p:E(_XZ),q:_Y0,r:E(_Y1),s:_Y2,t:E({_:0,a:E(_Y5),b:E(_Y6),c:E(_Y7),d:E(_wB),e:E(_Y8),f:E(_wA),g:E(_Y9),h:E(_Ya)}),u:E(_Y3)};}}},_Ye=function(_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_){var _YV=B(_VN(_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_wB,_YP,_YQ,_YR,_YS,_YT,_YU,_)),_YW=E(_YV),_YX=_YW.c,_YY=_YW.d,_YZ=_YW.e,_Z0=_YW.f,_Z1=_YW.g,_Z2=_YW.i,_Z3=_YW.j,_Z4=_YW.k,_Z5=_YW.l,_Z6=_YW.m,_Z7=_YW.n,_Z8=_YW.o,_Z9=_YW.p,_Za=_YW.q,_Zb=_YW.r,_Zc=_YW.s,_Zd=_YW.u,_Ze=E(_YW.t),_Zf=_Ze.a,_Zg=_Ze.b,_Zh=_Ze.c,_Zi=_Ze.e,_Zj=_Ze.g,_Zk=_Ze.h,_Zl=E(_YW.a),_Zm=E(_YW.b),_Zn=E(_YW.h);if(!E(_Ze.d)){return new F(function(){return _X3(_Yf,_Yg,_Yh,_Zl.a,_Zl.b,_Zl.c,_Zl.d,_Zl.e,_Zl.f,_Zl.g,_Zl.h,_Zl.i,_Zl.j,_Zl.k,_Zm.a,_Zm.b,_YX,_YY,_YZ,_Z0,_Z1,_Zn.a,_Zn.b,_Z2,_Z3,_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za,_Zb,_Zc,_Zf,_Zg,_Zh,_wA,_Zi,_Ze.f,_Zj,_Zk,_Zd,_);});}else{return {_:0,a:E(_Zl),b:E(_Zm),c:E(_YX),d:E(_YY),e:E(_YZ),f:E(_Z0),g:E(_Z1),h:E(_Zn),i:_Z2,j:_Z3,k:_Z4,l:_Z5,m:E(_Z6),n:_Z7,o:E(_Z8),p:E(_Z9),q:_Za,r:E(_Zb),s:_Zc,t:E({_:0,a:E(_Zf),b:E(_Zg),c:E(_Zh),d:E(_wB),e:E(_Zi),f:E(_wA),g:E(_Zj),h:E(_Zk)}),u:E(_Zd)};}},_Zo=function(_Zp,_Zq){while(1){var _Zr=E(_Zp);if(!_Zr._){return (E(_Zq)._==0)?1:0;}else{var _Zs=E(_Zq);if(!_Zs._){return 2;}else{var _Zt=E(_Zr.a),_Zu=E(_Zs.a);if(_Zt!=_Zu){return (_Zt>_Zu)?2:0;}else{_Zp=_Zr.b;_Zq=_Zs.b;continue;}}}}},_Zv=new T0(1),_Zw=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Zx=function(_Zy){return new F(function(){return err(_Zw);});},_Zz=new T(function(){return B(_Zx(_));}),_ZA=function(_ZB,_ZC,_ZD,_ZE){var _ZF=E(_ZD);if(!_ZF._){var _ZG=_ZF.a,_ZH=E(_ZE);if(!_ZH._){var _ZI=_ZH.a,_ZJ=_ZH.b,_ZK=_ZH.c;if(_ZI<=(imul(3,_ZG)|0)){return new T5(0,(1+_ZG|0)+_ZI|0,E(_ZB),_ZC,E(_ZF),E(_ZH));}else{var _ZL=E(_ZH.d);if(!_ZL._){var _ZM=_ZL.a,_ZN=_ZL.b,_ZO=_ZL.c,_ZP=_ZL.d,_ZQ=E(_ZH.e);if(!_ZQ._){var _ZR=_ZQ.a;if(_ZM>=(imul(2,_ZR)|0)){var _ZS=function(_ZT){var _ZU=E(_ZB),_ZV=E(_ZL.e);return (_ZV._==0)?new T5(0,(1+_ZG|0)+_ZI|0,E(_ZN),_ZO,E(new T5(0,(1+_ZG|0)+_ZT|0,E(_ZU),_ZC,E(_ZF),E(_ZP))),E(new T5(0,(1+_ZR|0)+_ZV.a|0,E(_ZJ),_ZK,E(_ZV),E(_ZQ)))):new T5(0,(1+_ZG|0)+_ZI|0,E(_ZN),_ZO,E(new T5(0,(1+_ZG|0)+_ZT|0,E(_ZU),_ZC,E(_ZF),E(_ZP))),E(new T5(0,1+_ZR|0,E(_ZJ),_ZK,E(_Zv),E(_ZQ))));},_ZW=E(_ZP);if(!_ZW._){return new F(function(){return _ZS(_ZW.a);});}else{return new F(function(){return _ZS(0);});}}else{return new T5(0,(1+_ZG|0)+_ZI|0,E(_ZJ),_ZK,E(new T5(0,(1+_ZG|0)+_ZM|0,E(_ZB),_ZC,E(_ZF),E(_ZL))),E(_ZQ));}}else{return E(_Zz);}}else{return E(_Zz);}}}else{return new T5(0,1+_ZG|0,E(_ZB),_ZC,E(_ZF),E(_Zv));}}else{var _ZX=E(_ZE);if(!_ZX._){var _ZY=_ZX.a,_ZZ=_ZX.b,_100=_ZX.c,_101=_ZX.e,_102=E(_ZX.d);if(!_102._){var _103=_102.a,_104=_102.b,_105=_102.c,_106=_102.d,_107=E(_101);if(!_107._){var _108=_107.a;if(_103>=(imul(2,_108)|0)){var _109=function(_10a){var _10b=E(_ZB),_10c=E(_102.e);return (_10c._==0)?new T5(0,1+_ZY|0,E(_104),_105,E(new T5(0,1+_10a|0,E(_10b),_ZC,E(_Zv),E(_106))),E(new T5(0,(1+_108|0)+_10c.a|0,E(_ZZ),_100,E(_10c),E(_107)))):new T5(0,1+_ZY|0,E(_104),_105,E(new T5(0,1+_10a|0,E(_10b),_ZC,E(_Zv),E(_106))),E(new T5(0,1+_108|0,E(_ZZ),_100,E(_Zv),E(_107))));},_10d=E(_106);if(!_10d._){return new F(function(){return _109(_10d.a);});}else{return new F(function(){return _109(0);});}}else{return new T5(0,1+_ZY|0,E(_ZZ),_100,E(new T5(0,1+_103|0,E(_ZB),_ZC,E(_Zv),E(_102))),E(_107));}}else{return new T5(0,3,E(_104),_105,E(new T5(0,1,E(_ZB),_ZC,E(_Zv),E(_Zv))),E(new T5(0,1,E(_ZZ),_100,E(_Zv),E(_Zv))));}}else{var _10e=E(_101);return (_10e._==0)?new T5(0,3,E(_ZZ),_100,E(new T5(0,1,E(_ZB),_ZC,E(_Zv),E(_Zv))),E(_10e)):new T5(0,2,E(_ZB),_ZC,E(_Zv),E(_ZX));}}else{return new T5(0,1,E(_ZB),_ZC,E(_Zv),E(_Zv));}}},_10f=function(_10g,_10h){return new T5(0,1,E(_10g),_10h,E(_Zv),E(_Zv));},_10i=function(_10j,_10k,_10l){var _10m=E(_10l);if(!_10m._){return new F(function(){return _ZA(_10m.b,_10m.c,_10m.d,B(_10i(_10j,_10k,_10m.e)));});}else{return new F(function(){return _10f(_10j,_10k);});}},_10n=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_10o=function(_10p){return new F(function(){return err(_10n);});},_10q=new T(function(){return B(_10o(_));}),_10r=function(_10s,_10t,_10u,_10v){var _10w=E(_10v);if(!_10w._){var _10x=_10w.a,_10y=E(_10u);if(!_10y._){var _10z=_10y.a,_10A=_10y.b,_10B=_10y.c;if(_10z<=(imul(3,_10x)|0)){return new T5(0,(1+_10z|0)+_10x|0,E(_10s),_10t,E(_10y),E(_10w));}else{var _10C=E(_10y.d);if(!_10C._){var _10D=_10C.a,_10E=E(_10y.e);if(!_10E._){var _10F=_10E.a,_10G=_10E.b,_10H=_10E.c,_10I=_10E.d;if(_10F>=(imul(2,_10D)|0)){var _10J=function(_10K){var _10L=E(_10E.e);return (_10L._==0)?new T5(0,(1+_10z|0)+_10x|0,E(_10G),_10H,E(new T5(0,(1+_10D|0)+_10K|0,E(_10A),_10B,E(_10C),E(_10I))),E(new T5(0,(1+_10x|0)+_10L.a|0,E(_10s),_10t,E(_10L),E(_10w)))):new T5(0,(1+_10z|0)+_10x|0,E(_10G),_10H,E(new T5(0,(1+_10D|0)+_10K|0,E(_10A),_10B,E(_10C),E(_10I))),E(new T5(0,1+_10x|0,E(_10s),_10t,E(_Zv),E(_10w))));},_10M=E(_10I);if(!_10M._){return new F(function(){return _10J(_10M.a);});}else{return new F(function(){return _10J(0);});}}else{return new T5(0,(1+_10z|0)+_10x|0,E(_10A),_10B,E(_10C),E(new T5(0,(1+_10x|0)+_10F|0,E(_10s),_10t,E(_10E),E(_10w))));}}else{return E(_10q);}}else{return E(_10q);}}}else{return new T5(0,1+_10x|0,E(_10s),_10t,E(_Zv),E(_10w));}}else{var _10N=E(_10u);if(!_10N._){var _10O=_10N.a,_10P=_10N.b,_10Q=_10N.c,_10R=_10N.e,_10S=E(_10N.d);if(!_10S._){var _10T=_10S.a,_10U=E(_10R);if(!_10U._){var _10V=_10U.a,_10W=_10U.b,_10X=_10U.c,_10Y=_10U.d;if(_10V>=(imul(2,_10T)|0)){var _10Z=function(_110){var _111=E(_10U.e);return (_111._==0)?new T5(0,1+_10O|0,E(_10W),_10X,E(new T5(0,(1+_10T|0)+_110|0,E(_10P),_10Q,E(_10S),E(_10Y))),E(new T5(0,1+_111.a|0,E(_10s),_10t,E(_111),E(_Zv)))):new T5(0,1+_10O|0,E(_10W),_10X,E(new T5(0,(1+_10T|0)+_110|0,E(_10P),_10Q,E(_10S),E(_10Y))),E(new T5(0,1,E(_10s),_10t,E(_Zv),E(_Zv))));},_112=E(_10Y);if(!_112._){return new F(function(){return _10Z(_112.a);});}else{return new F(function(){return _10Z(0);});}}else{return new T5(0,1+_10O|0,E(_10P),_10Q,E(_10S),E(new T5(0,1+_10V|0,E(_10s),_10t,E(_10U),E(_Zv))));}}else{return new T5(0,3,E(_10P),_10Q,E(_10S),E(new T5(0,1,E(_10s),_10t,E(_Zv),E(_Zv))));}}else{var _113=E(_10R);return (_113._==0)?new T5(0,3,E(_113.b),_113.c,E(new T5(0,1,E(_10P),_10Q,E(_Zv),E(_Zv))),E(new T5(0,1,E(_10s),_10t,E(_Zv),E(_Zv)))):new T5(0,2,E(_10s),_10t,E(_10N),E(_Zv));}}else{return new T5(0,1,E(_10s),_10t,E(_Zv),E(_Zv));}}},_114=function(_115,_116,_117){var _118=E(_117);if(!_118._){return new F(function(){return _10r(_118.b,_118.c,B(_114(_115,_116,_118.d)),_118.e);});}else{return new F(function(){return _10f(_115,_116);});}},_119=function(_11a,_11b,_11c,_11d,_11e,_11f,_11g){return new F(function(){return _10r(_11d,_11e,B(_114(_11a,_11b,_11f)),_11g);});},_11h=function(_11i,_11j,_11k,_11l,_11m,_11n,_11o,_11p){var _11q=E(_11k);if(!_11q._){var _11r=_11q.a,_11s=_11q.b,_11t=_11q.c,_11u=_11q.d,_11v=_11q.e;if((imul(3,_11r)|0)>=_11l){if((imul(3,_11l)|0)>=_11r){return new T5(0,(_11r+_11l|0)+1|0,E(_11i),_11j,E(_11q),E(new T5(0,_11l,E(_11m),_11n,E(_11o),E(_11p))));}else{return new F(function(){return _ZA(_11s,_11t,_11u,B(_11h(_11i,_11j,_11v,_11l,_11m,_11n,_11o,_11p)));});}}else{return new F(function(){return _10r(_11m,_11n,B(_11w(_11i,_11j,_11r,_11s,_11t,_11u,_11v,_11o)),_11p);});}}else{return new F(function(){return _119(_11i,_11j,_11l,_11m,_11n,_11o,_11p);});}},_11w=function(_11x,_11y,_11z,_11A,_11B,_11C,_11D,_11E){var _11F=E(_11E);if(!_11F._){var _11G=_11F.a,_11H=_11F.b,_11I=_11F.c,_11J=_11F.d,_11K=_11F.e;if((imul(3,_11z)|0)>=_11G){if((imul(3,_11G)|0)>=_11z){return new T5(0,(_11z+_11G|0)+1|0,E(_11x),_11y,E(new T5(0,_11z,E(_11A),_11B,E(_11C),E(_11D))),E(_11F));}else{return new F(function(){return _ZA(_11A,_11B,_11C,B(_11h(_11x,_11y,_11D,_11G,_11H,_11I,_11J,_11K)));});}}else{return new F(function(){return _10r(_11H,_11I,B(_11w(_11x,_11y,_11z,_11A,_11B,_11C,_11D,_11J)),_11K);});}}else{return new F(function(){return _10i(_11x,_11y,new T5(0,_11z,E(_11A),_11B,E(_11C),E(_11D)));});}},_11L=function(_11M,_11N,_11O,_11P){var _11Q=E(_11O);if(!_11Q._){var _11R=_11Q.a,_11S=_11Q.b,_11T=_11Q.c,_11U=_11Q.d,_11V=_11Q.e,_11W=E(_11P);if(!_11W._){var _11X=_11W.a,_11Y=_11W.b,_11Z=_11W.c,_120=_11W.d,_121=_11W.e;if((imul(3,_11R)|0)>=_11X){if((imul(3,_11X)|0)>=_11R){return new T5(0,(_11R+_11X|0)+1|0,E(_11M),_11N,E(_11Q),E(_11W));}else{return new F(function(){return _ZA(_11S,_11T,_11U,B(_11h(_11M,_11N,_11V,_11X,_11Y,_11Z,_120,_121)));});}}else{return new F(function(){return _10r(_11Y,_11Z,B(_11w(_11M,_11N,_11R,_11S,_11T,_11U,_11V,_120)),_121);});}}else{return new F(function(){return _10i(_11M,_11N,_11Q);});}}else{return new F(function(){return _114(_11M,_11N,_11P);});}},_122=function(_123,_124,_125,_126){var _127=E(_123);if(_127==1){var _128=E(_126);return (_128._==0)?new T3(0,new T(function(){return new T5(0,1,E(_124),_125,E(_Zv),E(_Zv));}),_S,_S):(B(_Zo(_124,E(_128.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_124),_125,E(_Zv),E(_Zv));}),_128,_S):new T3(0,new T(function(){return new T5(0,1,E(_124),_125,E(_Zv),E(_Zv));}),_S,_128);}else{var _129=B(_122(_127>>1,_124,_125,_126)),_12a=_129.a,_12b=_129.c,_12c=E(_129.b);if(!_12c._){return new T3(0,_12a,_S,_12b);}else{var _12d=E(_12c.a),_12e=_12d.a,_12f=_12d.b,_12g=E(_12c.b);if(!_12g._){return new T3(0,new T(function(){return B(_10i(_12e,_12f,_12a));}),_S,_12b);}else{var _12h=E(_12g.a),_12i=_12h.a;if(!B(_Zo(_12e,_12i))){var _12j=B(_122(_127>>1,_12i,_12h.b,_12g.b));return new T3(0,new T(function(){return B(_11L(_12e,_12f,_12a,_12j.a));}),_12j.b,_12j.c);}else{return new T3(0,_12a,_S,_12c);}}}}},_12k=function(_12l,_12m,_12n){var _12o=E(_12l),_12p=E(_12n);if(!_12p._){var _12q=_12p.b,_12r=_12p.c,_12s=_12p.d,_12t=_12p.e;switch(B(_Zo(_12o,_12q))){case 0:return new F(function(){return _10r(_12q,_12r,B(_12k(_12o,_12m,_12s)),_12t);});break;case 1:return new T5(0,_12p.a,E(_12o),_12m,E(_12s),E(_12t));default:return new F(function(){return _ZA(_12q,_12r,_12s,B(_12k(_12o,_12m,_12t)));});}}else{return new T5(0,1,E(_12o),_12m,E(_Zv),E(_Zv));}},_12u=function(_12v,_12w){while(1){var _12x=E(_12w);if(!_12x._){return E(_12v);}else{var _12y=E(_12x.a),_12z=B(_12k(_12y.a,_12y.b,_12v));_12v=_12z;_12w=_12x.b;continue;}}},_12A=function(_12B,_12C,_12D,_12E){return new F(function(){return _12u(B(_12k(_12C,_12D,_12B)),_12E);});},_12F=function(_12G,_12H,_12I){var _12J=E(_12H);return new F(function(){return _12u(B(_12k(_12J.a,_12J.b,_12G)),_12I);});},_12K=function(_12L,_12M,_12N){while(1){var _12O=E(_12N);if(!_12O._){return E(_12M);}else{var _12P=E(_12O.a),_12Q=_12P.a,_12R=_12P.b,_12S=E(_12O.b);if(!_12S._){return new F(function(){return _10i(_12Q,_12R,_12M);});}else{var _12T=E(_12S.a),_12U=_12T.a;if(!B(_Zo(_12Q,_12U))){var _12V=B(_122(_12L,_12U,_12T.b,_12S.b)),_12W=_12V.a,_12X=E(_12V.c);if(!_12X._){var _12Y=_12L<<1,_12Z=B(_11L(_12Q,_12R,_12M,_12W));_12L=_12Y;_12M=_12Z;_12N=_12V.b;continue;}else{return new F(function(){return _12F(B(_11L(_12Q,_12R,_12M,_12W)),_12X.a,_12X.b);});}}else{return new F(function(){return _12A(_12M,_12Q,_12R,_12S);});}}}}},_130=function(_131,_132,_133,_134,_135){var _136=E(_135);if(!_136._){return new F(function(){return _10i(_133,_134,_132);});}else{var _137=E(_136.a),_138=_137.a;if(!B(_Zo(_133,_138))){var _139=B(_122(_131,_138,_137.b,_136.b)),_13a=_139.a,_13b=E(_139.c);if(!_13b._){return new F(function(){return _12K(_131<<1,B(_11L(_133,_134,_132,_13a)),_139.b);});}else{return new F(function(){return _12F(B(_11L(_133,_134,_132,_13a)),_13b.a,_13b.b);});}}else{return new F(function(){return _12A(_132,_133,_134,_136);});}}},_13c=function(_13d){var _13e=E(_13d);if(!_13e._){return new T0(1);}else{var _13f=E(_13e.a),_13g=_13f.a,_13h=_13f.b,_13i=E(_13e.b);if(!_13i._){return new T5(0,1,E(_13g),_13h,E(_Zv),E(_Zv));}else{var _13j=_13i.b,_13k=E(_13i.a),_13l=_13k.a,_13m=_13k.b;if(!B(_Zo(_13g,_13l))){return new F(function(){return _130(1,new T5(0,1,E(_13g),_13h,E(_Zv),E(_Zv)),_13l,_13m,_13j);});}else{return new F(function(){return _12A(new T5(0,1,E(_13g),_13h,E(_Zv),E(_Zv)),_13l,_13m,_13j);});}}}},_13n=function(_13o){var _13p=E(_13o);if(!_13p._){return __Z;}else{var _13q=E(_13p.b);return (_13q._==0)?__Z:new T2(1,new T2(0,_13p.a,_13q.a),new T(function(){return B(_13n(_13q.b));}));}},_13r=function(_13s,_13t,_13u){return new T2(1,new T2(0,_13s,_13t),new T(function(){return B(_13n(_13u));}));},_13v=function(_13w,_13x){var _13y=E(_13x);return (_13y._==0)?__Z:new T2(1,new T2(0,_13w,_13y.a),new T(function(){return B(_13n(_13y.b));}));},_13z="Invalid JSON!",_13A=new T1(0,_13z),_13B="No such value",_13C=new T1(0,_13B),_13D=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_13E=function(_13F){return E(E(_13F).c);},_13G=function(_13H,_13I,_){var _13J=__app1(E(_13D),_13I),_13K=__eq(_13J,E(_3a));if(!E(_13K)){var _13L=__isUndef(_13J);return (E(_13L)==0)?new T(function(){var _13M=String(_13J),_13N=jsParseJSON(_13M);if(!_13N._){return E(_13A);}else{return B(A2(_13E,_13H,_13N.a));}}):_13C;}else{return _13C;}},_13O=new T1(0,0),_13P=function(_13Q,_13R){while(1){var _13S=E(_13Q);if(!_13S._){var _13T=_13S.a,_13U=E(_13R);if(!_13U._){return new T1(0,(_13T>>>0|_13U.a>>>0)>>>0&4294967295);}else{_13Q=new T1(1,I_fromInt(_13T));_13R=_13U;continue;}}else{var _13V=E(_13R);if(!_13V._){_13Q=_13S;_13R=new T1(1,I_fromInt(_13V.a));continue;}else{return new T1(1,I_or(_13S.a,_13V.a));}}}},_13W=function(_13X){var _13Y=E(_13X);if(!_13Y._){return E(_13O);}else{return new F(function(){return _13P(new T1(0,E(_13Y.a)),B(_cU(B(_13W(_13Y.b)),31)));});}},_13Z=function(_140,_141){if(!E(_140)){return new F(function(){return _fz(B(_13W(_141)));});}else{return new F(function(){return _13W(_141);});}},_142=1420103680,_143=465,_144=new T2(1,_143,_S),_145=new T2(1,_142,_144),_146=new T(function(){return B(_13Z(_wB,_145));}),_147=function(_148){return E(_146);},_149=new T(function(){return B(unCStr("s"));}),_14a=function(_14b,_14c){while(1){var _14d=E(_14b);if(!_14d._){return E(_14c);}else{_14b=_14d.b;_14c=_14d.a;continue;}}},_14e=function(_14f,_14g,_14h){return new F(function(){return _14a(_14g,_14f);});},_14i=new T1(0,1),_14j=function(_14k,_14l){var _14m=E(_14k);return new T2(0,_14m,new T(function(){var _14n=B(_14j(B(_cB(_14m,_14l)),_14l));return new T2(1,_14n.a,_14n.b);}));},_14o=function(_14p){var _14q=B(_14j(_14p,_14i));return new T2(1,_14q.a,_14q.b);},_14r=function(_14s,_14t){var _14u=B(_14j(_14s,new T(function(){return B(_eU(_14t,_14s));})));return new T2(1,_14u.a,_14u.b);},_14v=new T1(0,0),_14w=function(_14x,_14y){var _14z=E(_14x);if(!_14z._){var _14A=_14z.a,_14B=E(_14y);return (_14B._==0)?_14A>=_14B.a:I_compareInt(_14B.a,_14A)<=0;}else{var _14C=_14z.a,_14D=E(_14y);return (_14D._==0)?I_compareInt(_14C,_14D.a)>=0:I_compare(_14C,_14D.a)>=0;}},_14E=function(_14F,_14G,_14H){if(!B(_14w(_14G,_14v))){var _14I=function(_14J){return (!B(_dd(_14J,_14H)))?new T2(1,_14J,new T(function(){return B(_14I(B(_cB(_14J,_14G))));})):__Z;};return new F(function(){return _14I(_14F);});}else{var _14K=function(_14L){return (!B(_d4(_14L,_14H)))?new T2(1,_14L,new T(function(){return B(_14K(B(_cB(_14L,_14G))));})):__Z;};return new F(function(){return _14K(_14F);});}},_14M=function(_14N,_14O,_14P){return new F(function(){return _14E(_14N,B(_eU(_14O,_14N)),_14P);});},_14Q=function(_14R,_14S){return new F(function(){return _14E(_14R,_14i,_14S);});},_14T=function(_14U){return new F(function(){return _bg(_14U);});},_14V=function(_14W){return new F(function(){return _eU(_14W,_14i);});},_14X=function(_14Y){return new F(function(){return _cB(_14Y,_14i);});},_14Z=function(_150){return new F(function(){return _aX(E(_150));});},_151={_:0,a:_14X,b:_14V,c:_14Z,d:_14T,e:_14o,f:_14r,g:_14Q,h:_14M},_152=function(_153,_154){while(1){var _155=E(_153);if(!_155._){var _156=E(_155.a);if(_156==( -2147483648)){_153=new T1(1,I_fromInt( -2147483648));continue;}else{var _157=E(_154);if(!_157._){return new T1(0,B(_9p(_156,_157.a)));}else{_153=new T1(1,I_fromInt(_156));_154=_157;continue;}}}else{var _158=_155.a,_159=E(_154);return (_159._==0)?new T1(1,I_div(_158,I_fromInt(_159.a))):new T1(1,I_div(_158,_159.a));}}},_15a=function(_15b,_15c){if(!B(_ct(_15c,_oR))){return new F(function(){return _152(_15b,_15c);});}else{return E(_a0);}},_15d=function(_15e,_15f){while(1){var _15g=E(_15e);if(!_15g._){var _15h=E(_15g.a);if(_15h==( -2147483648)){_15e=new T1(1,I_fromInt( -2147483648));continue;}else{var _15i=E(_15f);if(!_15i._){var _15j=_15i.a;return new T2(0,new T1(0,B(_9p(_15h,_15j))),new T1(0,B(_au(_15h,_15j))));}else{_15e=new T1(1,I_fromInt(_15h));_15f=_15i;continue;}}}else{var _15k=E(_15f);if(!_15k._){_15e=_15g;_15f=new T1(1,I_fromInt(_15k.a));continue;}else{var _15l=I_divMod(_15g.a,_15k.a);return new T2(0,new T1(1,_15l.a),new T1(1,_15l.b));}}}},_15m=function(_15n,_15o){if(!B(_ct(_15o,_oR))){var _15p=B(_15d(_15n,_15o));return new T2(0,_15p.a,_15p.b);}else{return E(_a0);}},_15q=function(_15r,_15s){while(1){var _15t=E(_15r);if(!_15t._){var _15u=E(_15t.a);if(_15u==( -2147483648)){_15r=new T1(1,I_fromInt( -2147483648));continue;}else{var _15v=E(_15s);if(!_15v._){return new T1(0,B(_au(_15u,_15v.a)));}else{_15r=new T1(1,I_fromInt(_15u));_15s=_15v;continue;}}}else{var _15w=_15t.a,_15x=E(_15s);return (_15x._==0)?new T1(1,I_mod(_15w,I_fromInt(_15x.a))):new T1(1,I_mod(_15w,_15x.a));}}},_15y=function(_15z,_15A){if(!B(_ct(_15A,_oR))){return new F(function(){return _15q(_15z,_15A);});}else{return E(_a0);}},_15B=function(_15C,_15D){while(1){var _15E=E(_15C);if(!_15E._){var _15F=E(_15E.a);if(_15F==( -2147483648)){_15C=new T1(1,I_fromInt( -2147483648));continue;}else{var _15G=E(_15D);if(!_15G._){return new T1(0,quot(_15F,_15G.a));}else{_15C=new T1(1,I_fromInt(_15F));_15D=_15G;continue;}}}else{var _15H=_15E.a,_15I=E(_15D);return (_15I._==0)?new T1(0,I_toInt(I_quot(_15H,I_fromInt(_15I.a)))):new T1(1,I_quot(_15H,_15I.a));}}},_15J=function(_15K,_15L){if(!B(_ct(_15L,_oR))){return new F(function(){return _15B(_15K,_15L);});}else{return E(_a0);}},_15M=function(_15N,_15O){if(!B(_ct(_15O,_oR))){var _15P=B(_cK(_15N,_15O));return new T2(0,_15P.a,_15P.b);}else{return E(_a0);}},_15Q=function(_15R,_15S){while(1){var _15T=E(_15R);if(!_15T._){var _15U=E(_15T.a);if(_15U==( -2147483648)){_15R=new T1(1,I_fromInt( -2147483648));continue;}else{var _15V=E(_15S);if(!_15V._){return new T1(0,_15U%_15V.a);}else{_15R=new T1(1,I_fromInt(_15U));_15S=_15V;continue;}}}else{var _15W=_15T.a,_15X=E(_15S);return (_15X._==0)?new T1(1,I_rem(_15W,I_fromInt(_15X.a))):new T1(1,I_rem(_15W,_15X.a));}}},_15Y=function(_15Z,_160){if(!B(_ct(_160,_oR))){return new F(function(){return _15Q(_15Z,_160);});}else{return E(_a0);}},_161=function(_162){return E(_162);},_163=function(_164){return E(_164);},_165=function(_166){var _167=E(_166);if(!_167._){var _168=E(_167.a);return (_168==( -2147483648))?E(_fy):(_168<0)?new T1(0, -_168):E(_167);}else{var _169=_167.a;return (I_compareInt(_169,0)>=0)?E(_167):new T1(1,I_negate(_169));}},_16a=new T1(0, -1),_16b=function(_16c){var _16d=E(_16c);if(!_16d._){var _16e=_16d.a;return (_16e>=0)?(E(_16e)==0)?E(_13O):E(_dc):E(_16a);}else{var _16f=I_compareInt(_16d.a,0);return (_16f<=0)?(E(_16f)==0)?E(_13O):E(_16a):E(_dc);}},_16g={_:0,a:_cB,b:_eU,c:_ol,d:_fz,e:_165,f:_16b,g:_163},_16h=function(_16i,_16j){var _16k=E(_16i);if(!_16k._){var _16l=_16k.a,_16m=E(_16j);return (_16m._==0)?_16l!=_16m.a:(I_compareInt(_16m.a,_16l)==0)?false:true;}else{var _16n=_16k.a,_16o=E(_16j);return (_16o._==0)?(I_compareInt(_16n,_16o.a)==0)?false:true:(I_compare(_16n,_16o.a)==0)?false:true;}},_16p=new T2(0,_ct,_16h),_16q=function(_16r,_16s){return (!B(_eF(_16r,_16s)))?E(_16r):E(_16s);},_16t=function(_16u,_16v){return (!B(_eF(_16u,_16v)))?E(_16v):E(_16u);},_16w={_:0,a:_16p,b:_cd,c:_dd,d:_eF,e:_d4,f:_14w,g:_16q,h:_16t},_16x=function(_16y){return new T2(0,E(_16y),E(_b1));},_16z=new T3(0,_16g,_16w,_16x),_16A={_:0,a:_16z,b:_151,c:_15J,d:_15Y,e:_15a,f:_15y,g:_15M,h:_15m,i:_161},_16B=new T1(0,0),_16C=function(_16D,_16E,_16F){var _16G=B(A1(_16D,_16E));if(!B(_ct(_16G,_16B))){return new F(function(){return _152(B(_ol(_16E,_16F)),_16G);});}else{return E(_a0);}},_16H=function(_16I,_16J){while(1){if(!B(_ct(_16J,_oR))){var _16K=_16J,_16L=B(_15Y(_16I,_16J));_16I=_16K;_16J=_16L;continue;}else{return E(_16I);}}},_16M=5,_16N=new T(function(){return B(_9W(_16M));}),_16O=new T(function(){return die(_16N);}),_16P=function(_16Q,_16R){if(!B(_ct(_16R,_oR))){var _16S=B(_16H(B(_165(_16Q)),B(_165(_16R))));return (!B(_ct(_16S,_oR)))?new T2(0,B(_15B(_16Q,_16S)),B(_15B(_16R,_16S))):E(_a0);}else{return E(_16O);}},_16T=function(_16U,_16V,_16W,_16X){var _16Y=B(_ol(_16V,_16W));return new F(function(){return _16P(B(_ol(B(_ol(_16U,_16X)),B(_16b(_16Y)))),B(_165(_16Y)));});},_16Z=function(_170,_171,_172){var _173=new T(function(){if(!B(_ct(_172,_oR))){var _174=B(_cK(_171,_172));return new T2(0,_174.a,_174.b);}else{return E(_a0);}}),_175=new T(function(){return B(A2(_hk,B(_oa(B(_o8(_170)))),new T(function(){return E(E(_173).a);})));});return new T2(0,_175,new T(function(){return new T2(0,E(E(_173).b),E(_172));}));},_176=function(_177,_178,_179){var _17a=B(_16Z(_177,_178,_179)),_17b=_17a.a,_17c=E(_17a.b);if(!B(_dd(B(_ol(_17c.a,_b1)),B(_ol(_oR,_17c.b))))){return E(_17b);}else{var _17d=B(_oa(B(_o8(_177))));return new F(function(){return A3(_oN,_17d,_17b,new T(function(){return B(A2(_hk,_17d,_b1));}));});}},_17e=479723520,_17f=40233135,_17g=new T2(1,_17f,_S),_17h=new T2(1,_17e,_17g),_17i=new T(function(){return B(_13Z(_wB,_17h));}),_17j=new T1(0,40587),_17k=function(_17l){var _17m=new T(function(){var _17n=B(_16T(_17l,_b1,_146,_b1)),_17o=B(_16T(_17i,_b1,_146,_b1)),_17p=B(_16T(_17n.a,_17n.b,_17o.a,_17o.b));return B(_176(_16A,_17p.a,_17p.b));});return new T2(0,new T(function(){return B(_cB(_17j,_17m));}),new T(function(){return B(_eU(_17l,B(_16C(_147,B(_ol(_17m,_146)),_17i))));}));},_17q=function(_17r,_){var _17s=__get(_17r,0),_17t=__get(_17r,1),_17u=Number(_17s),_17v=jsTrunc(_17u),_17w=Number(_17t),_17x=jsTrunc(_17w);return new T2(0,_17v,_17x);},_17y=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_17z=660865024,_17A=465661287,_17B=new T2(1,_17A,_S),_17C=new T2(1,_17z,_17B),_17D=new T(function(){return B(_13Z(_wB,_17C));}),_17E=function(_){var _17F=__app0(E(_17y)),_17G=B(_17q(_17F,_));return new T(function(){var _17H=E(_17G);if(!B(_ct(_17D,_16B))){return B(_cB(B(_ol(B(_aX(E(_17H.a))),_146)),B(_152(B(_ol(B(_ol(B(_aX(E(_17H.b))),_146)),_146)),_17D))));}else{return E(_a0);}});},_17I=new T(function(){return B(err(_sA));}),_17J=new T(function(){return B(err(_sy));}),_17K=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_17L=new T1(0,1),_17M=new T1(0,10),_17N=function(_17O){while(1){var _17P=E(_17O);if(!_17P._){_17O=new T1(1,I_fromInt(_17P.a));continue;}else{return new F(function(){return I_toString(_17P.a);});}}},_17Q=function(_17R,_17S){return new F(function(){return _q(fromJSStr(B(_17N(_17R))),_17S);});},_17T=new T1(0,0),_17U=function(_17V,_17W,_17X){if(_17V<=6){return new F(function(){return _17Q(_17W,_17X);});}else{if(!B(_dd(_17W,_17T))){return new F(function(){return _17Q(_17W,_17X);});}else{return new T2(1,_z,new T(function(){return B(_q(fromJSStr(B(_17N(_17W))),new T2(1,_y,_17X)));}));}}},_17Y=function(_17Z){return new F(function(){return _17U(0,_17Z,_S);});},_180=new T(function(){return B(_ct(_17M,_16B));}),_181=function(_182){while(1){if(!B(_ct(_182,_16B))){if(!E(_180)){if(!B(_ct(B(_15q(_182,_17M)),_16B))){return new F(function(){return _17Y(_182);});}else{var _183=B(_152(_182,_17M));_182=_183;continue;}}else{return E(_a0);}}else{return __Z;}}},_184=46,_185=48,_186=function(_187,_188,_189){if(!B(_dd(_189,_16B))){var _18a=B(A1(_187,_189));if(!B(_ct(_18a,_16B))){var _18b=B(_15d(_189,_18a)),_18c=_18b.b,_18d=new T(function(){var _18e=Math.log(B(_fS(_18a)))/Math.log(10),_18f=_18e&4294967295,_18g=function(_18h){if(_18h>=0){var _18i=E(_18h);if(!_18i){var _18j=B(_152(B(_eU(B(_cB(B(_ol(_18c,_b1)),_18a)),_17L)),_18a));}else{var _18j=B(_152(B(_eU(B(_cB(B(_ol(_18c,B(_oB(_17M,_18i)))),_18a)),_17L)),_18a));}var _18k=function(_18l){var _18m=B(_17U(0,_18j,_S)),_18n=_18h-B(_mz(_18m,0))|0;if(0>=_18n){if(!E(_188)){return E(_18m);}else{return new F(function(){return _181(_18j);});}}else{var _18o=new T(function(){if(!E(_188)){return E(_18m);}else{return B(_181(_18j));}}),_18p=function(_18q){var _18r=E(_18q);return (_18r==1)?E(new T2(1,_185,_18o)):new T2(1,_185,new T(function(){return B(_18p(_18r-1|0));}));};return new F(function(){return _18p(_18n);});}};if(!E(_188)){var _18s=B(_18k(_));return (_18s._==0)?__Z:new T2(1,_184,_18s);}else{if(!B(_ct(_18j,_16B))){var _18t=B(_18k(_));return (_18t._==0)?__Z:new T2(1,_184,_18t);}else{return __Z;}}}else{return E(_px);}};if(_18f>=_18e){return B(_18g(_18f));}else{return B(_18g(_18f+1|0));}},1);return new F(function(){return _q(B(_17U(0,_18b.a,_S)),_18d);});}else{return E(_a0);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_186(_187,_188,B(_fz(_189))));}));});}},_18u=function(_18v,_18w,_){var _18x=B(_17E(_)),_18y=new T(function(){var _18z=new T(function(){var _18A=new T(function(){var _18B=B(_q(B(_186(_147,_wB,B(_17k(_18x)).b)),_149));if(!_18B._){return E(_S2);}else{var _18C=B(_RX(_18B.a,_18B.b));if(!_18C._){return B(_14e(_S,_S,_Tu));}else{var _18D=_18C.a,_18E=E(_18C.b);if(!_18E._){return B(_14e(new T2(1,_18D,_S),_S,_Tu));}else{var _18F=E(_18D),_18G=new T(function(){var _18H=B(_Hc(46,_18E.a,_18E.b));return new T2(0,_18H.a,_18H.b);});if(E(_18F)==46){return B(_14e(_S,new T2(1,new T(function(){return E(E(_18G).a);}),new T(function(){return E(E(_18G).b);})),_Tu));}else{return B(_14e(new T2(1,_18F,new T(function(){return E(E(_18G).a);})),new T(function(){return E(E(_18G).b);}),_Tu));}}}}}),_18I=B(_Gk(B(_sF(_17K,_18A))));if(!_18I._){return E(_17J);}else{if(!E(_18I.b)._){return B(_pU(3,B(_A(0,E(_18I.a)+(imul(E(_18w),E(_18v)-1|0)|0)|0,_S))));}else{return E(_17I);}}}),_18J=B(_Gk(B(_sF(_17K,_18z))));if(!_18J._){return E(_17J);}else{if(!E(_18J.b)._){return E(_18J.a);}else{return E(_17I);}}});return new T2(0,new T(function(){return B(_aB(_18y,_18v));}),_18y);},_18K=function(_18L,_18M){while(1){var _18N=E(_18M);if(!_18N._){return __Z;}else{var _18O=_18N.b,_18P=E(_18L);if(_18P==1){return E(_18O);}else{_18L=_18P-1|0;_18M=_18O;continue;}}}},_18Q=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_18R=new T(function(){return B(err(_18Q));}),_18S=0,_18T=function(_18U,_18V,_18W){return new F(function(){return _A(E(_18U),E(_18V),_18W);});},_18X=function(_18Y,_18Z){return new F(function(){return _A(0,E(_18Y),_18Z);});},_190=function(_191,_192){return new F(function(){return _2v(_18X,_191,_192);});},_193=new T3(0,_18T,_6H,_190),_194=0,_195=new T(function(){return B(unCStr(" out of range "));}),_196=new T(function(){return B(unCStr("}.index: Index "));}),_197=new T(function(){return B(unCStr("Ix{"));}),_198=new T2(1,_y,_S),_199=new T2(1,_y,_198),_19a=0,_19b=function(_19c){return E(E(_19c).a);},_19d=function(_19e,_19f,_19g,_19h,_19i){var _19j=new T(function(){var _19k=new T(function(){var _19l=new T(function(){var _19m=new T(function(){var _19n=new T(function(){return B(A3(_sk,_6D,new T2(1,new T(function(){return B(A3(_19b,_19g,_19a,_19h));}),new T2(1,new T(function(){return B(A3(_19b,_19g,_19a,_19i));}),_S)),_199));});return B(_q(_195,new T2(1,_z,new T2(1,_z,_19n))));});return B(A(_19b,[_19g,_194,_19f,new T2(1,_y,_19m)]));});return B(_q(_196,new T2(1,_z,_19l)));},1);return B(_q(_19e,_19k));},1);return new F(function(){return err(B(_q(_197,_19j)));});},_19o=function(_19p,_19q,_19r,_19s,_19t){return new F(function(){return _19d(_19p,_19q,_19t,_19r,_19s);});},_19u=function(_19v,_19w,_19x,_19y){var _19z=E(_19x);return new F(function(){return _19o(_19v,_19w,_19z.a,_19z.b,_19y);});},_19A=function(_19B,_19C,_19D,_19E){return new F(function(){return _19u(_19E,_19D,_19C,_19B);});},_19F=new T(function(){return B(unCStr("Int"));}),_19G=function(_19H,_19I,_19J){return new F(function(){return _19A(_193,new T2(0,_19I,_19J),_19H,_19F);});},_19K=new T(function(){return B(unCStr("Negative range size"));}),_19L=new T(function(){return B(err(_19K));}),_19M=function(_19N){var _19O=B(A1(_19N,_));return E(_19O);},_19P=function(_19Q,_19R,_19S,_){var _19T=E(_19Q);if(!_19T){return new T2(0,_S,_19R);}else{var _19U=new T(function(){return B(_mz(_19S,0))-1|0;}),_19V=B(_18u(new T(function(){return E(_19U)+1|0;}),_19R,_)),_19W=E(_19V),_19X=_19W.a,_19Y=_19W.b,_19Z=new T(function(){var _1a0=E(_19X);if(B(_mz(_19S,0))>=(_1a0+1|0)){var _1a1=new T(function(){var _1a2=_1a0+1|0;if(_1a2>0){return B(_18K(_1a2,_19S));}else{return E(_19S);}});if(0>=_1a0){return E(_1a1);}else{var _1a3=function(_1a4,_1a5){var _1a6=E(_1a4);if(!_1a6._){return E(_1a1);}else{var _1a7=_1a6.a,_1a8=E(_1a5);return (_1a8==1)?new T2(1,_1a7,_1a1):new T2(1,_1a7,new T(function(){return B(_1a3(_1a6.b,_1a8-1|0));}));}};return B(_1a3(_19S,_1a0));}}else{return E(_19S);}}),_1a9=B(_19P(_19T-1|0,_19Y,_19Z,_)),_1aa=new T(function(){var _1ab=function(_){var _1ac=E(_19U),_1ad=function(_1ae){if(_1ae>=0){var _1af=newArr(_1ae,_18R),_1ag=_1af,_1ah=E(_1ae);if(!_1ah){return new T4(0,E(_18S),E(_1ac),0,_1ag);}else{var _1ai=function(_1aj,_1ak,_){while(1){var _1al=E(_1aj);if(!_1al._){return E(_);}else{var _=_1ag[_1ak]=_1al.a;if(_1ak!=(_1ah-1|0)){var _1am=_1ak+1|0;_1aj=_1al.b;_1ak=_1am;continue;}else{return E(_);}}}},_=B(_1ai(_19S,0,_));return new T4(0,E(_18S),E(_1ac),_1ah,_1ag);}}else{return E(_19L);}};if(0>_1ac){return new F(function(){return _1ad(0);});}else{return new F(function(){return _1ad(_1ac+1|0);});}},_1an=B(_19M(_1ab)),_1ao=E(_1an.a),_1ap=E(_1an.b),_1aq=E(_19X);if(_1ao>_1aq){return B(_19G(_1aq,_1ao,_1ap));}else{if(_1aq>_1ap){return B(_19G(_1aq,_1ao,_1ap));}else{return E(_1an.d[_1aq-_1ao|0]);}}});return new T2(0,new T2(1,_1aa,new T(function(){return B(_sq(_1a9));})),_19Y);}},_1ar=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1as=function(_1at,_1au,_1av,_1aw,_){var _1ax=__app1(E(_gN),_1aw),_1ay=__app3(E(_1ar),_1aw,E(_1at),E(_1au)),_1az=B(A2(_1av,_1aw,_)),_1aA=__app1(E(_gM),_1aw);return new F(function(){return _gL(_);});},_1aB=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_1aC=function(_1aD,_1aE,_1aF,_1aG,_){var _1aH=__app4(E(_1aB),_1aG,_1aD,_1aE,_1aF);return new F(function(){return _gL(_);});},_1aI=2,_1aJ=function(_1aK,_1aL,_1aM,_1aN,_1aO,_1aP,_){var _1aQ=function(_1aR,_){return new F(function(){return _1as(_1aI,_1aI,function(_1aS,_){return new F(function(){return _1aC(B(_6X(_1aL,E(_1aP))),0,0,E(_1aS),_);});},E(_1aR),_);});};return new F(function(){return _gY(new T(function(){return E(_1aM)-E(_1aN)*16;},1),new T(function(){return E(_1aO)*20;},1),_1aQ,_1aK,_);});},_1aT=1,_1aU=new T(function(){return B(_6X(_ja,1));}),_1aV=function(_1aW){return E(_1aW).d;},_1aX=function(_1aY,_1aZ,_1b0,_1b1,_1b2,_1b3,_){var _1b4=new T(function(){return E(E(_1b3).r);}),_1b5=new T(function(){return E(E(_1b4).a);}),_1b6=new T(function(){if(!B(_au(E(_1b3).s,10))){var _1b7=E(E(_1b4).b);if(!(_1b7%2)){return _1b7+1|0;}else{return _1b7-1|0;}}else{return E(E(_1b4).b);}}),_1b8=new T(function(){var _1b9=E(_1b3);return {_:0,a:E(_1b9.a),b:E(_1b9.b),c:E(_1b9.c),d:E(_1b9.d),e:E(_1b9.e),f:E(_1b9.f),g:E(_1b9.g),h:E(_1b9.h),i:_1b9.i,j:_1b9.j,k:_1b9.k,l:_1b9.l,m:E(_1b9.m),n:_1b9.n,o:E(_1b9.o),p:E(_1b9.p),q:_1b9.q,r:E(new T2(0,_1b5,_1b6)),s:_1b9.s,t:E(_1b9.t),u:E(_1b9.u)};}),_1ba=new T(function(){return E(E(_1b8).a);}),_1bb=new T(function(){return E(E(_1b8).b);}),_1bc=new T(function(){return E(E(_1bb).a);}),_1bd=new T(function(){var _1be=E(_1b0)/16,_1bf=_1be&4294967295;if(_1be>=_1bf){return _1bf-2|0;}else{return (_1bf-1|0)-2|0;}}),_1bg=B(_nw(_1aY,_1aZ,new T(function(){return B(_ba(_1bd,_1bc));}),_nV,new T(function(){return E(E(_1ba).b);}),_)),_1bh=new T(function(){return E(E(E(_1b8).a).a);}),_1bi=B(A(_mU,[_1aY,new T(function(){if(E(E(_1ba).e)==32){return E(_nT);}else{return E(_nU);}}),new T(function(){return ((E(E(_1bh).a)+E(_1bd)|0)-E(_1bc)|0)+1|0;},1),new T(function(){return (E(E(_1bh).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1aV(_1ba));}),_S),_])),_1bj=E(_1b8),_1bk=_1bj.c,_1bl=_1bj.k,_1bm=E(_1bj.t),_1bn=new T(function(){var _1bo=E(_1b0)/28,_1bp=_1bo&4294967295;if(_1bo>=_1bp){return (_1bp-1|0)+_1bl|0;}else{return ((_1bp-1|0)-1|0)+_1bl|0;}}),_1bq=new T(function(){return (2+E(E(_1bb).b)|0)+3|0;}),_1br=new T2(0,_1aY,_1aZ),_1bs=function(_){var _1bt=function(_){var _1bu=function(_){var _1bv=B(_1aJ(_1aY,new T(function(){return E(E(_1b2).b);},1),_1b0,new T(function(){return E(_1bc)+10|0;},1),_nV,new T(function(){return (imul(E(_1b5),8)|0)+E(_1b6)|0;},1),_));return _1bj;};if(!E(_1bj.p)._){return new F(function(){return _1bu(_);});}else{var _1bw=B(A(_mU,[_1aY,_1aU,_1aT,_1aT,B(_A(0,_1bj.q,_S)),_]));return new F(function(){return _1bu(_);});}};if(!E(_1bm.g)){return new F(function(){return _1bt(_);});}else{var _1bx=B(_jg(_1br,_1b1,0,_1bq,_1bn,_1bq,B(_V8(_1bk,new T(function(){return B(_6k(_sq,_1bj.m));},1),_1bj.n)),_));return new F(function(){return _1bt(_);});}};if(!E(_1bm.c)){var _1by=B(_jg(_1br,_1b1,0,_1bq,_1bn,_1bq,_1bk,_));return new F(function(){return _1bs(_);});}else{return new F(function(){return _1bs(_);});}},_1bz=function(_1bA,_1bB){while(1){var _1bC=E(_1bA);if(!_1bC._){return E(_1bB);}else{_1bA=_1bC.b;_1bB=_1bC.a;continue;}}},_1bD=function(_1bE,_1bF,_1bG){return new F(function(){return _1bz(_1bF,_1bE);});},_1bH=function(_1bI,_1bJ){while(1){var _1bK=E(_1bI);if(!_1bK._){return E(_1bJ);}else{_1bI=_1bK.b;_1bJ=_1bK.a;continue;}}},_1bL=function(_1bM,_1bN,_1bO){return new F(function(){return _1bH(_1bN,_1bM);});},_1bP=function(_1bQ,_1bR){while(1){var _1bS=E(_1bR);if(!_1bS._){return __Z;}else{var _1bT=_1bS.b,_1bU=E(_1bQ);if(_1bU==1){return E(_1bT);}else{_1bQ=_1bU-1|0;_1bR=_1bT;continue;}}}},_1bV=function(_1bW,_1bX){var _1bY=new T(function(){var _1bZ=_1bW+1|0;if(_1bZ>0){return B(_1bP(_1bZ,_1bX));}else{return E(_1bX);}});if(0>=_1bW){return E(_1bY);}else{var _1c0=function(_1c1,_1c2){var _1c3=E(_1c1);if(!_1c3._){return E(_1bY);}else{var _1c4=_1c3.a,_1c5=E(_1c2);return (_1c5==1)?new T2(1,_1c4,_1bY):new T2(1,_1c4,new T(function(){return B(_1c0(_1c3.b,_1c5-1|0));}));}};return new F(function(){return _1c0(_1bX,_1bW);});}},_1c6=new T(function(){return B(unCStr(":"));}),_1c7=function(_1c8){var _1c9=E(_1c8);if(!_1c9._){return __Z;}else{var _1ca=new T(function(){return B(_q(_1c6,new T(function(){return B(_1c7(_1c9.b));},1)));},1);return new F(function(){return _q(_1c9.a,_1ca);});}},_1cb=function(_1cc,_1cd){var _1ce=new T(function(){return B(_q(_1c6,new T(function(){return B(_1c7(_1cd));},1)));},1);return new F(function(){return _q(_1cc,_1ce);});},_1cf=function(_1cg){return new F(function(){return _Lo("Check.hs:173:7-35|(co : na : xs)");});},_1ch=new T(function(){return B(_1cf(_));}),_1ci=new T(function(){return B(err(_sy));}),_1cj=new T(function(){return B(err(_sA));}),_1ck=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_1cl=0,_1cm=new T(function(){return B(unCStr("!"));}),_1cn=function(_1co,_1cp){var _1cq=E(_1cp);if(!_1cq._){return E(_1ch);}else{var _1cr=E(_1cq.b);if(!_1cr._){return E(_1ch);}else{var _1cs=E(_1cq.a),_1ct=new T(function(){var _1cu=B(_Hc(58,_1cr.a,_1cr.b));return new T2(0,_1cu.a,_1cu.b);}),_1cv=function(_1cw,_1cx,_1cy){var _1cz=function(_1cA){if((_1co+1|0)!=_1cA){return new T3(0,_1co+1|0,_1cx,_1cq);}else{var _1cB=E(_1cy);return (_1cB._==0)?new T3(0,_1cl,_1cx,_S):new T3(0,_1cl,_1cx,new T(function(){var _1cC=B(_1cb(_1cB.a,_1cB.b));if(!_1cC._){return E(_S2);}else{return B(_RX(_1cC.a,_1cC.b));}}));}};if(!B(_qV(_1cw,_1cm))){var _1cD=B(_Gk(B(_sF(_1ck,_1cw))));if(!_1cD._){return E(_1ci);}else{if(!E(_1cD.b)._){return new F(function(){return _1cz(E(_1cD.a));});}else{return E(_1cj);}}}else{return new F(function(){return _1cz( -1);});}};if(E(_1cs)==58){return new F(function(){return _1cv(_S,new T(function(){return E(E(_1ct).a);}),new T(function(){return E(E(_1ct).b);}));});}else{var _1cE=E(_1ct),_1cF=E(_1cE.b);if(!_1cF._){return E(_1ch);}else{return new F(function(){return _1cv(new T2(1,_1cs,_1cE.a),_1cF.a,_1cF.b);});}}}}},_1cG=function(_1cH,_1cI){while(1){var _1cJ=E(_1cI);if(!_1cJ._){return __Z;}else{var _1cK=_1cJ.b,_1cL=E(_1cH);if(_1cL==1){return E(_1cK);}else{_1cH=_1cL-1|0;_1cI=_1cK;continue;}}}},_1cM=function(_1cN,_1cO,_1cP){var _1cQ=new T2(1,_1cO,new T(function(){var _1cR=_1cN+1|0;if(_1cR>0){return B(_1cG(_1cR,_1cP));}else{return E(_1cP);}}));if(0>=_1cN){return E(_1cQ);}else{var _1cS=function(_1cT,_1cU){var _1cV=E(_1cT);if(!_1cV._){return E(_1cQ);}else{var _1cW=_1cV.a,_1cX=E(_1cU);return (_1cX==1)?new T2(1,_1cW,_1cQ):new T2(1,_1cW,new T(function(){return B(_1cS(_1cV.b,_1cX-1|0));}));}};return new F(function(){return _1cS(_1cP,_1cN);});}},_1cY=new T2(0,_RF,_Eg),_1cZ=function(_1d0,_1d1,_1d2){while(1){var _1d3=E(_1d2);if(!_1d3._){return E(_1cY);}else{var _1d4=_1d3.b,_1d5=E(_1d3.a),_1d6=E(_1d5.a);if(_1d0!=E(_1d6.a)){_1d2=_1d4;continue;}else{if(_1d1!=E(_1d6.b)){_1d2=_1d4;continue;}else{return E(_1d5.b);}}}}},_1d7=function(_1d8,_1d9){while(1){var _1da=E(_1d9);if(!_1da._){return __Z;}else{var _1db=_1da.b,_1dc=E(_1d8);if(_1dc==1){return E(_1db);}else{_1d8=_1dc-1|0;_1d9=_1db;continue;}}}},_1dd=function(_1de,_1df,_1dg){var _1dh=E(_1de);if(_1dh==1){return E(_1dg);}else{return new F(function(){return _1d7(_1dh-1|0,_1dg);});}},_1di=function(_1dj,_1dk,_1dl){return new T2(1,new T(function(){if(0>=_1dj){return __Z;}else{return B(_pU(_1dj,new T2(1,_1dk,_1dl)));}}),new T(function(){if(_1dj>0){return B(_1dm(_1dj,B(_1dd(_1dj,_1dk,_1dl))));}else{return B(_1di(_1dj,_1dk,_1dl));}}));},_1dm=function(_1dn,_1do){var _1dp=E(_1do);if(!_1dp._){return __Z;}else{var _1dq=_1dp.a,_1dr=_1dp.b;return new T2(1,new T(function(){if(0>=_1dn){return __Z;}else{return B(_pU(_1dn,_1dp));}}),new T(function(){if(_1dn>0){return B(_1dm(_1dn,B(_1dd(_1dn,_1dq,_1dr))));}else{return B(_1di(_1dn,_1dq,_1dr));}}));}},_1ds=function(_1dt,_1du,_1dv){var _1dw=_1du-1|0;if(0<=_1dw){var _1dx=E(_1dt),_1dy=function(_1dz){var _1dA=new T(function(){if(_1dz!=_1dw){return B(_1dy(_1dz+1|0));}else{return __Z;}}),_1dB=function(_1dC){var _1dD=E(_1dC);return (_1dD._==0)?E(_1dA):new T2(1,new T(function(){var _1dE=E(_1dv);if(!_1dE._){return E(_1cY);}else{var _1dF=_1dE.b,_1dG=E(_1dE.a),_1dH=E(_1dG.a),_1dI=E(_1dD.a);if(_1dI!=E(_1dH.a)){return B(_1cZ(_1dI,_1dz,_1dF));}else{if(_1dz!=E(_1dH.b)){return B(_1cZ(_1dI,_1dz,_1dF));}else{return E(_1dG.b);}}}}),new T(function(){return B(_1dB(_1dD.b));}));};return new F(function(){return _1dB(B(_8y(0,_1dx-1|0)));});};return new F(function(){return _1dm(_1dx,B(_1dy(0)));});}else{return __Z;}},_1dJ=function(_1dK){return new F(function(){return _Lo("Check.hs:72:21-47|(l : r : _)");});},_1dL=new T(function(){return B(_1dJ(_));}),_1dM=61,_1dN=function(_1dO,_1dP){while(1){var _1dQ=E(_1dO);if(!_1dQ._){return E(_1dP);}else{_1dO=_1dQ.b;_1dP=_1dQ.a;continue;}}},_1dR=function(_1dS,_1dT,_1dU){return new F(function(){return _1dN(_1dT,_1dS);});},_1dV=function(_1dW,_1dX){var _1dY=E(_1dX);if(!_1dY._){return new T2(0,_S,_S);}else{var _1dZ=_1dY.a;if(!B(A1(_1dW,_1dZ))){var _1e0=new T(function(){var _1e1=B(_1dV(_1dW,_1dY.b));return new T2(0,_1e1.a,_1e1.b);});return new T2(0,new T2(1,_1dZ,new T(function(){return E(E(_1e0).a);})),new T(function(){return E(E(_1e0).b);}));}else{return new T2(0,_S,_1dY);}}},_1e2=function(_1e3,_1e4){while(1){var _1e5=E(_1e4);if(!_1e5._){return __Z;}else{if(!B(A1(_1e3,_1e5.a))){return E(_1e5);}else{_1e4=_1e5.b;continue;}}}},_1e6=function(_1e7){var _1e8=_1e7>>>0;if(_1e8>887){var _1e9=u_iswspace(_1e7);return (E(_1e9)==0)?false:true;}else{var _1ea=E(_1e8);return (_1ea==32)?true:(_1ea-9>>>0>4)?(E(_1ea)==160)?true:false:true;}},_1eb=function(_1ec){return new F(function(){return _1e6(E(_1ec));});},_1ed=function(_1ee){var _1ef=B(_1e2(_1eb,_1ee));if(!_1ef._){return __Z;}else{var _1eg=new T(function(){var _1eh=B(_1dV(_1eb,_1ef));return new T2(0,_1eh.a,_1eh.b);});return new T2(1,new T(function(){return E(E(_1eg).a);}),new T(function(){return B(_1ed(E(_1eg).b));}));}},_1ei=function(_1ej){if(!B(_4A(_hd,_1dM,_1ej))){return new T2(0,_1ej,_S);}else{var _1ek=new T(function(){var _1el=E(_1ej);if(!_1el._){return E(_1dL);}else{var _1em=E(_1el.b);if(!_1em._){return E(_1dL);}else{var _1en=_1em.a,_1eo=_1em.b,_1ep=E(_1el.a);if(E(_1ep)==61){return new T2(0,_S,new T(function(){return E(B(_Hc(61,_1en,_1eo)).a);}));}else{var _1eq=B(_Hc(61,_1en,_1eo)),_1er=E(_1eq.b);if(!_1er._){return E(_1dL);}else{return new T2(0,new T2(1,_1ep,_1eq.a),_1er.a);}}}}});return new T2(0,new T(function(){var _1es=B(_1ed(E(_1ek).a));if(!_1es._){return __Z;}else{return B(_1dR(_1es.a,_1es.b,_Tu));}}),new T(function(){var _1et=B(_1ed(E(_1ek).b));if(!_1et._){return __Z;}else{return E(_1et.a);}}));}},_1eu=function(_1ev,_1ew){return new F(function(){return _1bV(E(_1ev),_1ew);});},_1ex=function(_1ey){var _1ez=E(_1ey);if(!_1ez._){return new T2(0,_S,_S);}else{var _1eA=E(_1ez.a),_1eB=new T(function(){var _1eC=B(_1ex(_1ez.b));return new T2(0,_1eC.a,_1eC.b);});return new T2(0,new T2(1,_1eA.a,new T(function(){return E(E(_1eB).a);})),new T2(1,_1eA.b,new T(function(){return E(E(_1eB).b);})));}},_1eD=new T(function(){return B(unCStr("\u306a\u305c \u308f\u305f\u3057\u306f \u3053\u3053\u306b\u3090\u3066\u3002\n\u306a\u305c \u308f\u305f\u3057\u306f \u3053\u306e\u3084\u3046\u306b\u601d\u3075\u306e\u3060\u3089\u3046\u3002\n\u306a\u3093\u306e\u305f\u3081\u306b \u308f\u305f\u3057\u306f\u3002\n\u751f\u304d\u3066\u3090\u308b\u306e\u3060\u3089\u3046\u30fb\u30fb\u30fb\u3002 {e.X.m1:s0}{sm}"));}),_1eE=new T(function(){return B(unCStr("s0_3"));}),_1eF=new T(function(){return B(unCStr("\n\u7406\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl1}{e.c0&s1.m1:s1}"));}),_1eG=new T2(0,_1eE,_1eF),_1eH=new T(function(){return B(unCStr("s0_n"));}),_1eI=new T(function(){return B(unCStr("\n\u4ed6\u306e\u6249\u3082\u898b\u3066\u307f\u3084\u3046\u304b"));}),_1eJ=new T2(0,_1eH,_1eI),_1eK=new T(function(){return B(unCStr("s4"));}),_1eL=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_1eM=new T2(0,_1eK,_1eL),_1eN=new T2(1,_1eM,_S),_1eO=new T(function(){return B(unCStr("s3c"));}),_1eP=new T(function(){return B(unCStr("\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c1.m1:s2}\n\u306a\u3093\u304b \u6249\u304c\u51fa\u3066\u304d\u305f\u3002"));}),_1eQ=new T2(0,_1eO,_1eP),_1eR=new T2(1,_1eQ,_1eN),_1eS=new T(function(){return B(unCStr("s3eq"));}),_1eT=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1eU=new T2(0,_1eS,_1eT),_1eV=new T2(1,_1eU,_1eR),_1eW=new T(function(){return B(unCStr("s3"));}),_1eX=new T(function(){return B(unCStr("\n\u306a\u3093\u3060\u3089\u3046 \u3053\u3053\u306f\u3002 {rk.1.z.abc.s3c}{e.b=0.m0:s3eq}"));}),_1eY=new T2(0,_1eW,_1eX),_1eZ=new T2(1,_1eY,_1eV),_1f0=new T(function(){return B(unCStr("s2n1"));}),_1f1=new T(function(){return B(unCStr("\n\u5165\u308b\u3088\u3002{e.X.l}{e.c2.m1:s3}"));}),_1f2=new T2(0,_1f0,_1f1),_1f3=new T2(1,_1f2,_1eZ),_1f4=new T(function(){return B(unCStr("s2n0"));}),_1f5=new T(function(){return B(unCStr("\n\u5165\u308b\u306e\u3092\u3084\u3081\u305f\u3002"));}),_1f6=new T2(0,_1f4,_1f5),_1f7=new T2(1,_1f6,_1f3),_1f8=new T(function(){return B(unCStr("s2n"));}),_1f9=new T(function(){return B(unCStr("\n\u6249\u304c\u3042\u308b\u3084\u3046\u3060\u3002\n\u5165\u308b\uff1f\n{ch.\u5165\u308b,s2n1.\u5165\u3089\u306a\u3044,s2n0}"));}),_1fa=new T2(0,_1f8,_1f9),_1fb=new T2(1,_1fa,_1f7),_1fc=new T(function(){return B(unCStr("s2D0"));}),_1fd=new T(function(){return B(unCStr("\n\u6b74\u53f2\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\u3078\u308b\u76ee\u7684\u3084 \u50b3\u3078\u308b\u4eba\u3005\u306e\u4e16\u754c\u89c0 \u50b3\u3078\u305f\u7576\u6642\u306b\u6b8b\u3063\u3066\u3090\u305f\u8cc7\u6599\u306e\u7a2e\u985e\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\u3058\u6642\u4ee3\u306b\u95dc\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\u7576\u7570\u306a\u3063\u305f\u50b3\u3078\u65b9\u304c\u70ba\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\u5be6\u306a\u6b74\u53f2\u306f\u5b58\u5728\u305b\u305a \u6b74\u53f2\u3092\u5b78\u3076\u610f\u7fa9\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\u5f97\u3057 \u4ed6\u306e\u4eba\u9054\u3068\u5171\u6709\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\u8eab\u304c\u898b\u51fa\u3057 \u7d21\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\u7d44\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\u5024\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\u304d\u308b\u610f\u5473\u306b\u3082 \u7e4b\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1fe=new T2(0,_1fc,_1fd),_1ff=new T2(1,_1fe,_1fb),_1fg=new T(function(){return B(unCStr("s2C0"));}),_1fh=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\u672c\u3092\u8a2a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\u6240\u306b\u306f \u305d\u306e\u5f62\u8de1\u304c \u3044\u304f\u3064\u3082\u6b8b\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\u6280\u3092\u6388\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\u9332\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1fi=new T2(0,_1fg,_1fh),_1fj=new T2(1,_1fi,_1ff),_1fk=new T(function(){return B(unCStr("s2B0"));}),_1fl=new T(function(){return B(unCStr("\n\u79c1\u306e\u6301\u3063\u3066\u3090\u308b\u60c5\u5831\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\u308b\u306e\u306b\u4f7f\u306f\u308c\u305f\u77f3\u306f \u7a7a\u4e2d\u306b\u6301\u3061\u4e0a\u3052\u3089\u308c\u3066 \u7d44\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1fm=new T2(0,_1fk,_1fl),_1fn=new T2(1,_1fm,_1fj),_1fo=new T(function(){return B(unCStr("s2A1_2"));}),_1fp=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1fq=new T2(0,_1fo,_1fp),_1fr=new T2(1,_1fq,_1fn),_1fs=new T(function(){return B(unCStr("s2A1_1"));}),_1ft=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\u7406\u306b\u77e5\u308b\u5fc5\u8981\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1fu=new T2(0,_1fs,_1ft),_1fv=new T2(1,_1fu,_1fr),_1fw=new T(function(){return B(unCStr("s2A1_0"));}),_1fx=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1fy=new T2(0,_1fw,_1fx),_1fz=new T2(1,_1fy,_1fv),_1fA=new T(function(){return B(unCStr("s2A0"));}),_1fB=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\u5206\u306e\u570b\u306e\u6b74\u53f2\u3092\u77e5\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1fC=new T2(0,_1fA,_1fB),_1fD=new T2(1,_1fC,_1fz),_1fE=new T(function(){return B(unCStr("s2"));}),_1fF=new T(function(){return B(unCStr("\n\u3042\u3063\u3002\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3060\u3002{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n}"));}),_1fG=new T2(0,_1fE,_1fF),_1fH=new T2(1,_1fG,_1fD),_1fI=new T(function(){return B(unCStr("s1c"));}),_1fJ=new T(function(){return B(unCStr("\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s2}\n\u306a\u3093\u304b \u6249\u304c\u51fa\u3066\u304d\u305f\u3002"));}),_1fK=new T2(0,_1fI,_1fJ),_1fL=new T2(1,_1fK,_1fH),_1fM=new T(function(){return B(unCStr("s1eq"));}),_1fN=new T2(0,_1fM,_1eT),_1fO=new T2(1,_1fN,_1fL),_1fP=new T(function(){return B(unCStr("s1"));}),_1fQ=new T(function(){return B(unCStr("\n\u306a\u3093\u3060\u3089\u3046 \u3053\u3053\u306f\u3002 {rk.1.z.abc.s1c}{e.b=0.m0:s1eq}"));}),_1fR=new T2(0,_1fP,_1fQ),_1fS=new T2(1,_1fR,_1fO),_1fT=new T(function(){return B(unCStr("nubatama"));}),_1fU=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1fV=new T2(0,_1fT,_1fU),_1fW=new T2(1,_1fV,_1fS),_1fX=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1fY=new T(function(){return B(unCStr("msgW"));}),_1fZ=new T2(0,_1fY,_1fX),_1g0=new T2(1,_1fZ,_1fW),_1g1=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1g2=new T(function(){return B(unCStr("msgR"));}),_1g3=new T2(0,_1g2,_1g1),_1g4=new T2(1,_1g3,_1g0),_1g5=new T2(1,_1eJ,_1g4),_1g6=new T2(1,_1eG,_1g5),_1g7=new T(function(){return B(unCStr("s0_2"));}),_1g8=new T(function(){return B(unCStr("\n\u6578\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl1}{e.c0&s1.m1:s1}"));}),_1g9=new T2(0,_1g7,_1g8),_1ga=new T2(1,_1g9,_1g6),_1gb=new T(function(){return B(unCStr("s0_1"));}),_1gc=new T(function(){return B(unCStr("\n\u53f2\u306e\u90e8\u5c4b\u306b\u5165\u3089\u3046 {e.X.jl1}{e.c0&s1.m1:s1}"));}),_1gd=new T2(0,_1gb,_1gc),_1ge=new T2(1,_1gd,_1ga),_1gf=new T(function(){return B(unCStr("s0S"));}),_1gg=new T(function(){return B(unCStr("\n\u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u306e\u90e8\u5c4b\u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_3.\u5165\u3089\u306a\u3044,s0_n}"));}),_1gh=new T2(0,_1gf,_1gg),_1gi=new T2(1,_1gh,_1ge),_1gj=new T(function(){return B(unCStr("s0M"));}),_1gk=new T(function(){return B(unCStr("\n\u6578\uff1a\u304b\u305a\uff1a\u306e\u90e8\u5c4b \u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_2.\u5165\u3089\u306a\u3044,s0_n}"));}),_1gl=new T2(0,_1gj,_1gk),_1gm=new T2(1,_1gl,_1gi),_1gn=new T(function(){return B(unCStr("s0H"));}),_1go=new T(function(){return B(unCStr("\n\u53f2\uff1a\u3075\u307f\uff1a\u306e\u90e8\u5c4b\u3068\u66f8\u3044\u3066\u3042\u308b\u3002\n\u3053\u3053\u306b\u5165\u3089\u3046\u304b\uff1f {ch.\u5165\u308b,s0_1.\u5165\u3089\u306a\u3044,s0_n}"));}),_1gp=new T2(0,_1gn,_1go),_1gq=new T2(1,_1gp,_1gm),_1gr=new T(function(){return B(unCStr("s0"));}),_1gs=new T(function(){return B(unCStr("\n\u4e09\u3064\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u304c\u3042\u308b\u307f\u305f\u3044\u3060 {e.bH.m0:s0H}{e.bM.m0:s0M}{e.bS.m0:s0S }"));}),_1gt=new T2(0,_1gr,_1gs),_1gu=new T2(1,_1gt,_1gq),_1gv=new T(function(){return B(unCStr("initMsg"));}),_1gw=function(_1gx,_1gy){var _1gz=new T(function(){var _1gA=B(_1ex(_1gx));return new T2(0,_1gA.a,_1gA.b);}),_1gB=function(_1gC){var _1gD=E(_1gC);if(!_1gD._){return E(_1gz);}else{var _1gE=E(_1gD.a),_1gF=new T(function(){return B(_1gB(_1gD.b));});return new T2(0,new T2(1,_1gE.a,new T(function(){return E(E(_1gF).a);})),new T2(1,_1gE.b,new T(function(){return E(E(_1gF).b);})));}},_1gG=function(_1gH,_1gI,_1gJ){var _1gK=new T(function(){return B(_1gB(_1gJ));});return new T2(0,new T2(1,_1gH,new T(function(){return E(E(_1gK).a);})),new T2(1,_1gI,new T(function(){return E(E(_1gK).b);})));},_1gL=B(_1gG(_1gv,_1eD,_1gu)),_1gM=_1gL.a;if(!B(_4A(_qk,_1gy,_1gM))){return __Z;}else{return new F(function(){return _6X(_1gL.b,B(_MK(_qk,_1gy,_1gM)));});}},_1gN=7,_1gO=new T2(0,_1gN,_1gN),_1gP=new T2(1,_1gO,_S),_1gQ=5,_1gR=new T2(0,_1gQ,_1gQ),_1gS=new T2(1,_1gR,_1gP),_1gT=6,_1gU=new T2(0,_1gQ,_1gT),_1gV=new T2(1,_1gU,_1gS),_1gW=new T2(1,_1gR,_1gV),_1gX=new T2(1,_1gR,_1gW),_1gY=2,_1gZ=4,_1h0=new T2(0,_1gZ,_1gY),_1h1=new T2(1,_1h0,_S),_1h2=new T2(0,_1gY,_1gY),_1h3=new T2(1,_1h2,_1h1),_1h4=new T2(1,_1h2,_1h3),_1h5=new T2(1,_1h2,_1h4),_1h6=0,_1h7=new T2(0,_1gY,_1h6),_1h8=new T2(1,_1h7,_1h5),_1h9=new T(function(){return B(unCStr("Int"));}),_1ha=function(_1hb,_1hc,_1hd){return new F(function(){return _19A(_193,new T2(0,_1hc,_1hd),_1hb,_1h9);});},_1he=new T(function(){return B(unCStr("msgR"));}),_1hf=new T(function(){return B(_1gw(_S,_1he));}),_1hg=new T(function(){return B(unCStr("msgW"));}),_1hh=new T(function(){return B(_1gw(_S,_1hg));}),_1hi=function(_1hj){var _1hk=E(_1hj);return 0;},_1hl=new T(function(){return B(unCStr("@@@@@"));}),_1hm=new T(function(){var _1hn=E(_1hl);if(!_1hn._){return E(_nn);}else{return E(_1hn.a);}}),_1ho=new T2(0,_1gY,_1gZ),_1hp=72,_1hq=new T2(0,_1hp,_Em),_1hr=new T2(0,_1ho,_1hq),_1hs=new T2(1,_1hr,_S),_1ht=77,_1hu=new T2(0,_1ht,_Em),_1hv=new T2(0,_1h0,_1hu),_1hw=new T2(1,_1hv,_1hs),_1hx=83,_1hy=new T2(0,_1hx,_Em),_1hz=new T2(0,_1h6,_1gY),_1hA=new T2(0,_1hz,_1hy),_1hB=new T2(1,_1hA,_1hw),_1hC=new T(function(){return B(_1ds(_1gQ,5,_1hB));}),_1hD=new T(function(){return B(_Lo("Check.hs:142:22-33|(ch : po)"));}),_1hE=new T(function(){return B(_ed("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1hF=122,_1hG=new T2(0,_1hF,_Em),_1hH=new T2(0,_1h6,_1h6),_1hI=new T2(0,_1hH,_1hG),_1hJ=61,_1hK=new T2(0,_1hJ,_Em),_1hL=1,_1hM=new T2(0,_1hL,_1h6),_1hN=new T2(0,_1hM,_1hK),_1hO=97,_1hP=new T2(0,_1hO,_Eg),_1hQ=new T2(0,_1h6,_1gZ),_1hR=new T2(0,_1hQ,_1hP),_1hS=98,_1hT=new T2(0,_1hS,_Eg),_1hU=new T2(0,_1ho,_1hT),_1hV=99,_1hW=new T2(0,_1hV,_Eg),_1hX=new T2(0,_1gZ,_1gZ),_1hY=new T2(0,_1hX,_1hW),_1hZ=new T2(1,_1hY,_S),_1i0=new T2(1,_1hU,_1hZ),_1i1=new T2(1,_1hR,_1i0),_1i2=new T2(1,_1hN,_1i1),_1i3=new T2(1,_1hI,_1i2),_1i4=110,_1i5=new T2(0,_1i4,_Es),_1i6=new T2(0,_1gZ,_1gQ),_1i7=new T2(0,_1i6,_1i5),_1i8=new T2(1,_1i7,_S),_1i9=66,_1ia=new T2(0,_1i9,_Em),_1ib=new T2(0,_1gY,_1gQ),_1ic=new T2(0,_1ib,_1ia),_1id=new T2(1,_1ic,_1i8),_1ie=67,_1if=new T2(0,_1ie,_Em),_1ig=3,_1ih=new T2(0,_1h6,_1ig),_1ii=new T2(0,_1ih,_1if),_1ij=new T2(1,_1ii,_1id),_1ik=65,_1il=new T2(0,_1ik,_Em),_1im=new T2(0,_1gZ,_1hL),_1in=new T2(0,_1im,_1il),_1io=new T2(1,_1in,_1ij),_1ip=68,_1iq=new T2(0,_1ip,_Em),_1ir=new T2(0,_1hM,_1iq),_1is=new T2(1,_1ir,_1io),_1it=new T2(1,_S,_S),_1iu=new T2(1,_1i3,_1it),_1iv=new T2(1,_1is,_1iu),_1iw=new T2(1,_1i3,_1iv),_1ix=new T2(1,_1hB,_1iw),_1iy=function(_1iz){var _1iA=E(_1iz);if(!_1iA._){return __Z;}else{var _1iB=_1iA.b,_1iC=E(_1iA.a),_1iD=_1iC.b,_1iE=E(_1iC.a),_1iF=function(_1iG){if(E(_1iE)==32){return new T2(1,_1iC,new T(function(){return B(_1iy(_1iB));}));}else{switch(E(_1iD)){case 0:return new T2(1,new T2(0,_1iE,_Eg),new T(function(){return B(_1iy(_1iB));}));case 1:return new T2(1,new T2(0,_1iE,_ER),new T(function(){return B(_1iy(_1iB));}));case 2:return new T2(1,new T2(0,_1iE,_Es),new T(function(){return B(_1iy(_1iB));}));case 3:return new T2(1,new T2(0,_1iE,_Ey),new T(function(){return B(_1iy(_1iB));}));case 4:return new T2(1,new T2(0,_1iE,_EE),new T(function(){return B(_1iy(_1iB));}));case 5:return new T2(1,new T2(0,_1iE,_F5),new T(function(){return B(_1iy(_1iB));}));case 6:return new T2(1,new T2(0,_1iE,_EY),new T(function(){return B(_1iy(_1iB));}));case 7:return new T2(1,new T2(0,_1iE,_ER),new T(function(){return B(_1iy(_1iB));}));default:return new T2(1,new T2(0,_1iE,_EK),new T(function(){return B(_1iy(_1iB));}));}}};if(E(_1iE)==32){return new F(function(){return _1iF(_);});}else{switch(E(_1iD)){case 0:return new T2(1,new T2(0,_1iE,_EK),new T(function(){return B(_1iy(_1iB));}));case 1:return new F(function(){return _1iF(_);});break;case 2:return new F(function(){return _1iF(_);});break;case 3:return new F(function(){return _1iF(_);});break;case 4:return new F(function(){return _1iF(_);});break;case 5:return new F(function(){return _1iF(_);});break;case 6:return new F(function(){return _1iF(_);});break;case 7:return new F(function(){return _1iF(_);});break;default:return new F(function(){return _1iF(_);});}}}},_1iH=function(_1iI){var _1iJ=E(_1iI);return (_1iJ._==0)?__Z:new T2(1,new T(function(){return B(_1iy(_1iJ.a));}),new T(function(){return B(_1iH(_1iJ.b));}));},_1iK=function(_1iL){var _1iM=E(_1iL);if(!_1iM._){return __Z;}else{var _1iN=_1iM.b,_1iO=E(_1iM.a),_1iP=_1iO.b,_1iQ=E(_1iO.a),_1iR=function(_1iS){if(E(_1iQ)==32){return new T2(1,_1iO,new T(function(){return B(_1iK(_1iN));}));}else{switch(E(_1iP)){case 0:return new T2(1,new T2(0,_1iQ,_Eg),new T(function(){return B(_1iK(_1iN));}));case 1:return new T2(1,new T2(0,_1iQ,_Em),new T(function(){return B(_1iK(_1iN));}));case 2:return new T2(1,new T2(0,_1iQ,_Es),new T(function(){return B(_1iK(_1iN));}));case 3:return new T2(1,new T2(0,_1iQ,_Ey),new T(function(){return B(_1iK(_1iN));}));case 4:return new T2(1,new T2(0,_1iQ,_EE),new T(function(){return B(_1iK(_1iN));}));case 5:return new T2(1,new T2(0,_1iQ,_F5),new T(function(){return B(_1iK(_1iN));}));case 6:return new T2(1,new T2(0,_1iQ,_EY),new T(function(){return B(_1iK(_1iN));}));case 7:return new T2(1,new T2(0,_1iQ,_Em),new T(function(){return B(_1iK(_1iN));}));default:return new T2(1,new T2(0,_1iQ,_EK),new T(function(){return B(_1iK(_1iN));}));}}};if(E(_1iQ)==32){return new F(function(){return _1iR(_);});}else{if(E(_1iP)==8){return new T2(1,new T2(0,_1iQ,_Eg),new T(function(){return B(_1iK(_1iN));}));}else{return new F(function(){return _1iR(_);});}}}},_1iT=function(_1iU){var _1iV=E(_1iU);return (_1iV._==0)?__Z:new T2(1,new T(function(){return B(_1iK(_1iV.a));}),new T(function(){return B(_1iT(_1iV.b));}));},_1iW=function(_1iX,_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4,_1j5,_1j6,_1j7,_1j8,_1j9,_1ja,_1jb,_1jc,_1jd,_1je,_1jf,_1jg,_1jh,_1ji,_1jj,_1jk,_1jl,_1jm,_1jn,_1jo,_1jp,_1jq,_1jr,_1js,_1jt,_1ju,_1jv,_1jw,_1jx,_1jy,_1jz,_1jA){var _1jB=E(_1iY);if(!_1jB._){return E(_1hE);}else{var _1jC=_1jB.b,_1jD=E(_1jB.a),_1jE=new T(function(){var _1jF=function(_){var _1jG=B(_mz(_1je,0))-1|0,_1jH=function(_1jI){if(_1jI>=0){var _1jJ=newArr(_1jI,_18R),_1jK=_1jJ,_1jL=E(_1jI);if(!_1jL){return new T4(0,E(_1cl),E(_1jG),0,_1jK);}else{var _1jM=function(_1jN,_1jO,_){while(1){var _1jP=E(_1jN);if(!_1jP._){return E(_);}else{var _=_1jK[_1jO]=_1jP.a;if(_1jO!=(_1jL-1|0)){var _1jQ=_1jO+1|0;_1jN=_1jP.b;_1jO=_1jQ;continue;}else{return E(_);}}}},_=B(_1jM(_1je,0,_));return new T4(0,E(_1cl),E(_1jG),_1jL,_1jK);}}else{return E(_19L);}};if(0>_1jG){return new F(function(){return _1jH(0);});}else{return new F(function(){return _1jH(_1jG+1|0);});}},_1jR=B(_19M(_1jF)),_1jS=E(_1jR.a),_1jT=E(_1jR.b),_1jU=E(_1iX);if(_1jS>_1jU){return B(_1ha(_1jU,_1jS,_1jT));}else{if(_1jU>_1jT){return B(_1ha(_1jU,_1jS,_1jT));}else{return E(_1jR.d[_1jU-_1jS|0]);}}});switch(E(_1jD)){case 97:var _1jV=new T(function(){var _1jW=E(_1jC);if(!_1jW._){return E(_1hD);}else{return new T2(0,_1jW.a,_1jW.b);}}),_1jX=new T(function(){var _1jY=B(_1ei(E(_1jV).b));return new T2(0,_1jY.a,_1jY.b);}),_1jZ=B(_Gk(B(_sF(_1ck,new T(function(){return E(E(_1jX).b);})))));if(!_1jZ._){return E(_1ci);}else{if(!E(_1jZ.b)._){var _1k0=new T(function(){var _1k1=B(_Gk(B(_sF(_1ck,new T(function(){return E(E(_1jX).a);})))));if(!_1k1._){return E(_1ci);}else{if(!E(_1k1.b)._){return E(_1k1.a);}else{return E(_1cj);}}},1);return {_:0,a:E({_:0,a:E(_1iZ),b:E(B(_KX(_1k0,E(_1jZ.a),new T(function(){return E(E(_1jV).a);}),_Eg,_1j0))),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};}else{return E(_1cj);}}break;case 104:return {_:0,a:E({_:0,a:E(_1iZ),b:E(B(_1iH(_1j0))),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};case 106:var _1k2=E(_1jC);if(!_1k2._){return {_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l: -1,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};}else{if(E(_1k2.a)==108){var _1k3=E(_1iX),_1k4=B(_Gk(B(_sF(_1ck,_1k2.b))));return (_1k4._==0)?E(_1ci):(E(_1k4.b)._==0)?{_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(B(_1bV(_1k3,_1jd))),f:E(B(_1bV(_1k3,_1je))),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:E(_1k4.a),m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_wB),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)}:E(_1cj);}else{var _1k5=B(_Gk(B(_sF(_1ck,_1k2))));return (_1k5._==0)?E(_1ci):(E(_1k5.b)._==0)?{_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:E(_1k5.a),m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)}:E(_1cj);}}break;case 108:var _1k6=E(_1iX);return {_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(B(_1bV(_1k6,_1jd))),f:E(B(_1bV(_1k6,_1je))),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_wB),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};case 109:var _1k7=B(_1cn(E(_1jE),_1jC)),_1k8=_1k7.c,_1k9=B(_qV(_1k8,_S));if(!E(_1k9)){var _1ka=E(_1iX),_1kb=new T(function(){var _1kc=function(_){var _1kd=B(_mz(_1jd,0))-1|0,_1ke=function(_1kf){if(_1kf>=0){var _1kg=newArr(_1kf,_18R),_1kh=_1kg,_1ki=E(_1kf);if(!_1ki){return new T4(0,E(_1cl),E(_1kd),0,_1kh);}else{var _1kj=function(_1kk,_1kl,_){while(1){var _1km=E(_1kk);if(!_1km._){return E(_);}else{var _=_1kh[_1kl]=_1km.a;if(_1kl!=(_1ki-1|0)){var _1kn=_1kl+1|0;_1kk=_1km.b;_1kl=_1kn;continue;}else{return E(_);}}}},_=B(_1kj(_1jd,0,_));return new T4(0,E(_1cl),E(_1kd),_1ki,_1kh);}}else{return E(_19L);}};if(0>_1kd){return new F(function(){return _1ke(0);});}else{return new F(function(){return _1ke(_1kd+1|0);});}},_1ko=B(_19M(_1kc)),_1kp=E(_1ko.a),_1kq=E(_1ko.b);if(_1kp>_1ka){return B(_1ha(_1ka,_1kp,_1kq));}else{if(_1ka>_1kq){return B(_1ha(_1ka,_1kp,_1kq));}else{return E(E(_1ko.d[_1ka-_1kp|0]).a);}}}),_1kr=B(_1cM(_1ka,new T2(0,_1kb,new T2(1,_1jD,_1k8)),_1jd));}else{var _1kr=B(_1eu(_1iX,_1jd));}if(!E(_1k9)){var _1ks=B(_1cM(E(_1iX),_1k7.a,_1je));}else{var _1ks=B(_1eu(_1iX,_1je));}return {_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(B(_1gw(_1jc,_1k7.b))),d:E(_1jc),e:E(_1kr),f:E(_1ks),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_wB),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};case 114:var _1kt=B(_6X(_1gX,_1j4));return {_:0,a:E({_:0,a:E(B(_6X(_1h8,_1j4))),b:E(B(_1ds(_1kt.a,E(_1kt.b),new T(function(){return B(_6X(_1ix,_1j4));})))),c:E(_1j1),d:B(_6X(_1hl,_1j4)),e:32,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1kt),c:E(_1hf),d:E(_1jc),e:E(_1jd),f:E(B(_6k(_1hi,_1je))),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_wB),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};case 115:return {_:0,a:E({_:0,a:E(_1iZ),b:E(B(_1iT(_1j0))),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};case 116:var _1ku=E(_1jE),_1kv=B(_1cn(_1ku,_1jC)),_1kw=E(_1kv.a);if(!E(_1kw)){var _1kx=true;}else{var _1kx=false;}if(!E(_1kx)){var _1ky=B(_1cM(E(_1iX),_1kw,_1je));}else{var _1ky=B(_1cM(E(_1iX),_1ku+1|0,_1je));}if(!E(_1kx)){var _1kz=__Z;}else{var _1kz=E(_1kv.b);}if(!B(_qV(_1kz,_S))){var _1kA=B(_1iW(_1iX,_1kz,_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4,_1j5,_1j6,_1j7,_1j8,_1j9,_1ja,_1jb,_1jc,_1jd,_1ky,_1jf,_1jg,_1jh,_1ji,_1jj,_1jk,_1jl,_1jm,_1jn,_1jo,_1jp,_1jq,_1jr,_1js,_1jt,_1ju,_1jv,_1jw,_1jx,_1jy,_1jz,_1jA)),_1kB=E(_1kA.a);return {_:0,a:E({_:0,a:E(_1kB.a),b:E(_1kB.b),c:E(_1kB.c),d:_1kB.d,e:_1kB.e,f:_1kB.f,g:E(_1kB.g),h:_1kB.h,i:E(B(_q(_1j7,_1jB))),j:E(_1kB.j),k:E(_1kB.k)}),b:E(_1kA.b),c:E(_1kA.c),d:E(_1kA.d),e:E(_1kA.e),f:E(_1kA.f),g:E(_1kA.g),h:E(_1kA.h),i:_1kA.i,j:_1kA.j,k:_1kA.k,l:_1kA.l,m:E(_1kA.m),n:_1kA.n,o:E(_1kA.o),p:E(_1kA.p),q:_1kA.q,r:E(_1kA.r),s:_1kA.s,t:E(_1kA.t),u:E(_1kA.u)};}else{return {_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1ky),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};}break;case 119:return {_:0,a:E({_:0,a:E(_1h7),b:E(_1hC),c:E(_1j1),d:E(_1hm),e:32,f:0,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1gR),c:E(_1hh),d:E(_1jc),e:E(_1jd),f:E(B(_6k(_1hi,_1je))),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_wB),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};default:return {_:0,a:E({_:0,a:E(_1iZ),b:E(_1j0),c:E(_1j1),d:_1j2,e:_1j3,f:_1j4,g:E(_1j5),h:_1j6,i:E(B(_q(_1j7,_1jB))),j:E(_1j8),k:E(_1j9)}),b:E(_1ja),c:E(_1jb),d:E(_1jc),e:E(_1jd),f:E(_1je),g:E(_1jf),h:E(_1jg),i:_1jh,j:_1ji,k:_1jj,l:_1jk,m:E(_1jl),n:_1jm,o:E(_1jn),p:E(_1jo),q:_1jp,r:E(_1jq),s:_1jr,t:E({_:0,a:E(_1js),b:E(_1jt),c:E(_1ju),d:E(_1jv),e:E(_1jw),f:E(_1jx),g:E(_1jy),h:E(_1jz)}),u:E(_1jA)};}}},_1kC=function(_1kD,_1kE){while(1){var _1kF=E(_1kE);if(!_1kF._){return __Z;}else{var _1kG=_1kF.b,_1kH=E(_1kD);if(_1kH==1){return E(_1kG);}else{_1kD=_1kH-1|0;_1kE=_1kG;continue;}}}},_1kI=new T(function(){return B(unCStr("X"));}),_1kJ=new T(function(){return B(_ed("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1kK=38,_1kL=function(_1kM,_1kN,_1kO,_1kP,_1kQ,_1kR,_1kS,_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3,_1l4,_1l5,_1l6,_1l7,_1l8,_1l9){var _1la=E(_1kO);if(!_1la._){return {_:0,a:_1kP,b:_1kQ,c:_1kR,d:_1kS,e:_1kT,f:_1kU,g:_1kV,h:_1kW,i:_1kX,j:_1kY,k:_1kZ,l:_1l0,m:_1l1,n:_1l2,o:_1l3,p:_1l4,q:_1l5,r:_1l6,s:_1l7,t:_1l8,u:_1l9};}else{var _1lb=_1la.b,_1lc=E(_1la.a),_1ld=_1lc.a,_1le=_1lc.b,_1lf=function(_1lg,_1lh,_1li){var _1lj=function(_1lk,_1ll){if(!B(_qV(_1lk,_S))){var _1lm=E(_1kP),_1ln=E(_1l8),_1lo=B(_1iW(_1ll,_1lk,_1lm.a,_1lm.b,_1lm.c,_1lm.d,_1lm.e,_1lm.f,_1lm.g,_1lm.h,_1lm.i,_1lm.j,_1lm.k,_1kQ,_1kR,_1kS,_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3,_1l4,_1l5,_1l6,_1l7,_1ln.a,_1ln.b,_1ln.c,_1ln.d,_1ln.e,_1ln.f,_1ln.g,_1ln.h,_1l9)),_1lp=_1lo.a,_1lq=_1lo.b,_1lr=_1lo.c,_1ls=_1lo.d,_1lt=_1lo.e,_1lu=_1lo.f,_1lv=_1lo.g,_1lw=_1lo.h,_1lx=_1lo.i,_1ly=_1lo.j,_1lz=_1lo.k,_1lA=_1lo.l,_1lB=_1lo.m,_1lC=_1lo.n,_1lD=_1lo.o,_1lE=_1lo.p,_1lF=_1lo.q,_1lG=_1lo.r,_1lH=_1lo.s,_1lI=_1lo.t,_1lJ=_1lo.u;if(B(_mz(_1lu,0))!=B(_mz(_1kU,0))){return {_:0,a:_1lp,b:_1lq,c:_1lr,d:_1ls,e:_1lt,f:_1lu,g:_1lv,h:_1lw,i:_1lx,j:_1ly,k:_1lz,l:_1lA,m:_1lB,n:_1lC,o:_1lD,p:_1lE,q:_1lF,r:_1lG,s:_1lH,t:_1lI,u:_1lJ};}else{return new F(function(){return _1kL(new T(function(){return E(_1kM)+1|0;}),_1kN,_1lb,_1lp,_1lq,_1lr,_1ls,_1lt,_1lu,_1lv,_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,_1lC,_1lD,_1lE,_1lF,_1lG,_1lH,_1lI,_1lJ);});}}else{return new F(function(){return _1kL(new T(function(){return E(_1kM)+1|0;}),_1kN,_1lb,_1kP,_1kQ,_1kR,_1kS,_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3,_1l4,_1l5,_1l6,_1l7,_1l8,_1l9);});}},_1lK=B(_mz(_1kN,0))-B(_mz(new T2(1,_1lg,_1lh),0))|0;if(_1lK>0){var _1lL=B(_1kC(_1lK,_1kN));}else{var _1lL=E(_1kN);}if(E(B(_1bD(_1lg,_1lh,_Tu)))==63){var _1lM=B(_RX(_1lg,_1lh));}else{var _1lM=new T2(1,_1lg,_1lh);}var _1lN=function(_1lO){if(!B(_4A(_hd,_1kK,_1ld))){return new T2(0,_1le,_1kM);}else{var _1lP=function(_1lQ){while(1){var _1lR=B((function(_1lS){var _1lT=E(_1lS);if(!_1lT._){return true;}else{var _1lU=_1lT.b,_1lV=E(_1lT.a);if(!_1lV._){return E(_1kJ);}else{switch(E(_1lV.a)){case 99:var _1lW=E(_1kP);if(!E(_1lW.k)){return false;}else{var _1lX=function(_1lY){while(1){var _1lZ=E(_1lY);if(!_1lZ._){return true;}else{var _1m0=_1lZ.b,_1m1=E(_1lZ.a);if(!_1m1._){return E(_1kJ);}else{if(E(_1m1.a)==115){var _1m2=B(_Gk(B(_sF(_1ck,_1m1.b))));if(!_1m2._){return E(_1ci);}else{if(!E(_1m2.b)._){if(_1lW.f!=E(_1m2.a)){return false;}else{_1lY=_1m0;continue;}}else{return E(_1cj);}}}else{_1lY=_1m0;continue;}}}}};return new F(function(){return _1lX(_1lU);});}break;case 115:var _1m3=E(_1kP),_1m4=_1m3.f,_1m5=B(_Gk(B(_sF(_1ck,_1lV.b))));if(!_1m5._){return E(_1ci);}else{if(!E(_1m5.b)._){if(_1m4!=E(_1m5.a)){return false;}else{var _1m6=function(_1m7){while(1){var _1m8=E(_1m7);if(!_1m8._){return true;}else{var _1m9=_1m8.b,_1ma=E(_1m8.a);if(!_1ma._){return E(_1kJ);}else{switch(E(_1ma.a)){case 99:if(!E(_1m3.k)){return false;}else{_1m7=_1m9;continue;}break;case 115:var _1mb=B(_Gk(B(_sF(_1ck,_1ma.b))));if(!_1mb._){return E(_1ci);}else{if(!E(_1mb.b)._){if(_1m4!=E(_1mb.a)){return false;}else{_1m7=_1m9;continue;}}else{return E(_1cj);}}break;default:_1m7=_1m9;continue;}}}}};return new F(function(){return _1m6(_1lU);});}}else{return E(_1cj);}}break;default:_1lQ=_1lU;return __continue;}}}})(_1lQ));if(_1lR!=__continue){return _1lR;}}};return (!B(_1lP(_1li)))?(!B(_qV(_1lM,_1kI)))?new T2(0,_S,_1kM):new T2(0,_1le,_1kM):new T2(0,_1le,_1kM);}};if(E(B(_1bL(_1lg,_1lh,_Tu)))==63){if(!B(_6f(_1lL,_S))){var _1mc=E(_1lL);if(!_1mc._){return E(_S2);}else{if(!B(_qV(_1lM,B(_RX(_1mc.a,_1mc.b))))){if(!B(_qV(_1lM,_1kI))){return new F(function(){return _1lj(_S,_1kM);});}else{return new F(function(){return _1lj(_1le,_1kM);});}}else{var _1md=B(_1lN(_));return new F(function(){return _1lj(_1md.a,_1md.b);});}}}else{if(!B(_qV(_1lM,_1lL))){if(!B(_qV(_1lM,_1kI))){return new F(function(){return _1lj(_S,_1kM);});}else{return new F(function(){return _1lj(_1le,_1kM);});}}else{var _1me=B(_1lN(_));return new F(function(){return _1lj(_1me.a,_1me.b);});}}}else{if(!B(_qV(_1lM,_1lL))){if(!B(_qV(_1lM,_1kI))){return new F(function(){return _1lj(_S,_1kM);});}else{return new F(function(){return _1lj(_1le,_1kM);});}}else{var _1mf=B(_1lN(_));return new F(function(){return _1lj(_1mf.a,_1mf.b);});}}},_1mg=E(_1ld);if(!_1mg._){return E(_Tu);}else{var _1mh=_1mg.a,_1mi=E(_1mg.b);if(!_1mi._){return new F(function(){return _1lf(_1mh,_S,_S);});}else{var _1mj=E(_1mh),_1mk=new T(function(){var _1ml=B(_Hc(38,_1mi.a,_1mi.b));return new T2(0,_1ml.a,_1ml.b);});if(E(_1mj)==38){return E(_Tu);}else{return new F(function(){return _1lf(_1mj,new T(function(){return E(E(_1mk).a);}),new T(function(){return E(E(_1mk).b);}));});}}}}},_1mm="]",_1mn="}",_1mo=":",_1mp=",",_1mq=new T(function(){return eval("JSON.stringify");}),_1mr="false",_1ms="null",_1mt="[",_1mu="{",_1mv="\"",_1mw="true",_1mx=function(_1my,_1mz){var _1mA=E(_1mz);switch(_1mA._){case 0:return new T2(0,new T(function(){return jsShow(_1mA.a);}),_1my);case 1:return new T2(0,new T(function(){var _1mB=__app1(E(_1mq),_1mA.a);return String(_1mB);}),_1my);case 2:return (!E(_1mA.a))?new T2(0,_1mr,_1my):new T2(0,_1mw,_1my);case 3:var _1mC=E(_1mA.a);if(!_1mC._){return new T2(0,_1mt,new T2(1,_1mm,_1my));}else{var _1mD=new T(function(){var _1mE=new T(function(){var _1mF=function(_1mG){var _1mH=E(_1mG);if(!_1mH._){return E(new T2(1,_1mm,_1my));}else{var _1mI=new T(function(){var _1mJ=B(_1mx(new T(function(){return B(_1mF(_1mH.b));}),_1mH.a));return new T2(1,_1mJ.a,_1mJ.b);});return new T2(1,_1mp,_1mI);}};return B(_1mF(_1mC.b));}),_1mK=B(_1mx(_1mE,_1mC.a));return new T2(1,_1mK.a,_1mK.b);});return new T2(0,_1mt,_1mD);}break;case 4:var _1mL=E(_1mA.a);if(!_1mL._){return new T2(0,_1mu,new T2(1,_1mn,_1my));}else{var _1mM=E(_1mL.a),_1mN=new T(function(){var _1mO=new T(function(){var _1mP=function(_1mQ){var _1mR=E(_1mQ);if(!_1mR._){return E(new T2(1,_1mn,_1my));}else{var _1mS=E(_1mR.a),_1mT=new T(function(){var _1mU=B(_1mx(new T(function(){return B(_1mP(_1mR.b));}),_1mS.b));return new T2(1,_1mU.a,_1mU.b);});return new T2(1,_1mp,new T2(1,_1mv,new T2(1,_1mS.a,new T2(1,_1mv,new T2(1,_1mo,_1mT)))));}};return B(_1mP(_1mL.b));}),_1mV=B(_1mx(_1mO,_1mM.b));return new T2(1,_1mV.a,_1mV.b);});return new T2(0,_1mu,new T2(1,new T(function(){var _1mW=__app1(E(_1mq),E(_1mM.a));return String(_1mW);}),new T2(1,_1mo,_1mN)));}break;default:return new T2(0,_1ms,_1my);}},_1mX=new T(function(){return toJSStr(_S);}),_1mY=function(_1mZ){var _1n0=B(_1mx(_S,_1mZ)),_1n1=jsCat(new T2(1,_1n0.a,_1n0.b),E(_1mX));return E(_1n1);},_1n2=function(_1n3){var _1n4=E(_1n3);if(!_1n4._){return new T2(0,_S,_S);}else{var _1n5=E(_1n4.a),_1n6=new T(function(){var _1n7=B(_1n2(_1n4.b));return new T2(0,_1n7.a,_1n7.b);});return new T2(0,new T2(1,_1n5.a,new T(function(){return E(E(_1n6).a);})),new T2(1,_1n5.b,new T(function(){return E(E(_1n6).b);})));}},_1n8=new T(function(){return B(unCStr("Rk"));}),_1n9=function(_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv){while(1){var _1nw=B((function(_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS){var _1nT=E(_1nx);if(!_1nT._){return {_:0,a:_1ny,b:_1nz,c:_1nA,d:_1nB,e:_1nC,f:_1nD,g:_1nE,h:_1nF,i:_1nG,j:_1nH,k:_1nI,l:_1nJ,m:_1nK,n:_1nL,o:_1nM,p:_1nN,q:_1nO,r:_1nP,s:_1nQ,t:_1nR,u:_1nS};}else{var _1nU=_1nT.a,_1nV=B(_Sl(B(unAppCStr("e.e",new T2(1,_1nU,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1nU,_1n8)));})))),_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS));_1na=_1nT.b;_1nb=_1nV.a;_1nc=_1nV.b;_1nd=_1nV.c;_1ne=_1nV.d;_1nf=_1nV.e;_1ng=_1nV.f;_1nh=_1nV.g;_1ni=_1nV.h;_1nj=_1nV.i;_1nk=_1nV.j;_1nl=_1nV.k;_1nm=_1nV.l;_1nn=_1nV.m;_1no=_1nV.n;_1np=_1nV.o;_1nq=_1nV.p;_1nr=_1nV.q;_1ns=_1nV.r;_1nt=_1nV.s;_1nu=_1nV.t;_1nv=_1nV.u;return __continue;}})(_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv));if(_1nw!=__continue){return _1nw;}}},_1nW=function(_1nX){var _1nY=E(_1nX);switch(_1nY){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1nY>>>0>1114111){return new F(function(){return _wL(_1nY);});}else{return _1nY;}}},_1nZ=function(_1o0,_1o1,_1o2){while(1){var _1o3=E(_1o1);if(!_1o3._){return (E(_1o2)._==0)?true:false;}else{var _1o4=E(_1o2);if(!_1o4._){return false;}else{if(!B(A3(_4y,_1o0,_1o3.a,_1o4.a))){return false;}else{_1o1=_1o3.b;_1o2=_1o4.b;continue;}}}}},_1o5=function(_1o6,_1o7){return (!B(_1nZ(_rs,_1o6,_1o7)))?true:false;},_1o8=function(_1o9,_1oa){return new F(function(){return _1nZ(_rs,_1o9,_1oa);});},_1ob=new T2(0,_1o8,_1o5),_1oc=function(_1od){var _1oe=E(_1od);if(!_1oe._){return new T2(0,_S,_S);}else{var _1of=E(_1oe.a),_1og=new T(function(){var _1oh=B(_1oc(_1oe.b));return new T2(0,_1oh.a,_1oh.b);});return new T2(0,new T2(1,_1of.a,new T(function(){return E(E(_1og).a);})),new T2(1,_1of.b,new T(function(){return E(E(_1og).b);})));}},_1oi=function(_1oj,_1ok){while(1){var _1ol=E(_1ok);if(!_1ol._){return __Z;}else{var _1om=_1ol.b,_1on=E(_1oj);if(_1on==1){return E(_1om);}else{_1oj=_1on-1|0;_1ok=_1om;continue;}}}},_1oo=function(_1op,_1oq){while(1){var _1or=E(_1oq);if(!_1or._){return __Z;}else{var _1os=_1or.b,_1ot=E(_1op);if(_1ot==1){return E(_1os);}else{_1op=_1ot-1|0;_1oq=_1os;continue;}}}},_1ou=function(_1ov){return new F(function(){return _Gr(_1ov,_S);});},_1ow=function(_1ox,_1oy,_1oz,_1oA){var _1oB=new T(function(){return B(_MK(_hd,_1oy,_1oz));}),_1oC=new T(function(){var _1oD=E(_1oB),_1oE=new T(function(){var _1oF=_1oD+1|0;if(_1oF>0){return B(_1oo(_1oF,_1oz));}else{return E(_1oz);}});if(0>=_1oD){return E(_1oE);}else{var _1oG=function(_1oH,_1oI){var _1oJ=E(_1oH);if(!_1oJ._){return E(_1oE);}else{var _1oK=_1oJ.a,_1oL=E(_1oI);return (_1oL==1)?new T2(1,_1oK,_1oE):new T2(1,_1oK,new T(function(){return B(_1oG(_1oJ.b,_1oL-1|0));}));}};return B(_1oG(_1oz,_1oD));}}),_1oM=new T(function(){var _1oN=E(_1oB),_1oO=new T(function(){if(E(_1oy)==94){return B(A2(_1ox,new T(function(){return B(_6X(_1oA,_1oN+1|0));}),new T(function(){return B(_6X(_1oA,_1oN));})));}else{return B(A2(_1ox,new T(function(){return B(_6X(_1oA,_1oN));}),new T(function(){return B(_6X(_1oA,_1oN+1|0));})));}}),_1oP=new T2(1,_1oO,new T(function(){var _1oQ=_1oN+2|0;if(_1oQ>0){return B(_1oi(_1oQ,_1oA));}else{return E(_1oA);}}));if(0>=_1oN){return E(_1oP);}else{var _1oR=function(_1oS,_1oT){var _1oU=E(_1oS);if(!_1oU._){return E(_1oP);}else{var _1oV=_1oU.a,_1oW=E(_1oT);return (_1oW==1)?new T2(1,_1oV,_1oP):new T2(1,_1oV,new T(function(){return B(_1oR(_1oU.b,_1oW-1|0));}));}};return B(_1oR(_1oA,_1oN));}});return (E(_1oy)==94)?new T2(0,new T(function(){return B(_1ou(_1oC));}),new T(function(){return B(_1ou(_1oM));})):new T2(0,_1oC,_1oM);},_1oX=new T(function(){return B(_ct(_oS,_oR));}),_1oY=function(_1oZ,_1p0,_1p1){while(1){if(!E(_1oX)){if(!B(_ct(B(_15Q(_1p0,_oS)),_oR))){if(!B(_ct(_1p0,_b1))){var _1p2=B(_ol(_1oZ,_1oZ)),_1p3=B(_15B(B(_eU(_1p0,_b1)),_oS)),_1p4=B(_ol(_1oZ,_1p1));_1oZ=_1p2;_1p0=_1p3;_1p1=_1p4;continue;}else{return new F(function(){return _ol(_1oZ,_1p1);});}}else{var _1p2=B(_ol(_1oZ,_1oZ)),_1p3=B(_15B(_1p0,_oS));_1oZ=_1p2;_1p0=_1p3;continue;}}else{return E(_a0);}}},_1p5=function(_1p6,_1p7){while(1){if(!E(_1oX)){if(!B(_ct(B(_15Q(_1p7,_oS)),_oR))){if(!B(_ct(_1p7,_b1))){return new F(function(){return _1oY(B(_ol(_1p6,_1p6)),B(_15B(B(_eU(_1p7,_b1)),_oS)),_1p6);});}else{return E(_1p6);}}else{var _1p8=B(_ol(_1p6,_1p6)),_1p9=B(_15B(_1p7,_oS));_1p6=_1p8;_1p7=_1p9;continue;}}else{return E(_a0);}}},_1pa=function(_1pb,_1pc){if(!B(_dd(_1pc,_oR))){if(!B(_ct(_1pc,_oR))){return new F(function(){return _1p5(_1pb,_1pc);});}else{return E(_b1);}}else{return E(_px);}},_1pd=94,_1pe=45,_1pf=43,_1pg=42,_1ph=function(_1pi,_1pj){while(1){var _1pk=B((function(_1pl,_1pm){var _1pn=E(_1pm);if(!_1pn._){return __Z;}else{if((B(_mz(_1pl,0))+1|0)==B(_mz(_1pn,0))){if(!B(_4A(_hd,_1pd,_1pl))){if(!B(_4A(_hd,_1pg,_1pl))){if(!B(_4A(_hd,_1pf,_1pl))){if(!B(_4A(_hd,_1pe,_1pl))){return E(_1pn);}else{var _1po=B(_1ow(_eU,45,_1pl,_1pn));_1pi=_1po.a;_1pj=_1po.b;return __continue;}}else{var _1pp=B(_1ow(_cB,43,_1pl,_1pn));_1pi=_1pp.a;_1pj=_1pp.b;return __continue;}}else{var _1pq=B(_1ow(_ol,42,_1pl,_1pn));_1pi=_1pq.a;_1pj=_1pq.b;return __continue;}}else{var _1pr=B(_1ow(_1pa,94,new T(function(){return B(_1ou(_1pl));}),new T(function(){return B(_Gr(_1pn,_S));})));_1pi=_1pr.a;_1pj=_1pr.b;return __continue;}}else{return __Z;}}})(_1pi,_1pj));if(_1pk!=__continue){return _1pk;}}},_1ps=function(_1pt){var _1pu=E(_1pt);if(!_1pu._){return new T2(0,_S,_S);}else{var _1pv=E(_1pu.a),_1pw=new T(function(){var _1px=B(_1ps(_1pu.b));return new T2(0,_1px.a,_1px.b);});return new T2(0,new T2(1,_1pv.a,new T(function(){return E(E(_1pw).a);})),new T2(1,_1pv.b,new T(function(){return E(E(_1pw).b);})));}},_1py=new T(function(){return B(unCStr("0123456789+-"));}),_1pz=function(_1pA){while(1){var _1pB=E(_1pA);if(!_1pB._){return true;}else{if(!B(_4A(_hd,_1pB.a,_1py))){return false;}else{_1pA=_1pB.b;continue;}}}},_1pC=new T(function(){return B(err(_sy));}),_1pD=new T(function(){return B(err(_sA));}),_1pE=function(_1pF,_1pG){var _1pH=function(_1pI,_1pJ){var _1pK=function(_1pL){return new F(function(){return A1(_1pJ,new T(function(){return B(_fz(_1pL));}));});},_1pM=new T(function(){return B(_De(function(_1pN){return new F(function(){return A3(_1pF,_1pN,_1pI,_1pK);});}));}),_1pO=function(_1pP){return E(_1pM);},_1pQ=function(_1pR){return new F(function(){return A2(_BV,_1pR,_1pO);});},_1pS=new T(function(){return B(_De(function(_1pT){var _1pU=E(_1pT);if(_1pU._==4){var _1pV=E(_1pU.a);if(!_1pV._){return new F(function(){return A3(_1pF,_1pU,_1pI,_1pJ);});}else{if(E(_1pV.a)==45){if(!E(_1pV.b)._){return E(new T1(1,_1pQ));}else{return new F(function(){return A3(_1pF,_1pU,_1pI,_1pJ);});}}else{return new F(function(){return A3(_1pF,_1pU,_1pI,_1pJ);});}}}else{return new F(function(){return A3(_1pF,_1pU,_1pI,_1pJ);});}}));}),_1pW=function(_1pX){return E(_1pS);};return new T1(1,function(_1pY){return new F(function(){return A2(_BV,_1pY,_1pW);});});};return new F(function(){return _E5(_1pH,_1pG);});},_1pZ=function(_1q0){var _1q1=E(_1q0);if(_1q1._==5){var _1q2=B(_G3(_1q1.a));return (_1q2._==0)?E(_G8):function(_1q3,_1q4){return new F(function(){return A1(_1q4,_1q2.a);});};}else{return E(_G8);}},_1q5=new T(function(){return B(A3(_1pE,_1pZ,_DL,_Fy));}),_1q6=function(_1q7,_1q8){var _1q9=E(_1q8);if(!_1q9._){return __Z;}else{var _1qa=_1q9.a,_1qb=_1q9.b,_1qc=function(_1qd){var _1qe=B(_1ps(_1q7)),_1qf=_1qe.a;return (!B(_4A(_qk,_1qa,_1qf)))?__Z:new T2(1,new T(function(){return B(_6X(_1qe.b,B(_MK(_qk,_1qa,_1qf))));}),new T(function(){return B(_1q6(_1q7,_1qb));}));};if(!B(_6f(_1qa,_S))){if(!B(_1pz(_1qa))){return new F(function(){return _1qc(_);});}else{return new T2(1,new T(function(){var _1qg=B(_Gk(B(_sF(_1q5,_1qa))));if(!_1qg._){return E(_1pC);}else{if(!E(_1qg.b)._){return E(_1qg.a);}else{return E(_1pD);}}}),new T(function(){return B(_1q6(_1q7,_1qb));}));}}else{return new F(function(){return _1qc(_);});}}},_1qh=new T(function(){return B(unCStr("+-*^"));}),_1qi=new T(function(){return B(unCStr("0123456789"));}),_1qj=new T(function(){return B(_Lo("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1qk=new T2(1,_S,_S),_1ql=function(_1qm){var _1qn=E(_1qm);if(!_1qn._){return new T2(0,_1qk,_S);}else{var _1qo=_1qn.a,_1qp=new T(function(){var _1qq=B(_1ql(_1qn.b)),_1qr=E(_1qq.a);if(!_1qr._){return E(_1qj);}else{return new T3(0,_1qr.a,_1qr.b,_1qq.b);}});return (!B(_4A(_hd,_1qo,_1qi)))?(!B(_4A(_hd,_1qo,_1qh)))?new T2(0,new T2(1,new T2(1,_1qo,new T(function(){return E(E(_1qp).a);})),new T(function(){return E(E(_1qp).b);})),new T(function(){return E(E(_1qp).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1qp).a);}),new T(function(){return E(E(_1qp).b);}))),new T2(1,_1qo,new T(function(){return E(E(_1qp).c);}))):new T2(0,new T2(1,new T2(1,_1qo,new T(function(){return E(E(_1qp).a);})),new T(function(){return E(E(_1qp).b);})),new T(function(){return E(E(_1qp).c);}));}},_1qs=function(_1qt,_1qu){var _1qv=new T(function(){var _1qw=B(_1ql(_1qu)),_1qx=E(_1qw.a);if(!_1qx._){return E(_1qj);}else{return new T3(0,_1qx.a,_1qx.b,_1qw.b);}});return (!B(_4A(_hd,_1qt,_1qi)))?(!B(_4A(_hd,_1qt,_1qh)))?new T2(0,new T2(1,new T2(1,_1qt,new T(function(){return E(E(_1qv).a);})),new T(function(){return E(E(_1qv).b);})),new T(function(){return E(E(_1qv).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1qv).a);}),new T(function(){return E(E(_1qv).b);}))),new T2(1,_1qt,new T(function(){return E(E(_1qv).c);}))):new T2(0,new T2(1,new T2(1,_1qt,new T(function(){return E(E(_1qv).a);})),new T(function(){return E(E(_1qv).b);})),new T(function(){return E(E(_1qv).c);}));},_1qy=function(_1qz,_1qA){while(1){var _1qB=E(_1qz);if(!_1qB._){return E(_1qA);}else{_1qz=_1qB.b;_1qA=_1qB.a;continue;}}},_1qC=function(_1qD,_1qE,_1qF){return new F(function(){return _1qy(_1qE,_1qD);});},_1qG=function(_1qH,_1qI){var _1qJ=E(_1qI);if(!_1qJ._){return __Z;}else{var _1qK=B(_1qs(_1qJ.a,_1qJ.b)),_1qL=B(_1ph(_1qK.b,B(_1q6(_1qH,_1qK.a))));if(!_1qL._){return E(_1qJ);}else{return new F(function(){return _17U(0,B(_1qC(_1qL.a,_1qL.b,_Tu)),_S);});}}},_1qM=function(_1qN,_1qO){var _1qP=function(_1qQ,_1qR){while(1){var _1qS=B((function(_1qT,_1qU){var _1qV=E(_1qU);if(!_1qV._){return (!B(_qV(_1qT,_S)))?new T2(0,_wB,_1qT):new T2(0,_wA,_S);}else{var _1qW=_1qV.b,_1qX=B(_1oc(_1qV.a)).a;if(!B(_4A(_hd,_1dM,_1qX))){var _1qY=_1qT;_1qQ=_1qY;_1qR=_1qW;return __continue;}else{var _1qZ=B(_1ei(_1qX)),_1r0=_1qZ.a,_1r1=_1qZ.b;if(!B(_6f(_1r1,_S))){if(!B(_qV(B(_1qG(_1qN,_1r0)),B(_1qG(_1qN,_1r1))))){return new T2(0,_wA,_S);}else{var _1r2=new T(function(){if(!B(_qV(_1qT,_S))){return B(_q(_1qT,new T(function(){return B(unAppCStr(" ",_1r0));},1)));}else{return E(_1r0);}});_1qQ=_1r2;_1qR=_1qW;return __continue;}}else{return new T2(0,_wA,_S);}}}})(_1qQ,_1qR));if(_1qS!=__continue){return _1qS;}}};return new F(function(){return _1qP(_S,_1qO);});},_1r3=function(_1r4,_1r5){var _1r6=new T(function(){var _1r7=B(_Gk(B(_sF(_17K,new T(function(){return B(_pU(3,B(_A(0,imul(E(_1r5),E(_1r4)-1|0)|0,_S))));})))));if(!_1r7._){return E(_17J);}else{if(!E(_1r7.b)._){return E(_1r7.a);}else{return E(_17I);}}});return new T2(0,new T(function(){return B(_aB(_1r6,_1r4));}),_1r6);},_1r8=function(_1r9,_1ra){while(1){var _1rb=E(_1ra);if(!_1rb._){return __Z;}else{var _1rc=_1rb.b,_1rd=E(_1r9);if(_1rd==1){return E(_1rc);}else{_1r9=_1rd-1|0;_1ra=_1rc;continue;}}}},_1re=function(_1rf,_1rg){while(1){var _1rh=E(_1rg);if(!_1rh._){return __Z;}else{var _1ri=_1rh.b,_1rj=E(_1rf);if(_1rj==1){return E(_1ri);}else{_1rf=_1rj-1|0;_1rg=_1ri;continue;}}}},_1rk=64,_1rl=new T2(1,_1rk,_S),_1rm=function(_1rn,_1ro,_1rp,_1rq){return (!B(_qV(_1rn,_1rp)))?true:(!B(_ct(_1ro,_1rq)))?true:false;},_1rr=function(_1rs,_1rt){var _1ru=E(_1rs),_1rv=E(_1rt);return new F(function(){return _1rm(_1ru.a,_1ru.b,_1rv.a,_1rv.b);});},_1rw=function(_1rx,_1ry,_1rz,_1rA){if(!B(_qV(_1rx,_1rz))){return false;}else{return new F(function(){return _ct(_1ry,_1rA);});}},_1rB=function(_1rC,_1rD){var _1rE=E(_1rC),_1rF=E(_1rD);return new F(function(){return _1rw(_1rE.a,_1rE.b,_1rF.a,_1rF.b);});},_1rG=new T2(0,_1rB,_1rr),_1rH=function(_1rI){var _1rJ=E(_1rI);if(!_1rJ._){return new T2(0,_S,_S);}else{var _1rK=E(_1rJ.a),_1rL=new T(function(){var _1rM=B(_1rH(_1rJ.b));return new T2(0,_1rM.a,_1rM.b);});return new T2(0,new T2(1,_1rK.a,new T(function(){return E(E(_1rL).a);})),new T2(1,_1rK.b,new T(function(){return E(E(_1rL).b);})));}},_1rN=function(_1rO){var _1rP=E(_1rO);if(!_1rP._){return new T2(0,_S,_S);}else{var _1rQ=E(_1rP.a),_1rR=new T(function(){var _1rS=B(_1rN(_1rP.b));return new T2(0,_1rS.a,_1rS.b);});return new T2(0,new T2(1,_1rQ.a,new T(function(){return E(E(_1rR).a);})),new T2(1,_1rQ.b,new T(function(){return E(E(_1rR).b);})));}},_1rT=function(_1rU){var _1rV=E(_1rU);if(!_1rV._){return new T2(0,_S,_S);}else{var _1rW=E(_1rV.a),_1rX=new T(function(){var _1rY=B(_1rT(_1rV.b));return new T2(0,_1rY.a,_1rY.b);});return new T2(0,new T2(1,_1rW.a,new T(function(){return E(E(_1rX).a);})),new T2(1,_1rW.b,new T(function(){return E(E(_1rX).b);})));}},_1rZ=function(_1s0,_1s1){return (_1s0<=_1s1)?new T2(1,_1s0,new T(function(){return B(_1rZ(_1s0+1|0,_1s1));})):__Z;},_1s2=new T(function(){return B(_1rZ(65,90));}),_1s3=function(_1s4){return (_1s4<=122)?new T2(1,_1s4,new T(function(){return B(_1s3(_1s4+1|0));})):E(_1s2);},_1s5=new T(function(){return B(_1s3(97));}),_1s6=function(_1s7){while(1){var _1s8=E(_1s7);if(!_1s8._){return true;}else{if(!B(_4A(_hd,_1s8.a,_1s5))){return false;}else{_1s7=_1s8.b;continue;}}}},_1s9=new T2(0,_S,_S),_1sa=new T(function(){return B(err(_sy));}),_1sb=new T(function(){return B(err(_sA));}),_1sc=new T(function(){return B(A3(_1pE,_1pZ,_DL,_Fy));}),_1sd=function(_1se,_1sf,_1sg){while(1){var _1sh=B((function(_1si,_1sj,_1sk){var _1sl=E(_1sk);if(!_1sl._){return __Z;}else{var _1sm=_1sl.b,_1sn=B(_1rN(_1sj)),_1so=_1sn.a,_1sp=B(_1rH(_1so)),_1sq=_1sp.a,_1sr=new T(function(){return E(B(_1rT(_1sl.a)).a);}),_1ss=new T(function(){return B(_4A(_hd,_1dM,_1sr));}),_1st=new T(function(){if(!E(_1ss)){return E(_1s9);}else{var _1su=B(_1ei(_1sr));return new T2(0,_1su.a,_1su.b);}}),_1sv=new T(function(){return E(E(_1st).a);}),_1sw=new T(function(){return B(_MK(_qk,_1sv,_1sq));}),_1sx=new T(function(){var _1sy=function(_){var _1sz=B(_mz(_1sj,0))-1|0,_1sA=function(_1sB){if(_1sB>=0){var _1sC=newArr(_1sB,_18R),_1sD=_1sC,_1sE=E(_1sB);if(!_1sE){return new T4(0,E(_1cl),E(_1sz),0,_1sD);}else{var _1sF=function(_1sG,_1sH,_){while(1){var _1sI=E(_1sG);if(!_1sI._){return E(_);}else{var _=_1sD[_1sH]=_1sI.a;if(_1sH!=(_1sE-1|0)){var _1sJ=_1sH+1|0;_1sG=_1sI.b;_1sH=_1sJ;continue;}else{return E(_);}}}},_=B(_1sF(_1sn.b,0,_));return new T4(0,E(_1cl),E(_1sz),_1sE,_1sD);}}else{return E(_19L);}};if(0>_1sz){return new F(function(){return _1sA(0);});}else{return new F(function(){return _1sA(_1sz+1|0);});}};return B(_19M(_1sy));});if(!B(_4A(_qk,_1sv,_1sq))){var _1sK=false;}else{var _1sL=E(_1sx),_1sM=E(_1sL.a),_1sN=E(_1sL.b),_1sO=E(_1sw);if(_1sM>_1sO){var _1sP=B(_1ha(_1sO,_1sM,_1sN));}else{if(_1sO>_1sN){var _1sQ=B(_1ha(_1sO,_1sM,_1sN));}else{var _1sQ=E(_1sL.d[_1sO-_1sM|0])==E(_1si);}var _1sP=_1sQ;}var _1sK=_1sP;}var _1sR=new T(function(){return E(E(_1st).b);}),_1sS=new T(function(){return B(_MK(_qk,_1sR,_1sq));}),_1sT=new T(function(){if(!B(_4A(_qk,_1sR,_1sq))){return false;}else{var _1sU=E(_1sx),_1sV=E(_1sU.a),_1sW=E(_1sU.b),_1sX=E(_1sS);if(_1sV>_1sX){return B(_1ha(_1sX,_1sV,_1sW));}else{if(_1sX>_1sW){return B(_1ha(_1sX,_1sV,_1sW));}else{return E(_1sU.d[_1sX-_1sV|0])==E(_1si);}}}}),_1sY=new T(function(){var _1sZ=function(_){var _1t0=B(_mz(_1so,0))-1|0,_1t1=function(_1t2){if(_1t2>=0){var _1t3=newArr(_1t2,_18R),_1t4=_1t3,_1t5=E(_1t2);if(!_1t5){return new T4(0,E(_1cl),E(_1t0),0,_1t4);}else{var _1t6=function(_1t7,_1t8,_){while(1){var _1t9=E(_1t7);if(!_1t9._){return E(_);}else{var _=_1t4[_1t8]=_1t9.a;if(_1t8!=(_1t5-1|0)){var _1ta=_1t8+1|0;_1t7=_1t9.b;_1t8=_1ta;continue;}else{return E(_);}}}},_=B(_1t6(_1sp.b,0,_));return new T4(0,E(_1cl),E(_1t0),_1t5,_1t4);}}else{return E(_19L);}};if(0>_1t0){return new F(function(){return _1t1(0);});}else{return new F(function(){return _1t1(_1t0+1|0);});}};return B(_19M(_1sZ));}),_1tb=function(_1tc){var _1td=function(_1te){return (!E(_1sK))?__Z:(!E(_1sT))?__Z:new T2(1,new T2(0,_1sv,new T(function(){var _1tf=E(_1sY),_1tg=E(_1tf.a),_1th=E(_1tf.b),_1ti=E(_1sw);if(_1tg>_1ti){return B(_1ha(_1ti,_1tg,_1th));}else{if(_1ti>_1th){return B(_1ha(_1ti,_1tg,_1th));}else{return E(_1tf.d[_1ti-_1tg|0]);}}})),new T2(1,new T2(0,_1sR,new T(function(){var _1tj=E(_1sY),_1tk=E(_1tj.a),_1tl=E(_1tj.b),_1tm=E(_1sS);if(_1tk>_1tm){return B(_1ha(_1tm,_1tk,_1tl));}else{if(_1tm>_1tl){return B(_1ha(_1tm,_1tk,_1tl));}else{return E(_1tj.d[_1tm-_1tk|0]);}}})),_S));};if(!E(_1sK)){if(!E(_1sT)){return new F(function(){return _1td(_);});}else{return new T2(1,new T2(0,_1sR,new T(function(){var _1tn=E(_1sY),_1to=E(_1tn.a),_1tp=E(_1tn.b),_1tq=E(_1sS);if(_1to>_1tq){return B(_1ha(_1tq,_1to,_1tp));}else{if(_1tq>_1tp){return B(_1ha(_1tq,_1to,_1tp));}else{return E(_1tn.d[_1tq-_1to|0]);}}})),_S);}}else{return new F(function(){return _1td(_);});}};if(!E(_1sK)){var _1tr=B(_1tb(_));}else{if(!E(_1sT)){var _1ts=new T2(1,new T2(0,_1sv,new T(function(){var _1tt=E(_1sY),_1tu=E(_1tt.a),_1tv=E(_1tt.b),_1tw=E(_1sw);if(_1tu>_1tw){return B(_1ha(_1tw,_1tu,_1tv));}else{if(_1tw>_1tv){return B(_1ha(_1tw,_1tu,_1tv));}else{return E(_1tt.d[_1tw-_1tu|0]);}}})),_S);}else{var _1ts=B(_1tb(_));}var _1tr=_1ts;}if(!B(_1nZ(_1rG,_1tr,_S))){return new F(function(){return _q(_1tr,new T(function(){return B(_1sd(_1si,_1sj,_1sm));},1));});}else{if(!E(_1ss)){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{if(!B(_1s6(_1sv))){if(!B(_1s6(_1sR))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{if(!E(_1sK)){if(!E(_1sT)){if(!B(_6f(_1sv,_S))){if(!B(_1pz(_1sv))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{return new T2(1,new T2(0,_1sR,new T(function(){var _1tz=B(_Gk(B(_sF(_1sc,_1sv))));if(!_1tz._){return E(_1sa);}else{if(!E(_1tz.b)._){return E(_1tz.a);}else{return E(_1sb);}}})),new T(function(){return B(_1sd(_1si,_1sj,_1sm));}));}}else{var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}else{var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}else{var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}}else{if(!E(_1sK)){if(!E(_1sT)){if(!B(_6f(_1sR,_S))){if(!B(_1pz(_1sR))){if(!B(_1s6(_1sR))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{if(!B(_6f(_1sv,_S))){if(!B(_1pz(_1sv))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{return new T2(1,new T2(0,_1sR,new T(function(){var _1tA=B(_Gk(B(_sF(_1sc,_1sv))));if(!_1tA._){return E(_1sa);}else{if(!E(_1tA.b)._){return E(_1tA.a);}else{return E(_1sb);}}})),new T(function(){return B(_1sd(_1si,_1sj,_1sm));}));}}else{var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}}else{return new T2(1,new T2(0,_1sv,new T(function(){var _1tB=B(_Gk(B(_sF(_1sc,_1sR))));if(!_1tB._){return E(_1sa);}else{if(!E(_1tB.b)._){return E(_1tB.a);}else{return E(_1sb);}}})),new T(function(){return B(_1sd(_1si,_1sj,_1sm));}));}}else{if(!B(_1s6(_1sR))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{if(!B(_6f(_1sv,_S))){if(!B(_1pz(_1sv))){var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}else{return new T2(1,new T2(0,_1sR,new T(function(){var _1tC=B(_Gk(B(_sF(_1sc,_1sv))));if(!_1tC._){return E(_1sa);}else{if(!E(_1tC.b)._){return E(_1tC.a);}else{return E(_1sb);}}})),new T(function(){return B(_1sd(_1si,_1sj,_1sm));}));}}else{var _1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}}}else{var _1tD=B(_1s6(_1sR)),_1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}else{var _1tE=B(_1s6(_1sR)),_1tx=_1si,_1ty=_1sj;_1se=_1tx;_1sf=_1ty;_1sg=_1sm;return __continue;}}}}}})(_1se,_1sf,_1sg));if(_1sh!=__continue){return _1sh;}}},_1tF=102,_1tG=101,_1tH=new T(function(){return B(unCStr("=="));}),_1tI=new T(function(){return B(_ed("Action.hs:(103,17)-(107,70)|case"));}),_1tJ=new T(function(){return B(_ed("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1tK=5,_1tL=117,_1tM=98,_1tN=110,_1tO=118,_1tP=function(_1tQ,_1tR,_1tS,_1tT,_1tU,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_1u1,_1u2,_1u3){var _1u4=B(_6X(B(_6X(_1tU,_1tR)),_1tQ)),_1u5=_1u4.a,_1u6=_1u4.b;if(E(_1tX)==32){if(!B(_4A(_hd,_1u5,_1rl))){var _1u7=false;}else{switch(E(_1u6)){case 0:var _1u8=true;break;case 1:var _1u8=false;break;case 2:var _1u8=false;break;case 3:var _1u8=false;break;case 4:var _1u8=false;break;case 5:var _1u8=false;break;case 6:var _1u8=false;break;case 7:var _1u8=false;break;default:var _1u8=false;}var _1u7=_1u8;}var _1u9=_1u7;}else{var _1u9=false;}if(E(_1tX)==32){if(E(_1u5)==32){var _1ua=false;}else{switch(E(_1u6)){case 0:if(!E(_1u9)){var _1ub=true;}else{var _1ub=false;}var _1uc=_1ub;break;case 1:var _1uc=false;break;case 2:var _1uc=false;break;case 3:var _1uc=false;break;case 4:var _1uc=false;break;case 5:var _1uc=false;break;case 6:var _1uc=false;break;case 7:var _1uc=false;break;default:if(!E(_1u9)){var _1ud=true;}else{var _1ud=false;}var _1uc=_1ud;}var _1ua=_1uc;}var _1ue=_1ua;}else{var _1ue=false;}var _1uf=new T(function(){return B(_KX(_1tQ,_1tR,new T(function(){if(!E(_1ue)){if(!E(_1u9)){return E(_1u5);}else{return _1tW;}}else{return E(_UT);}}),_1u6,_1tU));});switch(E(_1u6)){case 3:var _1ug=true;break;case 4:if(E(_1tX)==32){var _1uh=true;}else{var _1uh=false;}var _1ug=_1uh;break;default:var _1ug=false;}if(!E(_1ug)){var _1ui=E(_1uf);}else{var _1uj=E(_1tS),_1uk=new T(function(){return B(_6X(_1uf,_1tR));}),_1ul=function(_1um,_1un){var _1uo=E(_1um);if(_1uo==( -1)){return E(_1uf);}else{var _1up=new T(function(){return B(_KX(_1tQ,_1tR,_UT,_Eg,_1uf));}),_1uq=E(_1un);if(_1uq==( -1)){var _1ur=__Z;}else{var _1ur=B(_6X(_1up,_1uq));}if(E(B(_6X(_1ur,_1uo)).a)==32){var _1us=new T(function(){var _1ut=new T(function(){return B(_6X(_1uk,_1tQ));}),_1uu=new T2(1,new T2(0,new T(function(){return E(E(_1ut).a);}),new T(function(){return E(E(_1ut).b);})),new T(function(){var _1uv=_1uo+1|0;if(_1uv>0){return B(_1re(_1uv,_1ur));}else{return E(_1ur);}}));if(0>=_1uo){return E(_1uu);}else{var _1uw=function(_1ux,_1uy){var _1uz=E(_1ux);if(!_1uz._){return E(_1uu);}else{var _1uA=_1uz.a,_1uB=E(_1uy);return (_1uB==1)?new T2(1,_1uA,_1uu):new T2(1,_1uA,new T(function(){return B(_1uw(_1uz.b,_1uB-1|0));}));}};return B(_1uw(_1ur,_1uo));}}),_1uC=new T2(1,_1us,new T(function(){var _1uD=_1un+1|0;if(_1uD>0){return B(_1r8(_1uD,_1up));}else{return E(_1up);}}));if(0>=_1un){return E(_1uC);}else{var _1uE=function(_1uF,_1uG){var _1uH=E(_1uF);if(!_1uH._){return E(_1uC);}else{var _1uI=_1uH.a,_1uJ=E(_1uG);return (_1uJ==1)?new T2(1,_1uI,_1uC):new T2(1,_1uI,new T(function(){return B(_1uE(_1uH.b,_1uJ-1|0));}));}};return new F(function(){return _1uE(_1up,_1un);});}}else{return E(_1uf);}}};if(_1tQ<=_1uj){if(_1uj<=_1tQ){var _1uK=E(_1tT);if(_1tR<=_1uK){if(_1uK<=_1tR){var _1uL=E(_1tI);}else{var _1uM=E(_1tR);if(!_1uM){var _1uN=B(_1ul( -1, -1));}else{var _1uN=B(_1ul(_1tQ,_1uM-1|0));}var _1uL=_1uN;}var _1uO=_1uL;}else{if(_1tR!=(B(_mz(_1uf,0))-1|0)){var _1uP=B(_1ul(_1tQ,_1tR+1|0));}else{var _1uP=B(_1ul( -1, -1));}var _1uO=_1uP;}var _1uQ=_1uO;}else{var _1uR=E(_1tQ);if(!_1uR){var _1uS=B(_1ul( -1, -1));}else{var _1uS=B(_1ul(_1uR-1|0,_1tR));}var _1uQ=_1uS;}var _1uT=_1uQ;}else{if(_1tQ!=(B(_mz(_1uk,0))-1|0)){var _1uU=B(_1ul(_1tQ+1|0,_1tR));}else{var _1uU=B(_1ul( -1, -1));}var _1uT=_1uU;}var _1ui=_1uT;}if(!E(_1u2)){var _1uV=E(_1ui);}else{var _1uW=new T(function(){var _1uX=E(_1ui);if(!_1uX._){return E(_nn);}else{return B(_mz(_1uX.a,0));}}),_1uY=new T(function(){return B(_mz(_1ui,0));}),_1uZ=function(_1v0,_1v1,_1v2,_1v3,_1v4,_1v5,_1v6){while(1){var _1v7=B((function(_1v8,_1v9,_1va,_1vb,_1vc,_1vd,_1ve){var _1vf=E(_1ve);if(!_1vf._){return E(_1vb);}else{var _1vg=_1vf.b,_1vh=E(_1vf.a);if(!_1vh._){return E(_1tJ);}else{var _1vi=_1vh.b,_1vj=E(_1vh.a);if(E(_1vj.b)==5){var _1vk=new T(function(){var _1vl=B(_1r3(_1tK,_1v8));return new T2(0,_1vl.a,_1vl.b);}),_1vm=new T(function(){var _1vn=function(_1vo,_1vp){var _1vq=function(_1vr){return new F(function(){return _KX(_1v9,_1va,_UT,_Eg,new T(function(){return B(_KX(_1vo,_1vp,_1vj.a,_F5,_1vb));}));});};if(_1vo!=_1v9){return new F(function(){return _1vq(_);});}else{if(_1vp!=_1va){return new F(function(){return _1vq(_);});}else{return E(_1vb);}}};switch(E(E(_1vk).a)){case 1:var _1vs=_1v9-1|0;if(_1vs<0){return B(_1vn(_1v9,_1va));}else{if(_1vs>=E(_1uW)){return B(_1vn(_1v9,_1va));}else{if(_1va<0){return B(_1vn(_1v9,_1va));}else{if(_1va>=E(_1uY)){return B(_1vn(_1v9,_1va));}else{if(_1vs!=_1vc){if(E(B(_6X(B(_6X(_1vb,_1va)),_1vs)).a)==32){return B(_1vn(_1vs,_1va));}else{return B(_1vn(_1v9,_1va));}}else{if(_1va!=_1vd){if(E(B(_6X(B(_6X(_1vb,_1va)),_1vs)).a)==32){return B(_1vn(_1vs,_1va));}else{return B(_1vn(_1v9,_1va));}}else{return B(_1vn(_1v9,_1va));}}}}}}break;case 2:if(_1v9<0){return B(_1vn(_1v9,_1va));}else{if(_1v9>=E(_1uW)){return B(_1vn(_1v9,_1va));}else{var _1vt=_1va-1|0;if(_1vt<0){return B(_1vn(_1v9,_1va));}else{if(_1vt>=E(_1uY)){return B(_1vn(_1v9,_1va));}else{if(_1v9!=_1vc){if(E(B(_6X(B(_6X(_1vb,_1vt)),_1v9)).a)==32){return B(_1vn(_1v9,_1vt));}else{return B(_1vn(_1v9,_1va));}}else{if(_1vt!=_1vd){if(E(B(_6X(B(_6X(_1vb,_1vt)),_1v9)).a)==32){return B(_1vn(_1v9,_1vt));}else{return B(_1vn(_1v9,_1va));}}else{return B(_1vn(_1v9,_1va));}}}}}}break;case 3:var _1vu=_1v9+1|0;if(_1vu<0){return B(_1vn(_1v9,_1va));}else{if(_1vu>=E(_1uW)){return B(_1vn(_1v9,_1va));}else{if(_1va<0){return B(_1vn(_1v9,_1va));}else{if(_1va>=E(_1uY)){return B(_1vn(_1v9,_1va));}else{if(_1vu!=_1vc){if(E(B(_6X(B(_6X(_1vb,_1va)),_1vu)).a)==32){return B(_1vn(_1vu,_1va));}else{return B(_1vn(_1v9,_1va));}}else{if(_1va!=_1vd){if(E(B(_6X(B(_6X(_1vb,_1va)),_1vu)).a)==32){return B(_1vn(_1vu,_1va));}else{return B(_1vn(_1v9,_1va));}}else{return B(_1vn(_1v9,_1va));}}}}}}break;case 4:if(_1v9<0){return B(_1vn(_1v9,_1va));}else{if(_1v9>=E(_1uW)){return B(_1vn(_1v9,_1va));}else{var _1vv=_1va+1|0;if(_1vv<0){return B(_1vn(_1v9,_1va));}else{if(_1vv>=E(_1uY)){return B(_1vn(_1v9,_1va));}else{if(_1v9!=_1vc){if(E(B(_6X(B(_6X(_1vb,_1vv)),_1v9)).a)==32){return B(_1vn(_1v9,_1vv));}else{return B(_1vn(_1v9,_1va));}}else{if(_1vv!=_1vd){if(E(B(_6X(B(_6X(_1vb,_1vv)),_1v9)).a)==32){return B(_1vn(_1v9,_1vv));}else{return B(_1vn(_1v9,_1va));}}else{return B(_1vn(_1v9,_1va));}}}}}}break;default:if(_1v9<0){return B(_1vn(_1v9,_1va));}else{if(_1v9>=E(_1uW)){return B(_1vn(_1v9,_1va));}else{if(_1va<0){return B(_1vn(_1v9,_1va));}else{if(_1va>=E(_1uY)){return B(_1vn(_1v9,_1va));}else{if(_1v9!=_1vc){var _1vw=E(B(_6X(B(_6X(_1vb,_1va)),_1v9)).a);return B(_1vn(_1v9,_1va));}else{if(_1va!=_1vd){var _1vx=E(B(_6X(B(_6X(_1vb,_1va)),_1v9)).a);return B(_1vn(_1v9,_1va));}else{return B(_1vn(_1v9,_1va));}}}}}}}}),_1vy=E(_1vi);if(!_1vy._){var _1vz=_1va+1|0,_1vA=_1vc,_1vB=_1vd;_1v0=new T(function(){return E(E(_1vk).b);},1);_1v1=0;_1v2=_1vz;_1v3=_1vm;_1v4=_1vA;_1v5=_1vB;_1v6=_1vg;return __continue;}else{return new F(function(){return _1vC(new T(function(){return E(E(_1vk).b);},1),_1v9+1|0,_1va,_1vm,_1vc,_1vd,_1vy.a,_1vy.b,_1vg);});}}else{var _1vD=E(_1vi);if(!_1vD._){var _1vE=_1v8,_1vz=_1va+1|0,_1vF=_1vb,_1vA=_1vc,_1vB=_1vd;_1v0=_1vE;_1v1=0;_1v2=_1vz;_1v3=_1vF;_1v4=_1vA;_1v5=_1vB;_1v6=_1vg;return __continue;}else{return new F(function(){return _1vC(_1v8,_1v9+1|0,_1va,_1vb,_1vc,_1vd,_1vD.a,_1vD.b,_1vg);});}}}}})(_1v0,_1v1,_1v2,_1v3,_1v4,_1v5,_1v6));if(_1v7!=__continue){return _1v7;}}},_1vC=function(_1vG,_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM,_1vN,_1vO){while(1){var _1vP=B((function(_1vQ,_1vR,_1vS,_1vT,_1vU,_1vV,_1vW,_1vX,_1vY){var _1vZ=E(_1vW);if(E(_1vZ.b)==5){var _1w0=new T(function(){var _1w1=B(_1r3(_1tK,_1vQ));return new T2(0,_1w1.a,_1w1.b);}),_1w2=new T(function(){var _1w3=function(_1w4,_1w5){var _1w6=function(_1w7){return new F(function(){return _KX(_1vR,_1vS,_UT,_Eg,new T(function(){return B(_KX(_1w4,_1w5,_1vZ.a,_F5,_1vT));}));});};if(_1w4!=_1vR){return new F(function(){return _1w6(_);});}else{if(_1w5!=_1vS){return new F(function(){return _1w6(_);});}else{return E(_1vT);}}};switch(E(E(_1w0).a)){case 1:var _1w8=_1vR-1|0;if(_1w8<0){return B(_1w3(_1vR,_1vS));}else{if(_1w8>=E(_1uW)){return B(_1w3(_1vR,_1vS));}else{if(_1vS<0){return B(_1w3(_1vR,_1vS));}else{if(_1vS>=E(_1uY)){return B(_1w3(_1vR,_1vS));}else{if(_1w8!=_1vU){if(E(B(_6X(B(_6X(_1vT,_1vS)),_1w8)).a)==32){return B(_1w3(_1w8,_1vS));}else{return B(_1w3(_1vR,_1vS));}}else{if(_1vS!=_1vV){if(E(B(_6X(B(_6X(_1vT,_1vS)),_1w8)).a)==32){return B(_1w3(_1w8,_1vS));}else{return B(_1w3(_1vR,_1vS));}}else{return B(_1w3(_1vR,_1vS));}}}}}}break;case 2:if(_1vR<0){return B(_1w3(_1vR,_1vS));}else{if(_1vR>=E(_1uW)){return B(_1w3(_1vR,_1vS));}else{var _1w9=_1vS-1|0;if(_1w9<0){return B(_1w3(_1vR,_1vS));}else{if(_1w9>=E(_1uY)){return B(_1w3(_1vR,_1vS));}else{if(_1vR!=_1vU){if(E(B(_6X(B(_6X(_1vT,_1w9)),_1vR)).a)==32){return B(_1w3(_1vR,_1w9));}else{return B(_1w3(_1vR,_1vS));}}else{if(_1w9!=_1vV){if(E(B(_6X(B(_6X(_1vT,_1w9)),_1vR)).a)==32){return B(_1w3(_1vR,_1w9));}else{return B(_1w3(_1vR,_1vS));}}else{return B(_1w3(_1vR,_1vS));}}}}}}break;case 3:var _1wa=_1vR+1|0;if(_1wa<0){return B(_1w3(_1vR,_1vS));}else{if(_1wa>=E(_1uW)){return B(_1w3(_1vR,_1vS));}else{if(_1vS<0){return B(_1w3(_1vR,_1vS));}else{if(_1vS>=E(_1uY)){return B(_1w3(_1vR,_1vS));}else{if(_1wa!=_1vU){if(E(B(_6X(B(_6X(_1vT,_1vS)),_1wa)).a)==32){return B(_1w3(_1wa,_1vS));}else{return B(_1w3(_1vR,_1vS));}}else{if(_1vS!=_1vV){if(E(B(_6X(B(_6X(_1vT,_1vS)),_1wa)).a)==32){return B(_1w3(_1wa,_1vS));}else{return B(_1w3(_1vR,_1vS));}}else{return B(_1w3(_1vR,_1vS));}}}}}}break;case 4:if(_1vR<0){return B(_1w3(_1vR,_1vS));}else{if(_1vR>=E(_1uW)){return B(_1w3(_1vR,_1vS));}else{var _1wb=_1vS+1|0;if(_1wb<0){return B(_1w3(_1vR,_1vS));}else{if(_1wb>=E(_1uY)){return B(_1w3(_1vR,_1vS));}else{if(_1vR!=_1vU){if(E(B(_6X(B(_6X(_1vT,_1wb)),_1vR)).a)==32){return B(_1w3(_1vR,_1wb));}else{return B(_1w3(_1vR,_1vS));}}else{if(_1wb!=_1vV){if(E(B(_6X(B(_6X(_1vT,_1wb)),_1vR)).a)==32){return B(_1w3(_1vR,_1wb));}else{return B(_1w3(_1vR,_1vS));}}else{return B(_1w3(_1vR,_1vS));}}}}}}break;default:if(_1vR<0){return B(_1w3(_1vR,_1vS));}else{if(_1vR>=E(_1uW)){return B(_1w3(_1vR,_1vS));}else{if(_1vS<0){return B(_1w3(_1vR,_1vS));}else{if(_1vS>=E(_1uY)){return B(_1w3(_1vR,_1vS));}else{if(_1vR!=_1vU){var _1wc=E(B(_6X(B(_6X(_1vT,_1vS)),_1vR)).a);return B(_1w3(_1vR,_1vS));}else{if(_1vS!=_1vV){var _1wd=E(B(_6X(B(_6X(_1vT,_1vS)),_1vR)).a);return B(_1w3(_1vR,_1vS));}else{return B(_1w3(_1vR,_1vS));}}}}}}}}),_1we=E(_1vX);if(!_1we._){return new F(function(){return _1uZ(new T(function(){return E(E(_1w0).b);},1),0,_1vS+1|0,_1w2,_1vU,_1vV,_1vY);});}else{var _1wf=_1vR+1|0,_1wg=_1vS,_1wh=_1vU,_1wi=_1vV,_1wj=_1vY;_1vG=new T(function(){return E(E(_1w0).b);},1);_1vH=_1wf;_1vI=_1wg;_1vJ=_1w2;_1vK=_1wh;_1vL=_1wi;_1vM=_1we.a;_1vN=_1we.b;_1vO=_1wj;return __continue;}}else{var _1wk=E(_1vX);if(!_1wk._){return new F(function(){return _1uZ(_1vQ,0,_1vS+1|0,_1vT,_1vU,_1vV,_1vY);});}else{var _1wl=_1vQ,_1wf=_1vR+1|0,_1wg=_1vS,_1wm=_1vT,_1wh=_1vU,_1wi=_1vV,_1wj=_1vY;_1vG=_1wl;_1vH=_1wf;_1vI=_1wg;_1vJ=_1wm;_1vK=_1wh;_1vL=_1wi;_1vM=_1wk.a;_1vN=_1wk.b;_1vO=_1wj;return __continue;}}})(_1vG,_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM,_1vN,_1vO));if(_1vP!=__continue){return _1vP;}}},_1uV=B(_1uZ(_1u0,0,0,_1ui,_1tQ,_1tR,_1ui));}var _1wn=function(_1wo){var _1wp=function(_1wq){var _1wr=new T(function(){switch(E(_1u6)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1ws=new T(function(){if(!E(_1ug)){if(!E(_1wr)){return new T2(0,_1tQ,_1tR);}else{return new T2(0,_1tS,_1tT);}}else{if(!B(_1nZ(_1ob,_1uV,_1uf))){if(!E(_1wr)){return new T2(0,_1tQ,_1tR);}else{return new T2(0,_1tS,_1tT);}}else{return new T2(0,_1tS,_1tT);}}}),_1wt=new T(function(){return E(E(_1ws).b);}),_1wu=new T(function(){return E(E(_1ws).a);});if(!E(_1ug)){var _1wv=E(_1u3);}else{var _1wv=E(B(_1qM(new T(function(){return B(_1sd(_1tY,_1tZ,_1uV));}),_1uV)).a);}var _1ww=new T(function(){if(!E(_1ue)){if(!E(_1u9)){var _1wx=function(_1wy){var _1wz=function(_1wA){var _1wB=E(_1u6);if(_1wB==4){return new T2(1,_1tN,new T2(1,_1u5,_S));}else{if(!E(_1wr)){return (E(_1wB)==2)?new T2(1,_1tL,new T2(1,_1u5,_S)):__Z;}else{var _1wC=E(_1u5);return (E(_1wC)==61)?new T2(1,_1tM,new T2(1,_1wC,new T(function(){return B(_A(0,_1tR,_S));}))):new T2(1,_1tM,new T2(1,_1wC,_S));}}};if(!E(_1ug)){return new F(function(){return _1wz(_);});}else{if(E(_1tS)!=E(_1wu)){return new T2(1,_1tO,new T2(1,_1u5,_S));}else{if(E(_1tT)!=E(_1wt)){return new T2(1,_1tO,new T2(1,_1u5,_S));}else{return new F(function(){return _1wz(_);});}}}};if(!E(_1ug)){return B(_1wx(_));}else{if(!E(_1wv)){return B(_1wx(_));}else{return E(_1tH);}}}else{return new T2(1,_1tF,new T2(1,_1u5,_S));}}else{return new T2(1,_1tG,new T2(1,_1u5,_S));}},1);return {_:0,a:E(new T2(0,_1wu,_1wt)),b:E(_1uV),c:E(_1tV),d:_1wo,e:_1wq,f:_1tY,g:E(_1tZ),h:_1u0,i:E(B(_q(_1u1,_1ww))),j:E(_1u2),k:E(_1wv)};};if(!E(_1ue)){return new F(function(){return _1wp(_1tX);});}else{return new F(function(){return _1wp(E(_1u5));});}};if(!E(_1u9)){return new F(function(){return _1wn(_1tW);});}else{return new F(function(){return _1wn(E(_1u5));});}},_1wD=new T2(1,_5U,_S),_1wE=5,_1wF=new T2(1,_1wE,_S),_1wG=function(_1wH,_1wI){while(1){var _1wJ=E(_1wH);if(!_1wJ._){return E(_1wI);}else{_1wH=_1wJ.b;_1wI=_1wJ.a;continue;}}},_1wK=57,_1wL=48,_1wM=new T2(1,_1rk,_S),_1wN=new T(function(){return B(err(_sA));}),_1wO=new T(function(){return B(err(_sy));}),_1wP=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_1wQ=function(_1wR,_1wS){if((_1wS-48|0)>>>0>9){var _1wT=_1wS+_1wR|0,_1wU=function(_1wV){if(!B(_4A(_hd,_1wV,_1wM))){return E(_1wV);}else{return new F(function(){return _1wQ(_1wR,_1wV);});}};if(_1wT<=122){if(_1wT>=97){if(_1wT>>>0>1114111){return new F(function(){return _wL(_1wT);});}else{return new F(function(){return _1wU(_1wT);});}}else{if(_1wT<=90){if(_1wT>>>0>1114111){return new F(function(){return _wL(_1wT);});}else{return new F(function(){return _1wU(_1wT);});}}else{var _1wW=65+(_1wT-90|0)|0;if(_1wW>>>0>1114111){return new F(function(){return _wL(_1wW);});}else{return new F(function(){return _1wU(_1wW);});}}}}else{var _1wX=97+(_1wT-122|0)|0;if(_1wX>>>0>1114111){return new F(function(){return _wL(_1wX);});}else{return new F(function(){return _1wU(_1wX);});}}}else{var _1wY=B(_Gk(B(_sF(_1wP,new T2(1,_1wS,_S)))));if(!_1wY._){return E(_1wO);}else{if(!E(_1wY.b)._){var _1wZ=E(_1wY.a)+_1wR|0;switch(_1wZ){case  -1:return E(_1wL);case 10:return E(_1wK);default:return new F(function(){return _1wG(B(_A(0,_1wZ,_S)),_Tu);});}}else{return E(_1wN);}}}},_1x0=function(_1x1,_1x2){if((_1x1-48|0)>>>0>9){return _1x2;}else{var _1x3=B(_Gk(B(_sF(_1wP,new T2(1,_1x1,_S)))));if(!_1x3._){return E(_1wO);}else{if(!E(_1x3.b)._){return new F(function(){return _1wQ(E(_1x3.a),_1x2);});}else{return E(_1wN);}}}},_1x4=function(_1x5,_1x6){return new F(function(){return _1x0(E(_1x5),E(_1x6));});},_1x7=new T2(1,_1x4,_S),_1x8=112,_1x9=111,_1xa=function(_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh,_1xi,_1xj,_1xk,_1xl,_1xm){var _1xn=new T(function(){return B(_6X(B(_6X(_1xd,_1xc)),E(_1xb)));}),_1xo=new T(function(){return E(E(_1xn).b);}),_1xp=new T(function(){if(E(_1xo)==4){return true;}else{return false;}}),_1xq=new T(function(){return E(E(_1xn).a);});if(E(_1xg)==32){var _1xr=false;}else{if(E(_1xq)==32){var _1xs=true;}else{var _1xs=false;}var _1xr=_1xs;}var _1xt=new T(function(){var _1xu=new T(function(){return B(A3(_6X,_1wD,B(_MK(_hd,_1xf,_1rl)),_1xg));});if(!E(_1xr)){if(!E(_1xp)){return E(_1xq);}else{if(!B(_4A(_3L,_1xh,_1wF))){return E(_1xq);}else{return B(A(_6X,[_1x7,B(_MK(_3L,_1xh,_1wF)),_1xu,_1xq]));}}}else{return E(_1xu);}}),_1xv=B(_KX(_1xb,_1xc,_1xt,_1xo,_1xd)),_1xw=function(_1xx){var _1xy=B(_1qM(new T(function(){return B(_1sd(_1xh,_1xi,_1xv));}),_1xv)).a;return {_:0,a:E(new T2(0,_1xb,_1xc)),b:E(_1xv),c:E(_1xe),d:_1xf,e:_1xx,f:_1xh,g:E(_1xi),h:_1xj,i:E(B(_q(_1xk,new T(function(){if(!E(_1xy)){if(!E(_1xr)){if(!E(_1xp)){return __Z;}else{return new T2(1,_1x8,new T2(1,_1xt,_S));}}else{return new T2(1,_1x9,new T2(1,_1xt,_S));}}else{return E(_1tH);}},1)))),j:E(_1xl),k:E(_1xy)};};if(!E(_1xr)){return new F(function(){return _1xw(_1xg);});}else{return new F(function(){return _1xw(32);});}},_1xz=function(_1xA,_1xB){while(1){var _1xC=E(_1xB);if(!_1xC._){return __Z;}else{var _1xD=_1xC.b,_1xE=E(_1xA);if(_1xE==1){return E(_1xD);}else{_1xA=_1xE-1|0;_1xB=_1xD;continue;}}}},_1xF=4,_1xG=new T(function(){return B(unCStr("\u5e74 "));}),_1xH=function(_1xI,_1xJ,_1xK,_1xL,_1xM){var _1xN=new T(function(){var _1xO=new T(function(){var _1xP=new T(function(){return B(_q(_1xJ,new T(function(){return B(unAppCStr(" >>",_1xL));},1)));},1);return B(_q(_1xG,_1xP));},1);return B(_q(B(_A(0,_1xI,_S)),_1xO));});return new T2(0,new T2(1,_1xM,_1n8),_1xN);},_1xQ=function(_1xR){var _1xS=E(_1xR),_1xT=E(_1xS.a),_1xU=B(_1xH(_1xT.a,_1xT.b,_1xT.c,_1xT.d,_1xS.b));return new T2(0,_1xU.a,_1xU.b);},_1xV=function(_1xW){var _1xX=E(_1xW);return new T2(0,new T2(1,_1xX.b,_1n8),E(_1xX.a).b);},_1xY=new T(function(){return B(_ed("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1xZ=function(_1y0,_1y1){while(1){var _1y2=E(_1y1);if(!_1y2._){return false;}else{var _1y3=_1y2.b,_1y4=E(_1y0),_1y5=_1y4.a,_1y6=_1y4.b,_1y7=E(_1y2.a);if(!_1y7._){return E(_1xY);}else{var _1y8=E(_1y7.a),_1y9=_1y8.a,_1ya=_1y8.b,_1yb=E(_1y7.b);if(!_1yb._){var _1yc=E(_1y5),_1yd=E(_1yc);if(_1yd==32){switch(E(_1y6)){case 0:if(!E(_1ya)){return true;}else{_1y0=new T2(0,_1yc,_Eg);_1y1=_1y3;continue;}break;case 1:if(E(_1ya)==1){return true;}else{_1y0=new T2(0,_1yc,_Em);_1y1=_1y3;continue;}break;case 2:if(E(_1ya)==2){return true;}else{_1y0=new T2(0,_1yc,_Es);_1y1=_1y3;continue;}break;case 3:if(E(_1ya)==3){return true;}else{_1y0=new T2(0,_1yc,_Ey);_1y1=_1y3;continue;}break;case 4:if(E(_1ya)==4){return true;}else{_1y0=new T2(0,_1yc,_EE);_1y1=_1y3;continue;}break;case 5:if(E(_1ya)==5){return true;}else{_1y0=new T2(0,_1yc,_F5);_1y1=_1y3;continue;}break;case 6:if(E(_1ya)==6){return true;}else{_1y0=new T2(0,_1yc,_EY);_1y1=_1y3;continue;}break;case 7:if(E(_1ya)==7){return true;}else{_1y0=new T2(0,_1yc,_ER);_1y1=_1y3;continue;}break;default:if(E(_1ya)==8){return true;}else{_1y0=new T2(0,_1yc,_EK);_1y1=_1y3;continue;}}}else{if(_1yd!=E(_1y9)){_1y0=_1y4;_1y1=_1y3;continue;}else{switch(E(_1y6)){case 0:if(!E(_1ya)){return true;}else{_1y0=new T2(0,_1yc,_Eg);_1y1=_1y3;continue;}break;case 1:if(E(_1ya)==1){return true;}else{_1y0=new T2(0,_1yc,_Em);_1y1=_1y3;continue;}break;case 2:if(E(_1ya)==2){return true;}else{_1y0=new T2(0,_1yc,_Es);_1y1=_1y3;continue;}break;case 3:if(E(_1ya)==3){return true;}else{_1y0=new T2(0,_1yc,_Ey);_1y1=_1y3;continue;}break;case 4:if(E(_1ya)==4){return true;}else{_1y0=new T2(0,_1yc,_EE);_1y1=_1y3;continue;}break;case 5:if(E(_1ya)==5){return true;}else{_1y0=new T2(0,_1yc,_F5);_1y1=_1y3;continue;}break;case 6:if(E(_1ya)==6){return true;}else{_1y0=new T2(0,_1yc,_EY);_1y1=_1y3;continue;}break;case 7:if(E(_1ya)==7){return true;}else{_1y0=new T2(0,_1yc,_ER);_1y1=_1y3;continue;}break;default:if(E(_1ya)==8){return true;}else{_1y0=new T2(0,_1yc,_EK);_1y1=_1y3;continue;}}}}}else{var _1ye=E(_1y5),_1yf=E(_1ye);if(_1yf==32){switch(E(_1y6)){case 0:if(!E(_1ya)){return true;}else{_1y0=new T2(0,_1ye,_Eg);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 1:if(E(_1ya)==1){return true;}else{_1y0=new T2(0,_1ye,_Em);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 2:if(E(_1ya)==2){return true;}else{_1y0=new T2(0,_1ye,_Es);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 3:if(E(_1ya)==3){return true;}else{_1y0=new T2(0,_1ye,_Ey);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 4:if(E(_1ya)==4){return true;}else{_1y0=new T2(0,_1ye,_EE);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 5:if(E(_1ya)==5){return true;}else{_1y0=new T2(0,_1ye,_F5);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 6:if(E(_1ya)==6){return true;}else{_1y0=new T2(0,_1ye,_EY);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 7:if(E(_1ya)==7){return true;}else{_1y0=new T2(0,_1ye,_ER);_1y1=new T2(1,_1yb,_1y3);continue;}break;default:if(E(_1ya)==8){return true;}else{_1y0=new T2(0,_1ye,_EK);_1y1=new T2(1,_1yb,_1y3);continue;}}}else{if(_1yf!=E(_1y9)){_1y0=_1y4;_1y1=new T2(1,_1yb,_1y3);continue;}else{switch(E(_1y6)){case 0:if(!E(_1ya)){return true;}else{_1y0=new T2(0,_1ye,_Eg);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 1:if(E(_1ya)==1){return true;}else{_1y0=new T2(0,_1ye,_Em);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 2:if(E(_1ya)==2){return true;}else{_1y0=new T2(0,_1ye,_Es);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 3:if(E(_1ya)==3){return true;}else{_1y0=new T2(0,_1ye,_Ey);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 4:if(E(_1ya)==4){return true;}else{_1y0=new T2(0,_1ye,_EE);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 5:if(E(_1ya)==5){return true;}else{_1y0=new T2(0,_1ye,_F5);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 6:if(E(_1ya)==6){return true;}else{_1y0=new T2(0,_1ye,_EY);_1y1=new T2(1,_1yb,_1y3);continue;}break;case 7:if(E(_1ya)==7){return true;}else{_1y0=new T2(0,_1ye,_ER);_1y1=new T2(1,_1yb,_1y3);continue;}break;default:if(E(_1ya)==8){return true;}else{_1y0=new T2(0,_1ye,_EK);_1y1=new T2(1,_1yb,_1y3);continue;}}}}}}}}},_1yg=function(_1yh,_1yi,_1yj,_1yk,_1yl){var _1ym=E(_1yl);if(!_1ym._){var _1yn=new T(function(){var _1yo=B(_1yg(_1ym.a,_1ym.b,_1ym.c,_1ym.d,_1ym.e));return new T2(0,_1yo.a,_1yo.b);});return new T2(0,new T(function(){return E(E(_1yn).a);}),new T(function(){return B(_10r(_1yi,_1yj,_1yk,E(_1yn).b));}));}else{return new T2(0,new T2(0,_1yi,_1yj),_1yk);}},_1yp=function(_1yq,_1yr,_1ys,_1yt,_1yu){var _1yv=E(_1yt);if(!_1yv._){var _1yw=new T(function(){var _1yx=B(_1yp(_1yv.a,_1yv.b,_1yv.c,_1yv.d,_1yv.e));return new T2(0,_1yx.a,_1yx.b);});return new T2(0,new T(function(){return E(E(_1yw).a);}),new T(function(){return B(_ZA(_1yr,_1ys,E(_1yw).b,_1yu));}));}else{return new T2(0,new T2(0,_1yr,_1ys),_1yu);}},_1yy=function(_1yz,_1yA){var _1yB=E(_1yz);if(!_1yB._){var _1yC=_1yB.a,_1yD=E(_1yA);if(!_1yD._){var _1yE=_1yD.a;if(_1yC<=_1yE){var _1yF=B(_1yp(_1yE,_1yD.b,_1yD.c,_1yD.d,_1yD.e)),_1yG=E(_1yF.a);return new F(function(){return _10r(_1yG.a,_1yG.b,_1yB,_1yF.b);});}else{var _1yH=B(_1yg(_1yC,_1yB.b,_1yB.c,_1yB.d,_1yB.e)),_1yI=E(_1yH.a);return new F(function(){return _ZA(_1yI.a,_1yI.b,_1yH.b,_1yD);});}}else{return E(_1yB);}}else{return E(_1yA);}},_1yJ=function(_1yK,_1yL){var _1yM=E(_1yK),_1yN=E(_1yL);if(!_1yN._){var _1yO=_1yN.b,_1yP=_1yN.c,_1yQ=_1yN.d,_1yR=_1yN.e;switch(B(_Zo(_1yM,_1yO))){case 0:return new F(function(){return _ZA(_1yO,_1yP,B(_1yJ(_1yM,_1yQ)),_1yR);});break;case 1:return new F(function(){return _1yy(_1yQ,_1yR);});break;default:return new F(function(){return _10r(_1yO,_1yP,_1yQ,B(_1yJ(_1yM,_1yR)));});}}else{return new T0(1);}},_1yS=function(_1yT,_1yU){while(1){var _1yV=E(_1yT);if(!_1yV._){return E(_1yU);}else{var _1yW=B(_1yJ(new T2(1,_1yV.a,_1n8),_1yU));_1yT=_1yV.b;_1yU=_1yW;continue;}}},_1yX=new T(function(){return B(unCStr("\n"));}),_1yY=function(_1yZ,_1z0,_){var _1z1=jsWriteHandle(E(_1yZ),toJSStr(E(_1z0)));return _gK;},_1z2=function(_1z3,_1z4,_){var _1z5=E(_1z3),_1z6=jsWriteHandle(_1z5,toJSStr(E(_1z4)));return new F(function(){return _1yY(_1z5,_1yX,_);});},_1z7=function(_1z8){var _1z9=E(_1z8);if(!_1z9._){return __Z;}else{return new F(function(){return _q(_1z9.a,new T(function(){return B(_1z7(_1z9.b));},1));});}},_1za=new T(function(){return B(unCStr("removed"));}),_1zb=new T(function(){return B(unCStr("loadError"));}),_1zc=new T(function(){return B(unCStr("saved"));}),_1zd=new T(function(){return B(err(_sy));}),_1ze=new T(function(){return B(err(_sA));}),_1zf=10,_1zg=3,_1zh=new T(function(){return B(unCStr("Coding : yokoP"));}),_1zi=8,_1zj=new T(function(){return B(unCStr("Congratulations!"));}),_1zk=5,_1zl=32,_1zm=new T2(0,_1zl,_F5),_1zn=99,_1zo=64,_1zp=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_1zq=new T(function(){return B(_mz(_1ix,0));}),_1zr=new T(function(){return B(unCStr("loadError"));}),_1zs=new T(function(){return B(unCStr(","));}),_1zt=new T(function(){return B(unCStr("~"));}),_1zu=new T(function(){return B(unCStr("savedata"));}),_1zv=new T(function(){return B(unCStr("---"));}),_1zw=new T(function(){return B(unCStr("=="));}),_1zx=0,_1zy=4,_1zz=6,_1zA=function(_1zB){var _1zC=B(_Gk(B(_sF(_1zp,_1zB))));return (_1zC._==0)?E(_1zd):(E(_1zC.b)._==0)?E(_1zC.a):E(_1ze);},_1zD=new T1(0,333),_1zE=new T(function(){return B(_8y(1,2147483647));}),_1zF=new T(function(){var _1zG=E(_1hl);if(!_1zG._){return E(_nn);}else{return E(_1zG.a);}}),_1zH=new T(function(){return B(unAppCStr("[]",_S));}),_1zI=new T(function(){return B(unCStr("\""));}),_1zJ=new T2(1,_S,_S),_1zK=new T(function(){return B(_1ds(_1gQ,5,_1hB));}),_1zL=new T(function(){return B(_6k(_1zA,_1zJ));}),_1zM=function(_1zN,_1zO){return new T2(1,_6J,new T(function(){return B(_8q(_1zN,new T2(1,_6J,_1zO)));}));},_1zP=function(_1zQ,_1zR){var _1zS=E(_1zQ),_1zT=new T(function(){var _1zU=function(_1zV){var _1zW=E(_1zS.a),_1zX=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1zY){return new F(function(){return _1zM(_1zW.a,_1zY);});},new T2(1,function(_1zZ){return new F(function(){return _17U(0,_1zW.b,_1zZ);});},_S)),new T2(1,_y,_1zV)));});return new T2(1,_z,_1zX);};return B(A3(_sk,_6D,new T2(1,_1zU,new T2(1,function(_1A0){return new F(function(){return _A(0,E(_1zS.b),_1A0);});},_S)),new T2(1,_y,_1zR)));});return new T2(1,_z,_1zT);},_1A1=new T2(1,_6J,_S),_1A2=new T(function(){return B(unCStr("Thank you for playing!"));}),_1A3=17,_1A4=2,_1A5=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1A6=function(_1A7,_1A8){var _1A9=E(_1A8);return (_1A9._==0)?__Z:new T2(1,_1A7,new T2(1,_1A9.a,new T(function(){return B(_1A6(_1A7,_1A9.b));})));},_1Aa=new T(function(){return B(unCStr("noContent"));}),_1Ab=new T(function(){return B(unCStr("noHint"));}),_1Ac=new T(function(){return B(err(_sA));}),_1Ad=new T(function(){return B(err(_sy));}),_1Ae=new T(function(){return B(A3(_FI,_Gb,_DL,_Fy));}),_1Af=function(_1Ag,_1Ah){var _1Ai=E(_1Ah);if(!_1Ai._){var _1Aj=B(_Gk(B(_sF(_1Ae,_1Ag))));return (_1Aj._==0)?E(_1Ad):(E(_1Aj.b)._==0)?new T4(0,E(_1Aj.a),_S,_S,_S):E(_1Ac);}else{var _1Ak=_1Ai.a,_1Al=E(_1Ai.b);if(!_1Al._){var _1Am=B(_Gk(B(_sF(_1Ae,_1Ag))));return (_1Am._==0)?E(_1Ad):(E(_1Am.b)._==0)?new T4(0,E(_1Am.a),E(_1Ak),E(_1Ab),E(_1Aa)):E(_1Ac);}else{var _1An=_1Al.a,_1Ao=E(_1Al.b);if(!_1Ao._){var _1Ap=B(_Gk(B(_sF(_1Ae,_1Ag))));return (_1Ap._==0)?E(_1Ad):(E(_1Ap.b)._==0)?new T4(0,E(_1Ap.a),E(_1Ak),E(_1An),E(_1Aa)):E(_1Ac);}else{if(!E(_1Ao.b)._){var _1Aq=B(_Gk(B(_sF(_1Ae,_1Ag))));return (_1Aq._==0)?E(_1Ad):(E(_1Aq.b)._==0)?new T4(0,E(_1Aq.a),E(_1Ak),E(_1An),E(_1Ao.a)):E(_1Ac);}else{return new T4(0,0,_S,_S,_S);}}}}},_1Ar=function(_1As){var _1At=E(_1As);if(!_1At._){return new F(function(){return _1Af(_S,_S);});}else{var _1Au=_1At.a,_1Av=E(_1At.b);if(!_1Av._){return new F(function(){return _1Af(new T2(1,_1Au,_S),_S);});}else{var _1Aw=E(_1Au),_1Ax=new T(function(){var _1Ay=B(_Hc(44,_1Av.a,_1Av.b));return new T2(0,_1Ay.a,_1Ay.b);});if(E(_1Aw)==44){return new F(function(){return _1Af(_S,new T2(1,new T(function(){return E(E(_1Ax).a);}),new T(function(){return E(E(_1Ax).b);})));});}else{var _1Az=E(_1Ax);return new F(function(){return _1Af(new T2(1,_1Aw,_1Az.a),_1Az.b);});}}}},_1AA=function(_1AB){var _1AC=B(_1Ar(_1AB));return new T4(0,_1AC.a,E(_1AC.b),E(_1AC.c),E(_1AC.d));},_1AD=function(_1AE){return (E(_1AE)==10)?true:false;},_1AF=function(_1AG){var _1AH=E(_1AG);if(!_1AH._){return __Z;}else{var _1AI=new T(function(){var _1AJ=B(_1dV(_1AD,_1AH));return new T2(0,_1AJ.a,new T(function(){var _1AK=E(_1AJ.b);if(!_1AK._){return __Z;}else{return B(_1AF(_1AK.b));}}));});return new T2(1,new T(function(){return E(E(_1AI).a);}),new T(function(){return E(E(_1AI).b);}));}},_1AL=new T(function(){return B(unCStr("57,\u5974\u56fd\u738b\u304c\u5f8c\u6f22\u304b\u3089\u91d1\u5370,<\u5f8c\u6f22\u66f8>\u306b\u8a18\u8f09\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\u8cc0\u5cf6\u306b\u3066<\u6f22\u59d4\u5974\u570b\u738b>\u3068\u523b\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\u898b\u3055\u308c\u308b**\u5927\u548c\u671d\u5ef7\u3068\u306e\u95dc\u4fc2\u306f\u4e0d\u660e\n239,<\u5351\u5f25\u547c>\u304c\u9b4f\u306b\u9063\u4f7f,\u652f\u90a3\u306e\u6b74\u53f2\u66f8<\u9b4f\u5fd7>\u306b\u8a18\u8f09\u3055\u308c\u3066\u3090\u308b\u5deb\u5973,<\u9b4f\u5fd7>\u502d\u4eba\u4f1d\u306b\u8a18\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\u5fb3\u5929\u7687 \u7a0e\u3092\u514d\u9664,<\u53e4\u4e8b\u8a18><\u65e5\u672c\u66f8\u7d00>\u306b\u8a18\u8f09\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c<\u6c11\u306e\u304b\u307e\u3069\u3088\u308a\u7159\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\u3057\u304f\u3066\u708a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\u4e2d\u306e\u4fee\u7e55\u3092\u5f8c\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d>\u306e\u6b66\u738b \u5357\u671d\u306e\u5b8b\u3078\u9063\u4f7f,\u96c4\u7565\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\u8aac,<\u5b8b\u66f8>\u502d\u570b\u50b3\u306b\u8a18\u8f09\u304c\u3042\u308b**\u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\u6559\u516c\u4f1d,\u6b3d\u660e\u5929\u7687\u5fa1\u4ee3\u306b\u767e\u6e08\u306e\u8056\u660e\u738b\u304b\u3089\u4f1d\u6765\u3057\u305f\u3068\u306e\u6587\u732e\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\u8aac\u3042\u308b\n604,\u5341\u4e03\u6761\u61b2\u6cd5\u5236\u5b9a,\u8056\u5fb3\u592a\u5b50\u304c\u5236\u5b9a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\u3092\u4ee5\u3066\u8cb4\u3057\u3068\u70ba\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\u304d\u3092\u5b97\u3068\u305b\u3088>\n607,\u6cd5\u9686\u5bfa\u304c\u5275\u5efa\u3055\u308c\u308b,\u8056\u5fb3\u592a\u5b50\u3086\u304b\u308a\u306e\u5bfa\u9662,\u897f\u9662\u4f3d\u85cd\u306f\u73fe\u5b58\u3059\u308b\u4e16\u754c\u6700\u53e4\u306e\u6728\u9020\u5efa\u7bc9\u7269\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\u5df3\u306e\u5909,\u3053\u306e\u5f8c\u3059\u3050\u5927\u5316\u306e\u6539\u65b0\u306a\u308b,\u4e2d\u5927\u5144\u7687\u5b50(\u5f8c\u306e38\u4ee3\u5929\u667a\u5929\u7687)\u304c\u8607\u6211\u6c0f\u3092\u4ea1\u307c\u3059\n663,\u767d\u6751\u6c5f\u306e\u6226,\u5510\u3068\u65b0\u7f85\u306b\u6ec5\u307c\u3055\u308c\u305f\u767e\u6e08\u3092\u518d\u8208\u3059\u308b\u76ee\u7684,\u5510\u30fb\u65b0\u7f85\u9023\u5408\u8ecd\u306b\u6557\u308c\u308b\n672,\u58ec\u7533\u306e\u4e71,\u5929\u667a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\u7d99\u8005\u4e89\u3072,\u5f8c\u7d99\u8005\u3067\u3042\u3063\u305f\u5927\u53cb\u7687\u5b50\u306b\u53d4\u7236\u306e\u5927\u6d77\u4eba\u7687\u5b50\u304c\u53cd\u65d7\u3092\u7ffb\u3057 \u5927\u53cb\u7687\u5b50\u3092\u5012\u3057\u3066\u5929\u6b66\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b<\u82b1\u306e\u5fa1\u6240>\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075<\u4e0b\u524b\u4e0a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d <\u5929\u4e0b\u5e03\u6b66>\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b<\u9396\u56fd>\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c<\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4>\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1AM=new T(function(){return B(_1AF(_1AL));}),_1AN=new T(function(){return B(_6k(_1AA,_1AM));}),_1AO=new T(function(){return B(_8V(1,2));}),_1AP=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b\u300c\u4e0d\u5e73\u7b49\u300d\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,\u300c\u6276\u6e05\u6ec5\u6d0b\u300d\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***\u300c\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287\u300d\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b\u300c\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42\u300d,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059\u300d\u30fc\u30fc\u5f8c\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059\u300d"));}),_1AQ=new T(function(){return B(_1AF(_1AP));}),_1AR=new T(function(){return B(_6k(_1AA,_1AQ));}),_1AS=function(_1AT,_1AU){var _1AV=E(_1AT);if(!_1AV._){return __Z;}else{var _1AW=E(_1AU);return (_1AW._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1AV.a).a;}),_1AW.a),new T(function(){return B(_1AS(_1AV.b,_1AW.b));}));}},_1AX=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1AY=new T(function(){return B(unCStr("tail"));}),_1AZ=new T(function(){return B(_nk(_1AY));}),_1B0=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1B1=new T2(1,_2t,_S),_1B2=function(_1B3){var _1B4=E(_1B3);if(!_1B4._){return E(_1B1);}else{var _1B5=new T(function(){var _1B6=E(_1B4.a),_1B7=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1B8){return new F(function(){return _1zM(_1B6.a,_1B8);});},new T2(1,function(_1B9){return new F(function(){return _1zM(_1B6.b,_1B9);});},_S)),new T2(1,_y,new T(function(){return B(_1B2(_1B4.b));}))));});return new T2(1,_z,_1B7);});return new T2(1,_2s,_1B5);}},_1Ba=function(_1Bb){var _1Bc=E(_1Bb);if(!_1Bc._){return E(_1B1);}else{var _1Bd=new T(function(){return B(_A(0,E(_1Bc.a),new T(function(){return B(_1Ba(_1Bc.b));})));});return new T2(1,_2s,_1Bd);}},_1Be=function(_1Bf){var _1Bg=E(_1Bf);if(!_1Bg._){return E(_1B1);}else{var _1Bh=new T(function(){var _1Bi=E(_1Bg.a),_1Bj=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1Bk){return new F(function(){return _1zM(_1Bi.a,_1Bk);});},new T2(1,function(_1Bl){return new F(function(){return _1zM(_1Bi.b,_1Bl);});},_S)),new T2(1,_y,new T(function(){return B(_1Be(_1Bg.b));}))));});return new T2(1,_z,_1Bj);});return new T2(1,_2s,_1Bh);}},_1Bm=new T(function(){return B(unCStr("True"));}),_1Bn=new T(function(){return B(unCStr("False"));}),_1Bo=function(_1Bp){return E(E(_1Bp).b);},_1Bq=function(_1Br,_1Bs,_1Bt){var _1Bu=new T(function(){var _1Bv=E(_1Bt);if(!_1Bv._){return __Z;}else{var _1Bw=_1Bv.b,_1Bx=E(_1Bv.a),_1By=E(_1Bx.a);if(_1By<_1Br){var _1Bz=function(_1BA){while(1){var _1BB=B((function(_1BC){var _1BD=E(_1BC);if(!_1BD._){return __Z;}else{var _1BE=_1BD.b,_1BF=E(_1BD.a);if(E(_1BF.a)<_1Br){_1BA=_1BE;return __continue;}else{return new T2(1,_1BF,new T(function(){return B(_1Bz(_1BE));}));}}})(_1BA));if(_1BB!=__continue){return _1BB;}}};return B(_1BG(B(_1Bz(_1Bw))));}else{var _1BH=new T(function(){var _1BI=function(_1BJ){while(1){var _1BK=B((function(_1BL){var _1BM=E(_1BL);if(!_1BM._){return __Z;}else{var _1BN=_1BM.b,_1BO=E(_1BM.a);if(E(_1BO.a)<_1Br){_1BJ=_1BN;return __continue;}else{return new T2(1,_1BO,new T(function(){return B(_1BI(_1BN));}));}}})(_1BJ));if(_1BK!=__continue){return _1BK;}}};return B(_1BI(_1Bw));});return B(_1Bq(_1By,_1Bx.b,_1BH));}}}),_1BP=E(_1Bt);if(!_1BP._){return new F(function(){return _q(_S,new T2(1,new T2(0,_1Br,_1Bs),_1Bu));});}else{var _1BQ=_1BP.b,_1BR=E(_1BP.a),_1BS=E(_1BR.a);if(_1BS>=_1Br){var _1BT=function(_1BU){while(1){var _1BV=B((function(_1BW){var _1BX=E(_1BW);if(!_1BX._){return __Z;}else{var _1BY=_1BX.b,_1BZ=E(_1BX.a);if(E(_1BZ.a)>=_1Br){_1BU=_1BY;return __continue;}else{return new T2(1,_1BZ,new T(function(){return B(_1BT(_1BY));}));}}})(_1BU));if(_1BV!=__continue){return _1BV;}}};return new F(function(){return _q(B(_1BG(B(_1BT(_1BQ)))),new T2(1,new T2(0,_1Br,_1Bs),_1Bu));});}else{var _1C0=new T(function(){var _1C1=function(_1C2){while(1){var _1C3=B((function(_1C4){var _1C5=E(_1C4);if(!_1C5._){return __Z;}else{var _1C6=_1C5.b,_1C7=E(_1C5.a);if(E(_1C7.a)>=_1Br){_1C2=_1C6;return __continue;}else{return new T2(1,_1C7,new T(function(){return B(_1C1(_1C6));}));}}})(_1C2));if(_1C3!=__continue){return _1C3;}}};return B(_1C1(_1BQ));});return new F(function(){return _q(B(_1Bq(_1BS,_1BR.b,_1C0)),new T2(1,new T2(0,_1Br,_1Bs),_1Bu));});}}},_1BG=function(_1C8){var _1C9=E(_1C8);if(!_1C9._){return __Z;}else{var _1Ca=_1C9.b,_1Cb=E(_1C9.a),_1Cc=_1Cb.a,_1Cd=new T(function(){var _1Ce=E(_1Ca);if(!_1Ce._){return __Z;}else{var _1Cf=_1Ce.b,_1Cg=E(_1Ce.a),_1Ch=E(_1Cg.a),_1Ci=E(_1Cc);if(_1Ch<_1Ci){var _1Cj=function(_1Ck){while(1){var _1Cl=B((function(_1Cm){var _1Cn=E(_1Cm);if(!_1Cn._){return __Z;}else{var _1Co=_1Cn.b,_1Cp=E(_1Cn.a);if(E(_1Cp.a)<_1Ci){_1Ck=_1Co;return __continue;}else{return new T2(1,_1Cp,new T(function(){return B(_1Cj(_1Co));}));}}})(_1Ck));if(_1Cl!=__continue){return _1Cl;}}};return B(_1BG(B(_1Cj(_1Cf))));}else{var _1Cq=new T(function(){var _1Cr=function(_1Cs){while(1){var _1Ct=B((function(_1Cu){var _1Cv=E(_1Cu);if(!_1Cv._){return __Z;}else{var _1Cw=_1Cv.b,_1Cx=E(_1Cv.a);if(E(_1Cx.a)<_1Ci){_1Cs=_1Cw;return __continue;}else{return new T2(1,_1Cx,new T(function(){return B(_1Cr(_1Cw));}));}}})(_1Cs));if(_1Ct!=__continue){return _1Ct;}}};return B(_1Cr(_1Cf));});return B(_1Bq(_1Ch,_1Cg.b,_1Cq));}}}),_1Cy=E(_1Ca);if(!_1Cy._){return new F(function(){return _q(_S,new T2(1,_1Cb,_1Cd));});}else{var _1Cz=_1Cy.b,_1CA=E(_1Cy.a),_1CB=E(_1CA.a),_1CC=E(_1Cc);if(_1CB>=_1CC){var _1CD=function(_1CE){while(1){var _1CF=B((function(_1CG){var _1CH=E(_1CG);if(!_1CH._){return __Z;}else{var _1CI=_1CH.b,_1CJ=E(_1CH.a);if(E(_1CJ.a)>=_1CC){_1CE=_1CI;return __continue;}else{return new T2(1,_1CJ,new T(function(){return B(_1CD(_1CI));}));}}})(_1CE));if(_1CF!=__continue){return _1CF;}}};return new F(function(){return _q(B(_1BG(B(_1CD(_1Cz)))),new T2(1,_1Cb,_1Cd));});}else{var _1CK=new T(function(){var _1CL=function(_1CM){while(1){var _1CN=B((function(_1CO){var _1CP=E(_1CO);if(!_1CP._){return __Z;}else{var _1CQ=_1CP.b,_1CR=E(_1CP.a);if(E(_1CR.a)>=_1CC){_1CM=_1CQ;return __continue;}else{return new T2(1,_1CR,new T(function(){return B(_1CL(_1CQ));}));}}})(_1CM));if(_1CN!=__continue){return _1CN;}}};return B(_1CL(_1Cz));});return new F(function(){return _q(B(_1Bq(_1CB,_1CA.b,_1CK)),new T2(1,_1Cb,_1Cd));});}}}},_1CS=function(_){return new F(function(){return jsMkStdout();});},_1CT=new T(function(){return B(_36(_1CS));}),_1CU=new T(function(){return B(_Lo("Browser.hs:82:24-56|(Right j)"));}),_1CV=function(_1CW){var _1CX=jsParseJSON(toJSStr(E(_1CW)));return (_1CX._==0)?E(_1CU):E(_1CX.a);},_1CY=function(_1CZ,_1D0,_1D1,_1D2,_1D3,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1Df,_1Dg,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1Dm,_1Dn,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DA,_1DB,_1DC,_1DD,_1DE,_1DF,_1DG,_1DH,_1DI,_){var _1DJ={_:0,a:E(_1DA),b:E(_1DB),c:E(_1DC),d:E(_1DD),e:E(_1DE),f:E(_1DF),g:E(_1DG),h:E(_1DH)},_1DK=new T2(0,_1Dx,_1Dy),_1DL=new T2(0,_1Dm,_1Dn),_1DM=new T2(0,_1Df,_1Dg),_1DN={_:0,a:E(_1D4),b:E(_1D5),c:E(_1D6),d:_1D7,e:_1D8,f:_1D9,g:E(_1Da),h:_1Db,i:E(_1Dc),j:E(_1Dd),k:E(_1De)},_1DO={_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:_1Dt,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};if(!E(_1DF)){var _1DP=function(_1DQ){if(!E(_1DD)){if(!E(_1DH)){return _1DO;}else{var _1DR=function(_,_1DS,_1DT,_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2,_1E3,_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea,_1Eb,_1Ec,_1Ed,_1Ee,_1Ef,_1Eg,_1Eh,_1Ei,_1Ej,_1Ek,_1El,_1Em,_1En){var _1Eo=function(_){var _1Ep=function(_){var _1Eq=function(_){var _1Er=B(_1z2(_1CT,new T2(1,_6J,new T(function(){return B(_8q(_1E0,_1A1));})),_)),_1Es=function(_){var _1Et=B(_1z2(_1CT,B(_A(0,_1Dr,_S)),_)),_1Eu=B(_1z2(_1CT,B(_2v(_1zP,_1DY,_S)),_)),_1Ev=B(_18u(_1zk,_1DZ,_)),_1Ew=_1Ev,_1Ex=E(_1CZ),_1Ey=_1Ex.a,_1Ez=_1Ex.b,_1EA=new T(function(){return B(_1nW(E(_1D3)));}),_1EB=new T(function(){var _1EC=E(_1EA),_1ED=E(_1DS),_1EE=_1ED.a,_1EF=_1ED.b,_1EG=function(_1EH,_1EI){var _1EJ=E(_1EH),_1EK=E(_1EI),_1EL=E(_1EE);if(_1EJ<=_1EL){if(_1EL<=_1EJ){var _1EM=E(_1EF);if(_1EK<=_1EM){if(_1EM<=_1EK){var _1EN=4;}else{var _1EN=0;}var _1EO=_1EN;}else{var _1EO=1;}var _1EP=_1EO;}else{var _1EP=2;}var _1EQ=_1EP;}else{var _1EQ=3;}var _1ER=function(_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_1F1){switch(E(_1EQ)){case 0:if(!E(_1DU)){var _1F2=new T2(0,_1Ej,_1Ek);}else{var _1F2=new T2(0,_1Ej,_1A4);}var _1F3=_1F2;break;case 1:if(E(_1DU)==1){var _1F4=new T2(0,_1Ej,_1Ek);}else{var _1F4=new T2(0,_1Ej,_1zx);}var _1F3=_1F4;break;case 2:if(E(_1DU)==2){var _1F5=new T2(0,_1Ej,_1Ek);}else{var _1F5=new T2(0,_1Ej,_1zz);}var _1F3=_1F5;break;case 3:if(E(_1DU)==3){var _1F6=new T2(0,_1Ej,_1Ek);}else{var _1F6=new T2(0,_1Ej,_1zy);}var _1F3=_1F6;break;default:if(E(_1DU)==4){var _1F7=new T2(0,_1Ej,_1Ek);}else{var _1F7=new T2(0,_1Ej,_1zx);}var _1F3=_1F7;}var _1F8=B(_1kL(_1zx,_1EZ,_1E6,{_:0,a:E(_1ES),b:E(_1ET),c:E(_1EU),d:_1EV,e:_1EW,f:_1EX,g:E(_1EY),h:E(E(_1Ew).b),i:E(_1EZ),j:E(_1F0),k:E(_1F1)},_1E3,_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea,_1Eb,_1Ec,_1Ed,_1Ee,_1Ef,_1Eg,_1Eh,_1Ei,_1F3,_1El,_1Em,_1En)),_1F9=_1F8.a,_1Fa=_1F8.b,_1Fb=_1F8.c,_1Fc=_1F8.d,_1Fd=_1F8.e,_1Fe=_1F8.f,_1Ff=_1F8.g,_1Fg=_1F8.h,_1Fh=_1F8.i,_1Fi=_1F8.j,_1Fj=_1F8.k,_1Fk=_1F8.l,_1Fl=_1F8.m,_1Fm=_1F8.n,_1Fn=_1F8.o,_1Fo=_1F8.q,_1Fp=_1F8.r,_1Fq=_1F8.s,_1Fr=_1F8.t,_1Fs=_1F8.u,_1Ft=E(_1F8.p);if(!_1Ft._){return {_:0,a:E(_1F9),b:E(_1Fa),c:E(_1Fb),d:E(_1Fc),e:E(_1Fd),f:E(_1Fe),g:E(_1Ff),h:E(_1Fg),i:_1Fh,j:_1Fi,k:_1Fj,l:_1Fk,m:E(_1Fl),n:_1Fm,o:E(_1Fn),p:E(_S),q:_1Fo,r:E(_1Fp),s:_1Fq,t:E(_1Fr),u:E(_1Fs)};}else{var _1Fu=B(_mz(_1EZ,0))-2|0,_1Fv=function(_1Fw){var _1Fx=E(_1F9);return {_:0,a:E({_:0,a:E(_1Fx.a),b:E(_1Fx.b),c:E(_1Fx.c),d:_1Fx.d,e:_1Fx.e,f:_1Fx.f,g:E(_S),h:_1Fx.h,i:E(_1Fx.i),j:E(_1Fx.j),k:E(_1Fx.k)}),b:E(_1Fa),c:E(_1Fb),d:E(B(_q(B(_68(_S,B(_1yS(B(_6k(_1Bo,_1Ft)),B(_13c(_1Fc)))))),new T(function(){return B(_6k(_1xQ,_1Ft));},1)))),e:E(_1Fd),f:E(_1Fe),g:E(_1Ff),h:E(_1Fg),i:_1Fh,j:_1Fi,k:_1Fj,l:_1Fk,m:E(_1Fl),n:_1Fm,o:E(_1Fn),p:E(_S),q:_1Fo,r:E(_1Fp),s:_1Fq,t:E(_1Fr),u:E(_1Fs)};};if(_1Fu>0){if(!B(_qV(B(_1xz(_1Fu,_1EZ)),_1zw))){return {_:0,a:E(_1F9),b:E(_1Fa),c:E(_1Fb),d:E(_1Fc),e:E(_1Fd),f:E(_1Fe),g:E(_1Ff),h:E(_1Fg),i:_1Fh,j:_1Fi,k:_1Fj,l:_1Fk,m:E(_1Fl),n:_1Fm,o:E(_1Fn),p:E(_1Ft),q:_1Fo,r:E(_1Fp),s:_1Fq,t:E(_1Fr),u:E(_1Fs)};}else{return new F(function(){return _1Fv(_);});}}else{if(!B(_qV(_1EZ,_1zw))){return {_:0,a:E(_1F9),b:E(_1Fa),c:E(_1Fb),d:E(_1Fc),e:E(_1Fd),f:E(_1Fe),g:E(_1Ff),h:E(_1Fg),i:_1Fh,j:_1Fi,k:_1Fj,l:_1Fk,m:E(_1Fl),n:_1Fm,o:E(_1Fn),p:E(_1Ft),q:_1Fo,r:E(_1Fp),s:_1Fq,t:E(_1Fr),u:E(_1Fs)};}else{return new F(function(){return _1Fv(_);});}}}};if(E(_1EC)==32){var _1Fy=B(_1tP(_1EJ,_1EK,_1EL,_1EF,_1DT,_1EQ,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2)),_1Fz=E(_1Fy.a),_1FA=B(_1xa(_1Fz.a,E(_1Fz.b),_1Fy.b,_1Fy.c,_1Fy.d,_1Fy.e,_1Fy.f,_1Fy.g,_1Fy.h,_1Fy.i,_1Fy.j,_1Fy.k));return new F(function(){return _1ER(_1FA.a,_1FA.b,_1FA.c,_1FA.d,_1FA.e,_1FA.f,_1FA.g,_1FA.i,_1FA.j,_1FA.k);});}else{var _1FB=B(_1tP(_1EJ,_1EK,_1EL,_1EF,_1DT,_1EQ,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2));return new F(function(){return _1ER(_1FB.a,_1FB.b,_1FB.c,_1FB.d,_1FB.e,_1FB.f,_1FB.g,_1FB.i,_1FB.j,_1FB.k);});}};switch(E(_1EC)){case 72:var _1FC=E(_1EF);if(0<=(_1FC-1|0)){return B(_1EG(_1EE,_1FC-1|0));}else{return B(_1EG(_1EE,_1FC));}break;case 75:var _1FD=E(_1EE);if(0<=(_1FD-1|0)){return B(_1EG(_1FD-1|0,_1EF));}else{return B(_1EG(_1FD,_1EF));}break;case 77:var _1FE=E(_1EE);if(E(_1Df)!=(_1FE+1|0)){return B(_1EG(_1FE+1|0,_1EF));}else{return B(_1EG(_1FE,_1EF));}break;case 80:var _1FF=E(_1EF);if(E(_1Dg)!=(_1FF+1|0)){return B(_1EG(_1EE,_1FF+1|0));}else{return B(_1EG(_1EE,_1FF));}break;case 104:var _1FG=E(_1EE);if(0<=(_1FG-1|0)){return B(_1EG(_1FG-1|0,_1EF));}else{return B(_1EG(_1FG,_1EF));}break;case 106:var _1FH=E(_1EF);if(E(_1Dg)!=(_1FH+1|0)){return B(_1EG(_1EE,_1FH+1|0));}else{return B(_1EG(_1EE,_1FH));}break;case 107:var _1FI=E(_1EF);if(0<=(_1FI-1|0)){return B(_1EG(_1EE,_1FI-1|0));}else{return B(_1EG(_1EE,_1FI));}break;case 108:var _1FJ=E(_1EE);if(E(_1Df)!=(_1FJ+1|0)){return B(_1EG(_1FJ+1|0,_1EF));}else{return B(_1EG(_1FJ,_1EF));}break;default:return B(_1EG(_1EE,_1EF));}}),_1FK=B(_1aX(_1Ey,_1Ez,_1D0,_1D1,_1D2,_1EB,_)),_1FL=_1FK,_1FM=E(_1EA),_1FN=function(_,_1FO){var _1FP=function(_1FQ){var _1FR=B(_1z2(_1CT,B(_8w(_1FO)),_)),_1FS=E(_1FL),_1FT=_1FS.d,_1FU=_1FS.e,_1FV=_1FS.f,_1FW=_1FS.g,_1FX=_1FS.i,_1FY=_1FS.j,_1FZ=_1FS.k,_1G0=_1FS.l,_1G1=_1FS.m,_1G2=_1FS.n,_1G3=_1FS.o,_1G4=_1FS.p,_1G5=_1FS.q,_1G6=_1FS.s,_1G7=_1FS.u,_1G8=E(_1FS.t),_1G9=_1G8.a,_1Ga=_1G8.d,_1Gb=_1G8.e,_1Gc=_1G8.f,_1Gd=_1G8.g,_1Ge=_1G8.h,_1Gf=E(_1FS.a),_1Gg=_1Gf.c,_1Gh=_1Gf.f,_1Gi=_1Gf.g,_1Gj=_1Gf.h,_1Gk=E(_1FS.h),_1Gl=E(_1FS.r),_1Gm=function(_1Gn){var _1Go=function(_1Gp){if(_1Gp!=E(_1zq)){var _1Gq=B(_6X(_1gX,_1Gp)),_1Gr=_1Gq.a,_1Gs=E(_1Gq.b),_1Gt=B(_1ds(_1Gr,_1Gs,new T(function(){return B(_6X(_1ix,_1Gp));})));return new F(function(){return _1CY(_1Ex,_1D0,_1D1,_1D2,_1zo,B(_6X(_1h8,_1Gp)),_1Gt,_1Gg,B(_6X(_1hl,_1Gp)),32,_1Gp,_1Gi,_1Gj,B(_q(_1Gf.i,new T2(1,_1zn,new T(function(){return B(_A(0,_1Gh,_S));})))),B(_1xZ(_1zm,_1Gt)),_wA,_1Gr,_1Gs,_S,_1FT,_1FU,_1FV,_1FW,_1Gk.a,_1Gk.b,_1FX,_1FY,_1FZ, -1,_1G1,_1G2,_1G3,_1G4,_1G5,_1Gl.a,_1Gl.b,_1G6,_wA,_wA,_wA,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1G7,_);});}else{var _1Gu=__app1(E(_no),_1Ez),_1Gv=B(A2(_np,_1Ey,_)),_1Gw=B(A(_mU,[_1Ey,_j9,_1A4,_1zk,_1zj,_])),_1Gx=B(A(_mU,[_1Ey,_j9,_1zg,_1zi,_1zh,_])),_1Gy=B(A(_mU,[_1Ey,_j9,_1zg,_1zf,_1A5,_])),_1Gz=B(A(_mU,[_1Ey,_j9,_1A4,_1A3,_1A2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1h7),b:E(_1zK),c:E(_1Gg),d:E(_1zF),e:32,f:0,g:E(_1Gi),h:_1Gj,i:E(_S),j:E(_1Gf.j),k:E(_wA)}),b:E(_1gR),c:E(_1FS.c),d:E(_1FT),e:E(_1FU),f:E(_1FV),g:E(_1FW),h:E(_1Gk),i:_1FX,j:_1FY,k:_1FZ,l:_1G0,m:E(_1G1),n:_1G2,o:E(_1G3),p:E(_1G4),q:_1G5,r:E(_1Gl),s:_1G6,t:E({_:0,a:E(_1G9),b:E(_wA),c:E(_wA),d:E(_1Ga),e:E(_1Gb),f:E(_1Gc),g:E(_1Gd),h:E(_1Ge)}),u:E(_1G7)};});}};if(_1G0>=0){return new F(function(){return _1Go(_1G0);});}else{return new F(function(){return _1Go(_1Gh+1|0);});}};if(!E(_1G9)){if(E(_1FM)==110){return new F(function(){return _1Gm(_);});}else{return _1FS;}}else{return new F(function(){return _1Gm(_);});}};if(E(_1FM)==114){if(!B(_6f(_1FO,_1zr))){var _1GA=E(_1FO);if(!_1GA._){return _1FL;}else{var _1GB=_1GA.b;return new T(function(){var _1GC=E(_1FL),_1GD=E(_1GC.a),_1GE=E(_1GA.a),_1GF=E(_1GE);if(_1GF==34){var _1GG=B(_RX(_1GE,_1GB));if(!_1GG._){var _1GH=E(_1AZ);}else{var _1GI=E(_1GG.b);if(!_1GI._){var _1GJ=E(_1zJ);}else{var _1GK=_1GI.a,_1GL=E(_1GI.b);if(!_1GL._){var _1GM=new T2(1,new T2(1,_1GK,_S),_S);}else{var _1GN=E(_1GK),_1GO=new T(function(){var _1GP=B(_Hc(126,_1GL.a,_1GL.b));return new T2(0,_1GP.a,_1GP.b);});if(E(_1GN)==126){var _1GQ=new T2(1,_S,new T2(1,new T(function(){return E(E(_1GO).a);}),new T(function(){return E(E(_1GO).b);})));}else{var _1GQ=new T2(1,new T2(1,_1GN,new T(function(){return E(E(_1GO).a);})),new T(function(){return E(E(_1GO).b);}));}var _1GM=_1GQ;}var _1GJ=_1GM;}var _1GH=_1GJ;}var _1GR=_1GH;}else{var _1GS=E(_1GB);if(!_1GS._){var _1GT=new T2(1,new T2(1,_1GE,_S),_S);}else{var _1GU=new T(function(){var _1GV=B(_Hc(126,_1GS.a,_1GS.b));return new T2(0,_1GV.a,_1GV.b);});if(E(_1GF)==126){var _1GW=new T2(1,_S,new T2(1,new T(function(){return E(E(_1GU).a);}),new T(function(){return E(E(_1GU).b);})));}else{var _1GW=new T2(1,new T2(1,_1GE,new T(function(){return E(E(_1GU).a);})),new T(function(){return E(E(_1GU).b);}));}var _1GT=_1GW;}var _1GR=_1GT;}var _1GX=B(_Gk(B(_sF(_1zp,new T(function(){return B(_Jo(_1GR));})))));if(!_1GX._){return E(_1zd);}else{if(!E(_1GX.b)._){var _1GY=E(_1GX.a),_1GZ=B(_6X(_1gX,_1GY)),_1H0=B(_6X(_1GR,1));if(!_1H0._){var _1H1=__Z;}else{var _1H2=E(_1H0.b);if(!_1H2._){var _1H3=__Z;}else{var _1H4=E(_1H0.a),_1H5=new T(function(){var _1H6=B(_Hc(44,_1H2.a,_1H2.b));return new T2(0,_1H6.a,_1H6.b);});if(E(_1H4)==44){var _1H7=B(_13r(_S,new T(function(){return E(E(_1H5).a);}),new T(function(){return E(E(_1H5).b);})));}else{var _1H7=B(_13v(new T2(1,_1H4,new T(function(){return E(E(_1H5).a);})),new T(function(){return E(E(_1H5).b);})));}var _1H3=_1H7;}var _1H1=_1H3;}var _1H8=B(_6X(_1GR,2));if(!_1H8._){var _1H9=E(_1zL);}else{var _1Ha=_1H8.a,_1Hb=E(_1H8.b);if(!_1Hb._){var _1Hc=B(_6k(_1zA,new T2(1,new T2(1,_1Ha,_S),_S)));}else{var _1Hd=E(_1Ha),_1He=new T(function(){var _1Hf=B(_Hc(44,_1Hb.a,_1Hb.b));return new T2(0,_1Hf.a,_1Hf.b);});if(E(_1Hd)==44){var _1Hg=B(_6k(_1zA,new T2(1,_S,new T2(1,new T(function(){return E(E(_1He).a);}),new T(function(){return E(E(_1He).b);})))));}else{var _1Hg=B(_6k(_1zA,new T2(1,new T2(1,_1Hd,new T(function(){return E(E(_1He).a);})),new T(function(){return E(E(_1He).b);}))));}var _1Hc=_1Hg;}var _1H9=_1Hc;}return {_:0,a:E({_:0,a:E(B(_6X(_1h8,_1GY))),b:E(B(_1ds(_1GZ.a,E(_1GZ.b),new T(function(){return B(_6X(_1ix,_1GY));})))),c:E(_1GD.c),d:B(_6X(_1hl,_1GY)),e:32,f:_1GY,g:E(_1GD.g),h:_1GD.h,i:E(_1GD.i),j:E(_1GD.j),k:E(_1GD.k)}),b:E(_1GZ),c:E(_1GC.c),d:E(_1GC.d),e:E(_1H1),f:E(_1H9),g:E(_1GC.g),h:E(_1GC.h),i:_1GC.i,j:_1GC.j,k:_1GC.k,l:_1GC.l,m:E(_1GC.m),n:_1GC.n,o:E(_1GC.o),p:E(_1GC.p),q:_1GC.q,r:E(_1GC.r),s:_1GC.s,t:E(_1GC.t),u:E(_1GC.u)};}else{return E(_1ze);}}});}}else{return new F(function(){return _1FP(_);});}}else{return new F(function(){return _1FP(_);});}};switch(E(_1FM)){case 100:var _1Hh=__app1(E(_1AX),toJSStr(E(_1zu)));return new F(function(){return _1FN(_,_1za);});break;case 114:var _1Hi=B(_13G(_6C,toJSStr(E(_1zu)),_));return new F(function(){return _1FN(_,new T(function(){var _1Hj=E(_1Hi);if(!_1Hj._){return E(_1zb);}else{return fromJSStr(B(_1mY(_1Hj.a)));}}));});break;case 115:var _1Hk=new T(function(){var _1Hl=new T(function(){var _1Hm=new T(function(){var _1Hn=B(_6k(_6H,_1Dk));if(!_1Hn._){return __Z;}else{return B(_1z7(new T2(1,_1Hn.a,new T(function(){return B(_1A6(_1zs,_1Hn.b));}))));}}),_1Ho=new T(function(){var _1Hp=function(_1Hq){var _1Hr=E(_1Hq);if(!_1Hr._){return __Z;}else{var _1Hs=E(_1Hr.a);return new T2(1,_1Hs.a,new T2(1,_1Hs.b,new T(function(){return B(_1Hp(_1Hr.b));})));}},_1Ht=B(_1Hp(_1Dj));if(!_1Ht._){return __Z;}else{return B(_1z7(new T2(1,_1Ht.a,new T(function(){return B(_1A6(_1zs,_1Ht.b));}))));}});return B(_1A6(_1zt,new T2(1,_1Ho,new T2(1,_1Hm,_S))));});return B(_q(B(_1z7(new T2(1,new T(function(){return B(_A(0,_1D9,_S));}),_1Hl))),_1zI));}),_1Hu=__app2(E(_1B0),toJSStr(E(_1zu)),B(_1mY(B(_1CV(B(unAppCStr("\"",_1Hk)))))));return new F(function(){return _1FN(_,_1zc);});break;default:return new F(function(){return _1FN(_,_1zv);});}};if(!E(_1E2)){var _1Hv=B(_1z2(_1CT,_1Bn,_));return new F(function(){return _1Es(_);});}else{var _1Hw=B(_1z2(_1CT,_1Bm,_));return new F(function(){return _1Es(_);});}},_1Hx=E(_1Dl);if(!_1Hx._){var _1Hy=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1Eq(_);});}else{var _1Hz=new T(function(){var _1HA=E(_1Hx.a),_1HB=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1HC){return new F(function(){return _1zM(_1HA.a,_1HC);});},new T2(1,function(_1HD){return new F(function(){return _1zM(_1HA.b,_1HD);});},_S)),new T2(1,_y,new T(function(){return B(_1B2(_1Hx.b));}))));});return new T2(1,_z,_1HB);}),_1HE=B(_1z2(_1CT,new T2(1,_2u,_1Hz),_));return new F(function(){return _1Eq(_);});}},_1HF=E(_1Dk);if(!_1HF._){var _1HG=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1Ep(_);});}else{var _1HH=new T(function(){return B(_A(0,E(_1HF.a),new T(function(){return B(_1Ba(_1HF.b));})));}),_1HI=B(_1z2(_1CT,new T2(1,_2u,_1HH),_));return new F(function(){return _1Ep(_);});}},_1HJ=E(_1Dj);if(!_1HJ._){var _1HK=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1Eo(_);});}else{var _1HL=new T(function(){var _1HM=E(_1HJ.a),_1HN=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1HO){return new F(function(){return _1zM(_1HM.a,_1HO);});},new T2(1,function(_1HP){return new F(function(){return _1zM(_1HM.b,_1HP);});},_S)),new T2(1,_y,new T(function(){return B(_1Be(_1HJ.b));}))));});return new T2(1,_z,_1HN);}),_1HQ=B(_1z2(_1CT,new T2(1,_2u,_1HL),_));return new F(function(){return _1Eo(_);});}},_1HR=E(_1Du);if(!_1HR._){return new F(function(){return _1DR(_,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1DM,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DJ,_1DI);});}else{var _1HS=E(_1HR.b);if(!_1HS._){return new F(function(){return _1DR(_,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1DM,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DJ,_1DI);});}else{var _1HT=E(_1HS.b);if(!_1HT._){return new F(function(){return _1DR(_,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1DM,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DJ,_1DI);});}else{var _1HU=_1HT.a,_1HV=E(_1HT.b);if(!_1HV._){return new F(function(){return _1DR(_,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1DM,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DJ,_1DI);});}else{if(!E(_1HV.b)._){var _1HW=B(_19P(B(_mz(_1HU,0)),_1Db,new T(function(){var _1HX=B(_Gk(B(_sF(_1zp,_1HR.a))));if(!_1HX._){return E(_1AN);}else{if(!E(_1HX.b)._){if(E(_1HX.a)==2){return E(_1AR);}else{return E(_1AN);}}else{return E(_1AN);}}}),_)),_1HY=E(_1HW),_1HZ=_1HY.a,_1I0=new T(function(){var _1I1=new T(function(){return B(_6k(function(_1I2){var _1I3=B(_ss(_3L,_1I2,B(_Gw(_1zE,_1HU))));return (_1I3._==0)?E(_1zl):E(_1I3.a);},B(_6k(_1Bo,B(_1BG(B(_1AS(_1HZ,_1AO))))))));}),_1I4=B(_Gw(_1HZ,_1HU)),_1I5=B(_Sl(B(unAppCStr("e.==.m1:",_1HV.a)),{_:0,a:E(_1D4),b:E(_1D5),c:E(_1D6),d:_1D7,e:_1D8,f:_1D9,g:E(B(_q(_1Da,new T2(1,new T2(0,new T2(0,_1HS.a,_1zD),_1D9),new T2(1,new T2(0,new T2(0,_1I1,_1zD),_1D9),_S))))),h:E(_1HY.b),i:E(_1Dc),j:E(_1Dd),k:E(_1De)},_1DM,_1Dh,B(_q(B(_68(_S,B(_1yS(_1HU,B(_13c(_1Di)))))),new T(function(){return B(_6k(_1xV,_1I4));},1))),_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,E(_1I4),0,_1DK,_1Dz,_1DJ,_1DI)),_1I6=B(_1n9(_1HU,_1I5.a,_1I5.b,_1I5.c,_1I5.d,_1I5.e,_1I5.f,_1I5.g,_1I5.h,_1I5.i,_1I5.j,_1I5.k,_1I5.l,_1I5.m,_1I5.n,_1I5.o,_1I5.p,_1I5.q,_1I5.r,_1I5.s,_1I5.t,_1I5.u));return {_:0,a:E(_1I6.a),b:E(_1I6.b),c:E(_1I6.c),d:E(_1I6.d),e:E(_1I6.e),f:E(_1I6.f),g:E(_1I6.g),h:E(_1I6.h),i:_1I6.i,j:_1I6.j,k:_1I6.k,l:_1I6.l,m:E(_1I6.m),n:_1I6.n,o:E(_1I6.o),p:E(_1I6.p),q:_1I6.q,r:E(_1I6.r),s:_1I6.s,t:E(_1I6.t),u:E(_1I6.u)};}),_1I7=function(_){var _1I8=function(_){var _1I9=function(_){var _1Ia=new T(function(){var _1Ib=E(E(_1I0).a);return new T6(0,_1Ib,_1Ib.a,_1Ib.g,_1Ib.h,_1Ib.i,_1Ib.k);}),_1Ic=B(_1z2(_1CT,new T2(1,_6J,new T(function(){return B(_8q(E(_1Ia).e,_1A1));})),_)),_1Id=E(_1Ia),_1Ie=_1Id.a,_1If=function(_){var _1Ig=B(_1z2(_1CT,B(_A(0,_1Dr,_S)),_)),_1Ih=B(_1z2(_1CT,B(_2v(_1zP,_1Id.c,_S)),_)),_1Ii=B(_18u(_1zk,_1Id.d,_)),_1Ij=E(_1Ii).b,_1Ik=E(_1CZ),_1Il=_1Ik.a,_1Im=_1Ik.b,_1In=new T(function(){return B(_1nW(E(_1D3)));}),_1Io=new T(function(){var _1Ip=E(_1I0),_1Iq=_1Ip.b,_1Ir=_1Ip.c,_1Is=_1Ip.d,_1It=_1Ip.e,_1Iu=_1Ip.f,_1Iv=_1Ip.g,_1Iw=_1Ip.h,_1Ix=_1Ip.i,_1Iy=_1Ip.j,_1Iz=_1Ip.k,_1IA=_1Ip.l,_1IB=_1Ip.m,_1IC=_1Ip.n,_1ID=_1Ip.o,_1IE=_1Ip.p,_1IF=_1Ip.q,_1IG=_1Ip.s,_1IH=_1Ip.t,_1II=_1Ip.u,_1IJ=E(_1Ip.r),_1IK=_1IJ.a,_1IL=_1IJ.b,_1IM=E(_1In),_1IN=E(_1Id.b),_1IO=_1IN.a,_1IP=_1IN.b,_1IQ=function(_1IR,_1IS){var _1IT=E(_1IR),_1IU=E(_1IO);if(_1IT<=_1IU){if(_1IU<=_1IT){var _1IV=E(_1IP);if(_1IS<=_1IV){if(_1IV<=_1IS){var _1IW=4;}else{var _1IW=0;}var _1IX=_1IW;}else{var _1IX=1;}var _1IY=_1IX;}else{var _1IY=2;}var _1IZ=_1IY;}else{var _1IZ=3;}var _1J0=function(_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja){switch(E(_1IZ)){case 0:if(!E(E(_1Ie).c)){var _1Jb=new T2(0,_1IK,_1IL);}else{var _1Jb=new T2(0,_1IK,_1A4);}var _1Jc=_1Jb;break;case 1:if(E(E(_1Ie).c)==1){var _1Jd=new T2(0,_1IK,_1IL);}else{var _1Jd=new T2(0,_1IK,_1zx);}var _1Jc=_1Jd;break;case 2:if(E(E(_1Ie).c)==2){var _1Je=new T2(0,_1IK,_1IL);}else{var _1Je=new T2(0,_1IK,_1zz);}var _1Jc=_1Je;break;case 3:if(E(E(_1Ie).c)==3){var _1Jf=new T2(0,_1IK,_1IL);}else{var _1Jf=new T2(0,_1IK,_1zy);}var _1Jc=_1Jf;break;default:if(E(E(_1Ie).c)==4){var _1Jg=new T2(0,_1IK,_1IL);}else{var _1Jg=new T2(0,_1IK,_1zx);}var _1Jc=_1Jg;}var _1Jh=B(_1kL(_1zx,_1J8,_1It,{_:0,a:E(_1J1),b:E(_1J2),c:E(_1J3),d:_1J4,e:_1J5,f:_1J6,g:E(_1J7),h:E(_1Ij),i:E(_1J8),j:E(_1J9),k:E(_1Ja)},_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF,_1Jc,_1IG,_1IH,_1II)),_1Ji=_1Jh.a,_1Jj=_1Jh.b,_1Jk=_1Jh.c,_1Jl=_1Jh.d,_1Jm=_1Jh.e,_1Jn=_1Jh.f,_1Jo=_1Jh.g,_1Jp=_1Jh.h,_1Jq=_1Jh.i,_1Jr=_1Jh.j,_1Js=_1Jh.k,_1Jt=_1Jh.l,_1Ju=_1Jh.m,_1Jv=_1Jh.n,_1Jw=_1Jh.o,_1Jx=_1Jh.q,_1Jy=_1Jh.r,_1Jz=_1Jh.s,_1JA=_1Jh.t,_1JB=_1Jh.u,_1JC=E(_1Jh.p);if(!_1JC._){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_S),q:_1Jx,r:E(_1Jy),s:_1Jz,t:E(_1JA),u:E(_1JB)};}else{var _1JD=B(_mz(_1J8,0))-2|0,_1JE=function(_1JF){var _1JG=E(_1Ji);return {_:0,a:E({_:0,a:E(_1JG.a),b:E(_1JG.b),c:E(_1JG.c),d:_1JG.d,e:_1JG.e,f:_1JG.f,g:E(_S),h:_1JG.h,i:E(_1JG.i),j:E(_1JG.j),k:E(_1JG.k)}),b:E(_1Jj),c:E(_1Jk),d:E(B(_q(B(_68(_S,B(_1yS(B(_6k(_1Bo,_1JC)),B(_13c(_1Jl)))))),new T(function(){return B(_6k(_1xQ,_1JC));},1)))),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_S),q:_1Jx,r:E(_1Jy),s:_1Jz,t:E(_1JA),u:E(_1JB)};};if(_1JD>0){if(!B(_qV(B(_1xz(_1JD,_1J8)),_1zw))){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_1JC),q:_1Jx,r:E(_1Jy),s:_1Jz,t:E(_1JA),u:E(_1JB)};}else{return new F(function(){return _1JE(_);});}}else{if(!B(_qV(_1J8,_1zw))){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_1JC),q:_1Jx,r:E(_1Jy),s:_1Jz,t:E(_1JA),u:E(_1JB)};}else{return new F(function(){return _1JE(_);});}}}};if(E(_1IM)==32){var _1JH=E(_1Ie),_1JI=E(_1JH.a),_1JJ=B(_1tP(_1IT,_1IS,_1JI.a,_1JI.b,_1JH.b,_1IZ,_1JH.d,_1JH.e,_1JH.f,_1JH.g,_1JH.h,_1JH.i,_1JH.j,_1JH.k)),_1JK=E(_1JJ.a),_1JL=B(_1xa(_1JK.a,E(_1JK.b),_1JJ.b,_1JJ.c,_1JJ.d,_1JJ.e,_1JJ.f,_1JJ.g,_1JJ.h,_1JJ.i,_1JJ.j,_1JJ.k));return new F(function(){return _1J0(_1JL.a,_1JL.b,_1JL.c,_1JL.d,_1JL.e,_1JL.f,_1JL.g,_1JL.i,_1JL.j,_1JL.k);});}else{var _1JM=E(_1Ie),_1JN=E(_1JM.a),_1JO=B(_1tP(_1IT,_1IS,_1JN.a,_1JN.b,_1JM.b,_1IZ,_1JM.d,_1JM.e,_1JM.f,_1JM.g,_1JM.h,_1JM.i,_1JM.j,_1JM.k));return new F(function(){return _1J0(_1JO.a,_1JO.b,_1JO.c,_1JO.d,_1JO.e,_1JO.f,_1JO.g,_1JO.i,_1JO.j,_1JO.k);});}},_1JP=function(_1JQ,_1JR){var _1JS=E(_1JR),_1JT=E(_1IO);if(_1JQ<=_1JT){if(_1JT<=_1JQ){var _1JU=E(_1IP);if(_1JS<=_1JU){if(_1JU<=_1JS){var _1JV=4;}else{var _1JV=0;}var _1JW=_1JV;}else{var _1JW=1;}var _1JX=_1JW;}else{var _1JX=2;}var _1JY=_1JX;}else{var _1JY=3;}var _1JZ=function(_1K0,_1K1,_1K2,_1K3,_1K4,_1K5,_1K6,_1K7,_1K8,_1K9){switch(E(_1JY)){case 0:if(!E(E(_1Ie).c)){var _1Ka=new T2(0,_1IK,_1IL);}else{var _1Ka=new T2(0,_1IK,_1A4);}var _1Kb=_1Ka;break;case 1:if(E(E(_1Ie).c)==1){var _1Kc=new T2(0,_1IK,_1IL);}else{var _1Kc=new T2(0,_1IK,_1zx);}var _1Kb=_1Kc;break;case 2:if(E(E(_1Ie).c)==2){var _1Kd=new T2(0,_1IK,_1IL);}else{var _1Kd=new T2(0,_1IK,_1zz);}var _1Kb=_1Kd;break;case 3:if(E(E(_1Ie).c)==3){var _1Ke=new T2(0,_1IK,_1IL);}else{var _1Ke=new T2(0,_1IK,_1zy);}var _1Kb=_1Ke;break;default:if(E(E(_1Ie).c)==4){var _1Kf=new T2(0,_1IK,_1IL);}else{var _1Kf=new T2(0,_1IK,_1zx);}var _1Kb=_1Kf;}var _1Kg=B(_1kL(_1zx,_1K7,_1It,{_:0,a:E(_1K0),b:E(_1K1),c:E(_1K2),d:_1K3,e:_1K4,f:_1K5,g:E(_1K6),h:E(_1Ij),i:E(_1K7),j:E(_1K8),k:E(_1K9)},_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF,_1Kb,_1IG,_1IH,_1II)),_1Kh=_1Kg.a,_1Ki=_1Kg.b,_1Kj=_1Kg.c,_1Kk=_1Kg.d,_1Kl=_1Kg.e,_1Km=_1Kg.f,_1Kn=_1Kg.g,_1Ko=_1Kg.h,_1Kp=_1Kg.i,_1Kq=_1Kg.j,_1Kr=_1Kg.k,_1Ks=_1Kg.l,_1Kt=_1Kg.m,_1Ku=_1Kg.n,_1Kv=_1Kg.o,_1Kw=_1Kg.q,_1Kx=_1Kg.r,_1Ky=_1Kg.s,_1Kz=_1Kg.t,_1KA=_1Kg.u,_1KB=E(_1Kg.p);if(!_1KB._){return {_:0,a:E(_1Kh),b:E(_1Ki),c:E(_1Kj),d:E(_1Kk),e:E(_1Kl),f:E(_1Km),g:E(_1Kn),h:E(_1Ko),i:_1Kp,j:_1Kq,k:_1Kr,l:_1Ks,m:E(_1Kt),n:_1Ku,o:E(_1Kv),p:E(_S),q:_1Kw,r:E(_1Kx),s:_1Ky,t:E(_1Kz),u:E(_1KA)};}else{var _1KC=B(_mz(_1K7,0))-2|0,_1KD=function(_1KE){var _1KF=E(_1Kh);return {_:0,a:E({_:0,a:E(_1KF.a),b:E(_1KF.b),c:E(_1KF.c),d:_1KF.d,e:_1KF.e,f:_1KF.f,g:E(_S),h:_1KF.h,i:E(_1KF.i),j:E(_1KF.j),k:E(_1KF.k)}),b:E(_1Ki),c:E(_1Kj),d:E(B(_q(B(_68(_S,B(_1yS(B(_6k(_1Bo,_1KB)),B(_13c(_1Kk)))))),new T(function(){return B(_6k(_1xQ,_1KB));},1)))),e:E(_1Kl),f:E(_1Km),g:E(_1Kn),h:E(_1Ko),i:_1Kp,j:_1Kq,k:_1Kr,l:_1Ks,m:E(_1Kt),n:_1Ku,o:E(_1Kv),p:E(_S),q:_1Kw,r:E(_1Kx),s:_1Ky,t:E(_1Kz),u:E(_1KA)};};if(_1KC>0){if(!B(_qV(B(_1xz(_1KC,_1K7)),_1zw))){return {_:0,a:E(_1Kh),b:E(_1Ki),c:E(_1Kj),d:E(_1Kk),e:E(_1Kl),f:E(_1Km),g:E(_1Kn),h:E(_1Ko),i:_1Kp,j:_1Kq,k:_1Kr,l:_1Ks,m:E(_1Kt),n:_1Ku,o:E(_1Kv),p:E(_1KB),q:_1Kw,r:E(_1Kx),s:_1Ky,t:E(_1Kz),u:E(_1KA)};}else{return new F(function(){return _1KD(_);});}}else{if(!B(_qV(_1K7,_1zw))){return {_:0,a:E(_1Kh),b:E(_1Ki),c:E(_1Kj),d:E(_1Kk),e:E(_1Kl),f:E(_1Km),g:E(_1Kn),h:E(_1Ko),i:_1Kp,j:_1Kq,k:_1Kr,l:_1Ks,m:E(_1Kt),n:_1Ku,o:E(_1Kv),p:E(_1KB),q:_1Kw,r:E(_1Kx),s:_1Ky,t:E(_1Kz),u:E(_1KA)};}else{return new F(function(){return _1KD(_);});}}}};if(E(_1IM)==32){var _1KG=E(_1Ie),_1KH=E(_1KG.a),_1KI=B(_1tP(_1JQ,_1JS,_1KH.a,_1KH.b,_1KG.b,_1JY,_1KG.d,_1KG.e,_1KG.f,_1KG.g,_1KG.h,_1KG.i,_1KG.j,_1KG.k)),_1KJ=E(_1KI.a),_1KK=B(_1xa(_1KJ.a,E(_1KJ.b),_1KI.b,_1KI.c,_1KI.d,_1KI.e,_1KI.f,_1KI.g,_1KI.h,_1KI.i,_1KI.j,_1KI.k));return new F(function(){return _1JZ(_1KK.a,_1KK.b,_1KK.c,_1KK.d,_1KK.e,_1KK.f,_1KK.g,_1KK.i,_1KK.j,_1KK.k);});}else{var _1KL=E(_1Ie),_1KM=E(_1KL.a),_1KN=B(_1tP(_1JQ,_1JS,_1KM.a,_1KM.b,_1KL.b,_1JY,_1KL.d,_1KL.e,_1KL.f,_1KL.g,_1KL.h,_1KL.i,_1KL.j,_1KL.k));return new F(function(){return _1JZ(_1KN.a,_1KN.b,_1KN.c,_1KN.d,_1KN.e,_1KN.f,_1KN.g,_1KN.i,_1KN.j,_1KN.k);});}},_1KO=E(_1IM);switch(_1KO){case 72:var _1KP=E(_1IP);if(0<=(_1KP-1|0)){return B(_1IQ(_1IO,_1KP-1|0));}else{return B(_1IQ(_1IO,_1KP));}break;case 75:var _1KQ=E(_1IO);if(0<=(_1KQ-1|0)){return B(_1JP(_1KQ-1|0,_1IP));}else{return B(_1JP(_1KQ,_1IP));}break;case 77:var _1KR=E(_1IO);if(E(_1Df)!=(_1KR+1|0)){return B(_1JP(_1KR+1|0,_1IP));}else{return B(_1JP(_1KR,_1IP));}break;case 80:var _1KS=E(_1IP);if(E(_1Dg)!=(_1KS+1|0)){return B(_1IQ(_1IO,_1KS+1|0));}else{return B(_1IQ(_1IO,_1KS));}break;case 104:var _1KT=E(_1IO);if(0<=(_1KT-1|0)){return B(_1JP(_1KT-1|0,_1IP));}else{return B(_1JP(_1KT,_1IP));}break;case 106:var _1KU=E(_1IP);if(E(_1Dg)!=(_1KU+1|0)){return B(_1IQ(_1IO,_1KU+1|0));}else{return B(_1IQ(_1IO,_1KU));}break;case 107:var _1KV=E(_1IP);if(0<=(_1KV-1|0)){return B(_1IQ(_1IO,_1KV-1|0));}else{return B(_1IQ(_1IO,_1KV));}break;case 108:var _1KW=E(_1IO);if(E(_1Df)!=(_1KW+1|0)){return B(_1JP(_1KW+1|0,_1IP));}else{return B(_1JP(_1KW,_1IP));}break;default:var _1KX=E(_1IO),_1KY=E(_1IP),_1KZ=function(_1L0,_1L1,_1L2,_1L3,_1L4,_1L5,_1L6,_1L7,_1L8,_1L9){if(E(E(_1Ie).c)==4){var _1La=new T2(0,_1IK,_1IL);}else{var _1La=new T2(0,_1IK,_1zx);}var _1Lb=B(_1kL(_1zx,_1L7,_1It,{_:0,a:E(_1L0),b:E(_1L1),c:E(_1L2),d:_1L3,e:_1L4,f:_1L5,g:E(_1L6),h:E(_1Ij),i:E(_1L7),j:E(_1L8),k:E(_1L9)},_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF,_1La,_1IG,_1IH,_1II)),_1Lc=_1Lb.a,_1Ld=_1Lb.b,_1Le=_1Lb.c,_1Lf=_1Lb.d,_1Lg=_1Lb.e,_1Lh=_1Lb.f,_1Li=_1Lb.g,_1Lj=_1Lb.h,_1Lk=_1Lb.i,_1Ll=_1Lb.j,_1Lm=_1Lb.k,_1Ln=_1Lb.l,_1Lo=_1Lb.m,_1Lp=_1Lb.n,_1Lq=_1Lb.o,_1Lr=_1Lb.q,_1Ls=_1Lb.r,_1Lt=_1Lb.s,_1Lu=_1Lb.t,_1Lv=_1Lb.u,_1Lw=E(_1Lb.p);if(!_1Lw._){return {_:0,a:E(_1Lc),b:E(_1Ld),c:E(_1Le),d:E(_1Lf),e:E(_1Lg),f:E(_1Lh),g:E(_1Li),h:E(_1Lj),i:_1Lk,j:_1Ll,k:_1Lm,l:_1Ln,m:E(_1Lo),n:_1Lp,o:E(_1Lq),p:E(_S),q:_1Lr,r:E(_1Ls),s:_1Lt,t:E(_1Lu),u:E(_1Lv)};}else{var _1Lx=B(_mz(_1L7,0))-2|0,_1Ly=function(_1Lz){var _1LA=E(_1Lc);return {_:0,a:E({_:0,a:E(_1LA.a),b:E(_1LA.b),c:E(_1LA.c),d:_1LA.d,e:_1LA.e,f:_1LA.f,g:E(_S),h:_1LA.h,i:E(_1LA.i),j:E(_1LA.j),k:E(_1LA.k)}),b:E(_1Ld),c:E(_1Le),d:E(B(_q(B(_68(_S,B(_1yS(B(_6k(_1Bo,_1Lw)),B(_13c(_1Lf)))))),new T(function(){return B(_6k(_1xQ,_1Lw));},1)))),e:E(_1Lg),f:E(_1Lh),g:E(_1Li),h:E(_1Lj),i:_1Lk,j:_1Ll,k:_1Lm,l:_1Ln,m:E(_1Lo),n:_1Lp,o:E(_1Lq),p:E(_S),q:_1Lr,r:E(_1Ls),s:_1Lt,t:E(_1Lu),u:E(_1Lv)};};if(_1Lx>0){if(!B(_qV(B(_1xz(_1Lx,_1L7)),_1zw))){return {_:0,a:E(_1Lc),b:E(_1Ld),c:E(_1Le),d:E(_1Lf),e:E(_1Lg),f:E(_1Lh),g:E(_1Li),h:E(_1Lj),i:_1Lk,j:_1Ll,k:_1Lm,l:_1Ln,m:E(_1Lo),n:_1Lp,o:E(_1Lq),p:E(_1Lw),q:_1Lr,r:E(_1Ls),s:_1Lt,t:E(_1Lu),u:E(_1Lv)};}else{return new F(function(){return _1Ly(_);});}}else{if(!B(_qV(_1L7,_1zw))){return {_:0,a:E(_1Lc),b:E(_1Ld),c:E(_1Le),d:E(_1Lf),e:E(_1Lg),f:E(_1Lh),g:E(_1Li),h:E(_1Lj),i:_1Lk,j:_1Ll,k:_1Lm,l:_1Ln,m:E(_1Lo),n:_1Lp,o:E(_1Lq),p:E(_1Lw),q:_1Lr,r:E(_1Ls),s:_1Lt,t:E(_1Lu),u:E(_1Lv)};}else{return new F(function(){return _1Ly(_);});}}}};if(E(_1KO)==32){var _1LB=E(_1Ie),_1LC=E(_1LB.a),_1LD=B(_1tP(_1KX,_1KY,_1LC.a,_1LC.b,_1LB.b,_1xF,_1LB.d,_1LB.e,_1LB.f,_1LB.g,_1LB.h,_1LB.i,_1LB.j,_1LB.k)),_1LE=E(_1LD.a),_1LF=B(_1xa(_1LE.a,E(_1LE.b),_1LD.b,_1LD.c,_1LD.d,_1LD.e,_1LD.f,_1LD.g,_1LD.h,_1LD.i,_1LD.j,_1LD.k));return B(_1KZ(_1LF.a,_1LF.b,_1LF.c,_1LF.d,_1LF.e,_1LF.f,_1LF.g,_1LF.i,_1LF.j,_1LF.k));}else{var _1LG=E(_1Ie),_1LH=E(_1LG.a),_1LI=B(_1tP(_1KX,_1KY,_1LH.a,_1LH.b,_1LG.b,_1xF,_1LG.d,_1LG.e,_1LG.f,_1LG.g,_1LG.h,_1LG.i,_1LG.j,_1LG.k));return B(_1KZ(_1LI.a,_1LI.b,_1LI.c,_1LI.d,_1LI.e,_1LI.f,_1LI.g,_1LI.i,_1LI.j,_1LI.k));}}}),_1LJ=B(_1aX(_1Il,_1Im,_1D0,_1D1,_1D2,_1Io,_)),_1LK=_1LJ,_1LL=E(_1In),_1LM=function(_,_1LN){var _1LO=function(_1LP){var _1LQ=B(_1z2(_1CT,B(_8w(_1LN)),_)),_1LR=E(_1LK),_1LS=_1LR.d,_1LT=_1LR.e,_1LU=_1LR.f,_1LV=_1LR.g,_1LW=_1LR.i,_1LX=_1LR.j,_1LY=_1LR.k,_1LZ=_1LR.l,_1M0=_1LR.m,_1M1=_1LR.n,_1M2=_1LR.o,_1M3=_1LR.p,_1M4=_1LR.q,_1M5=_1LR.s,_1M6=_1LR.u,_1M7=E(_1LR.t),_1M8=_1M7.a,_1M9=_1M7.d,_1Ma=_1M7.e,_1Mb=_1M7.f,_1Mc=_1M7.g,_1Md=_1M7.h,_1Me=E(_1LR.a),_1Mf=_1Me.c,_1Mg=_1Me.f,_1Mh=_1Me.g,_1Mi=_1Me.h,_1Mj=E(_1LR.h),_1Mk=E(_1LR.r),_1Ml=function(_1Mm){var _1Mn=function(_1Mo){if(_1Mo!=E(_1zq)){var _1Mp=B(_6X(_1gX,_1Mo)),_1Mq=_1Mp.a,_1Mr=E(_1Mp.b),_1Ms=B(_1ds(_1Mq,_1Mr,new T(function(){return B(_6X(_1ix,_1Mo));})));return new F(function(){return _1CY(_1Ik,_1D0,_1D1,_1D2,_1zo,B(_6X(_1h8,_1Mo)),_1Ms,_1Mf,B(_6X(_1hl,_1Mo)),32,_1Mo,_1Mh,_1Mi,B(_q(_1Me.i,new T2(1,_1zn,new T(function(){return B(_A(0,_1Mg,_S));})))),B(_1xZ(_1zm,_1Ms)),_wA,_1Mq,_1Mr,_S,_1LS,_1LT,_1LU,_1LV,_1Mj.a,_1Mj.b,_1LW,_1LX,_1LY, -1,_1M0,_1M1,_1M2,_1M3,_1M4,_1Mk.a,_1Mk.b,_1M5,_wA,_wA,_wA,_1M9,_1Ma,_1Mb,_1Mc,_1Md,_1M6,_);});}else{var _1Mt=__app1(E(_no),_1Im),_1Mu=B(A2(_np,_1Il,_)),_1Mv=B(A(_mU,[_1Il,_j9,_1A4,_1zk,_1zj,_])),_1Mw=B(A(_mU,[_1Il,_j9,_1zg,_1zi,_1zh,_])),_1Mx=B(A(_mU,[_1Il,_j9,_1zg,_1zf,_1A5,_])),_1My=B(A(_mU,[_1Il,_j9,_1A4,_1A3,_1A2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1h7),b:E(_1zK),c:E(_1Mf),d:E(_1zF),e:32,f:0,g:E(_1Mh),h:_1Mi,i:E(_S),j:E(_1Me.j),k:E(_wA)}),b:E(_1gR),c:E(_1LR.c),d:E(_1LS),e:E(_1LT),f:E(_1LU),g:E(_1LV),h:E(_1Mj),i:_1LW,j:_1LX,k:_1LY,l:_1LZ,m:E(_1M0),n:_1M1,o:E(_1M2),p:E(_1M3),q:_1M4,r:E(_1Mk),s:_1M5,t:E({_:0,a:E(_1M8),b:E(_wA),c:E(_wA),d:E(_1M9),e:E(_1Ma),f:E(_1Mb),g:E(_1Mc),h:E(_1Md)}),u:E(_1M6)};});}};if(_1LZ>=0){return new F(function(){return _1Mn(_1LZ);});}else{return new F(function(){return _1Mn(_1Mg+1|0);});}};if(!E(_1M8)){if(E(_1LL)==110){return new F(function(){return _1Ml(_);});}else{return _1LR;}}else{return new F(function(){return _1Ml(_);});}};if(E(_1LL)==114){if(!B(_6f(_1LN,_1zr))){var _1Mz=E(_1LN);if(!_1Mz._){return _1LK;}else{var _1MA=_1Mz.b;return new T(function(){var _1MB=E(_1LK),_1MC=E(_1MB.a),_1MD=E(_1Mz.a),_1ME=E(_1MD);if(_1ME==34){var _1MF=B(_RX(_1MD,_1MA));if(!_1MF._){var _1MG=E(_1AZ);}else{var _1MH=E(_1MF.b);if(!_1MH._){var _1MI=E(_1zJ);}else{var _1MJ=_1MH.a,_1MK=E(_1MH.b);if(!_1MK._){var _1ML=new T2(1,new T2(1,_1MJ,_S),_S);}else{var _1MM=E(_1MJ),_1MN=new T(function(){var _1MO=B(_Hc(126,_1MK.a,_1MK.b));return new T2(0,_1MO.a,_1MO.b);});if(E(_1MM)==126){var _1MP=new T2(1,_S,new T2(1,new T(function(){return E(E(_1MN).a);}),new T(function(){return E(E(_1MN).b);})));}else{var _1MP=new T2(1,new T2(1,_1MM,new T(function(){return E(E(_1MN).a);})),new T(function(){return E(E(_1MN).b);}));}var _1ML=_1MP;}var _1MI=_1ML;}var _1MG=_1MI;}var _1MQ=_1MG;}else{var _1MR=E(_1MA);if(!_1MR._){var _1MS=new T2(1,new T2(1,_1MD,_S),_S);}else{var _1MT=new T(function(){var _1MU=B(_Hc(126,_1MR.a,_1MR.b));return new T2(0,_1MU.a,_1MU.b);});if(E(_1ME)==126){var _1MV=new T2(1,_S,new T2(1,new T(function(){return E(E(_1MT).a);}),new T(function(){return E(E(_1MT).b);})));}else{var _1MV=new T2(1,new T2(1,_1MD,new T(function(){return E(E(_1MT).a);})),new T(function(){return E(E(_1MT).b);}));}var _1MS=_1MV;}var _1MQ=_1MS;}var _1MW=B(_Gk(B(_sF(_1zp,new T(function(){return B(_Jo(_1MQ));})))));if(!_1MW._){return E(_1zd);}else{if(!E(_1MW.b)._){var _1MX=E(_1MW.a),_1MY=B(_6X(_1gX,_1MX)),_1MZ=B(_6X(_1MQ,1));if(!_1MZ._){var _1N0=__Z;}else{var _1N1=E(_1MZ.b);if(!_1N1._){var _1N2=__Z;}else{var _1N3=E(_1MZ.a),_1N4=new T(function(){var _1N5=B(_Hc(44,_1N1.a,_1N1.b));return new T2(0,_1N5.a,_1N5.b);});if(E(_1N3)==44){var _1N6=B(_13r(_S,new T(function(){return E(E(_1N4).a);}),new T(function(){return E(E(_1N4).b);})));}else{var _1N6=B(_13v(new T2(1,_1N3,new T(function(){return E(E(_1N4).a);})),new T(function(){return E(E(_1N4).b);})));}var _1N2=_1N6;}var _1N0=_1N2;}var _1N7=B(_6X(_1MQ,2));if(!_1N7._){var _1N8=E(_1zL);}else{var _1N9=_1N7.a,_1Na=E(_1N7.b);if(!_1Na._){var _1Nb=B(_6k(_1zA,new T2(1,new T2(1,_1N9,_S),_S)));}else{var _1Nc=E(_1N9),_1Nd=new T(function(){var _1Ne=B(_Hc(44,_1Na.a,_1Na.b));return new T2(0,_1Ne.a,_1Ne.b);});if(E(_1Nc)==44){var _1Nf=B(_6k(_1zA,new T2(1,_S,new T2(1,new T(function(){return E(E(_1Nd).a);}),new T(function(){return E(E(_1Nd).b);})))));}else{var _1Nf=B(_6k(_1zA,new T2(1,new T2(1,_1Nc,new T(function(){return E(E(_1Nd).a);})),new T(function(){return E(E(_1Nd).b);}))));}var _1Nb=_1Nf;}var _1N8=_1Nb;}return {_:0,a:E({_:0,a:E(B(_6X(_1h8,_1MX))),b:E(B(_1ds(_1MY.a,E(_1MY.b),new T(function(){return B(_6X(_1ix,_1MX));})))),c:E(_1MC.c),d:B(_6X(_1hl,_1MX)),e:32,f:_1MX,g:E(_1MC.g),h:_1MC.h,i:E(_1MC.i),j:E(_1MC.j),k:E(_1MC.k)}),b:E(_1MY),c:E(_1MB.c),d:E(_1MB.d),e:E(_1N0),f:E(_1N8),g:E(_1MB.g),h:E(_1MB.h),i:_1MB.i,j:_1MB.j,k:_1MB.k,l:_1MB.l,m:E(_1MB.m),n:_1MB.n,o:E(_1MB.o),p:E(_1MB.p),q:_1MB.q,r:E(_1MB.r),s:_1MB.s,t:E(_1MB.t),u:E(_1MB.u)};}else{return E(_1ze);}}});}}else{return new F(function(){return _1LO(_);});}}else{return new F(function(){return _1LO(_);});}};switch(E(_1LL)){case 100:var _1Ng=__app1(E(_1AX),toJSStr(E(_1zu)));return new F(function(){return _1LM(_,_1za);});break;case 114:var _1Nh=B(_13G(_6C,toJSStr(E(_1zu)),_));return new F(function(){return _1LM(_,new T(function(){var _1Ni=E(_1Nh);if(!_1Ni._){return E(_1zb);}else{return fromJSStr(B(_1mY(_1Ni.a)));}}));});break;case 115:var _1Nj=new T(function(){var _1Nk=new T(function(){var _1Nl=new T(function(){var _1Nm=B(_6k(_6H,_1Dk));if(!_1Nm._){return __Z;}else{return B(_1z7(new T2(1,_1Nm.a,new T(function(){return B(_1A6(_1zs,_1Nm.b));}))));}}),_1Nn=new T(function(){var _1No=function(_1Np){var _1Nq=E(_1Np);if(!_1Nq._){return __Z;}else{var _1Nr=E(_1Nq.a);return new T2(1,_1Nr.a,new T2(1,_1Nr.b,new T(function(){return B(_1No(_1Nq.b));})));}},_1Ns=B(_1No(_1Dj));if(!_1Ns._){return __Z;}else{return B(_1z7(new T2(1,_1Ns.a,new T(function(){return B(_1A6(_1zs,_1Ns.b));}))));}});return B(_1A6(_1zt,new T2(1,_1Nn,new T2(1,_1Nl,_S))));});return B(_q(B(_1z7(new T2(1,new T(function(){return B(_A(0,_1D9,_S));}),_1Nk))),_1zI));}),_1Nt=__app2(E(_1B0),toJSStr(E(_1zu)),B(_1mY(B(_1CV(B(unAppCStr("\"",_1Nj)))))));return new F(function(){return _1LM(_,_1zc);});break;default:return new F(function(){return _1LM(_,_1zv);});}};if(!E(_1Id.f)){var _1Nu=B(_1z2(_1CT,_1Bn,_));return new F(function(){return _1If(_);});}else{var _1Nv=B(_1z2(_1CT,_1Bm,_));return new F(function(){return _1If(_);});}},_1Nw=E(_1Dl);if(!_1Nw._){var _1Nx=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1I9(_);});}else{var _1Ny=new T(function(){var _1Nz=E(_1Nw.a),_1NA=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1NB){return new F(function(){return _1zM(_1Nz.a,_1NB);});},new T2(1,function(_1NC){return new F(function(){return _1zM(_1Nz.b,_1NC);});},_S)),new T2(1,_y,new T(function(){return B(_1B2(_1Nw.b));}))));});return new T2(1,_z,_1NA);}),_1ND=B(_1z2(_1CT,new T2(1,_2u,_1Ny),_));return new F(function(){return _1I9(_);});}},_1NE=E(_1Dk);if(!_1NE._){var _1NF=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1I8(_);});}else{var _1NG=new T(function(){return B(_A(0,E(_1NE.a),new T(function(){return B(_1Ba(_1NE.b));})));}),_1NH=B(_1z2(_1CT,new T2(1,_2u,_1NG),_));return new F(function(){return _1I8(_);});}},_1NI=E(_1Dj);if(!_1NI._){var _1NJ=B(_1z2(_1CT,_1zH,_));return new F(function(){return _1I7(_);});}else{var _1NK=new T(function(){var _1NL=E(_1NI.a),_1NM=new T(function(){return B(A3(_sk,_6D,new T2(1,function(_1NN){return new F(function(){return _1zM(_1NL.a,_1NN);});},new T2(1,function(_1NO){return new F(function(){return _1zM(_1NL.b,_1NO);});},_S)),new T2(1,_y,new T(function(){return B(_1Be(_1NI.b));}))));});return new T2(1,_z,_1NM);}),_1NP=B(_1z2(_1CT,new T2(1,_2u,_1NK),_));return new F(function(){return _1I7(_);});}}else{return new F(function(){return _1DR(_,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1DM,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1DL,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_S,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_1DJ,_1DI);});}}}}}}}else{if(!E(_1DG)){return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:_1Dt,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E({_:0,a:E(_1DA),b:E(_1DB),c:E(_1DC),d:E(_wA),e:E(_1DE),f:E(_wA),g:E(_wA),h:E(_1DH)}),u:E(_1DI)};}else{var _1NQ=E(_1CZ),_1NR=new T(function(){var _1NS=new T(function(){var _1NT=B(_1n2(_1Ds));return new T2(0,_1NT.a,_1NT.b);}),_1NU=new T(function(){return B(_mz(E(_1NS).a,0))-1|0;}),_1NV=function(_1NW){var _1NX=E(_1NW);switch(_1NX){case  -2:return E(_1DO);case  -1:return {_:0,a:E(_1DN),b:E(_1DM),c:E(B(_1gw(_S,new T(function(){return B(_6X(E(_1NS).b,_1Dt));})))),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:_1Dt,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E({_:0,a:E(_1DA),b:E(_1DB),c:E(_wB),d:E(_wA),e:E(_1DE),f:E(_wA),g:E(_wA),h:E(_1DH)}),u:E(_1DI)};default:return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:_1NX,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};}};switch(E(B(_1nW(E(_1D3))))){case 32:return {_:0,a:E(_1DN),b:E(_1DM),c:E(B(_1gw(_S,new T(function(){return B(_6X(E(_1NS).b,_1Dt));})))),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:_1Dt,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E({_:0,a:E(_1DA),b:E(_1DB),c:E(_wB),d:E(_wA),e:E(_1DE),f:E(_wA),g:E(_wA),h:E(_1DH)}),u:E(_1DI)};break;case 72:var _1NY=E(_1Dt);if(!_1NY){return B(_1NV(E(_1NU)));}else{return B(_1NV(_1NY-1|0));}break;case 75:if(_1Dt!=E(_1NU)){return B(_1NV(_1Dt+1|0));}else{return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:0,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};}break;case 77:var _1NZ=E(_1Dt);if(!_1NZ){return B(_1NV(E(_1NU)));}else{return B(_1NV(_1NZ-1|0));}break;case 80:if(_1Dt!=E(_1NU)){return B(_1NV(_1Dt+1|0));}else{return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:0,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};}break;case 104:if(_1Dt!=E(_1NU)){return B(_1NV(_1Dt+1|0));}else{return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:0,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};}break;case 106:if(_1Dt!=E(_1NU)){return B(_1NV(_1Dt+1|0));}else{return {_:0,a:E(_1DN),b:E(_1DM),c:E(_1Dh),d:E(_1Di),e:E(_1Dj),f:E(_1Dk),g:E(_1Dl),h:E(_1DL),i:_1Do,j:_1Dp,k:_1Dq,l:_1Dr,m:E(_1Ds),n:0,o:E(_1Du),p:E(_1Dv),q:_1Dw,r:E(_1DK),s:_1Dz,t:E(_1DJ),u:E(_1DI)};}break;case 107:var _1O0=E(_1Dt);if(!_1O0){return B(_1NV(E(_1NU)));}else{return B(_1NV(_1O0-1|0));}break;case 108:var _1O1=E(_1Dt);if(!_1O1){return B(_1NV(E(_1NU)));}else{return B(_1NV(_1O1-1|0));}break;default:return E(_1DO);}});return new F(function(){return _1aX(_1NQ.a,_1NQ.b,_1D0,_1D1,_1D2,_1NR,_);});}}};if(!E(_1DC)){return new F(function(){return _1DP(_);});}else{if(!E(_1DD)){return new F(function(){return _Ye(_1CZ,_1D0,_1D1,_1D4,_1D5,_1D6,_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd,_1De,_1Df,_1Dg,_1Dh,_1Di,_1Dj,_1Dk,_1Dl,_1Dm,_1Dn,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw,_1DK,_1Dz,_1DA,_1DB,_wA,_1DE,_wB,_1DG,_1DH,_1DI,_);});}else{return new F(function(){return _1DP(_);});}}}else{return _1DO;}},_1O2=function(_1O3){var _1O4=E(_1O3),_1O5=E(_1O4.a),_1O6=new T(function(){return B(_q(_1O5.b,new T(function(){return B(unAppCStr(" >>",_1O5.c));},1)));});return new T2(0,new T2(1,_1O4.b,_1n8),_1O6);},_1O7=function(_1O8,_1O9,_1Oa,_1Ob,_1Oc,_1Od,_1Oe,_1Of,_1Og,_1Oh,_1Oi,_1Oj,_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or,_1Os,_1Ot,_1Ou,_1Ov,_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1OB,_1OC,_1OD,_){var _1OE=function(_1OF){var _1OG=new T(function(){var _1OH=function(_1OI){var _1OJ=E(_1OI);return (_1OJ==30)?{_:0,a:E(_1Oc),b:E(_1Od),c:E(_1Oe),d:E(B(_q(B(_68(_S,B(_1yS(B(_6k(_1Bo,_1Or)),B(_13c(_1Of)))))),new T(function(){return B(_6k(_1O2,_1Or));},1)))),e:E(_1Og),f:E(_1Oh),g:E(_1Oi),h:E(_1Oj),i:_1Ok,j:_1Ol,k:_1Om,l:_1On,m:E(_1Oo),n:_1Op,o:E(_1Oq),p:E(_1Or),q:30,r:E(_1Ot),s:_1OF,t:E({_:0,a:E(_1Ov),b:E(_1Ow),c:E(_1Ox),d:E(_1Oy),e:E(_1Oz),f:E(_1OA),g:E(_1OB),h:E(_1OC)}),u:E(_1OD)}:{_:0,a:E(_1Oc),b:E(_1Od),c:E(_1Oe),d:E(_1Of),e:E(_1Og),f:E(_1Oh),g:E(_1Oi),h:E(_1Oj),i:_1Ok,j:_1Ol,k:_1Om,l:_1On,m:E(_1Oo),n:_1Op,o:E(_1Oq),p:E(_1Or),q:_1OJ,r:E(_1Ot),s:_1OF,t:E({_:0,a:E(_1Ov),b:E(_1Ow),c:E(_1Ox),d:E(_1Oy),e:E(_1Oz),f:E(_1OA),g:E(_1OB),h:E(_1OC)}),u:E(_1OD)};};if(!E(_1Or)._){return B(_1OH(_1Os));}else{if(!B(_au(_1OF,20))){return B(_1OH(_1Os+1|0));}else{return B(_1OH(_1Os));}}});if(!E(_1OC)){var _1OK=E(_1OG),_1OL=E(_1OK.a),_1OM=E(_1OK.b),_1ON=E(_1OK.h),_1OO=E(_1OK.t);return new F(function(){return _VN(_1O8,_1O9,_1Oa,_1OL.a,_1OL.b,_1OL.c,_1OL.d,_1OL.e,_1OL.f,_1OL.g,_1OL.h,_1OL.i,_1OL.j,_1OL.k,_1OM.a,_1OM.b,_1OK.c,_1OK.d,_1OK.e,_1OK.f,_1OK.g,_1ON.a,_1ON.b,_1OK.i,_1OK.j,_1OK.k,_1OK.l,_1OK.m,_1OK.n,_1OK.o,_1OK.p,_1OK.q,_1OK.r,_1OK.s,_1OO.a,_1OO.b,_1OO.c,_1OO.d,_1OO.e,_1OO.f,_1OO.g,_1OO.h,_1OK.u,_);});}else{if(!B(_au(_1OF,10))){if(!E(_1Ox)){var _1OP=E(_1O8);return new F(function(){return _1aX(_1OP.a,_1OP.b,_1O9,_1Oa,_1Ob,_1OG,_);});}else{var _1OQ=E(_1OG),_1OR=E(_1OQ.a),_1OS=E(_1OQ.b),_1OT=E(_1OQ.h),_1OU=E(_1OQ.t);return new F(function(){return _VN(_1O8,_1O9,_1Oa,_1OR.a,_1OR.b,_1OR.c,_1OR.d,_1OR.e,_1OR.f,_1OR.g,_1OR.h,_1OR.i,_1OR.j,_1OR.k,_1OS.a,_1OS.b,_1OQ.c,_1OQ.d,_1OQ.e,_1OQ.f,_1OQ.g,_1OT.a,_1OT.b,_1OQ.i,_1OQ.j,_1OQ.k,_1OQ.l,_1OQ.m,_1OQ.n,_1OQ.o,_1OQ.p,_1OQ.q,_1OQ.r,_1OQ.s,_1OU.a,_1OU.b,_1OU.c,_1OU.d,_1OU.e,_1OU.f,_1OU.g,_1OU.h,_1OQ.u,_);});}}else{var _1OV=E(_1OG),_1OW=E(_1OV.a),_1OX=E(_1OV.b),_1OY=E(_1OV.h),_1OZ=E(_1OV.t);return new F(function(){return _VN(_1O8,_1O9,_1Oa,_1OW.a,_1OW.b,_1OW.c,_1OW.d,_1OW.e,_1OW.f,_1OW.g,_1OW.h,_1OW.i,_1OW.j,_1OW.k,_1OX.a,_1OX.b,_1OV.c,_1OV.d,_1OV.e,_1OV.f,_1OV.g,_1OY.a,_1OY.b,_1OV.i,_1OV.j,_1OV.k,_1OV.l,_1OV.m,_1OV.n,_1OV.o,_1OV.p,_1OV.q,_1OV.r,_1OV.s,_1OZ.a,_1OZ.b,_1OZ.c,_1OZ.d,_1OZ.e,_1OZ.f,_1OZ.g,_1OZ.h,_1OV.u,_);});}}};if(_1Ou<=298){return new F(function(){return _1OE(_1Ou+1|0);});}else{return new F(function(){return _1OE(0);});}},_1P0=function(_1P1,_1P2,_1P3){var _1P4=E(_1P3);if(!_1P4._){return 0;}else{var _1P5=_1P4.b,_1P6=E(_1P4.a),_1P7=_1P6.a,_1P8=_1P6.b;return (_1P1<=_1P7)?1+B(_1P0(_1P1,_1P2,_1P5))|0:(_1P1>=_1P7+_1P6.c)?1+B(_1P0(_1P1,_1P2,_1P5))|0:(_1P2<=_1P8)?1+B(_1P0(_1P1,_1P2,_1P5))|0:(_1P2>=_1P8+_1P6.d)?1+B(_1P0(_1P1,_1P2,_1P5))|0:1;}},_1P9=function(_1Pa,_1Pb,_1Pc){var _1Pd=E(_1Pc);if(!_1Pd._){return 0;}else{var _1Pe=_1Pd.b,_1Pf=E(_1Pd.a),_1Pg=_1Pf.a,_1Ph=_1Pf.b;if(_1Pa<=_1Pg){return 1+B(_1P9(_1Pa,_1Pb,_1Pe))|0;}else{if(_1Pa>=_1Pg+_1Pf.c){return 1+B(_1P9(_1Pa,_1Pb,_1Pe))|0;}else{var _1Pi=E(_1Pb);return (_1Pi<=_1Ph)?1+B(_1P0(_1Pa,_1Pi,_1Pe))|0:(_1Pi>=_1Ph+_1Pf.d)?1+B(_1P0(_1Pa,_1Pi,_1Pe))|0:1;}}}},_1Pj=function(_1Pk,_1Pl,_1Pm){var _1Pn=E(_1Pm);if(!_1Pn._){return 0;}else{var _1Po=_1Pn.b,_1Pp=E(_1Pn.a),_1Pq=_1Pp.a,_1Pr=_1Pp.b,_1Ps=E(_1Pk);if(_1Ps<=_1Pq){return 1+B(_1P9(_1Ps,_1Pl,_1Po))|0;}else{if(_1Ps>=_1Pq+_1Pp.c){return 1+B(_1P9(_1Ps,_1Pl,_1Po))|0;}else{var _1Pt=E(_1Pl);return (_1Pt<=_1Pr)?1+B(_1P0(_1Ps,_1Pt,_1Po))|0:(_1Pt>=_1Pr+_1Pp.d)?1+B(_1P0(_1Ps,_1Pt,_1Po))|0:1;}}}},_1Pu=function(_1Pv,_1Pw){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1Pw)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1Pw)-100,E(_1Pv),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1Pv),100);}),new T2(1,new T(function(){return new T4(0,E(_1Pv)-100,100,100,E(_1Pw)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1Pv)-200,E(_1Pw)-200);}),_S)))));},_1Px=32,_1Py=76,_1Pz=75,_1PA=74,_1PB=72,_1PC=64,_1PD=function(_1PE,_1PF,_1PG,_1PH,_1PI){var _1PJ=new T(function(){var _1PK=E(_1PF),_1PL=E(_1PK.a),_1PM=_1PL.a,_1PN=_1PL.b,_1PO=B(_1Pu(_1PM,_1PN)),_1PP=new T(function(){var _1PQ=E(_1PK.b);return new T2(0,new T(function(){return B(_ge(_1PM,_1PQ.a));}),new T(function(){return B(_ge(_1PN,_1PQ.b));}));});switch(B(_1Pj(new T(function(){return E(_1PH)*E(E(_1PP).a);},1),new T(function(){return E(_1PI)*E(E(_1PP).b);},1),new T2(1,_1PO.a,_1PO.b)))){case 1:return E(_1PB);break;case 2:return E(_1PA);break;case 3:return E(_1Pz);break;case 4:return E(_1Py);break;case 5:return E(_1Px);break;default:return E(_1PC);}});return function(_1PR,_){var _1PS=E(E(_1PF).a),_1PT=E(_1PR),_1PU=E(_1PT.a),_1PV=E(_1PT.b),_1PW=E(_1PT.h),_1PX=E(_1PT.r),_1PY=E(_1PT.t);return new F(function(){return _1CY(_1PE,_1PS.a,_1PS.b,_1PG,_1PJ,_1PU.a,_1PU.b,_1PU.c,_1PU.d,_1PU.e,_1PU.f,_1PU.g,_1PU.h,_1PU.i,_1PU.j,_1PU.k,_1PV.a,_1PV.b,_1PT.c,_1PT.d,_1PT.e,_1PT.f,_1PT.g,_1PW.a,_1PW.b,_1PT.i,_1PT.j,_1PT.k,_1PT.l,_1PT.m,_1PT.n,_1PT.o,_1PT.p,_1PT.q,_1PX.a,_1PX.b,_1PT.s,_1PY.a,_1PY.b,_1PY.c,_1PY.d,_1PY.e,_1PY.f,_1PY.g,_1PY.h,_1PT.u,_);});};},_1PZ=0,_1Q0=2,_1Q1=2,_1Q2=0,_1Q3=new T(function(){return eval("document");}),_1Q4=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Q5=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1Q6=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1Q7=function(_1Q8){return E(E(_1Q8).b);},_1Q9=function(_1Qa,_1Qb){return new F(function(){return A2(_1Q7,_1Qa,function(_){var _1Qc=E(_1Qb),_1Qd=__app1(E(_1Q6),_1Qc);if(!_1Qd){return _2N;}else{var _1Qe=__app1(E(_1Q5),_1Qc);return new T1(1,new T2(0,_1Qe,_1Qc));}});});},_1Qf=1,_1Qg=new T(function(){var _1Qh=E(_1hl);if(!_1Qh._){return E(_nn);}else{return {_:0,a:E(_1h7),b:E(B(_1ds(_1gQ,5,_1hB))),c:E(_1Qf),d:E(_1Qh.a),e:32,f:0,g:E(_S),h:0,i:E(_S),j:E(_wA),k:E(_wA)};}}),_1Qi=0,_1Qj=4,_1Qk=new T2(0,_1Qj,_1Qi),_1Ql=new T2(0,_1Qi,_1Qi),_1Qm={_:0,a:E(_wA),b:E(_wA),c:E(_wB),d:E(_wA),e:E(_wA),f:E(_wA),g:E(_wA),h:E(_wA)},_1Qn=new T(function(){return {_:0,a:E(_1Qg),b:E(_1gR),c:E(_1eD),d:E(_S),e:E(_S),f:E(_S),g:E(_S),h:E(_1Ql),i:0,j:0,k:0,l: -1,m:E(_S),n:0,o:E(_S),p:E(_S),q:0,r:E(_1Qk),s:0,t:E(_1Qm),u:E(_S)};}),_1Qo=new T1(0,100),_1Qp=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1Qq=new T6(0,_2N,_2O,_S,_1Qp,_2N,_2N),_1Qr=new T(function(){return B(_2L(_1Qq));}),_1Qs=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1Qt=new T6(0,_2N,_2O,_S,_1Qs,_2N,_2N),_1Qu=new T(function(){return B(_2L(_1Qt));}),_1Qv=new T1(1,50),_1Qw=function(_1Qx){return E(E(_1Qx).a);},_1Qy=function(_1Qz){return E(E(_1Qz).a);},_1QA=function(_1QB){return E(E(_1QB).b);},_1QC=function(_1QD){return E(E(_1QD).b);},_1QE=function(_1QF){return E(E(_1QF).a);},_1QG=function(_){return new F(function(){return nMV(_2N);});},_1QH=new T(function(){return B(_36(_1QG));}),_1QI=function(_1QJ){return E(E(_1QJ).b);},_1QK=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1QL=function(_1QM){return E(E(_1QM).d);},_1QN=function(_1QO,_1QP,_1QQ,_1QR,_1QS,_1QT){var _1QU=B(_1Qw(_1QO)),_1QV=B(_1Qy(_1QU)),_1QW=new T(function(){return B(_1Q7(_1QU));}),_1QX=new T(function(){return B(_1QL(_1QV));}),_1QY=new T(function(){return B(A1(_1QP,_1QR));}),_1QZ=new T(function(){return B(A2(_1QE,_1QQ,_1QS));}),_1R0=function(_1R1){return new F(function(){return A1(_1QX,new T3(0,_1QZ,_1QY,_1R1));});},_1R2=function(_1R3){var _1R4=new T(function(){var _1R5=new T(function(){var _1R6=__createJSFunc(2,function(_1R7,_){var _1R8=B(A2(E(_1R3),_1R7,_));return _3a;}),_1R9=_1R6;return function(_){return new F(function(){return __app3(E(_1QK),E(_1QY),E(_1QZ),_1R9);});};});return B(A1(_1QW,_1R5));});return new F(function(){return A3(_1QA,_1QV,_1R4,_1R0);});},_1Ra=new T(function(){var _1Rb=new T(function(){return B(_1Q7(_1QU));}),_1Rc=function(_1Rd){var _1Re=new T(function(){return B(A1(_1Rb,function(_){var _=wMV(E(_1QH),new T1(1,_1Rd));return new F(function(){return A(_1QC,[_1QQ,_1QS,_1Rd,_]);});}));});return new F(function(){return A3(_1QA,_1QV,_1Re,_1QT);});};return B(A2(_1QI,_1QO,_1Rc));});return new F(function(){return A3(_1QA,_1QV,_1Ra,_1R2);});},_1Rf=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1Rg=function(_){var _1Rh=rMV(E(_1QH)),_1Ri=E(_1Rh);if(!_1Ri._){var _1Rj=__app1(E(_1Rf),E(_3a));return new F(function(){return _gL(_);});}else{var _1Rk=__app1(E(_1Rf),E(_1Ri.a));return new F(function(){return _gL(_);});}},_1Rl="src",_1Rm=new T(function(){return B(unCStr("img"));}),_1Rn=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1Ro=function(_1Rp,_1Rq){return new F(function(){return A2(_1Q7,_1Rp,function(_){var _1Rr=__app1(E(_1Rn),toJSStr(E(_1Rm))),_1Rs=__app3(E(_i7),_1Rr,E(_1Rl),E(_1Rq));return _1Rr;});});},_1Rt=new T(function(){return B(unCStr(".png"));}),_1Ru=function(_1Rv,_1Rw){var _1Rx=E(_1Rv);if(_1Rx==( -1)){return __Z;}else{var _1Ry=new T(function(){var _1Rz=new T(function(){return toJSStr(B(_q(_1Rw,new T(function(){return B(_q(B(_A(0,_1Rx,_S)),_1Rt));},1))));});return B(_1Ro(_5W,_1Rz));});return new F(function(){return _q(B(_1Ru(_1Rx-1|0,_1Rw)),new T2(1,_1Ry,_S));});}},_1RA=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1RB=new T(function(){return B(_1Ru(120,_1RA));}),_1RC=function(_1RD,_){var _1RE=E(_1RD);if(!_1RE._){return _S;}else{var _1RF=B(A1(_1RE.a,_)),_1RG=B(_1RC(_1RE.b,_));return new T2(1,_1RF,_1RG);}},_1RH=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1RI=new T(function(){return B(_1Ru(56,_1RH));}),_1RJ=function(_1RK,_){var _1RL=E(_1RK);if(!_1RL._){return _S;}else{var _1RM=B(A1(_1RL.a,_)),_1RN=B(_1RJ(_1RL.b,_));return new T2(1,_1RM,_1RN);}},_1RO=new T(function(){return B(unCStr("Images/img"));}),_1RP=new T(function(){return B(_1Ru(5,_1RO));}),_1RQ=function(_1RR,_){var _1RS=E(_1RR);if(!_1RS._){return _S;}else{var _1RT=B(A1(_1RS.a,_)),_1RU=B(_1RQ(_1RS.b,_));return new T2(1,_1RT,_1RU);}},_1RV=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1RW=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1RX=function(_1RY,_1RZ,_1S0){var _1S1=B(_1Qw(_1RY)),_1S2=new T(function(){return B(_1Q7(_1S1));}),_1S3=function(_1S4){var _1S5=function(_){var _1S6=E(_1RZ);if(!_1S6._){var _1S7=B(A1(_1S4,_gK)),_1S8=__createJSFunc(0,function(_){var _1S9=B(A1(_1S7,_));return _3a;}),_1Sa=__app2(E(_1RW),_1S6.a,_1S8);return new T(function(){var _1Sb=Number(_1Sa),_1Sc=jsTrunc(_1Sb);return new T2(0,_1Sc,E(_1S6));});}else{var _1Sd=B(A1(_1S4,_gK)),_1Se=__createJSFunc(0,function(_){var _1Sf=B(A1(_1Sd,_));return _3a;}),_1Sg=__app2(E(_1RV),_1S6.a,_1Se);return new T(function(){var _1Sh=Number(_1Sg),_1Si=jsTrunc(_1Sh);return new T2(0,_1Si,E(_1S6));});}};return new F(function(){return A1(_1S2,_1S5);});},_1Sj=new T(function(){return B(A2(_1QI,_1RY,function(_1Sk){return E(_1S0);}));});return new F(function(){return A3(_1QA,B(_1Qy(_1S1)),_1Sj,_1S3);});},_1Sl=function(_){var _1Sm=B(_1RQ(_1RP,_)),_1Sn=B(_1RJ(_1RI,_)),_1So=B(_1RC(_1RB,_)),_1Sp=__app1(E(_1Q4),"canvas"),_1Sq=__eq(_1Sp,E(_3a));if(!E(_1Sq)){var _1Sr=__isUndef(_1Sp);if(!E(_1Sr)){var _1Ss=B(A3(_1Q9,_5W,_1Sp,_)),_1St=E(_1Ss);if(!_1St._){return new F(function(){return die(_1Qu);});}else{var _1Su=E(_1St.a),_1Sv=B(_62(_1Su.b,_)),_1Sw=_1Sv,_1Sx=nMV(_1Qn),_1Sy=_1Sx,_1Sz=new T3(0,_1Sm,_1Sn,_1So),_1SA=B(A(_1QN,[_5X,_3D,_m,_1Q3,_1Q0,function(_1SB,_){var _1SC=B(_1Rg(_)),_1SD=rMV(_1Sy),_1SE=E(E(_1Sw).a),_1SF=E(_1SD),_1SG=E(_1SF.a),_1SH=E(_1SF.b),_1SI=E(_1SF.h),_1SJ=E(_1SF.r),_1SK=E(_1SF.t),_1SL=B(_1CY(_1Su,_1SE.a,_1SE.b,_1Sz,E(_1SB).a,_1SG.a,_1SG.b,_1SG.c,_1SG.d,_1SG.e,_1SG.f,_1SG.g,_1SG.h,_1SG.i,_1SG.j,_1SG.k,_1SH.a,_1SH.b,_1SF.c,_1SF.d,_1SF.e,_1SF.f,_1SF.g,_1SI.a,_1SI.b,_1SF.i,_1SF.j,_1SF.k,_1SF.l,_1SF.m,_1SF.n,_1SF.o,_1SF.p,_1SF.q,_1SJ.a,_1SJ.b,_1SF.s,_1SK.a,_1SK.b,_1SK.c,_1SK.d,_1SK.e,_1SK.f,_1SK.g,_1SK.h,_1SF.u,_)),_=wMV(_1Sy,_1SL);return _gK;},_])),_1SM=B(A(_1QN,[_5X,_3D,_3C,_1Sp,_1PZ,function(_1SN,_){var _1SO=E(E(_1SN).a),_1SP=rMV(_1Sy),_1SQ=B(A(_1PD,[_1Su,_1Sw,_1Sz,_1SO.a,_1SO.b,_1SP,_])),_=wMV(_1Sy,_1SQ);return _gK;},_])),_1SR=B(A(_1QN,[_5X,_3D,_5c,_1Sp,_1Q2,function(_1SS,_){var _1ST=E(_1SS),_1SU=rMV(_1Sy),_1SV=E(_1SU);if(!E(E(_1SV.t).e)){var _=wMV(_1Sy,_1SV);return _gK;}else{var _1SW=B(_1Rg(_)),_=wMV(_1Sy,_1SV);return _gK;}},_])),_1SX=function(_){var _1SY=rMV(_1Sy),_=wMV(_1Sy,new T(function(){var _1SZ=E(_1SY),_1T0=E(_1SZ.t);return {_:0,a:E(_1SZ.a),b:E(_1SZ.b),c:E(_1SZ.c),d:E(_1SZ.d),e:E(_1SZ.e),f:E(_1SZ.f),g:E(_1SZ.g),h:E(_1SZ.h),i:_1SZ.i,j:_1SZ.j,k:_1SZ.k,l:_1SZ.l,m:E(_1SZ.m),n:_1SZ.n,o:E(_1SZ.o),p:E(_1SZ.p),q:_1SZ.q,r:E(_1SZ.r),s:_1SZ.s,t:E({_:0,a:E(_1T0.a),b:E(_1T0.b),c:E(_1T0.c),d:E(_1T0.d),e:E(_wA),f:E(_1T0.f),g:E(_1T0.g),h:E(_1T0.h)}),u:E(_1SZ.u)};}));return _gK;},_1T1=function(_1T2,_){var _1T3=E(_1T2),_1T4=rMV(_1Sy),_=wMV(_1Sy,new T(function(){var _1T5=E(_1T4),_1T6=E(_1T5.t);return {_:0,a:E(_1T5.a),b:E(_1T5.b),c:E(_1T5.c),d:E(_1T5.d),e:E(_1T5.e),f:E(_1T5.f),g:E(_1T5.g),h:E(_1T5.h),i:_1T5.i,j:_1T5.j,k:_1T5.k,l:_1T5.l,m:E(_1T5.m),n:_1T5.n,o:E(_1T5.o),p:E(_1T5.p),q:_1T5.q,r:E(_1T5.r),s:_1T5.s,t:E({_:0,a:E(_1T6.a),b:E(_1T6.b),c:E(_1T6.c),d:E(_1T6.d),e:E(_wB),f:E(_1T6.f),g:E(_1T6.g),h:E(_1T6.h)}),u:E(_1T5.u)};})),_1T7=B(A(_1RX,[_5X,_1Qo,_1SX,_]));return _gK;},_1T8=B(A(_1QN,[_5X,_3D,_5c,_1Sp,_1Q1,_1T1,_])),_1T9=B(A(_1RX,[_5X,_1Qv,function(_){var _1Ta=rMV(_1Sy),_1Tb=E(E(_1Sw).a),_1Tc=E(_1Ta),_1Td=E(_1Tc.t),_1Te=B(_1O7(_1Su,_1Tb.a,_1Tb.b,_1Sz,_1Tc.a,_1Tc.b,_1Tc.c,_1Tc.d,_1Tc.e,_1Tc.f,_1Tc.g,_1Tc.h,_1Tc.i,_1Tc.j,_1Tc.k,_1Tc.l,_1Tc.m,_1Tc.n,_1Tc.o,_1Tc.p,_1Tc.q,_1Tc.r,_1Tc.s,_1Td.a,_1Td.b,_1Td.c,_1Td.d,_1Td.e,_1Td.f,_1Td.g,_1Td.h,_1Tc.u,_)),_=wMV(_1Sy,_1Te);return _gK;},_]));return _gK;}}else{return new F(function(){return die(_1Qr);});}}else{return new F(function(){return die(_1Qr);});}},_1Tf=function(_){return new F(function(){return _1Sl(_);});};
var hasteMain = function() {B(A(_1Tf, [0]));};window.onload = hasteMain;