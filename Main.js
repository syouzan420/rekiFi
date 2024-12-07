"use strict";
var __haste_prog_id = '0abb50a259359112efbb15911b0c5ddf0958a9ec29cc5f6d91053a2924a2102a';
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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n="deltaZ",_o="deltaY",_p="deltaX",_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v,_w){var _x=jsShowI(_v);return new F(function(){return _q(fromJSStr(_x),_w);});},_y=41,_z=40,_A=function(_B,_C,_D){if(_C>=0){return new F(function(){return _u(_C,_D);});}else{if(_B<=6){return new F(function(){return _u(_C,_D);});}else{return new T2(1,_z,new T(function(){var _E=jsShowI(_C);return B(_q(fromJSStr(_E),new T2(1,_y,_D)));}));}}},_F=new T(function(){return B(unCStr(")"));}),_G=new T(function(){return B(_A(0,2,_F));}),_H=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_G));}),_I=function(_J){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_A(0,_J,_H));}))));});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L)),_N=jsTrunc(_M);if(_N<0){return B(_I(_N));}else{if(_N>2){return B(_I(_N));}else{return _N;}}});},_O=0,_P=new T3(0,_O,_O,_O),_Q="button",_R=new T(function(){return eval("jsGetMouseCoords");}),_S=__Z,_T=function(_U,_){var _V=E(_U);if(!_V._){return _S;}else{var _W=B(_T(_V.b,_));return new T2(1,new T(function(){var _X=Number(E(_V.a));return jsTrunc(_X);}),_W);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _T(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return new T(function(){var _15=Number(E(_14));return jsTrunc(_15);});},_16=new T2(0,_13,_11),_17=function(_18,_){var _19=E(_18);if(!_19._){return _S;}else{var _1a=B(_17(_19.b,_));return new T2(1,_19.a,_1a);}},_1b=new T(function(){return B(unCStr("base"));}),_1c=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1d=new T(function(){return B(unCStr("IOException"));}),_1e=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1b,_1c,_1d),_1f=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1e,_S,_S),_1g=function(_1h){return E(_1f);},_1i=function(_1j){return E(E(_1j).a);},_1k=function(_1l,_1m,_1n){var _1o=B(A1(_1l,_)),_1p=B(A1(_1m,_)),_1q=hs_eqWord64(_1o.a,_1p.a);if(!_1q){return __Z;}else{var _1r=hs_eqWord64(_1o.b,_1p.b);return (!_1r)?__Z:new T1(1,_1n);}},_1s=function(_1t){var _1u=E(_1t);return new F(function(){return _1k(B(_1i(_1u.a)),_1g,_1u.b);});},_1v=new T(function(){return B(unCStr(": "));}),_1w=new T(function(){return B(unCStr(")"));}),_1x=new T(function(){return B(unCStr(" ("));}),_1y=new T(function(){return B(unCStr("interrupted"));}),_1z=new T(function(){return B(unCStr("system error"));}),_1A=new T(function(){return B(unCStr("unsatisified constraints"));}),_1B=new T(function(){return B(unCStr("user error"));}),_1C=new T(function(){return B(unCStr("permission denied"));}),_1D=new T(function(){return B(unCStr("illegal operation"));}),_1E=new T(function(){return B(unCStr("end of file"));}),_1F=new T(function(){return B(unCStr("resource exhausted"));}),_1G=new T(function(){return B(unCStr("resource busy"));}),_1H=new T(function(){return B(unCStr("does not exist"));}),_1I=new T(function(){return B(unCStr("already exists"));}),_1J=new T(function(){return B(unCStr("resource vanished"));}),_1K=new T(function(){return B(unCStr("timeout"));}),_1L=new T(function(){return B(unCStr("unsupported operation"));}),_1M=new T(function(){return B(unCStr("hardware fault"));}),_1N=new T(function(){return B(unCStr("inappropriate type"));}),_1O=new T(function(){return B(unCStr("invalid argument"));}),_1P=new T(function(){return B(unCStr("failed"));}),_1Q=new T(function(){return B(unCStr("protocol error"));}),_1R=function(_1S,_1T){switch(E(_1S)){case 0:return new F(function(){return _q(_1I,_1T);});break;case 1:return new F(function(){return _q(_1H,_1T);});break;case 2:return new F(function(){return _q(_1G,_1T);});break;case 3:return new F(function(){return _q(_1F,_1T);});break;case 4:return new F(function(){return _q(_1E,_1T);});break;case 5:return new F(function(){return _q(_1D,_1T);});break;case 6:return new F(function(){return _q(_1C,_1T);});break;case 7:return new F(function(){return _q(_1B,_1T);});break;case 8:return new F(function(){return _q(_1A,_1T);});break;case 9:return new F(function(){return _q(_1z,_1T);});break;case 10:return new F(function(){return _q(_1Q,_1T);});break;case 11:return new F(function(){return _q(_1P,_1T);});break;case 12:return new F(function(){return _q(_1O,_1T);});break;case 13:return new F(function(){return _q(_1N,_1T);});break;case 14:return new F(function(){return _q(_1M,_1T);});break;case 15:return new F(function(){return _q(_1L,_1T);});break;case 16:return new F(function(){return _q(_1K,_1T);});break;case 17:return new F(function(){return _q(_1J,_1T);});break;default:return new F(function(){return _q(_1y,_1T);});}},_1U=new T(function(){return B(unCStr("}"));}),_1V=new T(function(){return B(unCStr("{handle: "));}),_1W=function(_1X,_1Y,_1Z,_20,_21,_22){var _23=new T(function(){var _24=new T(function(){var _25=new T(function(){var _26=E(_20);if(!_26._){return E(_22);}else{var _27=new T(function(){return B(_q(_26,new T(function(){return B(_q(_1w,_22));},1)));},1);return B(_q(_1x,_27));}},1);return B(_1R(_1Y,_25));}),_28=E(_1Z);if(!_28._){return E(_24);}else{return B(_q(_28,new T(function(){return B(_q(_1v,_24));},1)));}}),_29=E(_21);if(!_29._){var _2a=E(_1X);if(!_2a._){return E(_23);}else{var _2b=E(_2a.a);if(!_2b._){var _2c=new T(function(){var _2d=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2d));},1);return new F(function(){return _q(_1V,_2c);});}else{var _2e=new T(function(){var _2f=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2f));},1);return new F(function(){return _q(_1V,_2e);});}}}else{return new F(function(){return _q(_29.a,new T(function(){return B(_q(_1v,_23));},1));});}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _1W(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_S);});},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1W(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1W(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2g,_2G),_2K=new T(function(){return new T5(0,_1g,_2J,_2L,_1s,_2g);}),_2L=function(_2M){return new T2(0,_2K,_2M);},_2N=__Z,_2O=7,_2P=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2Q=new T6(0,_2N,_2O,_S,_2P,_2N,_2N),_2R=new T(function(){return B(_2L(_2Q));}),_2S=function(_){return new F(function(){return die(_2R);});},_2T=function(_2U){return E(E(_2U).a);},_2V=function(_2W,_2X,_2Y,_){var _2Z=__arr2lst(0,_2Y),_30=B(_17(_2Z,_)),_31=E(_30);if(!_31._){return new F(function(){return _2S(_);});}else{var _32=E(_31.b);if(!_32._){return new F(function(){return _2S(_);});}else{if(!E(_32.b)._){var _33=B(A3(_2T,_2W,_31.a,_)),_34=B(A3(_2T,_2X,_32.a,_));return new T2(0,_33,_34);}else{return new F(function(){return _2S(_);});}}}},_35=function(_){return new F(function(){return __jsNull();});},_36=function(_37){var _38=B(A1(_37,_));return E(_38);},_39=new T(function(){return B(_36(_35));}),_3a=new T(function(){return E(_39);}),_3b=function(_3c,_3d,_){if(E(_3c)==7){var _3e=__app1(E(_R),_3d),_3f=B(_2V(_16,_16,_3e,_)),_3g=__get(_3d,E(_p)),_3h=__get(_3d,E(_o)),_3i=__get(_3d,E(_n));return new T(function(){return new T3(0,E(_3f),E(_2N),E(new T3(0,_3g,_3h,_3i)));});}else{var _3j=__app1(E(_R),_3d),_3k=B(_2V(_16,_16,_3j,_)),_3l=__get(_3d,E(_Q)),_3m=__eq(_3l,E(_3a));if(!E(_3m)){var _3n=__isUndef(_3l);if(!E(_3n)){var _3o=B(_K(_3l,_));return new T(function(){return new T3(0,E(_3k),E(new T1(1,_3o)),E(_P));});}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}},_3p=function(_3q,_3r,_){return new F(function(){return _3b(_3q,E(_3r),_);});},_3s="mouseout",_3t="mouseover",_3u="mousemove",_3v="mouseup",_3w="mousedown",_3x="dblclick",_3y="click",_3z="wheel",_3A=function(_3B){switch(E(_3B)){case 0:return E(_3y);case 1:return E(_3x);case 2:return E(_3w);case 3:return E(_3v);case 4:return E(_3u);case 5:return E(_3t);case 6:return E(_3s);default:return E(_3z);}},_3C=new T2(0,_3A,_3p),_3D=function(_3E){return E(_3E);},_3F=function(_3G,_3H){return E(_3G)==E(_3H);},_3I=function(_3J,_3K){return E(_3J)!=E(_3K);},_3L=new T2(0,_3F,_3I),_3M="screenY",_3N="screenX",_3O="clientY",_3P="clientX",_3Q="pageY",_3R="pageX",_3S="target",_3T="identifier",_3U=function(_3V,_){var _3W=__get(_3V,E(_3T)),_3X=__get(_3V,E(_3S)),_3Y=__get(_3V,E(_3R)),_3Z=__get(_3V,E(_3Q)),_40=__get(_3V,E(_3P)),_41=__get(_3V,E(_3O)),_42=__get(_3V,E(_3N)),_43=__get(_3V,E(_3M));return new T(function(){var _44=Number(_3W),_45=jsTrunc(_44);return new T5(0,_45,_3X,E(new T2(0,new T(function(){var _46=Number(_3Y);return jsTrunc(_46);}),new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}))),E(new T2(0,new T(function(){var _48=Number(_40);return jsTrunc(_48);}),new T(function(){var _49=Number(_41);return jsTrunc(_49);}))),E(new T2(0,new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}),new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}))));});},_4c=function(_4d,_){var _4e=E(_4d);if(!_4e._){return _S;}else{var _4f=B(_3U(E(_4e.a),_)),_4g=B(_4c(_4e.b,_));return new T2(1,_4f,_4g);}},_4h="touches",_4i=function(_4j){return E(E(_4j).b);},_4k=function(_4l,_4m,_){var _4n=__arr2lst(0,_4m),_4o=new T(function(){return B(_4i(_4l));}),_4p=function(_4q,_){var _4r=E(_4q);if(!_4r._){return _S;}else{var _4s=B(A2(_4o,_4r.a,_)),_4t=B(_4p(_4r.b,_));return new T2(1,_4s,_4t);}};return new F(function(){return _4p(_4n,_);});},_4u=function(_4v,_){return new F(function(){return _4k(_16,E(_4v),_);});},_4w=new T2(0,_11,_4u),_4x=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4y=function(_4z){return E(E(_4z).a);},_4A=function(_4B,_4C,_4D){while(1){var _4E=E(_4D);if(!_4E._){return false;}else{if(!B(A3(_4y,_4B,_4C,_4E.a))){_4D=_4E.b;continue;}else{return true;}}}},_4F=function(_4G,_4H){while(1){var _4I=B((function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return __Z;}else{var _4M=_4L.a,_4N=_4L.b;if(!B(A1(_4J,_4M))){var _4O=_4J;_4G=_4O;_4H=_4N;return __continue;}else{return new T2(1,_4M,new T(function(){return B(_4F(_4J,_4N));}));}}})(_4G,_4H));if(_4I!=__continue){return _4I;}}},_4P=function(_4Q,_){var _4R=__get(_4Q,E(_4h)),_4S=__arr2lst(0,_4R),_4T=B(_4c(_4S,_)),_4U=__app1(E(_4x),_4Q),_4V=B(_2V(_4w,_4w,_4U,_)),_4W=E(_4V),_4X=new T(function(){var _4Y=function(_4Z){return new F(function(){return _4A(_3L,new T(function(){return E(_4Z).a;}),_4W.a);});};return B(_4F(_4Y,_4T));}),_50=new T(function(){var _51=function(_52){return new F(function(){return _4A(_3L,new T(function(){return E(_52).a;}),_4W.b);});};return B(_4F(_51,_4T));});return new T3(0,_4T,_50,_4X);},_53=function(_54,_55,_){return new F(function(){return _4P(E(_55),_);});},_56="touchcancel",_57="touchend",_58="touchmove",_59="touchstart",_5a=function(_5b){switch(E(_5b)){case 0:return E(_59);case 1:return E(_58);case 2:return E(_57);default:return E(_56);}},_5c=new T2(0,_5a,_53),_5d=function(_5e,_5f,_){var _5g=B(A1(_5e,_)),_5h=B(A1(_5f,_));return _5g;},_5i=function(_5j,_5k,_){var _5l=B(A1(_5j,_)),_5m=B(A1(_5k,_));return new T(function(){return B(A1(_5l,_5m));});},_5n=function(_5o,_5p,_){var _5q=B(A1(_5p,_));return _5o;},_5r=function(_5s,_5t,_){var _5u=B(A1(_5t,_));return new T(function(){return B(A1(_5s,_5u));});},_5v=new T2(0,_5r,_5n),_5w=function(_5x,_){return _5x;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5z,_));return new F(function(){return A1(_5A,_);});},_5C=new T5(0,_5v,_5w,_5i,_5y,_5d),_5D=new T(function(){return E(_2K);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H){return new T6(0,_2N,_2O,_S,_5H,_2N,_2N);},_5I=function(_5J,_){var _5K=new T(function(){return B(A2(_5E,_5D,new T(function(){return B(A1(_5G,_5J));})));});return new F(function(){return die(_5K);});},_5L=function(_5M,_){return new F(function(){return _5I(_5M,_);});},_5N=function(_5O){return new F(function(){return A1(_5L,_5O);});},_5P=function(_5Q,_5R,_){var _5S=B(A1(_5Q,_));return new F(function(){return A2(_5R,_5S,_);});},_5T=new T5(0,_5C,_5P,_5y,_5w,_5N),_5U=function(_5V){return E(_5V);},_5W=new T2(0,_5T,_5U),_5X=new T2(0,_5W,_5w),_5Y=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_60=new T(function(){return eval("(function(cv){return cv.height})");}),_61=new T(function(){return eval("(function(cv){return cv.width})");}),_62=function(_63,_){var _64=__app1(E(_61),_63),_65=__app1(E(_60),_63),_66=__app1(E(_5Z),_63),_67=__app1(E(_5Y),_63);return new T2(0,new T2(0,_64,_65),new T2(0,_66,_67));},_68=function(_69,_6a){while(1){var _6b=E(_69);if(!_6b._){return (E(_6a)._==0)?true:false;}else{var _6c=E(_6a);if(!_6c._){return false;}else{if(E(_6b.a)!=E(_6c.a)){return false;}else{_69=_6b.b;_6a=_6c.b;continue;}}}}},_6d=function(_6e,_6f){var _6g=E(_6f);return (_6g._==0)?__Z:new T2(1,new T(function(){return B(A1(_6e,_6g.a));}),new T(function(){return B(_6d(_6e,_6g.b));}));},_6h=function(_6i){return new T1(3,E(B(_6d(_5U,_6i))));},_6j="Tried to deserialie a non-array to a list!",_6k=new T1(0,_6j),_6l=new T1(1,_S),_6m=function(_6n){var _6o=E(_6n);if(!_6o._){return E(_6l);}else{var _6p=B(_6m(_6o.b));return (_6p._==0)?new T1(0,_6p.a):new T1(1,new T2(1,_6o.a,_6p.a));}},_6q=function(_6r){var _6s=E(_6r);if(_6s._==3){return new F(function(){return _6m(_6s.a);});}else{return E(_6k);}},_6t=function(_6u){return new T1(1,_6u);},_6v=new T4(0,_5U,_6h,_6t,_6q),_6w=function(_6x,_6y,_6z){return new F(function(){return A1(_6x,new T2(1,_2s,new T(function(){return B(A1(_6y,_6z));})));});},_6A=function(_6B){return new F(function(){return _A(0,E(_6B),_S);});},_6C=34,_6D=new T2(1,_6C,_S),_6E=new T(function(){return B(unCStr("!!: negative index"));}),_6F=new T(function(){return B(unCStr("Prelude."));}),_6G=new T(function(){return B(_q(_6F,_6E));}),_6H=new T(function(){return B(err(_6G));}),_6I=new T(function(){return B(unCStr("!!: index too large"));}),_6J=new T(function(){return B(_q(_6F,_6I));}),_6K=new T(function(){return B(err(_6J));}),_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O._){return E(_6K);}else{var _6P=E(_6N);if(!_6P){return E(_6O.a);}else{_6M=_6O.b;_6N=_6P-1|0;continue;}}}},_6Q=function(_6R,_6S){if(_6S>=0){return new F(function(){return _6L(_6R,_6S);});}else{return E(_6H);}},_6T=new T(function(){return B(unCStr("ACK"));}),_6U=new T(function(){return B(unCStr("BEL"));}),_6V=new T(function(){return B(unCStr("BS"));}),_6W=new T(function(){return B(unCStr("SP"));}),_6X=new T2(1,_6W,_S),_6Y=new T(function(){return B(unCStr("US"));}),_6Z=new T2(1,_6Y,_6X),_70=new T(function(){return B(unCStr("RS"));}),_71=new T2(1,_70,_6Z),_72=new T(function(){return B(unCStr("GS"));}),_73=new T2(1,_72,_71),_74=new T(function(){return B(unCStr("FS"));}),_75=new T2(1,_74,_73),_76=new T(function(){return B(unCStr("ESC"));}),_77=new T2(1,_76,_75),_78=new T(function(){return B(unCStr("SUB"));}),_79=new T2(1,_78,_77),_7a=new T(function(){return B(unCStr("EM"));}),_7b=new T2(1,_7a,_79),_7c=new T(function(){return B(unCStr("CAN"));}),_7d=new T2(1,_7c,_7b),_7e=new T(function(){return B(unCStr("ETB"));}),_7f=new T2(1,_7e,_7d),_7g=new T(function(){return B(unCStr("SYN"));}),_7h=new T2(1,_7g,_7f),_7i=new T(function(){return B(unCStr("NAK"));}),_7j=new T2(1,_7i,_7h),_7k=new T(function(){return B(unCStr("DC4"));}),_7l=new T2(1,_7k,_7j),_7m=new T(function(){return B(unCStr("DC3"));}),_7n=new T2(1,_7m,_7l),_7o=new T(function(){return B(unCStr("DC2"));}),_7p=new T2(1,_7o,_7n),_7q=new T(function(){return B(unCStr("DC1"));}),_7r=new T2(1,_7q,_7p),_7s=new T(function(){return B(unCStr("DLE"));}),_7t=new T2(1,_7s,_7r),_7u=new T(function(){return B(unCStr("SI"));}),_7v=new T2(1,_7u,_7t),_7w=new T(function(){return B(unCStr("SO"));}),_7x=new T2(1,_7w,_7v),_7y=new T(function(){return B(unCStr("CR"));}),_7z=new T2(1,_7y,_7x),_7A=new T(function(){return B(unCStr("FF"));}),_7B=new T2(1,_7A,_7z),_7C=new T(function(){return B(unCStr("VT"));}),_7D=new T2(1,_7C,_7B),_7E=new T(function(){return B(unCStr("LF"));}),_7F=new T2(1,_7E,_7D),_7G=new T(function(){return B(unCStr("HT"));}),_7H=new T2(1,_7G,_7F),_7I=new T2(1,_6V,_7H),_7J=new T2(1,_6U,_7I),_7K=new T2(1,_6T,_7J),_7L=new T(function(){return B(unCStr("ENQ"));}),_7M=new T2(1,_7L,_7K),_7N=new T(function(){return B(unCStr("EOT"));}),_7O=new T2(1,_7N,_7M),_7P=new T(function(){return B(unCStr("ETX"));}),_7Q=new T2(1,_7P,_7O),_7R=new T(function(){return B(unCStr("STX"));}),_7S=new T2(1,_7R,_7Q),_7T=new T(function(){return B(unCStr("SOH"));}),_7U=new T2(1,_7T,_7S),_7V=new T(function(){return B(unCStr("NUL"));}),_7W=new T2(1,_7V,_7U),_7X=92,_7Y=new T(function(){return B(unCStr("\\DEL"));}),_7Z=new T(function(){return B(unCStr("\\a"));}),_80=new T(function(){return B(unCStr("\\\\"));}),_81=new T(function(){return B(unCStr("\\SO"));}),_82=new T(function(){return B(unCStr("\\r"));}),_83=new T(function(){return B(unCStr("\\f"));}),_84=new T(function(){return B(unCStr("\\v"));}),_85=new T(function(){return B(unCStr("\\n"));}),_86=new T(function(){return B(unCStr("\\t"));}),_87=new T(function(){return B(unCStr("\\b"));}),_88=function(_89,_8a){if(_89<=127){var _8b=E(_89);switch(_8b){case 92:return new F(function(){return _q(_80,_8a);});break;case 127:return new F(function(){return _q(_7Y,_8a);});break;default:if(_8b<32){var _8c=E(_8b);switch(_8c){case 7:return new F(function(){return _q(_7Z,_8a);});break;case 8:return new F(function(){return _q(_87,_8a);});break;case 9:return new F(function(){return _q(_86,_8a);});break;case 10:return new F(function(){return _q(_85,_8a);});break;case 11:return new F(function(){return _q(_84,_8a);});break;case 12:return new F(function(){return _q(_83,_8a);});break;case 13:return new F(function(){return _q(_82,_8a);});break;case 14:return new F(function(){return _q(_81,new T(function(){var _8d=E(_8a);if(!_8d._){return __Z;}else{if(E(_8d.a)==72){return B(unAppCStr("\\&",_8d));}else{return E(_8d);}}},1));});break;default:return new F(function(){return _q(new T2(1,_7X,new T(function(){return B(_6Q(_7W,_8c));})),_8a);});}}else{return new T2(1,_8b,_8a);}}}else{var _8e=new T(function(){var _8f=jsShowI(_89);return B(_q(fromJSStr(_8f),new T(function(){var _8g=E(_8a);if(!_8g._){return __Z;}else{var _8h=E(_8g.a);if(_8h<48){return E(_8g);}else{if(_8h>57){return E(_8g);}else{return B(unAppCStr("\\&",_8g));}}}},1)));});return new T2(1,_7X,_8e);}},_8i=new T(function(){return B(unCStr("\\\""));}),_8j=function(_8k,_8l){var _8m=E(_8k);if(!_8m._){return E(_8l);}else{var _8n=_8m.b,_8o=E(_8m.a);if(_8o==34){return new F(function(){return _q(_8i,new T(function(){return B(_8j(_8n,_8l));},1));});}else{return new F(function(){return _88(_8o,new T(function(){return B(_8j(_8n,_8l));}));});}}},_8p=function(_8q){return new T2(1,_6C,new T(function(){return B(_8j(_8q,_6D));}));},_8r=function(_8s,_8t){if(_8s<=_8t){var _8u=function(_8v){return new T2(1,_8v,new T(function(){if(_8v!=_8t){return B(_8u(_8v+1|0));}else{return __Z;}}));};return new F(function(){return _8u(_8s);});}else{return __Z;}},_8w=function(_8x){return new F(function(){return _8r(E(_8x),2147483647);});},_8y=function(_8z,_8A,_8B){if(_8B<=_8A){var _8C=new T(function(){var _8D=_8A-_8z|0,_8E=function(_8F){return (_8F>=(_8B-_8D|0))?new T2(1,_8F,new T(function(){return B(_8E(_8F+_8D|0));})):new T2(1,_8F,_S);};return B(_8E(_8A));});return new T2(1,_8z,_8C);}else{return (_8B<=_8z)?new T2(1,_8z,_S):__Z;}},_8G=function(_8H,_8I,_8J){if(_8J>=_8I){var _8K=new T(function(){var _8L=_8I-_8H|0,_8M=function(_8N){return (_8N<=(_8J-_8L|0))?new T2(1,_8N,new T(function(){return B(_8M(_8N+_8L|0));})):new T2(1,_8N,_S);};return B(_8M(_8I));});return new T2(1,_8H,_8K);}else{return (_8J>=_8H)?new T2(1,_8H,_S):__Z;}},_8O=function(_8P,_8Q){if(_8Q<_8P){return new F(function(){return _8y(_8P,_8Q, -2147483648);});}else{return new F(function(){return _8G(_8P,_8Q,2147483647);});}},_8R=function(_8S,_8T){return new F(function(){return _8O(E(_8S),E(_8T));});},_8U=function(_8V,_8W,_8X){if(_8W<_8V){return new F(function(){return _8y(_8V,_8W,_8X);});}else{return new F(function(){return _8G(_8V,_8W,_8X);});}},_8Y=function(_8Z,_90,_91){return new F(function(){return _8U(E(_8Z),E(_90),E(_91));});},_92=function(_93,_94){return new F(function(){return _8r(E(_93),E(_94));});},_95=function(_96){return E(_96);},_97=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_98=new T(function(){return B(err(_97));}),_99=function(_9a){var _9b=E(_9a);return (_9b==( -2147483648))?E(_98):_9b-1|0;},_9c=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f){var _9g=E(_9f);return (_9g==2147483647)?E(_9d):_9g+1|0;},_9h={_:0,a:_9e,b:_99,c:_95,d:_95,e:_8w,f:_8R,g:_92,h:_8Y},_9i=function(_9j,_9k){if(_9j<=0){if(_9j>=0){return new F(function(){return quot(_9j,_9k);});}else{if(_9k<=0){return new F(function(){return quot(_9j,_9k);});}else{return quot(_9j+1|0,_9k)-1|0;}}}else{if(_9k>=0){if(_9j>=0){return new F(function(){return quot(_9j,_9k);});}else{if(_9k<=0){return new F(function(){return quot(_9j,_9k);});}else{return quot(_9j+1|0,_9k)-1|0;}}}else{return quot(_9j-1|0,_9k)-1|0;}}},_9l=new T(function(){return B(unCStr("base"));}),_9m=new T(function(){return B(unCStr("GHC.Exception"));}),_9n=new T(function(){return B(unCStr("ArithException"));}),_9o=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9l,_9m,_9n),_9p=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9o,_S,_S),_9q=function(_9r){return E(_9p);},_9s=function(_9t){var _9u=E(_9t);return new F(function(){return _1k(B(_1i(_9u.a)),_9q,_9u.b);});},_9v=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9w=new T(function(){return B(unCStr("denormal"));}),_9x=new T(function(){return B(unCStr("divide by zero"));}),_9y=new T(function(){return B(unCStr("loss of precision"));}),_9z=new T(function(){return B(unCStr("arithmetic underflow"));}),_9A=new T(function(){return B(unCStr("arithmetic overflow"));}),_9B=function(_9C,_9D){switch(E(_9C)){case 0:return new F(function(){return _q(_9A,_9D);});break;case 1:return new F(function(){return _q(_9z,_9D);});break;case 2:return new F(function(){return _q(_9y,_9D);});break;case 3:return new F(function(){return _q(_9x,_9D);});break;case 4:return new F(function(){return _q(_9w,_9D);});break;default:return new F(function(){return _q(_9v,_9D);});}},_9E=function(_9F){return new F(function(){return _9B(_9F,_S);});},_9G=function(_9H,_9I,_9J){return new F(function(){return _9B(_9I,_9J);});},_9K=function(_9L,_9M){return new F(function(){return _2v(_9B,_9L,_9M);});},_9N=new T3(0,_9G,_9E,_9K),_9O=new T(function(){return new T5(0,_9q,_9N,_9P,_9s,_9E);}),_9P=function(_9Q){return new T2(0,_9O,_9Q);},_9R=3,_9S=new T(function(){return B(_9P(_9R));}),_9T=new T(function(){return die(_9S);}),_9U=0,_9V=new T(function(){return B(_9P(_9U));}),_9W=new T(function(){return die(_9V);}),_9X=function(_9Y,_9Z){var _a0=E(_9Z);switch(_a0){case  -1:var _a1=E(_9Y);if(_a1==( -2147483648)){return E(_9W);}else{return new F(function(){return _9i(_a1, -1);});}break;case 0:return E(_9T);default:return new F(function(){return _9i(_9Y,_a0);});}},_a2=function(_a3,_a4){return new F(function(){return _9X(E(_a3),E(_a4));});},_a5=0,_a6=new T2(0,_9W,_a5),_a7=function(_a8,_a9){var _aa=E(_a8),_ab=E(_a9);switch(_ab){case  -1:var _ac=E(_aa);if(_ac==( -2147483648)){return E(_a6);}else{if(_ac<=0){if(_ac>=0){var _ad=quotRemI(_ac, -1);return new T2(0,_ad.a,_ad.b);}else{var _ae=quotRemI(_ac, -1);return new T2(0,_ae.a,_ae.b);}}else{var _af=quotRemI(_ac-1|0, -1);return new T2(0,_af.a-1|0,(_af.b+( -1)|0)+1|0);}}break;case 0:return E(_9T);default:if(_aa<=0){if(_aa>=0){var _ag=quotRemI(_aa,_ab);return new T2(0,_ag.a,_ag.b);}else{if(_ab<=0){var _ah=quotRemI(_aa,_ab);return new T2(0,_ah.a,_ah.b);}else{var _ai=quotRemI(_aa+1|0,_ab);return new T2(0,_ai.a-1|0,(_ai.b+_ab|0)-1|0);}}}else{if(_ab>=0){if(_aa>=0){var _aj=quotRemI(_aa,_ab);return new T2(0,_aj.a,_aj.b);}else{if(_ab<=0){var _ak=quotRemI(_aa,_ab);return new T2(0,_ak.a,_ak.b);}else{var _al=quotRemI(_aa+1|0,_ab);return new T2(0,_al.a-1|0,(_al.b+_ab|0)-1|0);}}}else{var _am=quotRemI(_aa-1|0,_ab);return new T2(0,_am.a-1|0,(_am.b+_ab|0)+1|0);}}}},_an=function(_ao,_ap){var _aq=_ao%_ap;if(_ao<=0){if(_ao>=0){return E(_aq);}else{if(_ap<=0){return E(_aq);}else{var _ar=E(_aq);return (_ar==0)?0:_ar+_ap|0;}}}else{if(_ap>=0){if(_ao>=0){return E(_aq);}else{if(_ap<=0){return E(_aq);}else{var _as=E(_aq);return (_as==0)?0:_as+_ap|0;}}}else{var _at=E(_aq);return (_at==0)?0:_at+_ap|0;}}},_au=function(_av,_aw){var _ax=E(_aw);switch(_ax){case  -1:return E(_a5);case 0:return E(_9T);default:return new F(function(){return _an(E(_av),_ax);});}},_ay=function(_az,_aA){var _aB=E(_az),_aC=E(_aA);switch(_aC){case  -1:var _aD=E(_aB);if(_aD==( -2147483648)){return E(_9W);}else{return new F(function(){return quot(_aD, -1);});}break;case 0:return E(_9T);default:return new F(function(){return quot(_aB,_aC);});}},_aE=function(_aF,_aG){var _aH=E(_aF),_aI=E(_aG);switch(_aI){case  -1:var _aJ=E(_aH);if(_aJ==( -2147483648)){return E(_a6);}else{var _aK=quotRemI(_aJ, -1);return new T2(0,_aK.a,_aK.b);}break;case 0:return E(_9T);default:var _aL=quotRemI(_aH,_aI);return new T2(0,_aL.a,_aL.b);}},_aM=function(_aN,_aO){var _aP=E(_aO);switch(_aP){case  -1:return E(_a5);case 0:return E(_9T);default:return E(_aN)%_aP;}},_aQ=function(_aR){return new T1(0,_aR);},_aS=function(_aT){return new F(function(){return _aQ(E(_aT));});},_aU=new T1(0,1),_aV=function(_aW){return new T2(0,E(B(_aQ(E(_aW)))),E(_aU));},_aX=function(_aY,_aZ){return imul(E(_aY),E(_aZ))|0;},_b0=function(_b1,_b2){return E(_b1)+E(_b2)|0;},_b3=function(_b4,_b5){return E(_b4)-E(_b5)|0;},_b6=function(_b7){var _b8=E(_b7);return (_b8<0)? -_b8:E(_b8);},_b9=function(_ba){var _bb=E(_ba);if(!_bb._){return E(_bb.a);}else{return new F(function(){return I_toInt(_bb.a);});}},_bc=function(_bd){return new F(function(){return _b9(_bd);});},_be=function(_bf){return  -E(_bf);},_bg= -1,_bh=0,_bi=1,_bj=function(_bk){var _bl=E(_bk);return (_bl>=0)?(E(_bl)==0)?E(_bh):E(_bi):E(_bg);},_bm={_:0,a:_b0,b:_b3,c:_aX,d:_be,e:_b6,f:_bj,g:_bc},_bn=function(_bo,_bp){var _bq=E(_bo),_br=E(_bp);return (_bq>_br)?E(_bq):E(_br);},_bs=function(_bt,_bu){var _bv=E(_bt),_bw=E(_bu);return (_bv>_bw)?E(_bw):E(_bv);},_bx=function(_by,_bz){return (_by>=_bz)?(_by!=_bz)?2:1:0;},_bA=function(_bB,_bC){return new F(function(){return _bx(E(_bB),E(_bC));});},_bD=function(_bE,_bF){return E(_bE)>=E(_bF);},_bG=function(_bH,_bI){return E(_bH)>E(_bI);},_bJ=function(_bK,_bL){return E(_bK)<=E(_bL);},_bM=function(_bN,_bO){return E(_bN)<E(_bO);},_bP={_:0,a:_3L,b:_bA,c:_bM,d:_bJ,e:_bG,f:_bD,g:_bn,h:_bs},_bQ=new T3(0,_bm,_bP,_aV),_bR={_:0,a:_bQ,b:_9h,c:_ay,d:_aM,e:_a2,f:_au,g:_aE,h:_a7,i:_aS},_bS=function(_bT){var _bU=E(_bT);return new F(function(){return Math.log(_bU+(_bU+1)*Math.sqrt((_bU-1)/(_bU+1)));});},_bV=function(_bW){var _bX=E(_bW);return new F(function(){return Math.log(_bX+Math.sqrt(1+_bX*_bX));});},_bY=function(_bZ){var _c0=E(_bZ);return 0.5*Math.log((1+_c0)/(1-_c0));},_c1=function(_c2,_c3){return Math.log(E(_c3))/Math.log(E(_c2));},_c4=3.141592653589793,_c5=new T1(0,1),_c6=function(_c7,_c8){var _c9=E(_c7);if(!_c9._){var _ca=_c9.a,_cb=E(_c8);if(!_cb._){var _cc=_cb.a;return (_ca!=_cc)?(_ca>_cc)?2:0:1;}else{var _cd=I_compareInt(_cb.a,_ca);return (_cd<=0)?(_cd>=0)?1:2:0;}}else{var _ce=_c9.a,_cf=E(_c8);if(!_cf._){var _cg=I_compareInt(_ce,_cf.a);return (_cg>=0)?(_cg<=0)?1:2:0;}else{var _ch=I_compare(_ce,_cf.a);return (_ch>=0)?(_ch<=0)?1:2:0;}}},_ci=function(_cj,_ck){var _cl=E(_cj);return (_cl._==0)?_cl.a*Math.pow(2,_ck):I_toNumber(_cl.a)*Math.pow(2,_ck);},_cm=function(_cn,_co){var _cp=E(_cn);if(!_cp._){var _cq=_cp.a,_cr=E(_co);return (_cr._==0)?_cq==_cr.a:(I_compareInt(_cr.a,_cq)==0)?true:false;}else{var _cs=_cp.a,_ct=E(_co);return (_ct._==0)?(I_compareInt(_cs,_ct.a)==0)?true:false:(I_compare(_cs,_ct.a)==0)?true:false;}},_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx._){var _cy=_cx.a,_cz=E(_cw);if(!_cz._){var _cA=_cz.a,_cB=addC(_cy,_cA);if(!E(_cB.b)){return new T1(0,_cB.a);}else{_cv=new T1(1,I_fromInt(_cy));_cw=new T1(1,I_fromInt(_cA));continue;}}else{_cv=new T1(1,I_fromInt(_cy));_cw=_cz;continue;}}else{var _cC=E(_cw);if(!_cC._){_cv=_cx;_cw=new T1(1,I_fromInt(_cC.a));continue;}else{return new T1(1,I_add(_cx.a,_cC.a));}}}},_cD=function(_cE,_cF){while(1){var _cG=E(_cE);if(!_cG._){var _cH=E(_cG.a);if(_cH==( -2147483648)){_cE=new T1(1,I_fromInt( -2147483648));continue;}else{var _cI=E(_cF);if(!_cI._){var _cJ=_cI.a;return new T2(0,new T1(0,quot(_cH,_cJ)),new T1(0,_cH%_cJ));}else{_cE=new T1(1,I_fromInt(_cH));_cF=_cI;continue;}}}else{var _cK=E(_cF);if(!_cK._){_cE=_cG;_cF=new T1(1,I_fromInt(_cK.a));continue;}else{var _cL=I_quotRem(_cG.a,_cK.a);return new T2(0,new T1(1,_cL.a),new T1(1,_cL.b));}}}},_cM=new T1(0,0),_cN=function(_cO,_cP){while(1){var _cQ=E(_cO);if(!_cQ._){_cO=new T1(1,I_fromInt(_cQ.a));continue;}else{return new T1(1,I_shiftLeft(_cQ.a,_cP));}}},_cR=function(_cS,_cT,_cU){if(!B(_cm(_cU,_cM))){var _cV=B(_cD(_cT,_cU)),_cW=_cV.a;switch(B(_c6(B(_cN(_cV.b,1)),_cU))){case 0:return new F(function(){return _ci(_cW,_cS);});break;case 1:if(!(B(_b9(_cW))&1)){return new F(function(){return _ci(_cW,_cS);});}else{return new F(function(){return _ci(B(_cu(_cW,_c5)),_cS);});}break;default:return new F(function(){return _ci(B(_cu(_cW,_c5)),_cS);});}}else{return E(_9T);}},_cX=function(_cY,_cZ){var _d0=E(_cY);if(!_d0._){var _d1=_d0.a,_d2=E(_cZ);return (_d2._==0)?_d1>_d2.a:I_compareInt(_d2.a,_d1)<0;}else{var _d3=_d0.a,_d4=E(_cZ);return (_d4._==0)?I_compareInt(_d3,_d4.a)>0:I_compare(_d3,_d4.a)>0;}},_d5=new T1(0,1),_d6=function(_d7,_d8){var _d9=E(_d7);if(!_d9._){var _da=_d9.a,_db=E(_d8);return (_db._==0)?_da<_db.a:I_compareInt(_db.a,_da)>0;}else{var _dc=_d9.a,_dd=E(_d8);return (_dd._==0)?I_compareInt(_dc,_dd.a)<0:I_compare(_dc,_dd.a)<0;}},_de=new T(function(){return B(unCStr("base"));}),_df=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dg=new T(function(){return B(unCStr("PatternMatchFail"));}),_dh=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_de,_df,_dg),_di=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dh,_S,_S),_dj=function(_dk){return E(_di);},_dl=function(_dm){var _dn=E(_dm);return new F(function(){return _1k(B(_1i(_dn.a)),_dj,_dn.b);});},_do=function(_dp){return E(E(_dp).a);},_dq=function(_dr){return new T2(0,_ds,_dr);},_dt=function(_du,_dv){return new F(function(){return _q(E(_du).a,_dv);});},_dw=function(_dx,_dy){return new F(function(){return _2v(_dt,_dx,_dy);});},_dz=function(_dA,_dB,_dC){return new F(function(){return _q(E(_dB).a,_dC);});},_dD=new T3(0,_dz,_do,_dw),_ds=new T(function(){return new T5(0,_dj,_dD,_dq,_dl,_do);}),_dE=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dF=function(_dG,_dH){return new F(function(){return die(new T(function(){return B(A2(_5E,_dH,_dG));}));});},_dI=function(_dJ,_9Q){return new F(function(){return _dF(_dJ,_9Q);});},_dK=function(_dL,_dM){var _dN=E(_dM);if(!_dN._){return new T2(0,_S,_S);}else{var _dO=_dN.a;if(!B(A1(_dL,_dO))){return new T2(0,_S,_dN);}else{var _dP=new T(function(){var _dQ=B(_dK(_dL,_dN.b));return new T2(0,_dQ.a,_dQ.b);});return new T2(0,new T2(1,_dO,new T(function(){return E(E(_dP).a);})),new T(function(){return E(E(_dP).b);}));}}},_dR=32,_dS=new T(function(){return B(unCStr("\n"));}),_dT=function(_dU){return (E(_dU)==124)?false:true;},_dV=function(_dW,_dX){var _dY=B(_dK(_dT,B(unCStr(_dW)))),_dZ=_dY.a,_e0=function(_e1,_e2){var _e3=new T(function(){var _e4=new T(function(){return B(_q(_dX,new T(function(){return B(_q(_e2,_dS));},1)));});return B(unAppCStr(": ",_e4));},1);return new F(function(){return _q(_e1,_e3);});},_e5=E(_dY.b);if(!_e5._){return new F(function(){return _e0(_dZ,_S);});}else{if(E(_e5.a)==124){return new F(function(){return _e0(_dZ,new T2(1,_dR,_e5.b));});}else{return new F(function(){return _e0(_dZ,_S);});}}},_e6=function(_e7){return new F(function(){return _dI(new T1(0,new T(function(){return B(_dV(_e7,_dE));})),_ds);});},_e8=function(_e9){var _ea=function(_eb,_ec){while(1){if(!B(_d6(_eb,_e9))){if(!B(_cX(_eb,_e9))){if(!B(_cm(_eb,_e9))){return new F(function(){return _e6("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ec);}}else{return _ec-1|0;}}else{var _ed=B(_cN(_eb,1)),_ee=_ec+1|0;_eb=_ed;_ec=_ee;continue;}}};return new F(function(){return _ea(_d5,0);});},_ef=function(_eg){var _eh=E(_eg);if(!_eh._){var _ei=_eh.a>>>0;if(!_ei){return  -1;}else{var _ej=function(_ek,_el){while(1){if(_ek>=_ei){if(_ek<=_ei){if(_ek!=_ei){return new F(function(){return _e6("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_el);}}else{return _el-1|0;}}else{var _em=imul(_ek,2)>>>0,_en=_el+1|0;_ek=_em;_el=_en;continue;}}};return new F(function(){return _ej(1,0);});}}else{return new F(function(){return _e8(_eh);});}},_eo=function(_ep){var _eq=E(_ep);if(!_eq._){var _er=_eq.a>>>0;if(!_er){return new T2(0, -1,0);}else{var _es=function(_et,_eu){while(1){if(_et>=_er){if(_et<=_er){if(_et!=_er){return new F(function(){return _e6("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_eu);}}else{return _eu-1|0;}}else{var _ev=imul(_et,2)>>>0,_ew=_eu+1|0;_et=_ev;_eu=_ew;continue;}}};return new T2(0,B(_es(1,0)),(_er&_er-1>>>0)>>>0&4294967295);}}else{var _ex=_eq.a;return new T2(0,B(_ef(_eq)),I_compareInt(I_and(_ex,I_sub(_ex,I_fromInt(1))),0));}},_ey=function(_ez,_eA){var _eB=E(_ez);if(!_eB._){var _eC=_eB.a,_eD=E(_eA);return (_eD._==0)?_eC<=_eD.a:I_compareInt(_eD.a,_eC)>=0;}else{var _eE=_eB.a,_eF=E(_eA);return (_eF._==0)?I_compareInt(_eE,_eF.a)<=0:I_compare(_eE,_eF.a)<=0;}},_eG=function(_eH,_eI){while(1){var _eJ=E(_eH);if(!_eJ._){var _eK=_eJ.a,_eL=E(_eI);if(!_eL._){return new T1(0,(_eK>>>0&_eL.a>>>0)>>>0&4294967295);}else{_eH=new T1(1,I_fromInt(_eK));_eI=_eL;continue;}}else{var _eM=E(_eI);if(!_eM._){_eH=_eJ;_eI=new T1(1,I_fromInt(_eM.a));continue;}else{return new T1(1,I_and(_eJ.a,_eM.a));}}}},_eN=function(_eO,_eP){while(1){var _eQ=E(_eO);if(!_eQ._){var _eR=_eQ.a,_eS=E(_eP);if(!_eS._){var _eT=_eS.a,_eU=subC(_eR,_eT);if(!E(_eU.b)){return new T1(0,_eU.a);}else{_eO=new T1(1,I_fromInt(_eR));_eP=new T1(1,I_fromInt(_eT));continue;}}else{_eO=new T1(1,I_fromInt(_eR));_eP=_eS;continue;}}else{var _eV=E(_eP);if(!_eV._){_eO=_eQ;_eP=new T1(1,I_fromInt(_eV.a));continue;}else{return new T1(1,I_sub(_eQ.a,_eV.a));}}}},_eW=new T1(0,2),_eX=function(_eY,_eZ){var _f0=E(_eY);if(!_f0._){var _f1=(_f0.a>>>0&(2<<_eZ>>>0)-1>>>0)>>>0,_f2=1<<_eZ>>>0;return (_f2<=_f1)?(_f2>=_f1)?1:2:0;}else{var _f3=B(_eG(_f0,B(_eN(B(_cN(_eW,_eZ)),_d5)))),_f4=B(_cN(_d5,_eZ));return (!B(_cX(_f4,_f3)))?(!B(_d6(_f4,_f3)))?1:2:0;}},_f5=function(_f6,_f7){while(1){var _f8=E(_f6);if(!_f8._){_f6=new T1(1,I_fromInt(_f8.a));continue;}else{return new T1(1,I_shiftRight(_f8.a,_f7));}}},_f9=function(_fa,_fb,_fc,_fd){var _fe=B(_eo(_fd)),_ff=_fe.a;if(!E(_fe.b)){var _fg=B(_ef(_fc));if(_fg<((_ff+_fa|0)-1|0)){var _fh=_ff+(_fa-_fb|0)|0;if(_fh>0){if(_fh>_fg){if(_fh<=(_fg+1|0)){if(!E(B(_eo(_fc)).b)){return 0;}else{return new F(function(){return _ci(_c5,_fa-_fb|0);});}}else{return 0;}}else{var _fi=B(_f5(_fc,_fh));switch(B(_eX(_fc,_fh-1|0))){case 0:return new F(function(){return _ci(_fi,_fa-_fb|0);});break;case 1:if(!(B(_b9(_fi))&1)){return new F(function(){return _ci(_fi,_fa-_fb|0);});}else{return new F(function(){return _ci(B(_cu(_fi,_c5)),_fa-_fb|0);});}break;default:return new F(function(){return _ci(B(_cu(_fi,_c5)),_fa-_fb|0);});}}}else{return new F(function(){return _ci(_fc,(_fa-_fb|0)-_fh|0);});}}else{if(_fg>=_fb){var _fj=B(_f5(_fc,(_fg+1|0)-_fb|0));switch(B(_eX(_fc,_fg-_fb|0))){case 0:return new F(function(){return _ci(_fj,((_fg-_ff|0)+1|0)-_fb|0);});break;case 2:return new F(function(){return _ci(B(_cu(_fj,_c5)),((_fg-_ff|0)+1|0)-_fb|0);});break;default:if(!(B(_b9(_fj))&1)){return new F(function(){return _ci(_fj,((_fg-_ff|0)+1|0)-_fb|0);});}else{return new F(function(){return _ci(B(_cu(_fj,_c5)),((_fg-_ff|0)+1|0)-_fb|0);});}}}else{return new F(function(){return _ci(_fc, -_ff);});}}}else{var _fk=B(_ef(_fc))-_ff|0,_fl=function(_fm){var _fn=function(_fo,_fp){if(!B(_ey(B(_cN(_fp,_fb)),_fo))){return new F(function(){return _cR(_fm-_fb|0,_fo,_fp);});}else{return new F(function(){return _cR((_fm-_fb|0)+1|0,_fo,B(_cN(_fp,1)));});}};if(_fm>=_fb){if(_fm!=_fb){return new F(function(){return _fn(_fc,new T(function(){return B(_cN(_fd,_fm-_fb|0));}));});}else{return new F(function(){return _fn(_fc,_fd);});}}else{return new F(function(){return _fn(new T(function(){return B(_cN(_fc,_fb-_fm|0));}),_fd);});}};if(_fa>_fk){return new F(function(){return _fl(_fa);});}else{return new F(function(){return _fl(_fk);});}}},_fq=new T1(0,2147483647),_fr=new T(function(){return B(_cu(_fq,_d5));}),_fs=function(_ft){var _fu=E(_ft);if(!_fu._){var _fv=E(_fu.a);return (_fv==( -2147483648))?E(_fr):new T1(0, -_fv);}else{return new T1(1,I_negate(_fu.a));}},_fw=new T(function(){return 0/0;}),_fx=new T(function(){return  -1/0;}),_fy=new T(function(){return 1/0;}),_fz=0,_fA=function(_fB,_fC){if(!B(_cm(_fC,_cM))){if(!B(_cm(_fB,_cM))){if(!B(_d6(_fB,_cM))){return new F(function(){return _f9( -1021,53,_fB,_fC);});}else{return  -B(_f9( -1021,53,B(_fs(_fB)),_fC));}}else{return E(_fz);}}else{return (!B(_cm(_fB,_cM)))?(!B(_d6(_fB,_cM)))?E(_fy):E(_fx):E(_fw);}},_fD=function(_fE){var _fF=E(_fE);return new F(function(){return _fA(_fF.a,_fF.b);});},_fG=function(_fH){return 1/E(_fH);},_fI=function(_fJ){var _fK=E(_fJ);return (_fK!=0)?(_fK<=0)? -_fK:E(_fK):E(_fz);},_fL=function(_fM){var _fN=E(_fM);if(!_fN._){return _fN.a;}else{return new F(function(){return I_toNumber(_fN.a);});}},_fO=function(_fP){return new F(function(){return _fL(_fP);});},_fQ=1,_fR= -1,_fS=function(_fT){var _fU=E(_fT);return (_fU<=0)?(_fU>=0)?E(_fU):E(_fR):E(_fQ);},_fV=function(_fW,_fX){return E(_fW)-E(_fX);},_fY=function(_fZ){return  -E(_fZ);},_g0=function(_g1,_g2){return E(_g1)+E(_g2);},_g3=function(_g4,_g5){return E(_g4)*E(_g5);},_g6={_:0,a:_g0,b:_fV,c:_g3,d:_fY,e:_fI,f:_fS,g:_fO},_g7=function(_g8,_g9){return E(_g8)/E(_g9);},_ga=new T4(0,_g6,_g7,_fG,_fD),_gb=function(_gc){return new F(function(){return Math.acos(E(_gc));});},_gd=function(_ge){return new F(function(){return Math.asin(E(_ge));});},_gf=function(_gg){return new F(function(){return Math.atan(E(_gg));});},_gh=function(_gi){return new F(function(){return Math.cos(E(_gi));});},_gj=function(_gk){return new F(function(){return cosh(E(_gk));});},_gl=function(_gm){return new F(function(){return Math.exp(E(_gm));});},_gn=function(_go){return new F(function(){return Math.log(E(_go));});},_gp=function(_gq,_gr){return new F(function(){return Math.pow(E(_gq),E(_gr));});},_gs=function(_gt){return new F(function(){return Math.sin(E(_gt));});},_gu=function(_gv){return new F(function(){return sinh(E(_gv));});},_gw=function(_gx){return new F(function(){return Math.sqrt(E(_gx));});},_gy=function(_gz){return new F(function(){return Math.tan(E(_gz));});},_gA=function(_gB){return new F(function(){return tanh(E(_gB));});},_gC={_:0,a:_ga,b:_c4,c:_gl,d:_gn,e:_gw,f:_gp,g:_c1,h:_gs,i:_gh,j:_gy,k:_gd,l:_gb,m:_gf,n:_gu,o:_gj,p:_gA,q:_bV,r:_bS,s:_bY},_gD=0,_gE=function(_){return _gD;},_gF=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gG=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gH=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gI=function(_gJ,_gK,_gL,_){var _gM=__app1(E(_gG),_gL),_gN=__app2(E(_gH),_gL,E(_gJ)),_gO=B(A2(_gK,_gL,_)),_gP=__app1(E(_gF),_gL);return new F(function(){return _gE(_);});},_gQ=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gR=function(_gS,_gT,_gU,_gV,_){var _gW=__app1(E(_gG),_gV),_gX=__app3(E(_gQ),_gV,E(_gS),E(_gT)),_gY=B(A2(_gU,_gV,_)),_gZ=__app1(E(_gF),_gV);return new F(function(){return _gE(_);});},_h0=function(_h1,_h2){return E(_h1)!=E(_h2);},_h3=function(_h4,_h5){return E(_h4)==E(_h5);},_h6=new T2(0,_h3,_h0),_h7=function(_h8){return E(E(_h8).a);},_h9=function(_ha){return E(E(_ha).a);},_hb=function(_hc){return E(E(_hc).b);},_hd=function(_he){return E(E(_he).g);},_hf=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hg=0,_hh=3.3333333333333335,_hi=16.666666666666668,_hj=function(_hk){return E(E(_hk).b);},_hl=new T1(0,0),_hm=new T1(0,2),_hn=function(_ho){return E(E(_ho).i);},_hp=function(_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx){var _hy=new T(function(){var _hz=E(_hx);if(_hz<=31){return B(_4A(_h6,_hz,_hf));}else{if(_hz>=128){return B(_4A(_h6,_hz,_hf));}else{return true;}}}),_hA=new T(function(){if(E(_ht)==8){return new T2(0,new T(function(){return B(_fL(B(A2(_hn,_hr,_hv))))*28+20;}),new T(function(){return B(_fL(B(A2(_hn,_hs,_hw))))*20+8*(E(_hu)-1);}));}else{return new T2(0,new T(function(){return B(_fL(B(A2(_hn,_hr,_hv))))*28;}),new T(function(){return B(_fL(B(A2(_hn,_hs,_hw))))*20;}));}}),_hB=new T(function(){var _hC=B(_h7(_hq));if(!E(_hy)){return B(A2(_hd,B(_h9(_hC)),_hl));}else{return B(A3(_hb,_hC,new T(function(){return B(_hj(_hq));}),new T(function(){return B(A2(_hd,B(_h9(_hC)),_hm));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hA).a);}),new T(function(){return E(E(_hA).b);})),new T2(0,new T(function(){if(!E(_hy)){return E(_hg);}else{return E(_hh);}}),new T(function(){if(!E(_hy)){return E(_hg);}else{return E(_hi);}})),_hB);},_hD=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hE=function(_hF,_hG,_hH){var _hI=new T(function(){return toJSStr(E(_hH));});return function(_hJ,_){var _hK=__app4(E(_hD),E(_hJ),E(_hI),E(_hF),E(_hG));return new F(function(){return _gE(_);});};},_hL=0,_hM=",",_hN="rgba(",_hO=new T(function(){return toJSStr(_S);}),_hP="rgb(",_hQ=")",_hR=new T2(1,_hQ,_S),_hS=function(_hT){var _hU=E(_hT);if(!_hU._){var _hV=jsCat(new T2(1,_hP,new T2(1,new T(function(){return String(_hU.a);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.b);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.c);}),_hR)))))),E(_hO));return E(_hV);}else{var _hW=jsCat(new T2(1,_hN,new T2(1,new T(function(){return String(_hU.a);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.b);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.c);}),new T2(1,_hM,new T2(1,new T(function(){return String(_hU.d);}),_hR)))))))),E(_hO));return E(_hW);}},_hX="strokeStyle",_hY="fillStyle",_hZ=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i0=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i1=function(_i2,_i3){var _i4=new T(function(){return B(_hS(_i2));});return function(_i5,_){var _i6=E(_i5),_i7=E(_hY),_i8=E(_hZ),_i9=__app2(_i8,_i6,_i7),_ia=E(_hX),_ib=__app2(_i8,_i6,_ia),_ic=E(_i4),_id=E(_i0),_ie=__app3(_id,_i6,_i7,_ic),_if=__app3(_id,_i6,_ia,_ic),_ig=B(A2(_i3,_i6,_)),_ih=String(_i9),_ii=__app3(_id,_i6,_i7,_ih),_ij=String(_ib),_ik=__app3(_id,_i6,_ia,_ij);return new F(function(){return _gE(_);});};},_il="font",_im=function(_in,_io){var _ip=new T(function(){return toJSStr(E(_in));});return function(_iq,_){var _ir=E(_iq),_is=E(_il),_it=__app2(E(_hZ),_ir,_is),_iu=E(_i0),_iv=__app3(_iu,_ir,_is,E(_ip)),_iw=B(A2(_io,_ir,_)),_ix=String(_it),_iy=__app3(_iu,_ir,_is,_ix);return new F(function(){return _gE(_);});};},_iz=new T(function(){return B(unCStr("px IPAGothic"));}),_iA=function(_iB,_iC,_iD,_iE,_iF,_iG,_iH,_){var _iI=new T(function(){var _iJ=new T(function(){var _iK=B(_hp(_gC,_bR,_bR,_iD,_iE,_iF,_iG,_iH)),_iL=E(_iK.a),_iM=E(_iK.b);return new T5(0,_iL.a,_iL.b,_iM.a,_iM.b,_iK.c);}),_iN=new T(function(){var _iO=E(_iJ);return E(_iO.a)+E(_iO.c);}),_iP=new T(function(){var _iQ=E(_iJ);return E(_iQ.b)-E(_iQ.d);}),_iR=new T(function(){return E(E(_iJ).e);}),_iS=new T(function(){return B(_hE(_hL,_hL,new T2(1,_iH,_S)));}),_iT=function(_iU,_){return new F(function(){return _gI(_iR,_iS,E(_iU),_);});};return B(_im(new T(function(){return B(_q(B(_A(0,E(_iD),_S)),_iz));},1),function(_iV,_){return new F(function(){return _gR(_iN,_iP,_iT,E(_iV),_);});}));});return new F(function(){return A(_i1,[_iC,_iI,_iB,_]);});},_iW=new T3(0,153,255,255),_iX=new T2(1,_iW,_S),_iY=new T3(0,255,153,204),_iZ=new T2(1,_iY,_iX),_j0=new T3(0,255,204,153),_j1=new T2(1,_j0,_iZ),_j2=new T3(0,200,255,200),_j3=new T2(1,_j2,_j1),_j4=20,_j5=64,_j6=1,_j7=2,_j8=8,_j9=function(_ja,_jb,_jc,_jd,_je,_jf,_jg,_){while(1){var _jh=B((function(_ji,_jj,_jk,_jl,_jm,_jn,_jo,_){var _jp=E(_jo);if(!_jp._){return _gD;}else{var _jq=_jp.b,_jr=E(_jp.a),_js=E(_jr);switch(_js){case 10:var _jt=_ji,_ju=_jj,_jv=_jl,_jw=_jl;_ja=_jt;_jb=_ju;_jc=0;_jd=_jv;_je=new T(function(){return E(_jm)-1|0;});_jf=_jw;_jg=_jq;return __continue;case 123:return new F(function(){return _jx(_ji,_jj,_jk,_jl,_jm,_jn,_jq,_);});break;case 65306:var _jy=new T(function(){return B(_6Q(_j3,_jk));}),_jz=function(_jA,_jB,_jC,_jD,_jE,_jF,_){while(1){var _jG=B((function(_jH,_jI,_jJ,_jK,_jL,_jM,_){var _jN=E(_jM);if(!_jN._){return _gD;}else{var _jO=_jN.b,_jP=E(_jN.a);if(E(_jP)==65306){var _jQ=new T(function(){var _jR=E(_jL);if((_jR+1)*20<=E(_jj)-10){return new T2(0,_jK,_jR+1|0);}else{return new T2(0,new T(function(){return E(_jK)-1|0;}),_jI);}});return new F(function(){return _j9(_jH,_jj,_jk,_jI,new T(function(){return E(E(_jQ).a);}),new T(function(){return E(E(_jQ).b);}),_jO,_);});}else{var _jS=E(_jH),_jT=B(_iA(_jS.a,_jy,_j8,_jJ,_jK,_jL,_jP,_)),_jU=_jI,_jV=_jJ+1,_jW=_jK,_jX=_jL;_jA=_jS;_jB=_jU;_jC=_jV;_jD=_jW;_jE=_jX;_jF=_jO;return __continue;}}})(_jA,_jB,_jC,_jD,_jE,_jF,_));if(_jG!=__continue){return _jG;}}};return new F(function(){return _jz(_ji,_jl,0,new T(function(){if(E(_jl)!=E(_jn)){return E(_jm);}else{return E(_jm)+1|0;}}),new T(function(){var _jY=E(_jn);if(E(_jl)!=_jY){return _jY-1|0;}else{var _jZ=(E(_jj)-10)/20,_k0=_jZ&4294967295;if(_jZ>=_k0){return _k0;}else{return _k0-1|0;}}}),_jq,_);});break;default:var _k1=function(_k2,_k3){var _k4=new T(function(){switch(E(_js)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return _jk;}}),_k5=new T(function(){var _k6=E(_jn);if((_k6+1)*20<=E(_jj)-10){return new T2(0,_jm,_k6+1|0);}else{return new T2(0,new T(function(){return E(_jm)-1|0;}),_jl);}});if(E(_k2)==64){return new F(function(){return _k7(_ji,_jj,_k4,_jl,new T(function(){return E(E(_k5).a);}),new T(function(){return E(E(_k5).b);}),_jq,_);});}else{var _k8=E(_ji),_k9=B(_iA(_k8.a,new T(function(){return B(_6Q(_j3,E(_k4)));},1),_j4,_hL,_jm,_jn,_k3,_));return new F(function(){return _k7(_k8,_jj,_k4,_jl,new T(function(){return E(E(_k5).a);}),new T(function(){return E(E(_k5).b);}),_jq,_);});}},_ka=E(_js);switch(_ka){case 42:return new F(function(){return _k1(64,_j5);});break;case 12289:return new F(function(){return _k1(64,_j5);});break;case 12290:return new F(function(){return _k1(64,_j5);});break;default:return new F(function(){return _k1(_ka,_jr);});}}}})(_ja,_jb,_jc,_jd,_je,_jf,_jg,_));if(_jh!=__continue){return _jh;}}},_k7=function(_kb,_kc,_kd,_ke,_kf,_kg,_kh,_){var _ki=E(_kh);if(!_ki._){return _gD;}else{var _kj=_ki.b,_kk=E(_ki.a),_kl=E(_kk);switch(_kl){case 10:return new F(function(){return _j9(_kb,_kc,0,_ke,new T(function(){return E(_kf)-1|0;}),_ke,_kj,_);});break;case 123:return new F(function(){return _jx(_kb,_kc,_kd,_ke,_kf,_kg,_kj,_);});break;case 65306:var _km=new T(function(){return B(_6Q(_j3,E(_kd)));}),_kn=function(_ko,_kp,_kq,_kr,_ks,_kt,_){while(1){var _ku=B((function(_kv,_kw,_kx,_ky,_kz,_kA,_){var _kB=E(_kA);if(!_kB._){return _gD;}else{var _kC=_kB.b,_kD=E(_kB.a);if(E(_kD)==65306){var _kE=new T(function(){var _kF=E(_kz);if((_kF+1)*20<=E(_kc)-10){return new T2(0,_ky,_kF+1|0);}else{return new T2(0,new T(function(){return E(_ky)-1|0;}),_kw);}});return new F(function(){return _k7(_kv,_kc,_kd,_kw,new T(function(){return E(E(_kE).a);}),new T(function(){return E(E(_kE).b);}),_kC,_);});}else{var _kG=E(_kv),_kH=B(_iA(_kG.a,_km,_j8,_kx,_ky,_kz,_kD,_)),_kI=_kw,_kJ=_kx+1,_kK=_ky,_kL=_kz;_ko=_kG;_kp=_kI;_kq=_kJ;_kr=_kK;_ks=_kL;_kt=_kC;return __continue;}}})(_ko,_kp,_kq,_kr,_ks,_kt,_));if(_ku!=__continue){return _ku;}}};return new F(function(){return _kn(_kb,_ke,0,new T(function(){if(E(_ke)!=E(_kg)){return E(_kf);}else{return E(_kf)+1|0;}}),new T(function(){var _kM=E(_kg);if(E(_ke)!=_kM){return _kM-1|0;}else{var _kN=(E(_kc)-10)/20,_kO=_kN&4294967295;if(_kN>=_kO){return _kO;}else{return _kO-1|0;}}}),_kj,_);});break;default:var _kP=function(_kQ,_kR){var _kS=new T(function(){switch(E(_kl)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return E(_kd);}}),_kT=new T(function(){var _kU=E(_kg);if((_kU+1)*20<=E(_kc)-10){return new T2(0,_kf,_kU+1|0);}else{return new T2(0,new T(function(){return E(_kf)-1|0;}),_ke);}});if(E(_kQ)==64){return new F(function(){return _k7(_kb,_kc,_kS,_ke,new T(function(){return E(E(_kT).a);}),new T(function(){return E(E(_kT).b);}),_kj,_);});}else{var _kV=E(_kb),_kW=B(_iA(_kV.a,new T(function(){return B(_6Q(_j3,E(_kS)));},1),_j4,_hL,_kf,_kg,_kR,_));return new F(function(){return _k7(_kV,_kc,_kS,_ke,new T(function(){return E(E(_kT).a);}),new T(function(){return E(E(_kT).b);}),_kj,_);});}},_kX=E(_kl);switch(_kX){case 42:return new F(function(){return _kP(64,_j5);});break;case 12289:return new F(function(){return _kP(64,_j5);});break;case 12290:return new F(function(){return _kP(64,_j5);});break;default:return new F(function(){return _kP(_kX,_kk);});}}}},_jx=function(_kY,_kZ,_l0,_l1,_l2,_l3,_l4,_){while(1){var _l5=B((function(_l6,_l7,_l8,_l9,_la,_lb,_lc,_){var _ld=E(_lc);if(!_ld._){return _gD;}else{var _le=_ld.b;if(E(_ld.a)==125){var _lf=new T(function(){var _lg=E(_lb);if((_lg+1)*20<=E(_l7)-10){return new T2(0,_la,_lg+1|0);}else{return new T2(0,new T(function(){return E(_la)-1|0;}),_l9);}});return new F(function(){return _k7(_l6,_l7,_l8,_l9,new T(function(){return E(E(_lf).a);}),new T(function(){return E(E(_lf).b);}),_le,_);});}else{var _lh=_l6,_li=_l7,_lj=_l8,_lk=_l9,_ll=_la,_lm=_lb;_kY=_lh;_kZ=_li;_l0=_lj;_l1=_lk;_l2=_ll;_l3=_lm;_l4=_le;return __continue;}}})(_kY,_kZ,_l0,_l1,_l2,_l3,_l4,_));if(_l5!=__continue){return _l5;}}},_ln=function(_lo,_lp,_lq,_lr,_ls,_lt,_lu,_lv,_){while(1){var _lw=B((function(_lx,_ly,_lz,_lA,_lB,_lC,_lD,_lE,_){var _lF=E(_lE);if(!_lF._){return _gD;}else{var _lG=_lF.b,_lH=E(_lF.a),_lI=E(_lH);switch(_lI){case 10:var _lJ=_lx,_lK=_ly,_lL=_lz,_lM=_lB,_lN=_lB;_lo=_lJ;_lp=_lK;_lq=_lL;_lr=0;_ls=_lM;_lt=new T(function(){return E(_lC)-1|0;});_lu=_lN;_lv=_lG;return __continue;case 123:return new F(function(){return _jx(new T2(0,_lx,_ly),_lz,_lA,_lB,_lC,_lD,_lG,_);});break;case 65306:var _lO=new T(function(){return B(_6Q(_j3,_lA));}),_lP=function(_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_){while(1){var _lX=B((function(_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_){var _m5=E(_m4);if(!_m5._){return _gD;}else{var _m6=_m5.b,_m7=E(_m5.a);if(E(_m7)==65306){var _m8=new T(function(){var _m9=E(_m3);if((_m9+1)*20<=E(_lz)-10){return new T2(0,_m2,_m9+1|0);}else{return new T2(0,new T(function(){return E(_m2)-1|0;}),_m0);}});return new F(function(){return _ln(_lY,_lZ,_lz,_lA,_m0,new T(function(){return E(E(_m8).a);}),new T(function(){return E(E(_m8).b);}),_m6,_);});}else{var _ma=B(_iA(_lY,_lO,_j8,_m1,_m2,_m3,_m7,_)),_mb=_lY,_mc=_lZ,_md=_m0,_me=_m1+1,_mf=_m2,_mg=_m3;_lQ=_mb;_lR=_mc;_lS=_md;_lT=_me;_lU=_mf;_lV=_mg;_lW=_m6;return __continue;}}})(_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_));if(_lX!=__continue){return _lX;}}};return new F(function(){return _lP(_lx,_ly,_lB,0,new T(function(){if(E(_lB)!=E(_lD)){return E(_lC);}else{return E(_lC)+1|0;}}),new T(function(){var _mh=E(_lD);if(E(_lB)!=_mh){return _mh-1|0;}else{var _mi=(E(_lz)-10)/20,_mj=_mi&4294967295;if(_mi>=_mj){return _mj;}else{return _mj-1|0;}}}),_lG,_);});break;default:var _mk=function(_ml,_mm){var _mn=new T(function(){switch(E(_lI)){case 42:return E(_j7);break;case 12300:return E(_j6);break;default:return _lA;}}),_mo=new T(function(){var _mp=E(_lD);if((_mp+1)*20<=E(_lz)-10){return new T2(0,_lC,_mp+1|0);}else{return new T2(0,new T(function(){return E(_lC)-1|0;}),_lB);}});if(E(_ml)==64){return new F(function(){return _k7(new T2(0,_lx,_ly),_lz,_mn,_lB,new T(function(){return E(E(_mo).a);}),new T(function(){return E(E(_mo).b);}),_lG,_);});}else{var _mq=B(_iA(_lx,new T(function(){return B(_6Q(_j3,E(_mn)));},1),_j4,_hL,_lC,_lD,_mm,_));return new F(function(){return _k7(new T2(0,_lx,_ly),_lz,_mn,_lB,new T(function(){return E(E(_mo).a);}),new T(function(){return E(E(_mo).b);}),_lG,_);});}},_mr=E(_lI);switch(_mr){case 42:return new F(function(){return _mk(64,_j5);});break;case 12289:return new F(function(){return _mk(64,_j5);});break;case 12290:return new F(function(){return _mk(64,_j5);});break;default:return new F(function(){return _mk(_mr,_lH);});}}}})(_lo,_lp,_lq,_lr,_ls,_lt,_lu,_lv,_));if(_lw!=__continue){return _lw;}}},_ms=function(_mt,_mu){while(1){var _mv=E(_mt);if(!_mv._){return E(_mu);}else{var _mw=_mu+1|0;_mt=_mv.b;_mu=_mw;continue;}}},_mx=function(_my){return E(E(_my).a);},_mz=function(_mA,_mB){var _mC=E(_mB),_mD=new T(function(){var _mE=B(_h9(_mA)),_mF=B(_mz(_mA,B(A3(_mx,_mE,_mC,new T(function(){return B(A2(_hd,_mE,_aU));})))));return new T2(1,_mF.a,_mF.b);});return new T2(0,_mC,_mD);},_mG=new T(function(){var _mH=B(_mz(_ga,_hL));return new T2(1,_mH.a,_mH.b);}),_mI=new T(function(){return B(unCStr("px Courier"));}),_mJ=new T(function(){return B(_A(0,20,_S));}),_mK=new T(function(){return B(_q(_mJ,_mI));}),_mL=function(_mM,_){return _gD;},_mN=function(_mO,_mP,_mQ,_mR,_mS){var _mT=new T(function(){return E(_mQ)*16;}),_mU=new T(function(){return E(_mR)*20;}),_mV=function(_mW,_mX){var _mY=E(_mW);if(!_mY._){return E(_mL);}else{var _mZ=E(_mX);if(!_mZ._){return E(_mL);}else{var _n0=new T(function(){return B(_mV(_mY.b,_mZ.b));}),_n1=new T(function(){var _n2=new T(function(){var _n3=new T(function(){return B(_hE(new T(function(){return E(_mT)+16*E(_mZ.a);}),_mU,new T2(1,_mY.a,_S)));});return B(_im(_mK,_n3));});return B(_i1(_mP,_n2));});return function(_n4,_){var _n5=B(A2(_n1,_n4,_));return new F(function(){return A2(_n0,_n4,_);});};}}};return new F(function(){return A3(_mV,_mS,_mG,_mO);});},_n6=45,_n7=new T(function(){return B(unCStr("-"));}),_n8=new T2(1,_n6,_n7),_n9=function(_na){var _nb=E(_na);return (_nb==1)?E(_n8):new T2(1,_n6,new T(function(){return B(_n9(_nb-1|0));}));},_nc=new T(function(){return B(unCStr(": empty list"));}),_nd=function(_ne){return new F(function(){return err(B(_q(_6F,new T(function(){return B(_q(_ne,_nc));},1))));});},_nf=new T(function(){return B(unCStr("head"));}),_ng=new T(function(){return B(_nd(_nf));}),_nh=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ni=new T(function(){return B(_hE(_hL,_hL,_S));}),_nj=32,_nk=new T(function(){return B(unCStr("|"));}),_nl=function(_nm){var _nn=E(_nm);return (_nn._==0)?E(_nk):new T2(1,new T(function(){var _no=E(_nn.a);switch(E(_no.b)){case 7:return E(_nj);break;case 8:return E(_nj);break;default:return E(_no.a);}}),new T(function(){return B(_nl(_nn.b));}));},_np=function(_nq,_nr,_ns,_nt,_nu,_){var _nv=__app1(E(_nh),_nr),_nw=B(A2(_ni,_nq,_)),_nx=B(unAppCStr("-",new T(function(){var _ny=E(_nu);if(!_ny._){return E(_ng);}else{var _nz=B(_ms(_ny.a,0));if(0>=_nz){return E(_n7);}else{return B(_n9(_nz));}}}))),_nA=B(A(_mN,[_nq,_j2,_ns,_nt,_nx,_])),_nB=function(_nC,_nD,_nE,_){while(1){var _nF=B((function(_nG,_nH,_nI,_){var _nJ=E(_nI);if(!_nJ._){return new F(function(){return A(_mN,[_nq,_j2,_nG,_nH,_nx,_]);});}else{var _nK=B(A(_mN,[_nq,_j2,_nG,_nH,B(unAppCStr("|",new T(function(){return B(_nl(_nJ.a));}))),_])),_nL=_nG;_nC=_nL;_nD=new T(function(){return E(_nH)+1|0;});_nE=_nJ.b;return __continue;}})(_nC,_nD,_nE,_));if(_nF!=__continue){return _nF;}}};return new F(function(){return _nB(_ns,new T(function(){return E(_nt)+1|0;}),_nu,_);});},_nM=new T(function(){return B(_6Q(_j3,1));}),_nN=new T(function(){return B(_6Q(_j3,2));}),_nO=2,_nP=function(_nQ,_nR,_nS,_nT,_){var _nU=__app1(E(_nh),_nR),_nV=B(A2(_ni,_nQ,_)),_nW=E(_nT),_nX=E(_nW.b).a,_nY=E(_nW.a),_nZ=_nY.a;if(!E(E(_nW.s).h)){return _gD;}else{var _o0=B(_np(_nQ,_nR,new T(function(){return E(_nS)-E(_nX)|0;}),_nO,_nY.b,_));return new F(function(){return A(_mN,[_nQ,new T(function(){if(E(_nY.d)==32){return E(_nM);}else{return E(_nN);}}),new T(function(){return ((E(E(_nZ).a)+1|0)+E(_nS)|0)-E(_nX)|0;},1),new T(function(){return (E(E(_nZ).b)+2|0)+1|0;},1),new T2(1,_nY.c,_S),_]);});}},_o1=function(_o2){return E(E(_o2).a);},_o3=function(_o4){return E(E(_o4).a);},_o5=function(_o6,_o7){while(1){var _o8=E(_o6);if(!_o8._){return E(_o7);}else{_o6=_o8.b;_o7=_o8.a;continue;}}},_o9=function(_oa,_ob,_oc){return new F(function(){return _o5(_ob,_oa);});},_od=new T1(0,2),_oe=function(_of,_og){while(1){var _oh=E(_of);if(!_oh._){var _oi=_oh.a,_oj=E(_og);if(!_oj._){var _ok=_oj.a;if(!(imul(_oi,_ok)|0)){return new T1(0,imul(_oi,_ok)|0);}else{_of=new T1(1,I_fromInt(_oi));_og=new T1(1,I_fromInt(_ok));continue;}}else{_of=new T1(1,I_fromInt(_oi));_og=_oj;continue;}}else{var _ol=E(_og);if(!_ol._){_of=_oh;_og=new T1(1,I_fromInt(_ol.a));continue;}else{return new T1(1,I_mul(_oh.a,_ol.a));}}}},_om=function(_on,_oo,_op){while(1){if(!(_oo%2)){var _oq=B(_oe(_on,_on)),_or=quot(_oo,2);_on=_oq;_oo=_or;continue;}else{var _os=E(_oo);if(_os==1){return new F(function(){return _oe(_on,_op);});}else{var _oq=B(_oe(_on,_on)),_ot=B(_oe(_on,_op));_on=_oq;_oo=quot(_os-1|0,2);_op=_ot;continue;}}}},_ou=function(_ov,_ow){while(1){if(!(_ow%2)){var _ox=B(_oe(_ov,_ov)),_oy=quot(_ow,2);_ov=_ox;_ow=_oy;continue;}else{var _oz=E(_ow);if(_oz==1){return E(_ov);}else{return new F(function(){return _om(B(_oe(_ov,_ov)),quot(_oz-1|0,2),_ov);});}}}},_oA=function(_oB){return E(E(_oB).c);},_oC=function(_oD){return E(E(_oD).a);},_oE=function(_oF){return E(E(_oF).b);},_oG=function(_oH){return E(E(_oH).b);},_oI=function(_oJ){return E(E(_oJ).c);},_oK=new T1(0,0),_oL=new T1(0,2),_oM=function(_oN){return E(E(_oN).d);},_oO=function(_oP,_oQ){var _oR=B(_o1(_oP)),_oS=new T(function(){return B(_o3(_oR));}),_oT=new T(function(){return B(A3(_oM,_oP,_oQ,new T(function(){return B(A2(_hd,_oS,_oL));})));});return new F(function(){return A3(_4y,B(_oC(B(_oE(_oR)))),_oT,new T(function(){return B(A2(_hd,_oS,_oK));}));});},_oU=new T(function(){return B(unCStr("Negative exponent"));}),_oV=new T(function(){return B(err(_oU));}),_oW=function(_oX){return E(E(_oX).c);},_oY=function(_oZ,_p0,_p1,_p2){var _p3=B(_o1(_p0)),_p4=new T(function(){return B(_o3(_p3));}),_p5=B(_oE(_p3));if(!B(A3(_oI,_p5,_p2,new T(function(){return B(A2(_hd,_p4,_oK));})))){if(!B(A3(_4y,B(_oC(_p5)),_p2,new T(function(){return B(A2(_hd,_p4,_oK));})))){var _p6=new T(function(){return B(A2(_hd,_p4,_oL));}),_p7=new T(function(){return B(A2(_hd,_p4,_aU));}),_p8=B(_oC(_p5)),_p9=function(_pa,_pb,_pc){while(1){var _pd=B((function(_pe,_pf,_pg){if(!B(_oO(_p0,_pf))){if(!B(A3(_4y,_p8,_pf,_p7))){var _ph=new T(function(){return B(A3(_oW,_p0,new T(function(){return B(A3(_oG,_p4,_pf,_p7));}),_p6));});_pa=new T(function(){return B(A3(_oA,_oZ,_pe,_pe));});_pb=_ph;_pc=new T(function(){return B(A3(_oA,_oZ,_pe,_pg));});return __continue;}else{return new F(function(){return A3(_oA,_oZ,_pe,_pg);});}}else{var _pi=_pg;_pa=new T(function(){return B(A3(_oA,_oZ,_pe,_pe));});_pb=new T(function(){return B(A3(_oW,_p0,_pf,_p6));});_pc=_pi;return __continue;}})(_pa,_pb,_pc));if(_pd!=__continue){return _pd;}}},_pj=function(_pk,_pl){while(1){var _pm=B((function(_pn,_po){if(!B(_oO(_p0,_po))){if(!B(A3(_4y,_p8,_po,_p7))){var _pp=new T(function(){return B(A3(_oW,_p0,new T(function(){return B(A3(_oG,_p4,_po,_p7));}),_p6));});return new F(function(){return _p9(new T(function(){return B(A3(_oA,_oZ,_pn,_pn));}),_pp,_pn);});}else{return E(_pn);}}else{_pk=new T(function(){return B(A3(_oA,_oZ,_pn,_pn));});_pl=new T(function(){return B(A3(_oW,_p0,_po,_p6));});return __continue;}})(_pk,_pl));if(_pm!=__continue){return _pm;}}};return new F(function(){return _pj(_p1,_p2);});}else{return new F(function(){return A2(_hd,_oZ,_aU);});}}else{return E(_oV);}},_pq=new T(function(){return B(err(_oU));}),_pr=function(_ps){var _pt=I_decodeDouble(_ps);return new T2(0,new T1(1,_pt.b),_pt.a);},_pu=function(_pv,_pw){var _px=B(_pr(_pw)),_py=_px.a,_pz=_px.b,_pA=new T(function(){return B(_o3(new T(function(){return B(_o1(_pv));})));});if(_pz<0){var _pB= -_pz;if(_pB>=0){var _pC=E(_pB);if(!_pC){var _pD=E(_aU);}else{var _pD=B(_ou(_od,_pC));}if(!B(_cm(_pD,_cM))){var _pE=B(_cD(_py,_pD));return new T2(0,new T(function(){return B(A2(_hd,_pA,_pE.a));}),new T(function(){return B(_ci(_pE.b,_pz));}));}else{return E(_9T);}}else{return E(_pq);}}else{var _pF=new T(function(){var _pG=new T(function(){return B(_oY(_pA,_bR,new T(function(){return B(A2(_hd,_pA,_od));}),_pz));});return B(A3(_oA,_pA,new T(function(){return B(A2(_hd,_pA,_py));}),_pG));});return new T2(0,_pF,_fz);}},_pH=function(_pI,_pJ){while(1){var _pK=E(_pJ);if(!_pK._){return __Z;}else{var _pL=_pK.b,_pM=E(_pI);if(_pM==1){return E(_pL);}else{_pI=_pM-1|0;_pJ=_pL;continue;}}}},_pN=function(_pO,_pP){var _pQ=E(_pP);if(!_pQ._){return __Z;}else{var _pR=_pQ.a,_pS=E(_pO);return (_pS==1)?new T2(1,_pR,_S):new T2(1,_pR,new T(function(){return B(_pN(_pS-1|0,_pQ.b));}));}},_pT=function(_pU,_pV,_pW,_pX){while(1){if(B(_6Q(new T2(1,_pW,_pX),_pV))!=_pU){var _pY=_pV+1|0;_pV=_pY;continue;}else{if(0>=_pV){return __Z;}else{return new F(function(){return _pN(_pV,new T2(1,_pW,_pX));});}}}},_pZ=function(_q0,_q1,_q2){var _q3=E(_q2);if(!_q3._){return __Z;}else{var _q4=E(_q0);if(B(_6Q(_q3,_q1))!=_q4){return new F(function(){return _pT(_q4,_q1+1|0,_q3.a,_q3.b);});}else{if(0>=_q1){return __Z;}else{return new F(function(){return _pN(_q1,_q3);});}}}},_q5=function(_q6,_q7,_q8){var _q9=_q7+1|0;if(_q9>0){return new F(function(){return _pH(_q9,B(_pZ(_q6,_q9,_q8)));});}else{return new F(function(){return _pZ(_q6,_q9,_q8);});}},_qa=function(_qb,_qc){return (!B(_68(_qb,_qc)))?true:false;},_qd=new T2(0,_68,_qa),_qe=new T(function(){return B(_e6("Event.hs:(65,1)-(66,68)|function addEvent"));}),_qf=0,_qg=function(_qh,_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB){while(1){var _qC=E(_qh);if(!_qC._){return {_:0,a:_qi,b:_qj,c:_qk,d:_ql,e:_qm,f:_qn,g:_qo,h:_qp,i:_qq,j:_qr,k:_qs,l:_qt,m:_qu,n:_qv,o:_qw,p:_qx,q:_qy,r:_qz,s:_qA,t:_qB};}else{var _qD=E(_qC.b);if(!_qD._){return E(_qe);}else{var _qE=new T2(1,new T2(0,_qC.a,_qD.a),_qm),_qF=new T2(1,_qf,_qn);_qh=_qD.b;_qm=_qE;_qn=_qF;continue;}}}},_qG=function(_qH,_qI,_qJ){var _qK=E(_qJ);if(!_qK._){return __Z;}else{var _qL=_qK.a,_qM=_qK.b;return (!B(A2(_qH,_qI,_qL)))?new T2(1,_qL,new T(function(){return B(_qG(_qH,_qI,_qM));})):E(_qM);}},_qN=function(_qO,_qP){while(1){var _qQ=E(_qO);if(!_qQ._){return (E(_qP)._==0)?true:false;}else{var _qR=E(_qP);if(!_qR._){return false;}else{if(E(_qQ.a)!=E(_qR.a)){return false;}else{_qO=_qQ.b;_qP=_qR.b;continue;}}}}},_qS=function(_qT,_qU){while(1){var _qV=E(_qT);if(!_qV._){return (E(_qU)._==0)?true:false;}else{var _qW=E(_qU);if(!_qW._){return false;}else{if(!B(_68(_qV.a,_qW.a))){return false;}else{_qT=_qV.b;_qU=_qW.b;continue;}}}}},_qX=function(_qY,_qZ){switch(E(_qY)){case 0:return (E(_qZ)==0)?true:false;case 1:return (E(_qZ)==1)?true:false;case 2:return (E(_qZ)==2)?true:false;case 3:return (E(_qZ)==3)?true:false;case 4:return (E(_qZ)==4)?true:false;case 5:return (E(_qZ)==5)?true:false;case 6:return (E(_qZ)==6)?true:false;case 7:return (E(_qZ)==7)?true:false;default:return (E(_qZ)==8)?true:false;}},_r0=function(_r1,_r2,_r3,_r4){if(_r1!=_r3){return false;}else{return new F(function(){return _qX(_r2,_r4);});}},_r5=function(_r6,_r7){var _r8=E(_r6),_r9=E(_r7);return new F(function(){return _r0(E(_r8.a),_r8.b,E(_r9.a),_r9.b);});},_ra=function(_rb,_rc,_rd,_re){if(_rb!=_rd){return true;}else{switch(E(_rc)){case 0:return (E(_re)==0)?false:true;case 1:return (E(_re)==1)?false:true;case 2:return (E(_re)==2)?false:true;case 3:return (E(_re)==3)?false:true;case 4:return (E(_re)==4)?false:true;case 5:return (E(_re)==5)?false:true;case 6:return (E(_re)==6)?false:true;case 7:return (E(_re)==7)?false:true;default:return (E(_re)==8)?false:true;}}},_rf=function(_rg,_rh){var _ri=E(_rg),_rj=E(_rh);return new F(function(){return _ra(E(_ri.a),_ri.b,E(_rj.a),_rj.b);});},_rk=new T2(0,_r5,_rf),_rl=0,_rm=function(_rn,_ro){var _rp=E(_ro);if(!_rp._){return 0;}else{var _rq=_rp.b,_rr=E(_rn),_rs=E(_rp.a),_rt=_rs.b;if(E(_rr.a)!=E(_rs.a)){return 1+B(_rm(_rr,_rq))|0;}else{switch(E(_rr.b)){case 0:return (E(_rt)==0)?0:1+B(_rm(_rr,_rq))|0;case 1:return (E(_rt)==1)?0:1+B(_rm(_rr,_rq))|0;case 2:return (E(_rt)==2)?0:1+B(_rm(_rr,_rq))|0;case 3:return (E(_rt)==3)?0:1+B(_rm(_rr,_rq))|0;case 4:return (E(_rt)==4)?0:1+B(_rm(_rr,_rq))|0;case 5:return (E(_rt)==5)?0:1+B(_rm(_rr,_rq))|0;case 6:return (E(_rt)==6)?0:1+B(_rm(_rr,_rq))|0;case 7:return (E(_rt)==7)?0:1+B(_rm(_rr,_rq))|0;default:return (E(_rt)==8)?0:1+B(_rm(_rr,_rq))|0;}}}},_ru=function(_rv,_rw){return new F(function(){return _rm(_rv,_rw);});},_rx=function(_ry,_rz){var _rA=E(_rz);if(!_rA._){return new T2(0,_rl,_rl);}else{var _rB=_rA.a,_rC=_rA.b;return (!B(_4A(_rk,_ry,_rB)))?new T2(0,new T(function(){return E(B(_rx(_ry,_rC)).a);}),new T(function(){return 1+E(B(_rx(_ry,_rC)).b)|0;})):new T2(0,new T(function(){return B(_ru(_ry,_rB));}),_rl);}},_rD=function(_rE,_rF){while(1){var _rG=E(_rF);if(!_rG._){return __Z;}else{var _rH=_rG.b,_rI=E(_rE);if(_rI==1){return E(_rH);}else{_rE=_rI-1|0;_rF=_rH;continue;}}}},_rJ=new T(function(){return B(unCStr("getch"));}),_rK=new T(function(){return B(unCStr("=="));}),_rL=new T(function(){return B(unCStr("&&"));}),_rM=new T(function(){return B(unCStr("||"));}),_rN=new T(function(){return B(unCStr("getpos"));}),_rO=new T(function(){return B(unCStr("ch"));}),_rP=new T(function(){return B(unCStr("tp"));}),_rQ=new T2(1,_rP,_S),_rR=new T2(1,_rO,_rQ),_rS=new T2(0,_rN,_rR),_rT=new T(function(){return B(unCStr("a"));}),_rU=new T(function(){return B(unCStr("b"));}),_rV=new T2(1,_rU,_S),_rW=new T2(1,_rT,_rV),_rX=new T2(0,_rK,_rW),_rY=new T2(0,_rL,_rW),_rZ=new T2(0,_rM,_rW),_s0=new T2(1,_rZ,_S),_s1=new T2(1,_rY,_s0),_s2=new T2(1,_rX,_s1),_s3=new T2(1,_rS,_s2),_s4=new T(function(){return B(unCStr("p"));}),_s5=new T(function(){return B(unCStr("q"));}),_s6=new T2(1,_s5,_S),_s7=new T2(1,_s4,_s6),_s8=new T2(0,_rJ,_s7),_s9=new T2(1,_s8,_s3),_sa=new T(function(){return B(unCStr("foldr1"));}),_sb=new T(function(){return B(_nd(_sa));}),_sc=function(_sd,_se){var _sf=E(_se);if(!_sf._){return E(_sb);}else{var _sg=_sf.a,_sh=E(_sf.b);if(!_sh._){return E(_sg);}else{return new F(function(){return A2(_sd,_sg,new T(function(){return B(_sc(_sd,_sh));}));});}}},_si=function(_sj){return E(E(_sj).a);},_sk=function(_sl,_sm,_sn){while(1){var _so=E(_sn);if(!_so._){return __Z;}else{var _sp=E(_so.a);if(!B(A3(_4y,_sl,_sm,_sp.a))){_sn=_so.b;continue;}else{return new T1(1,_sp.b);}}}},_sq=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sr=new T(function(){return B(err(_sq));}),_ss=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_st=new T(function(){return B(err(_ss));}),_su=new T(function(){return B(unCStr("T"));}),_sv=new T(function(){return B(unCStr("F"));}),_sw=new T(function(){return B(_e6("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sx=function(_sy,_sz){while(1){var _sA=B((function(_sB,_sC){var _sD=E(_sB);switch(_sD._){case 0:var _sE=E(_sC);if(!_sE._){return __Z;}else{_sy=B(A1(_sD.a,_sE.a));_sz=_sE.b;return __continue;}break;case 1:var _sF=B(A1(_sD.a,_sC)),_sG=_sC;_sy=_sF;_sz=_sG;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sD.a,_sC),new T(function(){return B(_sx(_sD.b,_sC));}));default:return E(_sD.a);}})(_sy,_sz));if(_sA!=__continue){return _sA;}}},_sH=function(_sI,_sJ){var _sK=function(_sL){var _sM=E(_sJ);if(_sM._==3){return new T2(3,_sM.a,new T(function(){return B(_sH(_sI,_sM.b));}));}else{var _sN=E(_sI);if(_sN._==2){return E(_sM);}else{var _sO=E(_sM);if(_sO._==2){return E(_sN);}else{var _sP=function(_sQ){var _sR=E(_sO);if(_sR._==4){var _sS=function(_sT){return new T1(4,new T(function(){return B(_q(B(_sx(_sN,_sT)),_sR.a));}));};return new T1(1,_sS);}else{var _sU=E(_sN);if(_sU._==1){var _sV=_sU.a,_sW=E(_sR);if(!_sW._){return new T1(1,function(_sX){return new F(function(){return _sH(B(A1(_sV,_sX)),_sW);});});}else{var _sY=function(_sZ){return new F(function(){return _sH(B(A1(_sV,_sZ)),new T(function(){return B(A1(_sW.a,_sZ));}));});};return new T1(1,_sY);}}else{var _t0=E(_sR);if(!_t0._){return E(_sw);}else{var _t1=function(_t2){return new F(function(){return _sH(_sU,new T(function(){return B(A1(_t0.a,_t2));}));});};return new T1(1,_t1);}}}},_t3=E(_sN);switch(_t3._){case 1:var _t4=E(_sO);if(_t4._==4){var _t5=function(_t6){return new T1(4,new T(function(){return B(_q(B(_sx(B(A1(_t3.a,_t6)),_t6)),_t4.a));}));};return new T1(1,_t5);}else{return new F(function(){return _sP(_);});}break;case 4:var _t7=_t3.a,_t8=E(_sO);switch(_t8._){case 0:var _t9=function(_ta){var _tb=new T(function(){return B(_q(_t7,new T(function(){return B(_sx(_t8,_ta));},1)));});return new T1(4,_tb);};return new T1(1,_t9);case 1:var _tc=function(_td){var _te=new T(function(){return B(_q(_t7,new T(function(){return B(_sx(B(A1(_t8.a,_td)),_td));},1)));});return new T1(4,_te);};return new T1(1,_tc);default:return new T1(4,new T(function(){return B(_q(_t7,_t8.a));}));}break;default:return new F(function(){return _sP(_);});}}}}},_tf=E(_sI);switch(_tf._){case 0:var _tg=E(_sJ);if(!_tg._){var _th=function(_ti){return new F(function(){return _sH(B(A1(_tf.a,_ti)),new T(function(){return B(A1(_tg.a,_ti));}));});};return new T1(0,_th);}else{return new F(function(){return _sK(_);});}break;case 3:return new T2(3,_tf.a,new T(function(){return B(_sH(_tf.b,_sJ));}));default:return new F(function(){return _sK(_);});}},_tj=new T(function(){return B(unCStr("("));}),_tk=new T(function(){return B(unCStr(")"));}),_tl=function(_tm,_tn){var _to=E(_tm);switch(_to._){case 0:return new T1(0,function(_tp){return new F(function(){return _tl(B(A1(_to.a,_tp)),_tn);});});case 1:return new T1(1,function(_tq){return new F(function(){return _tl(B(A1(_to.a,_tq)),_tn);});});case 2:return new T0(2);case 3:return new F(function(){return _sH(B(A1(_tn,_to.a)),new T(function(){return B(_tl(_to.b,_tn));}));});break;default:var _tr=function(_ts){var _tt=E(_ts);if(!_tt._){return __Z;}else{var _tu=E(_tt.a);return new F(function(){return _q(B(_sx(B(A1(_tn,_tu.a)),_tu.b)),new T(function(){return B(_tr(_tt.b));},1));});}},_tv=B(_tr(_to.a));return (_tv._==0)?new T0(2):new T1(4,_tv);}},_tw=new T0(2),_tx=function(_ty){return new T2(3,_ty,_tw);},_tz=function(_tA,_tB){var _tC=E(_tA);if(!_tC){return new F(function(){return A1(_tB,_gD);});}else{var _tD=new T(function(){return B(_tz(_tC-1|0,_tB));});return new T1(0,function(_tE){return E(_tD);});}},_tF=function(_tG,_tH,_tI){var _tJ=new T(function(){return B(A1(_tG,_tx));}),_tK=function(_tL,_tM,_tN,_tO){while(1){var _tP=B((function(_tQ,_tR,_tS,_tT){var _tU=E(_tQ);switch(_tU._){case 0:var _tV=E(_tR);if(!_tV._){return new F(function(){return A1(_tH,_tT);});}else{var _tW=_tS+1|0,_tX=_tT;_tL=B(A1(_tU.a,_tV.a));_tM=_tV.b;_tN=_tW;_tO=_tX;return __continue;}break;case 1:var _tY=B(A1(_tU.a,_tR)),_tZ=_tR,_tW=_tS,_tX=_tT;_tL=_tY;_tM=_tZ;_tN=_tW;_tO=_tX;return __continue;case 2:return new F(function(){return A1(_tH,_tT);});break;case 3:var _u0=new T(function(){return B(_tl(_tU,_tT));});return new F(function(){return _tz(_tS,function(_u1){return E(_u0);});});break;default:return new F(function(){return _tl(_tU,_tT);});}})(_tL,_tM,_tN,_tO));if(_tP!=__continue){return _tP;}}};return function(_u2){return new F(function(){return _tK(_tJ,_u2,0,_tI);});};},_u3=function(_u4){return new F(function(){return A1(_u4,_S);});},_u5=function(_u6,_u7){var _u8=function(_u9){var _ua=E(_u9);if(!_ua._){return E(_u3);}else{var _ub=_ua.a;if(!B(A1(_u6,_ub))){return E(_u3);}else{var _uc=new T(function(){return B(_u8(_ua.b));}),_ud=function(_ue){var _uf=new T(function(){return B(A1(_uc,function(_ug){return new F(function(){return A1(_ue,new T2(1,_ub,_ug));});}));});return new T1(0,function(_uh){return E(_uf);});};return E(_ud);}}};return function(_ui){return new F(function(){return A2(_u8,_ui,_u7);});};},_uj=new T0(6),_uk=new T(function(){return B(unCStr("valDig: Bad base"));}),_ul=new T(function(){return B(err(_uk));}),_um=function(_un,_uo){var _up=function(_uq,_ur){var _us=E(_uq);if(!_us._){var _ut=new T(function(){return B(A1(_ur,_S));});return function(_uu){return new F(function(){return A1(_uu,_ut);});};}else{var _uv=E(_us.a),_uw=function(_ux){var _uy=new T(function(){return B(_up(_us.b,function(_uz){return new F(function(){return A1(_ur,new T2(1,_ux,_uz));});}));}),_uA=function(_uB){var _uC=new T(function(){return B(A1(_uy,_uB));});return new T1(0,function(_uD){return E(_uC);});};return E(_uA);};switch(E(_un)){case 8:if(48>_uv){var _uE=new T(function(){return B(A1(_ur,_S));});return function(_uF){return new F(function(){return A1(_uF,_uE);});};}else{if(_uv>55){var _uG=new T(function(){return B(A1(_ur,_S));});return function(_uH){return new F(function(){return A1(_uH,_uG);});};}else{return new F(function(){return _uw(_uv-48|0);});}}break;case 10:if(48>_uv){var _uI=new T(function(){return B(A1(_ur,_S));});return function(_uJ){return new F(function(){return A1(_uJ,_uI);});};}else{if(_uv>57){var _uK=new T(function(){return B(A1(_ur,_S));});return function(_uL){return new F(function(){return A1(_uL,_uK);});};}else{return new F(function(){return _uw(_uv-48|0);});}}break;case 16:if(48>_uv){if(97>_uv){if(65>_uv){var _uM=new T(function(){return B(A1(_ur,_S));});return function(_uN){return new F(function(){return A1(_uN,_uM);});};}else{if(_uv>70){var _uO=new T(function(){return B(A1(_ur,_S));});return function(_uP){return new F(function(){return A1(_uP,_uO);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{if(_uv>102){if(65>_uv){var _uQ=new T(function(){return B(A1(_ur,_S));});return function(_uR){return new F(function(){return A1(_uR,_uQ);});};}else{if(_uv>70){var _uS=new T(function(){return B(A1(_ur,_S));});return function(_uT){return new F(function(){return A1(_uT,_uS);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{return new F(function(){return _uw((_uv-97|0)+10|0);});}}}else{if(_uv>57){if(97>_uv){if(65>_uv){var _uU=new T(function(){return B(A1(_ur,_S));});return function(_uV){return new F(function(){return A1(_uV,_uU);});};}else{if(_uv>70){var _uW=new T(function(){return B(A1(_ur,_S));});return function(_uX){return new F(function(){return A1(_uX,_uW);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{if(_uv>102){if(65>_uv){var _uY=new T(function(){return B(A1(_ur,_S));});return function(_uZ){return new F(function(){return A1(_uZ,_uY);});};}else{if(_uv>70){var _v0=new T(function(){return B(A1(_ur,_S));});return function(_v1){return new F(function(){return A1(_v1,_v0);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{return new F(function(){return _uw((_uv-97|0)+10|0);});}}}else{return new F(function(){return _uw(_uv-48|0);});}}break;default:return E(_ul);}}},_v2=function(_v3){var _v4=E(_v3);if(!_v4._){return new T0(2);}else{return new F(function(){return A1(_uo,_v4);});}};return function(_v5){return new F(function(){return A3(_up,_v5,_5U,_v2);});};},_v6=16,_v7=8,_v8=function(_v9){var _va=function(_vb){return new F(function(){return A1(_v9,new T1(5,new T2(0,_v7,_vb)));});},_vc=function(_vd){return new F(function(){return A1(_v9,new T1(5,new T2(0,_v6,_vd)));});},_ve=function(_vf){switch(E(_vf)){case 79:return new T1(1,B(_um(_v7,_va)));case 88:return new T1(1,B(_um(_v6,_vc)));case 111:return new T1(1,B(_um(_v7,_va)));case 120:return new T1(1,B(_um(_v6,_vc)));default:return new T0(2);}};return function(_vg){return (E(_vg)==48)?E(new T1(0,_ve)):new T0(2);};},_vh=function(_vi){return new T1(0,B(_v8(_vi)));},_vj=function(_vk){return new F(function(){return A1(_vk,_2N);});},_vl=function(_vm){return new F(function(){return A1(_vm,_2N);});},_vn=10,_vo=new T1(0,10),_vp=function(_vq){return new F(function(){return _aQ(E(_vq));});},_vr=new T(function(){return B(unCStr("this should not happen"));}),_vs=new T(function(){return B(err(_vr));}),_vt=function(_vu,_vv){var _vw=E(_vv);if(!_vw._){return __Z;}else{var _vx=E(_vw.b);return (_vx._==0)?E(_vs):new T2(1,B(_cu(B(_oe(_vw.a,_vu)),_vx.a)),new T(function(){return B(_vt(_vu,_vx.b));}));}},_vy=new T1(0,0),_vz=function(_vA,_vB,_vC){while(1){var _vD=B((function(_vE,_vF,_vG){var _vH=E(_vG);if(!_vH._){return E(_vy);}else{if(!E(_vH.b)._){return E(_vH.a);}else{var _vI=E(_vF);if(_vI<=40){var _vJ=function(_vK,_vL){while(1){var _vM=E(_vL);if(!_vM._){return E(_vK);}else{var _vN=B(_cu(B(_oe(_vK,_vE)),_vM.a));_vK=_vN;_vL=_vM.b;continue;}}};return new F(function(){return _vJ(_vy,_vH);});}else{var _vO=B(_oe(_vE,_vE));if(!(_vI%2)){var _vP=B(_vt(_vE,_vH));_vA=_vO;_vB=quot(_vI+1|0,2);_vC=_vP;return __continue;}else{var _vP=B(_vt(_vE,new T2(1,_vy,_vH)));_vA=_vO;_vB=quot(_vI+1|0,2);_vC=_vP;return __continue;}}}}})(_vA,_vB,_vC));if(_vD!=__continue){return _vD;}}},_vQ=function(_vR,_vS){return new F(function(){return _vz(_vR,new T(function(){return B(_ms(_vS,0));},1),B(_6d(_vp,_vS)));});},_vT=function(_vU){var _vV=new T(function(){var _vW=new T(function(){var _vX=function(_vY){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_vQ(_vo,_vY));})));});};return new T1(1,B(_um(_vn,_vX)));}),_vZ=function(_w0){if(E(_w0)==43){var _w1=function(_w2){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_vQ(_vo,_w2));})));});};return new T1(1,B(_um(_vn,_w1)));}else{return new T0(2);}},_w3=function(_w4){if(E(_w4)==45){var _w5=function(_w6){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_fs(B(_vQ(_vo,_w6))));})));});};return new T1(1,B(_um(_vn,_w5)));}else{return new T0(2);}};return B(_sH(B(_sH(new T1(0,_w3),new T1(0,_vZ))),_vW));});return new F(function(){return _sH(new T1(0,function(_w7){return (E(_w7)==101)?E(_vV):new T0(2);}),new T1(0,function(_w8){return (E(_w8)==69)?E(_vV):new T0(2);}));});},_w9=function(_wa){var _wb=function(_wc){return new F(function(){return A1(_wa,new T1(1,_wc));});};return function(_wd){return (E(_wd)==46)?new T1(1,B(_um(_vn,_wb))):new T0(2);};},_we=function(_wf){return new T1(0,B(_w9(_wf)));},_wg=function(_wh){var _wi=function(_wj){var _wk=function(_wl){return new T1(1,B(_tF(_vT,_vj,function(_wm){return new F(function(){return A1(_wh,new T1(5,new T3(1,_wj,_wl,_wm)));});})));};return new T1(1,B(_tF(_we,_vl,_wk)));};return new F(function(){return _um(_vn,_wi);});},_wn=function(_wo){return new T1(1,B(_wg(_wo)));},_wp=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wq=function(_wr){return new F(function(){return _4A(_h6,_wr,_wp);});},_ws=false,_wt=true,_wu=function(_wv){var _ww=new T(function(){return B(A1(_wv,_v7));}),_wx=new T(function(){return B(A1(_wv,_v6));});return function(_wy){switch(E(_wy)){case 79:return E(_ww);case 88:return E(_wx);case 111:return E(_ww);case 120:return E(_wx);default:return new T0(2);}};},_wz=function(_wA){return new T1(0,B(_wu(_wA)));},_wB=function(_wC){return new F(function(){return A1(_wC,_vn);});},_wD=function(_wE){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_A(9,_wE,_S));}))));});},_wF=function(_wG){return new T0(2);},_wH=function(_wI){var _wJ=E(_wI);if(!_wJ._){return E(_wF);}else{var _wK=_wJ.a,_wL=E(_wJ.b);if(!_wL._){return E(_wK);}else{var _wM=new T(function(){return B(_wH(_wL));}),_wN=function(_wO){return new F(function(){return _sH(B(A1(_wK,_wO)),new T(function(){return B(A1(_wM,_wO));}));});};return E(_wN);}}},_wP=function(_wQ,_wR){var _wS=function(_wT,_wU,_wV){var _wW=E(_wT);if(!_wW._){return new F(function(){return A1(_wV,_wQ);});}else{var _wX=E(_wU);if(!_wX._){return new T0(2);}else{if(E(_wW.a)!=E(_wX.a)){return new T0(2);}else{var _wY=new T(function(){return B(_wS(_wW.b,_wX.b,_wV));});return new T1(0,function(_wZ){return E(_wY);});}}}};return function(_x0){return new F(function(){return _wS(_wQ,_x0,_wR);});};},_x1=new T(function(){return B(unCStr("SO"));}),_x2=14,_x3=function(_x4){var _x5=new T(function(){return B(A1(_x4,_x2));});return new T1(1,B(_wP(_x1,function(_x6){return E(_x5);})));},_x7=new T(function(){return B(unCStr("SOH"));}),_x8=1,_x9=function(_xa){var _xb=new T(function(){return B(A1(_xa,_x8));});return new T1(1,B(_wP(_x7,function(_xc){return E(_xb);})));},_xd=function(_xe){return new T1(1,B(_tF(_x9,_x3,_xe)));},_xf=new T(function(){return B(unCStr("NUL"));}),_xg=0,_xh=function(_xi){var _xj=new T(function(){return B(A1(_xi,_xg));});return new T1(1,B(_wP(_xf,function(_xk){return E(_xj);})));},_xl=new T(function(){return B(unCStr("STX"));}),_xm=2,_xn=function(_xo){var _xp=new T(function(){return B(A1(_xo,_xm));});return new T1(1,B(_wP(_xl,function(_xq){return E(_xp);})));},_xr=new T(function(){return B(unCStr("ETX"));}),_xs=3,_xt=function(_xu){var _xv=new T(function(){return B(A1(_xu,_xs));});return new T1(1,B(_wP(_xr,function(_xw){return E(_xv);})));},_xx=new T(function(){return B(unCStr("EOT"));}),_xy=4,_xz=function(_xA){var _xB=new T(function(){return B(A1(_xA,_xy));});return new T1(1,B(_wP(_xx,function(_xC){return E(_xB);})));},_xD=new T(function(){return B(unCStr("ENQ"));}),_xE=5,_xF=function(_xG){var _xH=new T(function(){return B(A1(_xG,_xE));});return new T1(1,B(_wP(_xD,function(_xI){return E(_xH);})));},_xJ=new T(function(){return B(unCStr("ACK"));}),_xK=6,_xL=function(_xM){var _xN=new T(function(){return B(A1(_xM,_xK));});return new T1(1,B(_wP(_xJ,function(_xO){return E(_xN);})));},_xP=new T(function(){return B(unCStr("BEL"));}),_xQ=7,_xR=function(_xS){var _xT=new T(function(){return B(A1(_xS,_xQ));});return new T1(1,B(_wP(_xP,function(_xU){return E(_xT);})));},_xV=new T(function(){return B(unCStr("BS"));}),_xW=8,_xX=function(_xY){var _xZ=new T(function(){return B(A1(_xY,_xW));});return new T1(1,B(_wP(_xV,function(_y0){return E(_xZ);})));},_y1=new T(function(){return B(unCStr("HT"));}),_y2=9,_y3=function(_y4){var _y5=new T(function(){return B(A1(_y4,_y2));});return new T1(1,B(_wP(_y1,function(_y6){return E(_y5);})));},_y7=new T(function(){return B(unCStr("LF"));}),_y8=10,_y9=function(_ya){var _yb=new T(function(){return B(A1(_ya,_y8));});return new T1(1,B(_wP(_y7,function(_yc){return E(_yb);})));},_yd=new T(function(){return B(unCStr("VT"));}),_ye=11,_yf=function(_yg){var _yh=new T(function(){return B(A1(_yg,_ye));});return new T1(1,B(_wP(_yd,function(_yi){return E(_yh);})));},_yj=new T(function(){return B(unCStr("FF"));}),_yk=12,_yl=function(_ym){var _yn=new T(function(){return B(A1(_ym,_yk));});return new T1(1,B(_wP(_yj,function(_yo){return E(_yn);})));},_yp=new T(function(){return B(unCStr("CR"));}),_yq=13,_yr=function(_ys){var _yt=new T(function(){return B(A1(_ys,_yq));});return new T1(1,B(_wP(_yp,function(_yu){return E(_yt);})));},_yv=new T(function(){return B(unCStr("SI"));}),_yw=15,_yx=function(_yy){var _yz=new T(function(){return B(A1(_yy,_yw));});return new T1(1,B(_wP(_yv,function(_yA){return E(_yz);})));},_yB=new T(function(){return B(unCStr("DLE"));}),_yC=16,_yD=function(_yE){var _yF=new T(function(){return B(A1(_yE,_yC));});return new T1(1,B(_wP(_yB,function(_yG){return E(_yF);})));},_yH=new T(function(){return B(unCStr("DC1"));}),_yI=17,_yJ=function(_yK){var _yL=new T(function(){return B(A1(_yK,_yI));});return new T1(1,B(_wP(_yH,function(_yM){return E(_yL);})));},_yN=new T(function(){return B(unCStr("DC2"));}),_yO=18,_yP=function(_yQ){var _yR=new T(function(){return B(A1(_yQ,_yO));});return new T1(1,B(_wP(_yN,function(_yS){return E(_yR);})));},_yT=new T(function(){return B(unCStr("DC3"));}),_yU=19,_yV=function(_yW){var _yX=new T(function(){return B(A1(_yW,_yU));});return new T1(1,B(_wP(_yT,function(_yY){return E(_yX);})));},_yZ=new T(function(){return B(unCStr("DC4"));}),_z0=20,_z1=function(_z2){var _z3=new T(function(){return B(A1(_z2,_z0));});return new T1(1,B(_wP(_yZ,function(_z4){return E(_z3);})));},_z5=new T(function(){return B(unCStr("NAK"));}),_z6=21,_z7=function(_z8){var _z9=new T(function(){return B(A1(_z8,_z6));});return new T1(1,B(_wP(_z5,function(_za){return E(_z9);})));},_zb=new T(function(){return B(unCStr("SYN"));}),_zc=22,_zd=function(_ze){var _zf=new T(function(){return B(A1(_ze,_zc));});return new T1(1,B(_wP(_zb,function(_zg){return E(_zf);})));},_zh=new T(function(){return B(unCStr("ETB"));}),_zi=23,_zj=function(_zk){var _zl=new T(function(){return B(A1(_zk,_zi));});return new T1(1,B(_wP(_zh,function(_zm){return E(_zl);})));},_zn=new T(function(){return B(unCStr("CAN"));}),_zo=24,_zp=function(_zq){var _zr=new T(function(){return B(A1(_zq,_zo));});return new T1(1,B(_wP(_zn,function(_zs){return E(_zr);})));},_zt=new T(function(){return B(unCStr("EM"));}),_zu=25,_zv=function(_zw){var _zx=new T(function(){return B(A1(_zw,_zu));});return new T1(1,B(_wP(_zt,function(_zy){return E(_zx);})));},_zz=new T(function(){return B(unCStr("SUB"));}),_zA=26,_zB=function(_zC){var _zD=new T(function(){return B(A1(_zC,_zA));});return new T1(1,B(_wP(_zz,function(_zE){return E(_zD);})));},_zF=new T(function(){return B(unCStr("ESC"));}),_zG=27,_zH=function(_zI){var _zJ=new T(function(){return B(A1(_zI,_zG));});return new T1(1,B(_wP(_zF,function(_zK){return E(_zJ);})));},_zL=new T(function(){return B(unCStr("FS"));}),_zM=28,_zN=function(_zO){var _zP=new T(function(){return B(A1(_zO,_zM));});return new T1(1,B(_wP(_zL,function(_zQ){return E(_zP);})));},_zR=new T(function(){return B(unCStr("GS"));}),_zS=29,_zT=function(_zU){var _zV=new T(function(){return B(A1(_zU,_zS));});return new T1(1,B(_wP(_zR,function(_zW){return E(_zV);})));},_zX=new T(function(){return B(unCStr("RS"));}),_zY=30,_zZ=function(_A0){var _A1=new T(function(){return B(A1(_A0,_zY));});return new T1(1,B(_wP(_zX,function(_A2){return E(_A1);})));},_A3=new T(function(){return B(unCStr("US"));}),_A4=31,_A5=function(_A6){var _A7=new T(function(){return B(A1(_A6,_A4));});return new T1(1,B(_wP(_A3,function(_A8){return E(_A7);})));},_A9=new T(function(){return B(unCStr("SP"));}),_Aa=32,_Ab=function(_Ac){var _Ad=new T(function(){return B(A1(_Ac,_Aa));});return new T1(1,B(_wP(_A9,function(_Ae){return E(_Ad);})));},_Af=new T(function(){return B(unCStr("DEL"));}),_Ag=127,_Ah=function(_Ai){var _Aj=new T(function(){return B(A1(_Ai,_Ag));});return new T1(1,B(_wP(_Af,function(_Ak){return E(_Aj);})));},_Al=new T2(1,_Ah,_S),_Am=new T2(1,_Ab,_Al),_An=new T2(1,_A5,_Am),_Ao=new T2(1,_zZ,_An),_Ap=new T2(1,_zT,_Ao),_Aq=new T2(1,_zN,_Ap),_Ar=new T2(1,_zH,_Aq),_As=new T2(1,_zB,_Ar),_At=new T2(1,_zv,_As),_Au=new T2(1,_zp,_At),_Av=new T2(1,_zj,_Au),_Aw=new T2(1,_zd,_Av),_Ax=new T2(1,_z7,_Aw),_Ay=new T2(1,_z1,_Ax),_Az=new T2(1,_yV,_Ay),_AA=new T2(1,_yP,_Az),_AB=new T2(1,_yJ,_AA),_AC=new T2(1,_yD,_AB),_AD=new T2(1,_yx,_AC),_AE=new T2(1,_yr,_AD),_AF=new T2(1,_yl,_AE),_AG=new T2(1,_yf,_AF),_AH=new T2(1,_y9,_AG),_AI=new T2(1,_y3,_AH),_AJ=new T2(1,_xX,_AI),_AK=new T2(1,_xR,_AJ),_AL=new T2(1,_xL,_AK),_AM=new T2(1,_xF,_AL),_AN=new T2(1,_xz,_AM),_AO=new T2(1,_xt,_AN),_AP=new T2(1,_xn,_AO),_AQ=new T2(1,_xh,_AP),_AR=new T2(1,_xd,_AQ),_AS=new T(function(){return B(_wH(_AR));}),_AT=34,_AU=new T1(0,1114111),_AV=92,_AW=39,_AX=function(_AY){var _AZ=new T(function(){return B(A1(_AY,_xQ));}),_B0=new T(function(){return B(A1(_AY,_xW));}),_B1=new T(function(){return B(A1(_AY,_y2));}),_B2=new T(function(){return B(A1(_AY,_y8));}),_B3=new T(function(){return B(A1(_AY,_ye));}),_B4=new T(function(){return B(A1(_AY,_yk));}),_B5=new T(function(){return B(A1(_AY,_yq));}),_B6=new T(function(){return B(A1(_AY,_AV));}),_B7=new T(function(){return B(A1(_AY,_AW));}),_B8=new T(function(){return B(A1(_AY,_AT));}),_B9=new T(function(){var _Ba=function(_Bb){var _Bc=new T(function(){return B(_aQ(E(_Bb)));}),_Bd=function(_Be){var _Bf=B(_vQ(_Bc,_Be));if(!B(_ey(_Bf,_AU))){return new T0(2);}else{return new F(function(){return A1(_AY,new T(function(){var _Bg=B(_b9(_Bf));if(_Bg>>>0>1114111){return B(_wD(_Bg));}else{return _Bg;}}));});}};return new T1(1,B(_um(_Bb,_Bd)));},_Bh=new T(function(){var _Bi=new T(function(){return B(A1(_AY,_A4));}),_Bj=new T(function(){return B(A1(_AY,_zY));}),_Bk=new T(function(){return B(A1(_AY,_zS));}),_Bl=new T(function(){return B(A1(_AY,_zM));}),_Bm=new T(function(){return B(A1(_AY,_zG));}),_Bn=new T(function(){return B(A1(_AY,_zA));}),_Bo=new T(function(){return B(A1(_AY,_zu));}),_Bp=new T(function(){return B(A1(_AY,_zo));}),_Bq=new T(function(){return B(A1(_AY,_zi));}),_Br=new T(function(){return B(A1(_AY,_zc));}),_Bs=new T(function(){return B(A1(_AY,_z6));}),_Bt=new T(function(){return B(A1(_AY,_z0));}),_Bu=new T(function(){return B(A1(_AY,_yU));}),_Bv=new T(function(){return B(A1(_AY,_yO));}),_Bw=new T(function(){return B(A1(_AY,_yI));}),_Bx=new T(function(){return B(A1(_AY,_yC));}),_By=new T(function(){return B(A1(_AY,_yw));}),_Bz=new T(function(){return B(A1(_AY,_x2));}),_BA=new T(function(){return B(A1(_AY,_xK));}),_BB=new T(function(){return B(A1(_AY,_xE));}),_BC=new T(function(){return B(A1(_AY,_xy));}),_BD=new T(function(){return B(A1(_AY,_xs));}),_BE=new T(function(){return B(A1(_AY,_xm));}),_BF=new T(function(){return B(A1(_AY,_x8));}),_BG=new T(function(){return B(A1(_AY,_xg));}),_BH=function(_BI){switch(E(_BI)){case 64:return E(_BG);case 65:return E(_BF);case 66:return E(_BE);case 67:return E(_BD);case 68:return E(_BC);case 69:return E(_BB);case 70:return E(_BA);case 71:return E(_AZ);case 72:return E(_B0);case 73:return E(_B1);case 74:return E(_B2);case 75:return E(_B3);case 76:return E(_B4);case 77:return E(_B5);case 78:return E(_Bz);case 79:return E(_By);case 80:return E(_Bx);case 81:return E(_Bw);case 82:return E(_Bv);case 83:return E(_Bu);case 84:return E(_Bt);case 85:return E(_Bs);case 86:return E(_Br);case 87:return E(_Bq);case 88:return E(_Bp);case 89:return E(_Bo);case 90:return E(_Bn);case 91:return E(_Bm);case 92:return E(_Bl);case 93:return E(_Bk);case 94:return E(_Bj);case 95:return E(_Bi);default:return new T0(2);}};return B(_sH(new T1(0,function(_BJ){return (E(_BJ)==94)?E(new T1(0,_BH)):new T0(2);}),new T(function(){return B(A1(_AS,_AY));})));});return B(_sH(new T1(1,B(_tF(_wz,_wB,_Ba))),_Bh));});return new F(function(){return _sH(new T1(0,function(_BK){switch(E(_BK)){case 34:return E(_B8);case 39:return E(_B7);case 92:return E(_B6);case 97:return E(_AZ);case 98:return E(_B0);case 102:return E(_B4);case 110:return E(_B2);case 114:return E(_B5);case 116:return E(_B1);case 118:return E(_B3);default:return new T0(2);}}),_B9);});},_BL=function(_BM){return new F(function(){return A1(_BM,_gD);});},_BN=function(_BO){var _BP=E(_BO);if(!_BP._){return E(_BL);}else{var _BQ=E(_BP.a),_BR=_BQ>>>0,_BS=new T(function(){return B(_BN(_BP.b));});if(_BR>887){var _BT=u_iswspace(_BQ);if(!E(_BT)){return E(_BL);}else{var _BU=function(_BV){var _BW=new T(function(){return B(A1(_BS,_BV));});return new T1(0,function(_BX){return E(_BW);});};return E(_BU);}}else{var _BY=E(_BR);if(_BY==32){var _BZ=function(_C0){var _C1=new T(function(){return B(A1(_BS,_C0));});return new T1(0,function(_C2){return E(_C1);});};return E(_BZ);}else{if(_BY-9>>>0>4){if(E(_BY)==160){var _C3=function(_C4){var _C5=new T(function(){return B(A1(_BS,_C4));});return new T1(0,function(_C6){return E(_C5);});};return E(_C3);}else{return E(_BL);}}else{var _C7=function(_C8){var _C9=new T(function(){return B(A1(_BS,_C8));});return new T1(0,function(_Ca){return E(_C9);});};return E(_C7);}}}}},_Cb=function(_Cc){var _Cd=new T(function(){return B(_Cb(_Cc));}),_Ce=function(_Cf){return (E(_Cf)==92)?E(_Cd):new T0(2);},_Cg=function(_Ch){return E(new T1(0,_Ce));},_Ci=new T1(1,function(_Cj){return new F(function(){return A2(_BN,_Cj,_Cg);});}),_Ck=new T(function(){return B(_AX(function(_Cl){return new F(function(){return A1(_Cc,new T2(0,_Cl,_wt));});}));}),_Cm=function(_Cn){var _Co=E(_Cn);if(_Co==38){return E(_Cd);}else{var _Cp=_Co>>>0;if(_Cp>887){var _Cq=u_iswspace(_Co);return (E(_Cq)==0)?new T0(2):E(_Ci);}else{var _Cr=E(_Cp);return (_Cr==32)?E(_Ci):(_Cr-9>>>0>4)?(E(_Cr)==160)?E(_Ci):new T0(2):E(_Ci);}}};return new F(function(){return _sH(new T1(0,function(_Cs){return (E(_Cs)==92)?E(new T1(0,_Cm)):new T0(2);}),new T1(0,function(_Ct){var _Cu=E(_Ct);if(E(_Cu)==92){return E(_Ck);}else{return new F(function(){return A1(_Cc,new T2(0,_Cu,_ws));});}}));});},_Cv=function(_Cw,_Cx){var _Cy=new T(function(){return B(A1(_Cx,new T1(1,new T(function(){return B(A1(_Cw,_S));}))));}),_Cz=function(_CA){var _CB=E(_CA),_CC=E(_CB.a);if(E(_CC)==34){if(!E(_CB.b)){return E(_Cy);}else{return new F(function(){return _Cv(function(_CD){return new F(function(){return A1(_Cw,new T2(1,_CC,_CD));});},_Cx);});}}else{return new F(function(){return _Cv(function(_CE){return new F(function(){return A1(_Cw,new T2(1,_CC,_CE));});},_Cx);});}};return new F(function(){return _Cb(_Cz);});},_CF=new T(function(){return B(unCStr("_\'"));}),_CG=function(_CH){var _CI=u_iswalnum(_CH);if(!E(_CI)){return new F(function(){return _4A(_h6,_CH,_CF);});}else{return true;}},_CJ=function(_CK){return new F(function(){return _CG(E(_CK));});},_CL=new T(function(){return B(unCStr(",;()[]{}`"));}),_CM=new T(function(){return B(unCStr("=>"));}),_CN=new T2(1,_CM,_S),_CO=new T(function(){return B(unCStr("~"));}),_CP=new T2(1,_CO,_CN),_CQ=new T(function(){return B(unCStr("@"));}),_CR=new T2(1,_CQ,_CP),_CS=new T(function(){return B(unCStr("->"));}),_CT=new T2(1,_CS,_CR),_CU=new T(function(){return B(unCStr("<-"));}),_CV=new T2(1,_CU,_CT),_CW=new T(function(){return B(unCStr("|"));}),_CX=new T2(1,_CW,_CV),_CY=new T(function(){return B(unCStr("\\"));}),_CZ=new T2(1,_CY,_CX),_D0=new T(function(){return B(unCStr("="));}),_D1=new T2(1,_D0,_CZ),_D2=new T(function(){return B(unCStr("::"));}),_D3=new T2(1,_D2,_D1),_D4=new T(function(){return B(unCStr(".."));}),_D5=new T2(1,_D4,_D3),_D6=function(_D7){var _D8=new T(function(){return B(A1(_D7,_uj));}),_D9=new T(function(){var _Da=new T(function(){var _Db=function(_Dc){var _Dd=new T(function(){return B(A1(_D7,new T1(0,_Dc)));});return new T1(0,function(_De){return (E(_De)==39)?E(_Dd):new T0(2);});};return B(_AX(_Db));}),_Df=function(_Dg){var _Dh=E(_Dg);switch(E(_Dh)){case 39:return new T0(2);case 92:return E(_Da);default:var _Di=new T(function(){return B(A1(_D7,new T1(0,_Dh)));});return new T1(0,function(_Dj){return (E(_Dj)==39)?E(_Di):new T0(2);});}},_Dk=new T(function(){var _Dl=new T(function(){return B(_Cv(_5U,_D7));}),_Dm=new T(function(){var _Dn=new T(function(){var _Do=new T(function(){var _Dp=function(_Dq){var _Dr=E(_Dq),_Ds=u_iswalpha(_Dr);return (E(_Ds)==0)?(E(_Dr)==95)?new T1(1,B(_u5(_CJ,function(_Dt){return new F(function(){return A1(_D7,new T1(3,new T2(1,_Dr,_Dt)));});}))):new T0(2):new T1(1,B(_u5(_CJ,function(_Du){return new F(function(){return A1(_D7,new T1(3,new T2(1,_Dr,_Du)));});})));};return B(_sH(new T1(0,_Dp),new T(function(){return new T1(1,B(_tF(_vh,_wn,_D7)));})));}),_Dv=function(_Dw){return (!B(_4A(_h6,_Dw,_wp)))?new T0(2):new T1(1,B(_u5(_wq,function(_Dx){var _Dy=new T2(1,_Dw,_Dx);if(!B(_4A(_qd,_Dy,_D5))){return new F(function(){return A1(_D7,new T1(4,_Dy));});}else{return new F(function(){return A1(_D7,new T1(2,_Dy));});}})));};return B(_sH(new T1(0,_Dv),_Do));});return B(_sH(new T1(0,function(_Dz){if(!B(_4A(_h6,_Dz,_CL))){return new T0(2);}else{return new F(function(){return A1(_D7,new T1(2,new T2(1,_Dz,_S)));});}}),_Dn));});return B(_sH(new T1(0,function(_DA){return (E(_DA)==34)?E(_Dl):new T0(2);}),_Dm));});return B(_sH(new T1(0,function(_DB){return (E(_DB)==39)?E(new T1(0,_Df)):new T0(2);}),_Dk));});return new F(function(){return _sH(new T1(1,function(_DC){return (E(_DC)._==0)?E(_D8):new T0(2);}),_D9);});},_DD=0,_DE=function(_DF,_DG){var _DH=new T(function(){var _DI=new T(function(){var _DJ=function(_DK){var _DL=new T(function(){var _DM=new T(function(){return B(A1(_DG,_DK));});return B(_D6(function(_DN){var _DO=E(_DN);return (_DO._==2)?(!B(_qN(_DO.a,_tk)))?new T0(2):E(_DM):new T0(2);}));}),_DP=function(_DQ){return E(_DL);};return new T1(1,function(_DR){return new F(function(){return A2(_BN,_DR,_DP);});});};return B(A2(_DF,_DD,_DJ));});return B(_D6(function(_DS){var _DT=E(_DS);return (_DT._==2)?(!B(_qN(_DT.a,_tj)))?new T0(2):E(_DI):new T0(2);}));}),_DU=function(_DV){return E(_DH);};return function(_DW){return new F(function(){return A2(_BN,_DW,_DU);});};},_DX=function(_DY,_DZ){var _E0=function(_E1){var _E2=new T(function(){return B(A1(_DY,_E1));}),_E3=function(_E4){return new F(function(){return _sH(B(A1(_E2,_E4)),new T(function(){return new T1(1,B(_DE(_E0,_E4)));}));});};return E(_E3);},_E5=new T(function(){return B(A1(_DY,_DZ));}),_E6=function(_E7){return new F(function(){return _sH(B(A1(_E5,_E7)),new T(function(){return new T1(1,B(_DE(_E0,_E7)));}));});};return E(_E6);},_E8=0,_E9=function(_Ea,_Eb){return new F(function(){return A1(_Eb,_E8);});},_Ec=new T(function(){return B(unCStr("Fr"));}),_Ed=new T2(0,_Ec,_E9),_Ee=1,_Ef=function(_Eg,_Eh){return new F(function(){return A1(_Eh,_Ee);});},_Ei=new T(function(){return B(unCStr("Bl"));}),_Ej=new T2(0,_Ei,_Ef),_Ek=2,_El=function(_Em,_En){return new F(function(){return A1(_En,_Ek);});},_Eo=new T(function(){return B(unCStr("Ex"));}),_Ep=new T2(0,_Eo,_El),_Eq=3,_Er=function(_Es,_Et){return new F(function(){return A1(_Et,_Eq);});},_Eu=new T(function(){return B(unCStr("Mv"));}),_Ev=new T2(0,_Eu,_Er),_Ew=4,_Ex=function(_Ey,_Ez){return new F(function(){return A1(_Ez,_Ew);});},_EA=new T(function(){return B(unCStr("Pn"));}),_EB=new T2(0,_EA,_Ex),_EC=8,_ED=function(_EE,_EF){return new F(function(){return A1(_EF,_EC);});},_EG=new T(function(){return B(unCStr("DF"));}),_EH=new T2(0,_EG,_ED),_EI=new T2(1,_EH,_S),_EJ=7,_EK=function(_EL,_EM){return new F(function(){return A1(_EM,_EJ);});},_EN=new T(function(){return B(unCStr("DB"));}),_EO=new T2(0,_EN,_EK),_EP=new T2(1,_EO,_EI),_EQ=6,_ER=function(_ES,_ET){return new F(function(){return A1(_ET,_EQ);});},_EU=new T(function(){return B(unCStr("Cm"));}),_EV=new T2(0,_EU,_ER),_EW=new T2(1,_EV,_EP),_EX=5,_EY=function(_EZ,_F0){return new F(function(){return A1(_F0,_EX);});},_F1=new T(function(){return B(unCStr("Wn"));}),_F2=new T2(0,_F1,_EY),_F3=new T2(1,_F2,_EW),_F4=new T2(1,_EB,_F3),_F5=new T2(1,_Ev,_F4),_F6=new T2(1,_Ep,_F5),_F7=new T2(1,_Ej,_F6),_F8=new T2(1,_Ed,_F7),_F9=function(_Fa,_Fb,_Fc){var _Fd=E(_Fa);if(!_Fd._){return new T0(2);}else{var _Fe=E(_Fd.a),_Ff=_Fe.a,_Fg=new T(function(){return B(A2(_Fe.b,_Fb,_Fc));}),_Fh=new T(function(){return B(_D6(function(_Fi){var _Fj=E(_Fi);switch(_Fj._){case 3:return (!B(_qN(_Ff,_Fj.a)))?new T0(2):E(_Fg);case 4:return (!B(_qN(_Ff,_Fj.a)))?new T0(2):E(_Fg);default:return new T0(2);}}));}),_Fk=function(_Fl){return E(_Fh);};return new F(function(){return _sH(new T1(1,function(_Fm){return new F(function(){return A2(_BN,_Fm,_Fk);});}),new T(function(){return B(_F9(_Fd.b,_Fb,_Fc));}));});}},_Fn=function(_Fo,_Fp){return new F(function(){return _F9(_F8,_Fo,_Fp);});},_Fq=function(_Fr){var _Fs=function(_Ft){return E(new T2(3,_Fr,_tw));};return new T1(1,function(_Fu){return new F(function(){return A2(_BN,_Fu,_Fs);});});},_Fv=new T(function(){return B(A3(_DX,_Fn,_DD,_Fq));}),_Fw=new T(function(){return B(unCStr("empty"));}),_Fx=new T2(1,_Fw,_S),_Fy=new T(function(){return B(err(_sq));}),_Fz=new T(function(){return B(err(_ss));}),_FA=function(_FB,_FC){var _FD=function(_FE,_FF){var _FG=function(_FH){return new F(function(){return A1(_FF,new T(function(){return  -E(_FH);}));});},_FI=new T(function(){return B(_D6(function(_FJ){return new F(function(){return A3(_FB,_FJ,_FE,_FG);});}));}),_FK=function(_FL){return E(_FI);},_FM=function(_FN){return new F(function(){return A2(_BN,_FN,_FK);});},_FO=new T(function(){return B(_D6(function(_FP){var _FQ=E(_FP);if(_FQ._==4){var _FR=E(_FQ.a);if(!_FR._){return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}else{if(E(_FR.a)==45){if(!E(_FR.b)._){return E(new T1(1,_FM));}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}));}),_FS=function(_FT){return E(_FO);};return new T1(1,function(_FU){return new F(function(){return A2(_BN,_FU,_FS);});});};return new F(function(){return _DX(_FD,_FC);});},_FV=function(_FW){var _FX=E(_FW);if(!_FX._){var _FY=_FX.b,_FZ=new T(function(){return B(_vz(new T(function(){return B(_aQ(E(_FX.a)));}),new T(function(){return B(_ms(_FY,0));},1),B(_6d(_vp,_FY))));});return new T1(1,_FZ);}else{return (E(_FX.b)._==0)?(E(_FX.c)._==0)?new T1(1,new T(function(){return B(_vQ(_vo,_FX.a));})):__Z:__Z;}},_G0=function(_G1,_G2){return new T0(2);},_G3=function(_G4){var _G5=E(_G4);if(_G5._==5){var _G6=B(_FV(_G5.a));if(!_G6._){return E(_G0);}else{var _G7=new T(function(){return B(_b9(_G6.a));});return function(_G8,_G9){return new F(function(){return A1(_G9,_G7);});};}}else{return E(_G0);}},_Ga=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_Gb=new T2(1,_y,_S),_Gc=function(_Gd){while(1){var _Ge=B((function(_Gf){var _Gg=E(_Gf);if(!_Gg._){return __Z;}else{var _Gh=_Gg.b,_Gi=E(_Gg.a);if(!E(_Gi.b)._){return new T2(1,_Gi.a,new T(function(){return B(_Gc(_Gh));}));}else{_Gd=_Gh;return __continue;}}})(_Gd));if(_Ge!=__continue){return _Ge;}}},_Gj=function(_Gk,_Gl){while(1){var _Gm=E(_Gk);if(!_Gm._){return E(_Gl);}else{var _Gn=new T2(1,_Gm.a,_Gl);_Gk=_Gm.b;_Gl=_Gn;continue;}}},_Go=function(_Gp,_Gq){var _Gr=E(_Gp);if(!_Gr._){return __Z;}else{var _Gs=E(_Gq);return (_Gs._==0)?__Z:new T2(1,new T2(0,_Gr.a,_Gs.a),new T(function(){return B(_Go(_Gr.b,_Gs.b));}));}},_Gt=function(_Gu,_Gv,_Gw){while(1){var _Gx=B((function(_Gy,_Gz,_GA){var _GB=E(_GA);if(!_GB._){return E(_Gz);}else{var _GC=_GB.a,_GD=_GB.b,_GE=B(_sk(_qd,_GC,_s9));if(!_GE._){var _GF=E(_Fx);}else{var _GF=E(_GE.a);}if(!B(_qS(_GF,_Fx))){var _GG=B(_Gj(B(_Go(B(_Gj(_Gz,_S)),new T(function(){return B(_Gj(_GF,_S));},1))),_S)),_GH=B(_ms(_GG,0)),_GI=new T(function(){var _GJ=B(_6d(_si,_GG));if(!_GJ._){return __Z;}else{var _GK=_GJ.a,_GL=E(_GJ.b);if(!_GL._){return __Z;}else{var _GM=_GL.a;if(!E(_GL.b)._){if(!B(_qN(_GC,_rL))){if(!B(_qN(_GC,_rK))){if(!B(_qN(_GC,_rJ))){if(!B(_qN(_GC,_rN))){if(!B(_qN(_GC,_rM))){return __Z;}else{if(!B(_qN(_GK,_su))){if(!B(_qN(_GM,_su))){return E(_sv);}else{return E(_su);}}else{return E(_su);}}}else{var _GN=B(_rx(new T2(0,new T(function(){var _GO=E(_GK);if(!_GO._){return E(_ng);}else{return E(_GO.a);}}),new T(function(){var _GP=B(_Gc(B(_sx(_Fv,_GM))));if(!_GP._){return E(_sr);}else{if(!E(_GP.b)._){return E(_GP.a);}else{return E(_st);}}})),E(E(_Gy).a).b)),_GQ=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_GR){return new F(function(){return _A(0,E(_GN.a),_GR);});},new T2(1,function(_GS){return new F(function(){return _A(0,E(_GN.b),_GS);});},_S)),_Gb));});return new T2(1,_z,_GQ);}}else{return new T2(1,new T(function(){var _GT=B(_Gc(B(_sx(_Ga,_GK))));if(!_GT._){return E(_Fy);}else{if(!E(_GT.b)._){var _GU=B(_Gc(B(_sx(_Ga,_GM))));if(!_GU._){return E(_Fy);}else{if(!E(_GU.b)._){return E(B(_6Q(B(_6Q(E(E(_Gy).a).b,E(_GU.a))),E(_GT.a))).a);}else{return E(_Fz);}}}else{return E(_Fz);}}}),_S);}}else{if(!B(_qN(_GK,_GM))){return E(_sv);}else{return E(_su);}}}else{if(!B(_qN(_GK,_su))){return E(_sv);}else{if(!B(_qN(_GM,_su))){return E(_sv);}else{return E(_su);}}}}else{return __Z;}}}});if(_GH>0){var _GV=_Gy,_GW=B(_q(B(_Gj(B(_rD(_GH,B(_Gj(_Gz,_S)))),_S)),new T2(1,_GI,_S)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}else{var _GV=_Gy,_GW=B(_q(B(_Gj(B(_Gj(_Gz,_S)),_S)),new T2(1,_GI,_S)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}}else{var _GV=_Gy,_GW=B(_q(_Gz,new T2(1,_GC,_S)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}}})(_Gu,_Gv,_Gw));if(_Gx!=__continue){return _Gx;}}},_GX=new T(function(){return B(_e6("Event.hs:(86,1)-(90,73)|function addMemory"));}),_GY=function(_GZ,_H0){var _H1=E(_GZ),_H2=E(_H0);if(!B(_qN(_H1.a,_H2.a))){return false;}else{return new F(function(){return _qN(_H1.b,_H2.b);});}},_H3=new T2(1,_S,_S),_H4=function(_H5,_H6,_H7){var _H8=E(_H7);if(!_H8._){return new T2(0,new T2(1,_H6,_S),_S);}else{var _H9=E(_H6),_Ha=new T(function(){var _Hb=B(_H4(_H5,_H8.a,_H8.b));return new T2(0,_Hb.a,_Hb.b);});return (_H5!=_H9)?new T2(0,new T2(1,_H9,new T(function(){return E(E(_Ha).a);})),new T(function(){return E(E(_Ha).b);})):new T2(0,_S,new T2(1,new T(function(){return E(E(_Ha).a);}),new T(function(){return E(E(_Ha).b);})));}},_Hc=32,_Hd=function(_He){var _Hf=E(_He);if(!_Hf._){return __Z;}else{var _Hg=new T(function(){return B(_q(_Hf.a,new T(function(){return B(_Hd(_Hf.b));},1)));});return new T2(1,_Hc,_Hg);}},_Hh=function(_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC){while(1){var _HD=B((function(_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_HQ,_HR,_HS,_HT,_HU,_HV,_HW,_HX,_HY){var _HZ=E(_HE);if(!_HZ._){return {_:0,a:_HF,b:_HG,c:_HH,d:_HI,e:_HJ,f:_HK,g:_HL,h:_HM,i:_HN,j:_HO,k:_HP,l:_HQ,m:_HR,n:_HS,o:_HT,p:_HU,q:_HV,r:_HW,s:_HX,t:_HY};}else{var _I0=_HZ.a,_I1=E(_HZ.b);if(!_I1._){return E(_GX);}else{var _I2=new T(function(){var _I3=E(_I1.a);if(!_I3._){var _I4=B(_Gt({_:0,a:E(_HF),b:E(_HG),c:E(_HH),d:E(_HI),e:E(_HJ),f:E(_HK),g:E(_HL),h:E(_HM),i:_HN,j:_HO,k:_HP,l:_HQ,m:E(_HR),n:_HS,o:E(_HT),p:E(_HU),q:E(_HV),r:_HW,s:E(_HX),t:E(_HY)},_S,_H3));if(!_I4._){return __Z;}else{return B(_q(_I4.a,new T(function(){return B(_Hd(_I4.b));},1)));}}else{var _I5=_I3.a,_I6=E(_I3.b);if(!_I6._){var _I7=B(_Gt({_:0,a:E(_HF),b:E(_HG),c:E(_HH),d:E(_HI),e:E(_HJ),f:E(_HK),g:E(_HL),h:E(_HM),i:_HN,j:_HO,k:_HP,l:_HQ,m:E(_HR),n:_HS,o:E(_HT),p:E(_HU),q:E(_HV),r:_HW,s:E(_HX),t:E(_HY)},_S,new T2(1,new T2(1,_I5,_S),_S)));if(!_I7._){return __Z;}else{return B(_q(_I7.a,new T(function(){return B(_Hd(_I7.b));},1)));}}else{var _I8=E(_I5),_I9=new T(function(){var _Ia=B(_H4(95,_I6.a,_I6.b));return new T2(0,_Ia.a,_Ia.b);});if(E(_I8)==95){var _Ib=B(_Gt({_:0,a:E(_HF),b:E(_HG),c:E(_HH),d:E(_HI),e:E(_HJ),f:E(_HK),g:E(_HL),h:E(_HM),i:_HN,j:_HO,k:_HP,l:_HQ,m:E(_HR),n:_HS,o:E(_HT),p:E(_HU),q:E(_HV),r:_HW,s:E(_HX),t:E(_HY)},_S,new T2(1,_S,new T2(1,new T(function(){return E(E(_I9).a);}),new T(function(){return E(E(_I9).b);})))));if(!_Ib._){return __Z;}else{return B(_q(_Ib.a,new T(function(){return B(_Hd(_Ib.b));},1)));}}else{var _Ic=B(_Gt({_:0,a:E(_HF),b:E(_HG),c:E(_HH),d:E(_HI),e:E(_HJ),f:E(_HK),g:E(_HL),h:E(_HM),i:_HN,j:_HO,k:_HP,l:_HQ,m:E(_HR),n:_HS,o:E(_HT),p:E(_HU),q:E(_HV),r:_HW,s:E(_HX),t:E(_HY)},_S,new T2(1,new T2(1,_I8,new T(function(){return E(E(_I9).a);})),new T(function(){return E(E(_I9).b);}))));if(!_Ic._){return __Z;}else{return B(_q(_Ic.a,new T(function(){return B(_Hd(_Ic.b));},1)));}}}}}),_Id=_HF,_Ie=_HG,_If=_HH,_Ig=_HI,_Ih=_HJ,_Ii=_HK,_Ij=_HM,_Ik=_HN,_Il=_HO,_Im=_HP,_In=_HQ,_Io=_HR,_Ip=_HS,_Iq=_HT,_Ir=_HU,_Is=_HV,_It=_HW,_Iu=_HX,_Iv=_HY;_Hi=_I1.b;_Hj=_Id;_Hk=_Ie;_Hl=_If;_Hm=_Ig;_Hn=_Ih;_Ho=_Ii;_Hp=new T2(1,new T2(0,_I0,_I2),new T(function(){var _Iw=B(_sk(_qd,_I0,_HL));if(!_Iw._){var _Ix=__Z;}else{var _Ix=E(_Iw.a);}if(!B(_qN(_Ix,_S))){return B(_qG(_GY,new T2(0,_I0,_Ix),_HL));}else{return E(_HL);}}));_Hq=_Ij;_Hr=_Ik;_Hs=_Il;_Ht=_Im;_Hu=_In;_Hv=_Io;_Hw=_Ip;_Hx=_Iq;_Hy=_Ir;_Hz=_Is;_HA=_It;_HB=_Iu;_HC=_Iv;return __continue;}}})(_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC));if(_HD!=__continue){return _HD;}}},_Iy=function(_Iz){var _IA=E(_Iz);if(!_IA._){return new T2(0,_S,_S);}else{var _IB=E(_IA.a),_IC=new T(function(){var _ID=B(_Iy(_IA.b));return new T2(0,_ID.a,_ID.b);});return new T2(0,new T2(1,_IB.a,new T(function(){return E(E(_IC).a);})),new T2(1,_IB.b,new T(function(){return E(E(_IC).b);})));}},_IE=function(_IF,_IG,_IH){while(1){var _II=B((function(_IJ,_IK,_IL){var _IM=E(_IL);if(!_IM._){return __Z;}else{var _IN=_IM.b;if(_IK!=E(_IM.a)){var _IO=_IJ+1|0,_IP=_IK;_IF=_IO;_IG=_IP;_IH=_IN;return __continue;}else{return new T2(1,_IJ,new T(function(){return B(_IE(_IJ+1|0,_IK,_IN));}));}}})(_IF,_IG,_IH));if(_II!=__continue){return _II;}}},_IQ=function(_IR,_IS,_IT){var _IU=E(_IT);if(!_IU._){return __Z;}else{var _IV=_IU.b,_IW=E(_IS);if(_IW!=E(_IU.a)){return new F(function(){return _IE(_IR+1|0,_IW,_IV);});}else{return new T2(1,_IR,new T(function(){return B(_IE(_IR+1|0,_IW,_IV));}));}}},_IX=function(_IY,_IZ,_J0,_J1){var _J2=E(_J1);if(!_J2._){return __Z;}else{var _J3=_J2.b;return (!B(_4A(_3L,_IY,_J0)))?new T2(1,_J2.a,new T(function(){return B(_IX(_IY+1|0,_IZ,_J0,_J3));})):new T2(1,_IZ,new T(function(){return B(_IX(_IY+1|0,_IZ,_J0,_J3));}));}},_J4=function(_J5,_J6,_J7){var _J8=E(_J7);if(!_J8._){return __Z;}else{var _J9=new T(function(){var _Ja=B(_Iy(_J8.a)),_Jb=_Ja.a,_Jc=new T(function(){return B(_IX(0,_J6,new T(function(){return B(_IQ(0,_J5,_Jb));}),_Ja.b));},1);return B(_Go(_Jb,_Jc));});return new T2(1,_J9,new T(function(){return B(_J4(_J5,_J6,_J8.b));}));}},_Jd=function(_Je){var _Jf=E(_Je);return (_Jf._==0)?E(_ng):E(_Jf.a);},_Jg=new T(function(){return B(_e6("Event.hs:(59,1)-(62,93)|function changeType"));}),_Jh=new T(function(){return B(_e6("Event.hs:56:16-116|case"));}),_Ji=new T(function(){return B(unCStr("Wn"));}),_Jj=new T(function(){return B(unCStr("Pn"));}),_Jk=new T(function(){return B(unCStr("Mv"));}),_Jl=new T(function(){return B(unCStr("Fr"));}),_Jm=new T(function(){return B(unCStr("Ex"));}),_Jn=new T(function(){return B(unCStr("DF"));}),_Jo=new T(function(){return B(unCStr("DB"));}),_Jp=new T(function(){return B(unCStr("Cm"));}),_Jq=new T(function(){return B(unCStr("Bl"));}),_Jr=function(_Js){return (!B(_qN(_Js,_Jq)))?(!B(_qN(_Js,_Jp)))?(!B(_qN(_Js,_Jo)))?(!B(_qN(_Js,_Jn)))?(!B(_qN(_Js,_Jm)))?(!B(_qN(_Js,_Jl)))?(!B(_qN(_Js,_Jk)))?(!B(_qN(_Js,_Jj)))?(!B(_qN(_Js,_Ji)))?E(_Jh):5:4:3:0:2:8:7:6:1;},_Jt=function(_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO){while(1){var _JP=B((function(_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0,_K1,_K2,_K3,_K4,_K5,_K6,_K7,_K8,_K9,_Ka){var _Kb=E(_JQ);if(!_Kb._){return {_:0,a:_JR,b:_JS,c:_JT,d:_JU,e:_JV,f:_JW,g:_JX,h:_JY,i:_JZ,j:_K0,k:_K1,l:_K2,m:_K3,n:_K4,o:_K5,p:_K6,q:_K7,r:_K8,s:_K9,t:_Ka};}else{var _Kc=E(_Kb.b);if(!_Kc._){return E(_Jg);}else{var _Kd=E(_JR),_Ke=_JS,_Kf=_JT,_Kg=_JU,_Kh=_JV,_Ki=_JW,_Kj=_JX,_Kk=_JY,_Kl=_JZ,_Km=_K0,_Kn=_K1,_Ko=_K2,_Kp=_K3,_Kq=_K4,_Kr=_K5,_Ks=_K6,_Kt=_K7,_Ku=_K8,_Kv=_K9,_Kw=_Ka;_Ju=_Kc.b;_Jv={_:0,a:E(_Kd.a),b:E(B(_J4(new T(function(){return B(_Jd(_Kb.a));}),new T(function(){return B(_Jr(_Kc.a));}),_Kd.b))),c:_Kd.c,d:_Kd.d,e:_Kd.e,f:E(_Kd.f),g:_Kd.g,h:E(_Kd.h),i:E(_Kd.i),j:E(_Kd.j)};_Jw=_Ke;_Jx=_Kf;_Jy=_Kg;_Jz=_Kh;_JA=_Ki;_JB=_Kj;_JC=_Kk;_JD=_Kl;_JE=_Km;_JF=_Kn;_JG=_Ko;_JH=_Kp;_JI=_Kq;_JJ=_Kr;_JK=_Ks;_JL=_Kt;_JM=_Ku;_JN=_Kv;_JO=_Kw;return __continue;}}})(_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO));if(_JP!=__continue){return _JP;}}},_Kx=function(_Ky,_Kz){while(1){var _KA=E(_Kz);if(!_KA._){return __Z;}else{var _KB=_KA.b,_KC=E(_Ky);if(_KC==1){return E(_KB);}else{_Ky=_KC-1|0;_Kz=_KB;continue;}}}},_KD=function(_KE,_KF){while(1){var _KG=E(_KF);if(!_KG._){return __Z;}else{var _KH=_KG.b,_KI=E(_KE);if(_KI==1){return E(_KH);}else{_KE=_KI-1|0;_KF=_KH;continue;}}}},_KJ=function(_KK,_KL,_KM,_KN,_KO){var _KP=new T(function(){var _KQ=E(_KK),_KR=new T(function(){return B(_6Q(_KO,_KL));}),_KS=new T2(1,new T2(0,_KM,_KN),new T(function(){var _KT=_KQ+1|0;if(_KT>0){return B(_KD(_KT,_KR));}else{return E(_KR);}}));if(0>=_KQ){return E(_KS);}else{var _KU=function(_KV,_KW){var _KX=E(_KV);if(!_KX._){return E(_KS);}else{var _KY=_KX.a,_KZ=E(_KW);return (_KZ==1)?new T2(1,_KY,_KS):new T2(1,_KY,new T(function(){return B(_KU(_KX.b,_KZ-1|0));}));}};return B(_KU(_KR,_KQ));}}),_L0=new T2(1,_KP,new T(function(){var _L1=_KL+1|0;if(_L1>0){return B(_Kx(_L1,_KO));}else{return E(_KO);}}));if(0>=_KL){return E(_L0);}else{var _L2=function(_L3,_L4){var _L5=E(_L3);if(!_L5._){return E(_L0);}else{var _L6=_L5.a,_L7=E(_L4);return (_L7==1)?new T2(1,_L6,_L0):new T2(1,_L6,new T(function(){return B(_L2(_L5.b,_L7-1|0));}));}};return new F(function(){return _L2(_KO,_KL);});}},_L8=32,_L9=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_La=function(_Lb){return new F(function(){return _dI(new T1(0,new T(function(){return B(_dV(_Lb,_L9));})),_ds);});},_Lc=function(_Ld){return new F(function(){return _La("Event.hs:42:27-53|(x\' : y\' : _)");});},_Le=new T(function(){return B(_Lc(_));}),_Lf=function(_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA){while(1){var _LB=B((function(_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO,_LP,_LQ,_LR,_LS,_LT,_LU,_LV,_LW){var _LX=E(_LC);if(!_LX._){return {_:0,a:_LD,b:_LE,c:_LF,d:_LG,e:_LH,f:_LI,g:_LJ,h:_LK,i:_LL,j:_LM,k:_LN,l:_LO,m:_LP,n:_LQ,o:_LR,p:_LS,q:_LT,r:_LU,s:_LV,t:_LW};}else{var _LY=E(_LD),_LZ=new T(function(){var _M0=E(_LX.a);if(!_M0._){return E(_Le);}else{var _M1=E(_M0.b);if(!_M1._){return E(_Le);}else{var _M2=_M1.a,_M3=_M1.b,_M4=E(_M0.a);if(E(_M4)==44){return new T2(0,_S,new T(function(){return E(B(_H4(44,_M2,_M3)).a);}));}else{var _M5=B(_H4(44,_M2,_M3)),_M6=E(_M5.b);if(!_M6._){return E(_Le);}else{return new T2(0,new T2(1,_M4,_M5.a),_M6.a);}}}}}),_M7=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_LZ).b);})))));if(!_M7._){return E(_Fy);}else{if(!E(_M7.b)._){var _M8=new T(function(){var _M9=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_LZ).a);})))));if(!_M9._){return E(_Fy);}else{if(!E(_M9.b)._){return E(_M9.a);}else{return E(_Fz);}}},1),_Ma=_LE,_Mb=_LF,_Mc=_LG,_Md=_LH,_Me=_LI,_Mf=_LJ,_Mg=_LK,_Mh=_LL,_Mi=_LM,_Mj=_LN,_Mk=_LO,_Ml=_LP,_Mm=_LQ,_Mn=_LR,_Mo=_LS,_Mp=_LT,_Mq=_LU,_Mr=_LV,_Ms=_LW;_Lg=_LX.b;_Lh={_:0,a:E(_LY.a),b:E(B(_KJ(_M8,E(_M7.a),_L8,_E8,_LY.b))),c:_LY.c,d:_LY.d,e:_LY.e,f:E(_LY.f),g:_LY.g,h:E(_LY.h),i:E(_LY.i),j:E(_LY.j)};_Li=_Ma;_Lj=_Mb;_Lk=_Mc;_Ll=_Md;_Lm=_Me;_Ln=_Mf;_Lo=_Mg;_Lp=_Mh;_Lq=_Mi;_Lr=_Mj;_Ls=_Mk;_Lt=_Ml;_Lu=_Mm;_Lv=_Mn;_Lw=_Mo;_Lx=_Mp;_Ly=_Mq;_Lz=_Mr;_LA=_Ms;return __continue;}else{return E(_Fz);}}}})(_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA));if(_LB!=__continue){return _LB;}}},_Mt=function(_Mu,_Mv,_Mw){var _Mx=E(_Mw);return (_Mx._==0)?0:(!B(A3(_4y,_Mu,_Mv,_Mx.a)))?1+B(_Mt(_Mu,_Mv,_Mx.b))|0:0;},_My=function(_Mz,_MA){while(1){var _MB=E(_MA);if(!_MB._){return __Z;}else{var _MC=_MB.b,_MD=E(_Mz);if(_MD==1){return E(_MC);}else{_Mz=_MD-1|0;_MA=_MC;continue;}}}},_ME=function(_MF,_MG){var _MH=new T(function(){var _MI=_MF+1|0;if(_MI>0){return B(_My(_MI,_MG));}else{return E(_MG);}});if(0>=_MF){return E(_MH);}else{var _MJ=function(_MK,_ML){var _MM=E(_MK);if(!_MM._){return E(_MH);}else{var _MN=_MM.a,_MO=E(_ML);return (_MO==1)?new T2(1,_MN,_MH):new T2(1,_MN,new T(function(){return B(_MJ(_MM.b,_MO-1|0));}));}};return new F(function(){return _MJ(_MG,_MF);});}},_MP=function(_MQ,_MR){return new F(function(){return _ME(E(_MQ),_MR);});},_MS= -1,_MT=function(_MU,_MV,_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne){while(1){var _Nf=B((function(_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx,_Ny,_Nz,_NA){var _NB=E(_Ng);if(!_NB._){return {_:0,a:_Nh,b:_Ni,c:_Nj,d:_Nk,e:_Nl,f:_Nm,g:_Nn,h:_No,i:_Np,j:_Nq,k:_Nr,l:_Ns,m:_Nt,n:_Nu,o:_Nv,p:_Nw,q:_Nx,r:_Ny,s:_Nz,t:_NA};}else{var _NC=_NB.a,_ND=B(_6d(_si,_Nl)),_NE=B(_4A(_qd,_NC,_ND)),_NF=new T(function(){if(!E(_NE)){return E(_MS);}else{return B(_Mt(_qd,_NC,_ND));}});if(!E(_NE)){var _NG=E(_Nl);}else{var _NG=B(_MP(_NF,_Nl));}if(!E(_NE)){var _NH=E(_Nm);}else{var _NH=B(_MP(_NF,_Nm));}var _NI=_Nh,_NJ=_Ni,_NK=_Nj,_NL=_Nk,_NM=_Nn,_NN=_No,_NO=_Np,_NP=_Nq,_NQ=_Nr,_NR=_Ns,_NS=_Nt,_NT=_Nu,_NU=_Nv,_NV=_Nw,_NW=_Nx,_NX=_Ny,_NY=_Nz,_NZ=_NA;_MU=_NB.b;_MV=_NI;_MW=_NJ;_MX=_NK;_MY=_NL;_MZ=_NG;_N0=_NH;_N1=_NM;_N2=_NN;_N3=_NO;_N4=_NP;_N5=_NQ;_N6=_NR;_N7=_NS;_N8=_NT;_N9=_NU;_Na=_NV;_Nb=_NW;_Nc=_NX;_Nd=_NY;_Ne=_NZ;return __continue;}})(_MU,_MV,_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne));if(_Nf!=__continue){return _Nf;}}},_O0=function(_O1){var _O2=E(_O1);if(!_O2._){return new T2(0,_S,_S);}else{var _O3=E(_O2.a),_O4=new T(function(){var _O5=B(_O0(_O2.b));return new T2(0,_O5.a,_O5.b);});return new T2(0,new T2(1,_O3.a,new T(function(){return E(E(_O4).a);})),new T2(1,_O3.b,new T(function(){return E(E(_O4).b);})));}},_O6=function(_O7){return new F(function(){return _La("Event.hs:103:28-52|(c : d : _)");});},_O8=new T(function(){return B(_O6(_));}),_O9=function(_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB){while(1){var _OC=B((function(_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY,_OZ,_P0,_P1,_P2,_P3,_P4){var _P5=E(_OD);if(!_P5._){return {_:0,a:E(_OE),b:E(_OF),c:E(_OG),d:E(_OH),e:E(_OI),f:E(_OJ),g:E(_OK),h:E(_OL),i:_OM,j:_ON,k:_OO,l:_OP,m:E(_OQ),n:_OR,o:E(_OS),p:E(_OT),q:E(_OU),r:_OV,s:E({_:0,a:E(_OW),b:E(_OX),c:E(_OY),d:E(_wt),e:E(_P0),f:E(_P1),g:E(_wt),h:E(_P3)}),t:E(_P4)};}else{var _P6=new T(function(){var _P7=E(_P5.a);if(!_P7._){return E(_O8);}else{var _P8=E(_P7.b);if(!_P8._){return E(_O8);}else{var _P9=_P8.a,_Pa=_P8.b,_Pb=E(_P7.a);if(E(_Pb)==44){return new T2(0,_S,new T(function(){return E(B(_H4(44,_P9,_Pa)).a);}));}else{var _Pc=B(_H4(44,_P9,_Pa)),_Pd=E(_Pc.b);if(!_Pd._){return E(_O8);}else{return new T2(0,new T2(1,_Pb,_Pc.a),_Pd.a);}}}}}),_Pe=_OE,_Pf=_OF,_Pg=_OG,_Ph=_OH,_Pi=_OI,_Pj=_OJ,_Pk=_OK,_Pl=_OL,_Pm=_OM,_Pn=_ON,_Po=_OO,_Pp=_OP,_Pq=B(_q(_OQ,new T2(1,new T2(0,new T(function(){return E(E(_P6).a);}),new T(function(){return E(E(_P6).b);})),_S))),_Pr=_OR,_Ps=_OS,_Pt=_OT,_Pu=_OU,_Pv=_OV,_Pw=_OW,_Px=_OX,_Py=_OY,_Pz=_OZ,_PA=_P0,_PB=_P1,_PC=_P2,_PD=_P3,_PE=_P4;_Oa=_P5.b;_Ob=_Pe;_Oc=_Pf;_Od=_Pg;_Oe=_Ph;_Of=_Pi;_Og=_Pj;_Oh=_Pk;_Oi=_Pl;_Oj=_Pm;_Ok=_Pn;_Ol=_Po;_Om=_Pp;_On=_Pq;_Oo=_Pr;_Op=_Ps;_Oq=_Pt;_Or=_Pu;_Os=_Pv;_Ot=_Pw;_Ou=_Px;_Ov=_Py;_Ow=_Pz;_Ox=_PA;_Oy=_PB;_Oz=_PC;_OA=_PD;_OB=_PE;return __continue;}})(_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB));if(_OC!=__continue){return _OC;}}},_PF=function(_PG){return new F(function(){return _La("Event.hs:49:27-53|(x\' : y\' : _)");});},_PH=new T(function(){return B(_PF(_));}),_PI=function(_PJ){return new F(function(){return _La("Event.hs:50:27-55|(chs : tps : _)");});},_PK=new T(function(){return B(_PI(_));}),_PL=new T(function(){return B(_e6("Event.hs:(47,1)-(53,83)|function putCell"));}),_PM=function(_PN,_PO,_PP,_PQ,_PR,_PS,_PT,_PU,_PV,_PW,_PX,_PY,_PZ,_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7){while(1){var _Q8=B((function(_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt){var _Qu=E(_Q9);if(!_Qu._){return {_:0,a:_Qa,b:_Qb,c:_Qc,d:_Qd,e:_Qe,f:_Qf,g:_Qg,h:_Qh,i:_Qi,j:_Qj,k:_Qk,l:_Ql,m:_Qm,n:_Qn,o:_Qo,p:_Qp,q:_Qq,r:_Qr,s:_Qs,t:_Qt};}else{var _Qv=E(_Qu.b);if(!_Qv._){return E(_PL);}else{var _Qw=E(_Qa),_Qx=new T(function(){var _Qy=E(_Qu.a);if(!_Qy._){return E(_PH);}else{var _Qz=E(_Qy.b);if(!_Qz._){return E(_PH);}else{var _QA=_Qz.a,_QB=_Qz.b,_QC=E(_Qy.a);if(E(_QC)==44){return new T2(0,_S,new T(function(){return E(B(_H4(44,_QA,_QB)).a);}));}else{var _QD=B(_H4(44,_QA,_QB)),_QE=E(_QD.b);if(!_QE._){return E(_PH);}else{return new T2(0,new T2(1,_QC,_QD.a),_QE.a);}}}}}),_QF=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_Qx).b);})))));if(!_QF._){return E(_Fy);}else{if(!E(_QF.b)._){var _QG=new T(function(){var _QH=E(_Qv.a);if(!_QH._){return E(_PK);}else{var _QI=E(_QH.b);if(!_QI._){return E(_PK);}else{var _QJ=_QI.a,_QK=_QI.b,_QL=E(_QH.a);if(E(_QL)==44){return new T2(0,_S,new T(function(){return E(B(_H4(44,_QJ,_QK)).a);}));}else{var _QM=B(_H4(44,_QJ,_QK)),_QN=E(_QM.b);if(!_QN._){return E(_PK);}else{return new T2(0,new T2(1,_QL,_QM.a),_QN.a);}}}}}),_QO=new T(function(){var _QP=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_Qx).a);})))));if(!_QP._){return E(_Fy);}else{if(!E(_QP.b)._){return E(_QP.a);}else{return E(_Fz);}}},1),_QQ=_Qb,_QR=_Qc,_QS=_Qd,_QT=_Qe,_QU=_Qf,_QV=_Qg,_QW=_Qh,_QX=_Qi,_QY=_Qj,_QZ=_Qk,_R0=_Ql,_R1=_Qm,_R2=_Qn,_R3=_Qo,_R4=_Qp,_R5=_Qq,_R6=_Qr,_R7=_Qs,_R8=_Qt;_PN=_Qv.b;_PO={_:0,a:E(_Qw.a),b:E(B(_KJ(_QO,E(_QF.a),new T(function(){return B(_Jd(E(_QG).a));}),new T(function(){return B(_Jr(E(_QG).b));}),_Qw.b))),c:_Qw.c,d:_Qw.d,e:_Qw.e,f:E(_Qw.f),g:_Qw.g,h:E(_Qw.h),i:E(_Qw.i),j:E(_Qw.j)};_PP=_QQ;_PQ=_QR;_PR=_QS;_PS=_QT;_PT=_QU;_PU=_QV;_PV=_QW;_PW=_QX;_PX=_QY;_PY=_QZ;_PZ=_R0;_Q0=_R1;_Q1=_R2;_Q2=_R3;_Q3=_R4;_Q4=_R5;_Q5=_R6;_Q6=_R7;_Q7=_R8;return __continue;}else{return E(_Fz);}}}}})(_PN,_PO,_PP,_PQ,_PR,_PS,_PT,_PU,_PV,_PW,_PX,_PY,_PZ,_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7));if(_Q8!=__continue){return _Q8;}}},_R9=function(_Ra){var _Rb=E(_Ra);if(!_Rb._){return new T2(0,_S,_S);}else{var _Rc=E(_Rb.a),_Rd=new T(function(){var _Re=B(_R9(_Rb.b));return new T2(0,_Re.a,_Re.b);});return new T2(0,new T2(1,_Rc.a,new T(function(){return E(E(_Rd).a);})),new T2(1,_Rc.b,new T(function(){return E(E(_Rd).b);})));}},_Rf=32,_Rg=function(_Rh,_Ri,_Rj,_Rk){var _Rl=E(_Rk);if(!_Rl._){return __Z;}else{var _Rm=_Rl.b;if(!B(_4A(_3L,_Rh,_Rj))){var _Rn=new T(function(){return B(_Rg(new T(function(){return E(_Rh)+1|0;}),_Ri,_Rj,_Rm));});return new T2(1,_Rl.a,_Rn);}else{var _Ro=new T(function(){return B(_Rg(new T(function(){return E(_Rh)+1|0;}),_Ri,_Rj,_Rm));});return new T2(1,_Ri,_Ro);}}},_Rp=function(_Rq,_Rr){var _Rs=E(_Rr);if(!_Rs._){return __Z;}else{var _Rt=new T(function(){var _Ru=B(_R9(_Rs.a)),_Rv=_Ru.a,_Rw=new T(function(){return B(_IQ(0,_Rq,_Rv));});return B(_Go(B(_Rg(_rl,_Rf,_Rw,_Rv)),new T(function(){return B(_IX(0,_E8,_Rw,_Ru.b));},1)));});return new T2(1,_Rt,new T(function(){return B(_Rp(_Rq,_Rs.b));}));}},_Rx=function(_Ry,_Rz){var _RA=E(_Rz);return (_RA._==0)?__Z:new T2(1,_Ry,new T(function(){return B(_Rx(_RA.a,_RA.b));}));},_RB=new T(function(){return B(unCStr("init"));}),_RC=new T(function(){return B(_nd(_RB));}),_RD=function(_RE,_RF){var _RG=function(_RH){var _RI=E(_RH);if(!_RI._){return __Z;}else{var _RJ=new T(function(){return B(_q(new T2(1,_RE,_S),new T(function(){return B(_RG(_RI.b));},1)));},1);return new F(function(){return _q(_RI.a,_RJ);});}},_RK=B(_RG(_RF));if(!_RK._){return E(_RC);}else{return new F(function(){return _Rx(_RK.a,_RK.b);});}},_RL=61,_RM=46,_RN=new T(function(){return B(_e6("Event.hs:(93,1)-(99,61)|function makeDecision"));}),_RO=new T(function(){return B(unCStr("sm"));}),_RP=new T(function(){return B(unCStr("rk"));}),_RQ=new T(function(){return B(unCStr("if"));}),_RR=new T(function(){return B(unCStr("hm"));}),_RS=new T(function(){return B(unCStr("cleq"));}),_RT=new T(function(){return B(unCStr("da"));}),_RU=new T(function(){return B(unCStr("ct"));}),_RV=function(_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg){var _Sh=function(_Si,_Sj){var _Sk=function(_Sl){if(!B(_qN(_Si,_RU))){if(!B(_qN(_Si,_RT))){var _Sm=function(_Sn){if(!B(_qN(_Si,_RS))){var _So=function(_Sp){if(!B(_qN(_Si,_rO))){if(!B(_qN(_Si,_RR))){if(!B(_qN(_Si,_RQ))){if(!B(_qN(_Si,_RP))){if(!B(_qN(_Si,_RO))){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{var _Sq=E(_Sf);return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E({_:0,a:E(_Sq.a),b:E(_Sq.b),c:E(_Sq.c),d:E(_Sq.d),e:E(_Sq.e),f:E(_Sq.f),g:E(_Sq.g),h:E(_wt)}),t:E(_Sg)};}}else{return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sj),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}}else{var _Sr=E(_Sj);if(!_Sr._){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{var _Ss=_Sr.a,_St=E(_Sr.b);if(!_St._){return E(_RN);}else{var _Su=_St.a,_Sv=B(_O0(_S3)),_Sw=_Sv.a,_Sx=_Sv.b,_Sy=function(_Sz){if(!B(_4A(_qd,_Ss,_Sw))){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{if(!B(_qN(_Su,B(_6Q(_Sx,B(_Mt(_qd,_Ss,_Sw))))))){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{return new F(function(){return _RV(_Sz,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}}},_SA=B(_RD(_RM,_St.b));if(!_SA._){return new F(function(){return _Sy(_S);});}else{var _SB=_SA.a,_SC=E(_SA.b);if(!_SC._){return new F(function(){return _Sy(new T2(1,_SB,_S));});}else{var _SD=_SC.a,_SE=_SC.b,_SF=E(_SB);if(E(_SF)==47){if(!B(_4A(_qd,_Ss,_Sw))){return new F(function(){return _RV(B(_H4(47,_SD,_SE)).a,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}else{if(!B(_qN(_Su,B(_6Q(_Sx,B(_Mt(_qd,_Ss,_Sw))))))){return new F(function(){return _RV(B(_H4(47,_SD,_SE)).a,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}else{return new F(function(){return _RV(_S,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}}}else{if(!B(_4A(_qd,_Ss,_Sw))){var _SG=E(B(_H4(47,_SD,_SE)).b);if(!_SG._){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{return new F(function(){return _RV(_SG.a,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}}else{if(!B(_qN(_Su,B(_6Q(_Sx,B(_Mt(_qd,_Ss,_Sw))))))){var _SH=E(B(_H4(47,_SD,_SE)).b);if(!_SH._){return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}else{return new F(function(){return _RV(_SH.a,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}}else{return new F(function(){return _RV(new T2(1,_SF,new T(function(){return E(B(_H4(47,_SD,_SE)).a);})),_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg);});}}}}}}}}}else{var _SI=E(_Sf);return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E({_:0,a:E(_SI.a),b:E(_SI.b),c:E(_SI.c),d:E(_SI.d),e:E(_SI.e),f:E(_SI.f),g:E(_SI.g),h:E(_ws)}),t:E(_Sg)};}}else{var _SJ=E(_Sf);return new F(function(){return _O9(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S,_Sa,_Sb,_Sc,_Sd,_Se,_SJ.a,_SJ.b,_SJ.c,_SJ.d,_SJ.e,_SJ.f,_SJ.g,_SJ.h,_Sg);});}},_SK=E(_Si);if(!_SK._){return new F(function(){return _So(_);});}else{if(E(_SK.a)==109){if(!E(_SK.b)._){var _SL=B(_Hh(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SL.a),b:E(_SL.b),c:E(_SL.c),d:E(_SL.d),e:E(_SL.e),f:E(_SL.f),g:E(_SL.g),h:E(_SL.h),i:_SL.i,j:_SL.j,k:_SL.k,l:_SL.l,m:E(_SL.m),n:_SL.n,o:E(_SL.o),p:E(_SL.p),q:E(_SL.q),r:_SL.r,s:E(_SL.s),t:E(_SL.t)};}else{return new F(function(){return _So(_);});}}else{return new F(function(){return _So(_);});}}}else{var _SM=E(_RX);return {_:0,a:E({_:0,a:E(_SM.a),b:E(B(_Rp(_RL,_SM.b))),c:_SM.c,d:_SM.d,e:_SM.e,f:E(_SM.f),g:_SM.g,h:E(_SM.h),i:E(_SM.i),j:E(_SM.j)}),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S1),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}},_SN=E(_Si);if(!_SN._){return new F(function(){return _Sm(_);});}else{var _SO=_SN.b;switch(E(_SN.a)){case 99:if(!E(_SO)._){var _SP=B(_Lf(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SP.a),b:E(_SP.b),c:E(_SP.c),d:E(_SP.d),e:E(_SP.e),f:E(_SP.f),g:E(_SP.g),h:E(_SP.h),i:_SP.i,j:_SP.j,k:_SP.k,l:_SP.l,m:E(_SP.m),n:_SP.n,o:E(_SP.o),p:E(_SP.p),q:E(_SP.q),r:_SP.r,s:E(_SP.s),t:E(_SP.t)};}else{return new F(function(){return _Sm(_);});}break;case 112:if(!E(_SO)._){var _SQ=B(_PM(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SQ.a),b:E(_SQ.b),c:E(_SQ.c),d:E(_SQ.d),e:E(_SQ.e),f:E(_SQ.f),g:E(_SQ.g),h:E(_SQ.h),i:_SQ.i,j:_SQ.j,k:_SQ.k,l:_SQ.l,m:E(_SQ.m),n:_SQ.n,o:E(_SQ.o),p:E(_SQ.p),q:E(_SQ.q),r:_SQ.r,s:E(_SQ.s),t:E(_SQ.t)};}else{return new F(function(){return _Sm(_);});}break;default:return new F(function(){return _Sm(_);});}}}else{return {_:0,a:E(_RX),b:E(_RY),c:E(_RZ),d:E(_S0),e:E(_S),f:E(_S2),g:E(_S3),h:E(_S4),i:_S5,j:_S6,k:_S7,l:_S8,m:E(_S9),n:_Sa,o:E(_Sb),p:E(_Sc),q:E(_Sd),r:_Se,s:E(_Sf),t:E(_Sg)};}}else{var _SR=B(_Jt(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SR.a),b:E(_SR.b),c:E(_SR.c),d:E(_SR.d),e:E(_SR.e),f:E(_SR.f),g:E(_SR.g),h:E(_SR.h),i:_SR.i,j:_SR.j,k:_SR.k,l:_SR.l,m:E(_SR.m),n:_SR.n,o:E(_SR.o),p:E(_SR.p),q:E(_SR.q),r:_SR.r,s:E(_SR.s),t:E(_SR.t)};}},_SS=E(_Si);if(!_SS._){return new F(function(){return _Sk(_);});}else{var _ST=_SS.b;switch(E(_SS.a)){case 100:if(!E(_ST)._){var _SU=B(_MT(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SU.a),b:E(_SU.b),c:E(_SU.c),d:E(_SU.d),e:E(_SU.e),f:E(_SU.f),g:E(_SU.g),h:E(_SU.h),i:_SU.i,j:_SU.j,k:_SU.k,l:_SU.l,m:E(_SU.m),n:_SU.n,o:E(_SU.o),p:E(_SU.p),q:E(_SU.q),r:_SU.r,s:E(_SU.s),t:E(_SU.t)};}else{return new F(function(){return _Sk(_);});}break;case 101:if(!E(_ST)._){var _SV=B(_qg(_Sj,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg));return {_:0,a:E(_SV.a),b:E(_SV.b),c:E(_SV.c),d:E(_SV.d),e:E(_SV.e),f:E(_SV.f),g:E(_SV.g),h:E(_SV.h),i:_SV.i,j:_SV.j,k:_SV.k,l:_SV.l,m:E(_SV.m),n:_SV.n,o:E(_SV.o),p:E(_SV.p),q:E(_SV.q),r:_SV.r,s:E(_SV.s),t:E(_SV.t)};}else{return new F(function(){return _Sk(_);});}break;default:return new F(function(){return _Sk(_);});}}},_SW=E(_RW);if(!_SW._){return new F(function(){return _Sh(_S,_S);});}else{var _SX=_SW.a,_SY=E(_SW.b);if(!_SY._){return new F(function(){return _Sh(new T2(1,_SX,_S),_S);});}else{var _SZ=E(_SX),_T0=new T(function(){var _T1=B(_H4(46,_SY.a,_SY.b));return new T2(0,_T1.a,_T1.b);});if(E(_SZ)==46){return new F(function(){return _Sh(_S,new T2(1,new T(function(){return E(E(_T0).a);}),new T(function(){return E(E(_T0).b);})));});}else{return new F(function(){return _Sh(new T2(1,_SZ,new T(function(){return E(E(_T0).a);})),new T(function(){return E(E(_T0).b);}));});}}}},_T2=new T(function(){return B(unCStr("last"));}),_T3=new T(function(){return B(_nd(_T2));}),_T4=32,_T5=0,_T6=65306,_T7=125,_T8=new T1(0,1),_T9=function(_Ta,_Tb,_Tc,_Td,_Te){var _Tf=new T(function(){return E(_Te).i;}),_Tg=new T(function(){return E(E(_Te).c);}),_Th=new T(function(){var _Ti=E(_Tf)+1|0;if(0>=_Ti){return E(_T4);}else{var _Tj=B(_pN(_Ti,_Tg));if(!_Tj._){return E(_T4);}else{return B(_o9(_Tj.a,_Tj.b,_T3));}}}),_Tk=new T(function(){var _Tl=E(_Th);switch(E(_Tl)){case 125:return E(_T4);break;case 12289:return E(_T4);break;case 12290:return E(_T4);break;default:return E(_Tl);}}),_Tm=new T(function(){if(E(_Tk)==10){return true;}else{return false;}}),_Tn=new T(function(){if(!E(_Tm)){if(E(_Tk)==12300){return E(_j6);}else{return E(_Te).j;}}else{return E(_T5);}}),_To=new T(function(){var _Tp=E(_Tb)/28,_Tq=_Tp&4294967295;if(_Tp>=_Tq){return _Tq-1|0;}else{return (_Tq-1|0)-1|0;}}),_Tr=new T(function(){if(!E(E(_Td).h)){return E(_j7);}else{return 2+(E(E(E(_Te).b).b)+3|0)|0;}}),_Ts=new T(function(){if(!E(_Tf)){return new T2(0,_To,_Tr);}else{return E(E(_Te).h);}}),_Tt=new T(function(){return E(E(_Ts).b);}),_Tu=new T(function(){return E(E(_Ts).a);}),_Tv=new T(function(){if(E(_Tk)==65306){return true;}else{return false;}}),_Tw=new T(function(){if(!E(_Tv)){if(!E(_Tm)){var _Tx=E(_Tt);if((_Tx+1)*20<=E(_Tc)-10){return new T2(0,_Tu,_Tx+1|0);}else{return new T2(0,new T(function(){return E(_Tu)-1|0;}),_Tr);}}else{return new T2(0,new T(function(){return E(_Tu)-1|0;}),_Tr);}}else{return new T2(0,_Tu,_Tt);}}),_Ty=new T(function(){if(E(E(_Tw).a)==1){if(E(_Tu)==1){return false;}else{return true;}}else{return false;}}),_Tz=new T(function(){if(!E(_Tv)){return __Z;}else{return B(_q5(_T6,E(_Tf),_Tg));}}),_TA=new T(function(){if(E(_Tk)==123){return true;}else{return false;}}),_TB=new T(function(){if(!E(_TA)){return __Z;}else{return B(_q5(_T7,E(_Tf),_Tg));}}),_TC=new T(function(){if(!E(_TA)){var _TD=E(_Te),_TE=E(_Td);if(E(_Th)==12290){var _TF=true;}else{var _TF=false;}return {_:0,a:E(_TD.a),b:E(_TD.b),c:E(_TD.c),d:E(_TD.d),e:E(_TD.e),f:E(_TD.f),g:E(_TD.g),h:E(_TD.h),i:_TD.i,j:_TD.j,k:_TD.k,l:_TD.l,m:E(_TD.m),n:_TD.n,o:E(_TD.o),p:E(_TD.p),q:E(_TD.q),r:_TD.r,s:E({_:0,a:E(_TE.a),b:E(_TE.b),c:E(_TE.c),d:E(_TF),e:E(_TE.e),f:E(_TE.f),g:E(_TE.g),h:E(_TE.h)}),t:E(_TD.t)};}else{var _TG=E(_Te),_TH=E(_Td);if(E(_Th)==12290){var _TI=true;}else{var _TI=false;}return B(_RV(_TB,_TG.a,_TG.b,_TG.c,_TG.d,_TG.e,_TG.f,_TG.g,_TG.h,_TG.i,_TG.j,_TG.k,_TG.l,_TG.m,_TG.n,_TG.o,_TG.p,_TG.q,_TG.r,{_:0,a:E(_TH.a),b:E(_TH.b),c:E(_TH.c),d:E(_TI),e:E(_TH.e),f:E(_TH.f),g:E(_TH.g),h:E(_TH.h)},_TG.t));}}),_TJ=new T(function(){return E(E(_TC).s);}),_TK=new T(function(){if(!E(_Tf)){return E(_T5);}else{return E(_TC).k;}}),_TL=new T(function(){var _TM=E(_TC),_TN=_TM.a,_TO=_TM.b,_TP=_TM.c,_TQ=_TM.d,_TR=_TM.e,_TS=_TM.f,_TT=_TM.g,_TU=_TM.l,_TV=_TM.m,_TW=_TM.n,_TX=_TM.o,_TY=_TM.p,_TZ=_TM.q,_U0=_TM.r,_U1=_TM.t;if(!E(_Ty)){var _U2=E(_Tw);}else{var _U2=new T2(0,_Tu,_Tr);}var _U3=E(_Tf),_U4=function(_U5){var _U6=B(_ms(_Tg,0))-1|0,_U7=function(_U8){var _U9=E(_Tn);if(!E(_Ty)){var _Ua=E(_TJ);return {_:0,a:E(_TN),b:E(_TO),c:E(_TP),d:E(_TQ),e:E(_TR),f:E(_TS),g:E(_TT),h:E(_U2),i:_U8,j:_U9,k:E(_TK),l:_TU,m:E(_TV),n:_TW,o:E(_TX),p:E(_TY),q:E(_TZ),r:_U0,s:E({_:0,a:E(_Ua.a),b:E(_Ua.b),c:(_U3+_U5|0)<=_U6,d:E(_Ua.d),e:E(_Ua.e),f:E(_Ua.f),g:E(_Ua.g),h:E(_Ua.h)}),t:E(_U1)};}else{var _Ub=E(_TJ);return {_:0,a:E(_TN),b:E(_TO),c:E(_TP),d:E(_TQ),e:E(_TR),f:E(_TS),g:E(_TT),h:E(_U2),i:_U8,j:_U9,k:E(_TK)+1|0,l:_TU,m:E(_TV),n:_TW,o:E(_TX),p:E(_TY),q:E(_TZ),r:_U0,s:E({_:0,a:E(_Ub.a),b:E(_Ub.b),c:(_U3+_U5|0)<=_U6,d:E(_Ub.d),e:E(_Ub.e),f:E(_Ub.f),g:E(_Ub.g),h:E(_Ub.h)}),t:E(_U1)};}};if((_U3+_U5|0)<=_U6){return new F(function(){return _U7(_U3+_U5|0);});}else{return new F(function(){return _U7(0);});}};if(!E(_Tv)){if(!E(_TA)){return B(_U4(1));}else{return B(_U4(B(_ms(_TB,0))+2|0));}}else{return B(_U4(B(_ms(_Tz,0))+2|0));}}),_Uc=new T(function(){var _Ud=B(_o3(B(_o1(_Ta)))),_Ue=new T(function(){var _Uf=B(_pu(_Ta,E(_Tb)/16)),_Ug=_Uf.a;if(E(_Uf.b)>=0){return E(_Ug);}else{return B(A3(_oG,_Ud,_Ug,new T(function(){return B(A2(_hd,_Ud,_T8));})));}});return B(A3(_oG,_Ud,_Ue,new T(function(){return B(A2(_hd,_Ud,_hm));})));});return {_:0,a:_Tk,b:_Tu,c:_Tt,d:new T(function(){if(E(_Tr)!=E(_Tt)){return E(_Tu);}else{return E(_Tu)+1|0;}}),e:new T(function(){var _Uh=E(_Tt);if(E(_Tr)!=_Uh){return _Uh-1|0;}else{var _Ui=(E(_Tc)-10)/20,_Uj=_Ui&4294967295;if(_Ui>=_Uj){return _Uj;}else{return _Uj-1|0;}}}),f:_Tr,g:_Tf,h:_Tg,i:new T(function(){return B(_6Q(_j3,E(_Tn)));}),j:_Tz,k:_To,l:_Uc,m:_TK,n:_j8,o:_Tv,p:_TA,q:_Ty,r:_TJ,s:_TC,t:_TL};},_Uk=function(_Ul){var _Um=E(_Ul);if(!_Um._){return new T2(0,_S,_S);}else{var _Un=E(_Um.a),_Uo=new T(function(){var _Up=B(_Uk(_Um.b));return new T2(0,_Up.a,_Up.b);});return new T2(0,new T2(1,_Un.a,new T(function(){return E(E(_Uo).a);})),new T2(1,_Un.b,new T(function(){return E(E(_Uo).b);})));}},_Uq=42,_Ur=32,_Us=function(_Ut,_Uu,_Uv){var _Uw=E(_Ut);if(!_Uw._){return __Z;}else{var _Ux=_Uw.a,_Uy=_Uw.b;if(_Uu!=_Uv){var _Uz=E(_Ux);return (_Uz._==0)?E(_ng):(E(_Uz.a)==42)?new T2(1,new T2(1,_Ur,_Uz.b),new T(function(){return B(_Us(_Uy,_Uu,_Uv+1|0));})):new T2(1,new T2(1,_Ur,_Uz),new T(function(){return B(_Us(_Uy,_Uu,_Uv+1|0));}));}else{var _UA=E(_Ux);return (_UA._==0)?E(_ng):(E(_UA.a)==42)?new T2(1,new T2(1,_Ur,_UA),new T(function(){return B(_Us(_Uy,_Uu,_Uv+1|0));})):new T2(1,new T2(1,_Uq,_UA),new T(function(){return B(_Us(_Uy,_Uu,_Uv+1|0));}));}}},_UB=new T(function(){return B(unCStr("\n\n"));}),_UC=function(_UD){var _UE=E(_UD);if(!_UE._){return __Z;}else{var _UF=new T(function(){return B(_q(_UB,new T(function(){return B(_UC(_UE.b));},1)));},1);return new F(function(){return _q(_UE.a,_UF);});}},_UG=function(_UH,_UI,_UJ){var _UK=new T(function(){var _UL=new T(function(){var _UM=E(_UI);if(!_UM._){return B(_UC(_S));}else{var _UN=_UM.a,_UO=_UM.b,_UP=E(_UJ);if(!_UP){var _UQ=E(_UN);if(!_UQ._){return E(_ng);}else{if(E(_UQ.a)==42){return B(_UC(new T2(1,new T2(1,_Ur,_UQ),new T(function(){return B(_Us(_UO,0,1));}))));}else{return B(_UC(new T2(1,new T2(1,_Uq,_UQ),new T(function(){return B(_Us(_UO,0,1));}))));}}}else{var _UR=E(_UN);if(!_UR._){return E(_ng);}else{if(E(_UR.a)==42){return B(_UC(new T2(1,new T2(1,_Ur,_UR.b),new T(function(){return B(_Us(_UO,_UP,1));}))));}else{return B(_UC(new T2(1,new T2(1,_Ur,_UR),new T(function(){return B(_Us(_UO,_UP,1));}))));}}}}});return B(unAppCStr("\n\n",_UL));},1);return new F(function(){return _q(_UH,_UK);});},_US=function(_UT){return E(E(_UT).c);},_UU=function(_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3){var _V4=new T(function(){if(!E(_UW)){return E(_UX);}else{return false;}}),_V5=new T(function(){if(!E(_UW)){return false;}else{return E(E(_V2).g);}}),_V6=new T(function(){if(!E(_V5)){if(!E(_V4)){return B(A2(_hd,_UV,_hl));}else{return B(A3(_mx,_UV,new T(function(){return B(A3(_mx,_UV,_V0,_V1));}),new T(function(){return B(A2(_hd,_UV,_T8));})));}}else{return B(A3(_mx,_UV,_V0,_V1));}}),_V7=new T(function(){if(!E(_V5)){if(!E(_V4)){return __Z;}else{var _V8=E(_UY)+1|0;if(0>=_V8){return __Z;}else{return B(_pN(_V8,_UZ));}}}else{return B(_UG(B(_US(_V3)),new T(function(){return E(B(_Uk(E(_V3).m)).a);},1),new T(function(){return E(_V3).n;},1)));}});return new T4(0,_V5,_V4,_V7,_V6);},_V9=function(_Va,_Vb,_Vc){var _Vd=E(_Vb),_Ve=E(_Vc),_Vf=new T(function(){var _Vg=B(_h9(_Va)),_Vh=B(_V9(_Va,_Ve,B(A3(_oG,_Vg,new T(function(){return B(A3(_mx,_Vg,_Ve,_Ve));}),_Vd))));return new T2(1,_Vh.a,_Vh.b);});return new T2(0,_Vd,_Vf);},_Vi=1,_Vj=new T(function(){var _Vk=B(_V9(_ga,_hL,_Vi));return new T2(1,_Vk.a,_Vk.b);}),_Vl=function(_Vm,_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw,_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE,_VF,_VG,_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_){var _W1={_:0,a:E(_VS),b:E(_VT),c:E(_VU),d:E(_VV),e:E(_VW),f:E(_VX),g:E(_VY),h:E(_VZ)};if(!E(_VU)){return {_:0,a:E({_:0,a:E(_Vp),b:E(_Vq),c:_Vr,d:_Vs,e:_Vt,f:E(_Vu),g:_Vv,h:E(_Vw),i:E(_Vx),j:E(_Vy)}),b:E(new T2(0,_Vz,_VA)),c:E(_VB),d:E(_VC),e:E(_VD),f:E(_VE),g:E(_VF),h:E(new T2(0,_VG,_VH)),i:_VI,j:_VJ,k:_VK,l:_VL,m:E(_VM),n:_VN,o:E(_VO),p:E(_VP),q:E(_VQ),r:_VR,s:E(_W1),t:E(_W0)};}else{if(!E(_VV)){var _W2=B(_T9(_bR,_Vn,_Vo,_W1,{_:0,a:E({_:0,a:E(_Vp),b:E(_Vq),c:_Vr,d:_Vs,e:_Vt,f:E(_Vu),g:_Vv,h:E(_Vw),i:E(_Vx),j:E(_Vy)}),b:E(new T2(0,_Vz,_VA)),c:E(_VB),d:E(_VC),e:E(_VD),f:E(_VE),g:E(_VF),h:E(new T2(0,_VG,_VH)),i:_VI,j:_VJ,k:_VK,l:_VL,m:E(_VM),n:_VN,o:E(_VO),p:E(_VP),q:E(_VQ),r:_VR,s:E(_W1),t:E(_W0)})),_W3=_W2.d,_W4=_W2.e,_W5=_W2.f,_W6=_W2.i,_W7=_W2.n,_W8=_W2.p,_W9=_W2.q,_Wa=_W2.s,_Wb=_W2.t;if(!E(_W2.o)){var _Wc=B(_UU(_bm,_W8,_W9,_W2.g,_W2.h,_W2.k,_W2.m,_W2.r,_Wa)),_Wd=function(_){if(!E(_W8)){if(!E(_W9)){var _We=B(_iA(E(_Vm).a,_W6,_j4,_hL,_W2.b,_W2.c,_W2.a,_));return _Wb;}else{return _Wb;}}else{return _Wb;}},_Wf=function(_Wg){var _Wh=E(_Vm),_Wi=_Wh.a,_Wj=_Wh.b,_Wk=B(_nP(_Wi,_Wj,_W2.l,_Wa,_)),_Wl=B(_ln(_Wi,_Wj,_Vo,0,_W5,_Wc.d,_W5,_Wc.c,_));return new F(function(){return _Wd(_);});};if(!E(_Wc.a)){if(!E(_Wc.b)){return new F(function(){return _Wd(_);});}else{return new F(function(){return _Wf(_);});}}else{return new F(function(){return _Wf(_);});}}else{var _Wm=E(_W2.j);if(!_Wm._){return _Wb;}else{var _Wn=E(_Vj);if(!_Wn._){return _Wb;}else{var _Wo=E(_Vm).a,_Wp=B(_iA(_Wo,_W6,_W7,_Wn.a,_W3,_W4,_Wm.a,_)),_Wq=function(_Wr,_Ws,_){while(1){var _Wt=E(_Wr);if(!_Wt._){return _gD;}else{var _Wu=E(_Ws);if(!_Wu._){return _gD;}else{var _Wv=B(_iA(_Wo,_W6,_W7,_Wu.a,_W3,_W4,_Wt.a,_));_Wr=_Wt.b;_Ws=_Wu.b;continue;}}}},_Ww=B(_Wq(_Wm.b,_Wn.b,_));return _Wb;}}}}else{return {_:0,a:E({_:0,a:E(_Vp),b:E(_Vq),c:_Vr,d:_Vs,e:_Vt,f:E(_Vu),g:_Vv,h:E(_Vw),i:E(_Vx),j:E(_Vy)}),b:E(new T2(0,_Vz,_VA)),c:E(_VB),d:E(_VC),e:E(_VD),f:E(_VE),g:E(_VF),h:E(new T2(0,_VG,_VH)),i:_VI,j:_VJ,k:_VK,l:_VL,m:E(_VM),n:_VN,o:E(_VO),p:E(_VP),q:E(_VQ),r:_VR,s:E(_W1),t:E(_W0)};}}},_Wx=function(_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_){while(1){var _Xd=B(_Vl(_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa,_Xb,_Xc,_)),_Xe=E(_Xd),_Xf=_Xe.c,_Xg=_Xe.d,_Xh=_Xe.e,_Xi=_Xe.f,_Xj=_Xe.g,_Xk=_Xe.i,_Xl=_Xe.j,_Xm=_Xe.k,_Xn=_Xe.l,_Xo=_Xe.m,_Xp=_Xe.n,_Xq=_Xe.o,_Xr=_Xe.p,_Xs=_Xe.q,_Xt=_Xe.r,_Xu=_Xe.t,_Xv=E(_Xe.s),_Xw=_Xv.a,_Xx=_Xv.b,_Xy=_Xv.c,_Xz=_Xv.e,_XA=_Xv.g,_XB=_Xv.h,_XC=E(_Xe.a),_XD=E(_Xe.b),_XE=E(_Xe.h);if(!E(_Xv.d)){if(!E(_X6)){return {_:0,a:E(_XC),b:E(_XD),c:E(_Xf),d:E(_Xg),e:E(_Xh),f:E(_Xi),g:E(_Xj),h:E(_XE),i:_Xk,j:_Xl,k:_Xm,l:_Xn,m:E(_Xo),n:_Xp,o:E(_Xq),p:E(_Xr),q:E(_Xs),r:_Xt,s:E({_:0,a:E(_Xw),b:E(_Xx),c:E(_Xy),d:E(_ws),e:E(_Xz),f:E(_ws),g:E(_XA),h:E(_XB)}),t:E(_Xu)};}else{_WB=_XC.a;_WC=_XC.b;_WD=_XC.c;_WE=_XC.d;_WF=_XC.e;_WG=_XC.f;_WH=_XC.g;_WI=_XC.h;_WJ=_XC.i;_WK=_XC.j;_WL=_XD.a;_WM=_XD.b;_WN=_Xf;_WO=_Xg;_WP=_Xh;_WQ=_Xi;_WR=_Xj;_WS=_XE.a;_WT=_XE.b;_WU=_Xk;_WV=_Xl;_WW=_Xm;_WX=_Xn;_WY=_Xo;_WZ=_Xp;_X0=_Xq;_X1=_Xr;_X2=_Xs;_X3=_Xt;_X4=_Xw;_X5=_Xx;_X6=_Xy;_X7=_ws;_X8=_Xz;_X9=_Xv.f;_Xa=_XA;_Xb=_XB;_Xc=_Xu;continue;}}else{return {_:0,a:E(_XC),b:E(_XD),c:E(_Xf),d:E(_Xg),e:E(_Xh),f:E(_Xi),g:E(_Xj),h:E(_XE),i:_Xk,j:_Xl,k:_Xm,l:_Xn,m:E(_Xo),n:_Xp,o:E(_Xq),p:E(_Xr),q:E(_Xs),r:_Xt,s:E({_:0,a:E(_Xw),b:E(_Xx),c:E(_Xy),d:E(_wt),e:E(_Xz),f:E(_ws),g:E(_XA),h:E(_XB)}),t:E(_Xu)};}}},_XF=function(_XG,_XH,_XI,_XJ,_XK,_XL,_XM,_XN,_XO,_XP,_XQ,_XR,_XS,_XT,_XU,_XV,_XW,_XX,_XY,_XZ,_Y0,_Y1,_Y2,_Y3,_Y4,_Y5,_Y6,_Y7,_Y8,_Y9,_Ya,_Yb,_Yc,_Yd,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj,_){var _Yk=B(_Vl(_XG,_XH,_XI,_XJ,_XK,_XL,_XM,_XN,_XO,_XP,_XQ,_XR,_XS,_XT,_XU,_XV,_XW,_XX,_XY,_XZ,_Y0,_Y1,_Y2,_Y3,_Y4,_Y5,_Y6,_Y7,_Y8,_Y9,_Ya,_Yb,_Yc,_Yd,_wt,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj,_)),_Yl=E(_Yk),_Ym=_Yl.c,_Yn=_Yl.d,_Yo=_Yl.e,_Yp=_Yl.f,_Yq=_Yl.g,_Yr=_Yl.i,_Ys=_Yl.j,_Yt=_Yl.k,_Yu=_Yl.l,_Yv=_Yl.m,_Yw=_Yl.n,_Yx=_Yl.o,_Yy=_Yl.p,_Yz=_Yl.q,_YA=_Yl.r,_YB=_Yl.t,_YC=E(_Yl.s),_YD=_YC.a,_YE=_YC.b,_YF=_YC.c,_YG=_YC.e,_YH=_YC.g,_YI=_YC.h,_YJ=E(_Yl.a),_YK=E(_Yl.b),_YL=E(_Yl.h);if(!E(_YC.d)){return new F(function(){return _Wx(_XG,_XH,_XI,_YJ.a,_YJ.b,_YJ.c,_YJ.d,_YJ.e,_YJ.f,_YJ.g,_YJ.h,_YJ.i,_YJ.j,_YK.a,_YK.b,_Ym,_Yn,_Yo,_Yp,_Yq,_YL.a,_YL.b,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YD,_YE,_YF,_ws,_YG,_YC.f,_YH,_YI,_YB,_);});}else{return {_:0,a:E(_YJ),b:E(_YK),c:E(_Ym),d:E(_Yn),e:E(_Yo),f:E(_Yp),g:E(_Yq),h:E(_YL),i:_Yr,j:_Ys,k:_Yt,l:_Yu,m:E(_Yv),n:_Yw,o:E(_Yx),p:E(_Yy),q:E(_Yz),r:_YA,s:E({_:0,a:E(_YD),b:E(_YE),c:E(_YF),d:E(_wt),e:E(_YG),f:E(_ws),g:E(_YH),h:E(_YI)}),t:E(_YB)};}},_YM=function(_YN){var _YO=E(_YN);if(!_YO._){return __Z;}else{var _YP=E(_YO.b);return (_YP._==0)?__Z:new T2(1,new T2(0,_YO.a,_YP.a),new T(function(){return B(_YM(_YP.b));}));}},_YQ=function(_YR,_YS,_YT){return new T2(1,new T2(0,_YR,_YS),new T(function(){return B(_YM(_YT));}));},_YU=function(_YV,_YW){var _YX=E(_YW);return (_YX._==0)?__Z:new T2(1,new T2(0,_YV,_YX.a),new T(function(){return B(_YM(_YX.b));}));},_YY=new T(function(){return B(err(_sq));}),_YZ=new T(function(){return B(err(_ss));}),_Z0=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_Z1=function(_Z2){var _Z3=B(_Gc(B(_sx(_Z0,_Z2))));return (_Z3._==0)?E(_YY):(E(_Z3.b)._==0)?E(_Z3.a):E(_YZ);},_Z4="Invalid JSON!",_Z5=new T1(0,_Z4),_Z6="No such value",_Z7=new T1(0,_Z6),_Z8=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_Z9=function(_Za){return E(E(_Za).c);},_Zb=function(_Zc,_Zd,_){var _Ze=__app1(E(_Z8),_Zd),_Zf=__eq(_Ze,E(_3a));if(!E(_Zf)){var _Zg=__isUndef(_Ze);return (E(_Zg)==0)?new T(function(){var _Zh=String(_Ze),_Zi=jsParseJSON(_Zh);if(!_Zi._){return E(_Z5);}else{return B(A2(_Z9,_Zc,_Zi.a));}}):_Z7;}else{return _Z7;}},_Zj=new T1(0,0),_Zk=function(_Zl,_Zm){while(1){var _Zn=E(_Zl);if(!_Zn._){var _Zo=_Zn.a,_Zp=E(_Zm);if(!_Zp._){return new T1(0,(_Zo>>>0|_Zp.a>>>0)>>>0&4294967295);}else{_Zl=new T1(1,I_fromInt(_Zo));_Zm=_Zp;continue;}}else{var _Zq=E(_Zm);if(!_Zq._){_Zl=_Zn;_Zm=new T1(1,I_fromInt(_Zq.a));continue;}else{return new T1(1,I_or(_Zn.a,_Zq.a));}}}},_Zr=function(_Zs){var _Zt=E(_Zs);if(!_Zt._){return E(_Zj);}else{return new F(function(){return _Zk(new T1(0,E(_Zt.a)),B(_cN(B(_Zr(_Zt.b)),31)));});}},_Zu=function(_Zv,_Zw){if(!E(_Zv)){return new F(function(){return _fs(B(_Zr(_Zw)));});}else{return new F(function(){return _Zr(_Zw);});}},_Zx=1420103680,_Zy=465,_Zz=new T2(1,_Zy,_S),_ZA=new T2(1,_Zx,_Zz),_ZB=new T(function(){return B(_Zu(_wt,_ZA));}),_ZC=function(_ZD){return E(_ZB);},_ZE=new T(function(){return B(unCStr("s"));}),_ZF=function(_ZG,_ZH){while(1){var _ZI=E(_ZG);if(!_ZI._){return E(_ZH);}else{_ZG=_ZI.b;_ZH=_ZI.a;continue;}}},_ZJ=function(_ZK,_ZL,_ZM){return new F(function(){return _ZF(_ZL,_ZK);});},_ZN=new T1(0,1),_ZO=function(_ZP,_ZQ){var _ZR=E(_ZP);return new T2(0,_ZR,new T(function(){var _ZS=B(_ZO(B(_cu(_ZR,_ZQ)),_ZQ));return new T2(1,_ZS.a,_ZS.b);}));},_ZT=function(_ZU){var _ZV=B(_ZO(_ZU,_ZN));return new T2(1,_ZV.a,_ZV.b);},_ZW=function(_ZX,_ZY){var _ZZ=B(_ZO(_ZX,new T(function(){return B(_eN(_ZY,_ZX));})));return new T2(1,_ZZ.a,_ZZ.b);},_100=new T1(0,0),_101=function(_102,_103){var _104=E(_102);if(!_104._){var _105=_104.a,_106=E(_103);return (_106._==0)?_105>=_106.a:I_compareInt(_106.a,_105)<=0;}else{var _107=_104.a,_108=E(_103);return (_108._==0)?I_compareInt(_107,_108.a)>=0:I_compare(_107,_108.a)>=0;}},_109=function(_10a,_10b,_10c){if(!B(_101(_10b,_100))){var _10d=function(_10e){return (!B(_d6(_10e,_10c)))?new T2(1,_10e,new T(function(){return B(_10d(B(_cu(_10e,_10b))));})):__Z;};return new F(function(){return _10d(_10a);});}else{var _10f=function(_10g){return (!B(_cX(_10g,_10c)))?new T2(1,_10g,new T(function(){return B(_10f(B(_cu(_10g,_10b))));})):__Z;};return new F(function(){return _10f(_10a);});}},_10h=function(_10i,_10j,_10k){return new F(function(){return _109(_10i,B(_eN(_10j,_10i)),_10k);});},_10l=function(_10m,_10n){return new F(function(){return _109(_10m,_ZN,_10n);});},_10o=function(_10p){return new F(function(){return _b9(_10p);});},_10q=function(_10r){return new F(function(){return _eN(_10r,_ZN);});},_10s=function(_10t){return new F(function(){return _cu(_10t,_ZN);});},_10u=function(_10v){return new F(function(){return _aQ(E(_10v));});},_10w={_:0,a:_10s,b:_10q,c:_10u,d:_10o,e:_ZT,f:_ZW,g:_10l,h:_10h},_10x=function(_10y,_10z){while(1){var _10A=E(_10y);if(!_10A._){var _10B=E(_10A.a);if(_10B==( -2147483648)){_10y=new T1(1,I_fromInt( -2147483648));continue;}else{var _10C=E(_10z);if(!_10C._){return new T1(0,B(_9i(_10B,_10C.a)));}else{_10y=new T1(1,I_fromInt(_10B));_10z=_10C;continue;}}}else{var _10D=_10A.a,_10E=E(_10z);return (_10E._==0)?new T1(1,I_div(_10D,I_fromInt(_10E.a))):new T1(1,I_div(_10D,_10E.a));}}},_10F=function(_10G,_10H){if(!B(_cm(_10H,_oK))){return new F(function(){return _10x(_10G,_10H);});}else{return E(_9T);}},_10I=function(_10J,_10K){while(1){var _10L=E(_10J);if(!_10L._){var _10M=E(_10L.a);if(_10M==( -2147483648)){_10J=new T1(1,I_fromInt( -2147483648));continue;}else{var _10N=E(_10K);if(!_10N._){var _10O=_10N.a;return new T2(0,new T1(0,B(_9i(_10M,_10O))),new T1(0,B(_an(_10M,_10O))));}else{_10J=new T1(1,I_fromInt(_10M));_10K=_10N;continue;}}}else{var _10P=E(_10K);if(!_10P._){_10J=_10L;_10K=new T1(1,I_fromInt(_10P.a));continue;}else{var _10Q=I_divMod(_10L.a,_10P.a);return new T2(0,new T1(1,_10Q.a),new T1(1,_10Q.b));}}}},_10R=function(_10S,_10T){if(!B(_cm(_10T,_oK))){var _10U=B(_10I(_10S,_10T));return new T2(0,_10U.a,_10U.b);}else{return E(_9T);}},_10V=function(_10W,_10X){while(1){var _10Y=E(_10W);if(!_10Y._){var _10Z=E(_10Y.a);if(_10Z==( -2147483648)){_10W=new T1(1,I_fromInt( -2147483648));continue;}else{var _110=E(_10X);if(!_110._){return new T1(0,B(_an(_10Z,_110.a)));}else{_10W=new T1(1,I_fromInt(_10Z));_10X=_110;continue;}}}else{var _111=_10Y.a,_112=E(_10X);return (_112._==0)?new T1(1,I_mod(_111,I_fromInt(_112.a))):new T1(1,I_mod(_111,_112.a));}}},_113=function(_114,_115){if(!B(_cm(_115,_oK))){return new F(function(){return _10V(_114,_115);});}else{return E(_9T);}},_116=function(_117,_118){while(1){var _119=E(_117);if(!_119._){var _11a=E(_119.a);if(_11a==( -2147483648)){_117=new T1(1,I_fromInt( -2147483648));continue;}else{var _11b=E(_118);if(!_11b._){return new T1(0,quot(_11a,_11b.a));}else{_117=new T1(1,I_fromInt(_11a));_118=_11b;continue;}}}else{var _11c=_119.a,_11d=E(_118);return (_11d._==0)?new T1(0,I_toInt(I_quot(_11c,I_fromInt(_11d.a)))):new T1(1,I_quot(_11c,_11d.a));}}},_11e=function(_11f,_11g){if(!B(_cm(_11g,_oK))){return new F(function(){return _116(_11f,_11g);});}else{return E(_9T);}},_11h=function(_11i,_11j){if(!B(_cm(_11j,_oK))){var _11k=B(_cD(_11i,_11j));return new T2(0,_11k.a,_11k.b);}else{return E(_9T);}},_11l=function(_11m,_11n){while(1){var _11o=E(_11m);if(!_11o._){var _11p=E(_11o.a);if(_11p==( -2147483648)){_11m=new T1(1,I_fromInt( -2147483648));continue;}else{var _11q=E(_11n);if(!_11q._){return new T1(0,_11p%_11q.a);}else{_11m=new T1(1,I_fromInt(_11p));_11n=_11q;continue;}}}else{var _11r=_11o.a,_11s=E(_11n);return (_11s._==0)?new T1(1,I_rem(_11r,I_fromInt(_11s.a))):new T1(1,I_rem(_11r,_11s.a));}}},_11t=function(_11u,_11v){if(!B(_cm(_11v,_oK))){return new F(function(){return _11l(_11u,_11v);});}else{return E(_9T);}},_11w=function(_11x){return E(_11x);},_11y=function(_11z){return E(_11z);},_11A=function(_11B){var _11C=E(_11B);if(!_11C._){var _11D=E(_11C.a);return (_11D==( -2147483648))?E(_fr):(_11D<0)?new T1(0, -_11D):E(_11C);}else{var _11E=_11C.a;return (I_compareInt(_11E,0)>=0)?E(_11C):new T1(1,I_negate(_11E));}},_11F=new T1(0, -1),_11G=function(_11H){var _11I=E(_11H);if(!_11I._){var _11J=_11I.a;return (_11J>=0)?(E(_11J)==0)?E(_Zj):E(_d5):E(_11F);}else{var _11K=I_compareInt(_11I.a,0);return (_11K<=0)?(E(_11K)==0)?E(_Zj):E(_11F):E(_d5);}},_11L={_:0,a:_cu,b:_eN,c:_oe,d:_fs,e:_11A,f:_11G,g:_11y},_11M=function(_11N,_11O){var _11P=E(_11N);if(!_11P._){var _11Q=_11P.a,_11R=E(_11O);return (_11R._==0)?_11Q!=_11R.a:(I_compareInt(_11R.a,_11Q)==0)?false:true;}else{var _11S=_11P.a,_11T=E(_11O);return (_11T._==0)?(I_compareInt(_11S,_11T.a)==0)?false:true:(I_compare(_11S,_11T.a)==0)?false:true;}},_11U=new T2(0,_cm,_11M),_11V=function(_11W,_11X){return (!B(_ey(_11W,_11X)))?E(_11W):E(_11X);},_11Y=function(_11Z,_120){return (!B(_ey(_11Z,_120)))?E(_120):E(_11Z);},_121={_:0,a:_11U,b:_c6,c:_d6,d:_ey,e:_cX,f:_101,g:_11V,h:_11Y},_122=function(_123){return new T2(0,E(_123),E(_aU));},_124=new T3(0,_11L,_121,_122),_125={_:0,a:_124,b:_10w,c:_11e,d:_11t,e:_10F,f:_113,g:_11h,h:_10R,i:_11w},_126=new T1(0,0),_127=function(_128,_129,_12a){var _12b=B(A1(_128,_129));if(!B(_cm(_12b,_126))){return new F(function(){return _10x(B(_oe(_129,_12a)),_12b);});}else{return E(_9T);}},_12c=function(_12d,_12e){while(1){if(!B(_cm(_12e,_oK))){var _12f=_12e,_12g=B(_11t(_12d,_12e));_12d=_12f;_12e=_12g;continue;}else{return E(_12d);}}},_12h=5,_12i=new T(function(){return B(_9P(_12h));}),_12j=new T(function(){return die(_12i);}),_12k=function(_12l,_12m){if(!B(_cm(_12m,_oK))){var _12n=B(_12c(B(_11A(_12l)),B(_11A(_12m))));return (!B(_cm(_12n,_oK)))?new T2(0,B(_116(_12l,_12n)),B(_116(_12m,_12n))):E(_9T);}else{return E(_12j);}},_12o=function(_12p,_12q,_12r,_12s){var _12t=B(_oe(_12q,_12r));return new F(function(){return _12k(B(_oe(B(_oe(_12p,_12s)),B(_11G(_12t)))),B(_11A(_12t)));});},_12u=function(_12v,_12w,_12x){var _12y=new T(function(){if(!B(_cm(_12x,_oK))){var _12z=B(_cD(_12w,_12x));return new T2(0,_12z.a,_12z.b);}else{return E(_9T);}}),_12A=new T(function(){return B(A2(_hd,B(_o3(B(_o1(_12v)))),new T(function(){return E(E(_12y).a);})));});return new T2(0,_12A,new T(function(){return new T2(0,E(E(_12y).b),E(_12x));}));},_12B=function(_12C,_12D,_12E){var _12F=B(_12u(_12C,_12D,_12E)),_12G=_12F.a,_12H=E(_12F.b);if(!B(_d6(B(_oe(_12H.a,_aU)),B(_oe(_oK,_12H.b))))){return E(_12G);}else{var _12I=B(_o3(B(_o1(_12C))));return new F(function(){return A3(_oG,_12I,_12G,new T(function(){return B(A2(_hd,_12I,_aU));}));});}},_12J=479723520,_12K=40233135,_12L=new T2(1,_12K,_S),_12M=new T2(1,_12J,_12L),_12N=new T(function(){return B(_Zu(_wt,_12M));}),_12O=new T1(0,40587),_12P=function(_12Q){var _12R=new T(function(){var _12S=B(_12o(_12Q,_aU,_ZB,_aU)),_12T=B(_12o(_12N,_aU,_ZB,_aU)),_12U=B(_12o(_12S.a,_12S.b,_12T.a,_12T.b));return B(_12B(_125,_12U.a,_12U.b));});return new T2(0,new T(function(){return B(_cu(_12O,_12R));}),new T(function(){return B(_eN(_12Q,B(_127(_ZC,B(_oe(_12R,_ZB)),_12N))));}));},_12V=function(_12W,_){var _12X=__get(_12W,0),_12Y=__get(_12W,1),_12Z=Number(_12X),_130=jsTrunc(_12Z),_131=Number(_12Y),_132=jsTrunc(_131);return new T2(0,_130,_132);},_133=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_134=660865024,_135=465661287,_136=new T2(1,_135,_S),_137=new T2(1,_134,_136),_138=new T(function(){return B(_Zu(_wt,_137));}),_139=function(_){var _13a=__app0(E(_133)),_13b=B(_12V(_13a,_));return new T(function(){var _13c=E(_13b);if(!B(_cm(_138,_126))){return B(_cu(B(_oe(B(_aQ(E(_13c.a))),_ZB)),B(_10x(B(_oe(B(_oe(B(_aQ(E(_13c.b))),_ZB)),_ZB)),_138))));}else{return E(_9T);}});},_13d=new T(function(){return B(err(_ss));}),_13e=new T(function(){return B(err(_sq));}),_13f=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_13g=new T1(0,1),_13h=new T1(0,10),_13i=function(_13j){while(1){var _13k=E(_13j);if(!_13k._){_13j=new T1(1,I_fromInt(_13k.a));continue;}else{return new F(function(){return I_toString(_13k.a);});}}},_13l=function(_13m,_13n){return new F(function(){return _q(fromJSStr(B(_13i(_13m))),_13n);});},_13o=new T1(0,0),_13p=function(_13q,_13r,_13s){if(_13q<=6){return new F(function(){return _13l(_13r,_13s);});}else{if(!B(_d6(_13r,_13o))){return new F(function(){return _13l(_13r,_13s);});}else{return new T2(1,_z,new T(function(){return B(_q(fromJSStr(B(_13i(_13r))),new T2(1,_y,_13s)));}));}}},_13t=function(_13u){return new F(function(){return _13p(0,_13u,_S);});},_13v=new T(function(){return B(_cm(_13h,_126));}),_13w=function(_13x){while(1){if(!B(_cm(_13x,_126))){if(!E(_13v)){if(!B(_cm(B(_10V(_13x,_13h)),_126))){return new F(function(){return _13t(_13x);});}else{var _13y=B(_10x(_13x,_13h));_13x=_13y;continue;}}else{return E(_9T);}}else{return __Z;}}},_13z=46,_13A=48,_13B=function(_13C,_13D,_13E){if(!B(_d6(_13E,_126))){var _13F=B(A1(_13C,_13E));if(!B(_cm(_13F,_126))){var _13G=B(_10I(_13E,_13F)),_13H=_13G.b,_13I=new T(function(){var _13J=Math.log(B(_fL(_13F)))/Math.log(10),_13K=_13J&4294967295,_13L=function(_13M){if(_13M>=0){var _13N=E(_13M);if(!_13N){var _13O=B(_10x(B(_eN(B(_cu(B(_oe(_13H,_aU)),_13F)),_13g)),_13F));}else{var _13O=B(_10x(B(_eN(B(_cu(B(_oe(_13H,B(_ou(_13h,_13N)))),_13F)),_13g)),_13F));}var _13P=function(_13Q){var _13R=B(_13p(0,_13O,_S)),_13S=_13M-B(_ms(_13R,0))|0;if(0>=_13S){if(!E(_13D)){return E(_13R);}else{return new F(function(){return _13w(_13O);});}}else{var _13T=new T(function(){if(!E(_13D)){return E(_13R);}else{return B(_13w(_13O));}}),_13U=function(_13V){var _13W=E(_13V);return (_13W==1)?E(new T2(1,_13A,_13T)):new T2(1,_13A,new T(function(){return B(_13U(_13W-1|0));}));};return new F(function(){return _13U(_13S);});}};if(!E(_13D)){var _13X=B(_13P(_));return (_13X._==0)?__Z:new T2(1,_13z,_13X);}else{if(!B(_cm(_13O,_126))){var _13Y=B(_13P(_));return (_13Y._==0)?__Z:new T2(1,_13z,_13Y);}else{return __Z;}}}else{return E(_pq);}};if(_13K>=_13J){return B(_13L(_13K));}else{return B(_13L(_13K+1|0));}},1);return new F(function(){return _q(B(_13p(0,_13G.a,_S)),_13I);});}else{return E(_9T);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_13B(_13C,_13D,B(_fs(_13E))));}));});}},_13Z=function(_140,_141,_){var _142=B(_139(_)),_143=new T(function(){var _144=new T(function(){var _145=new T(function(){var _146=B(_q(B(_13B(_ZC,_wt,B(_12P(_142)).b)),_ZE));if(!_146._){return E(_RC);}else{var _147=B(_Rx(_146.a,_146.b));if(!_147._){return B(_ZJ(_S,_S,_T3));}else{var _148=_147.a,_149=E(_147.b);if(!_149._){return B(_ZJ(new T2(1,_148,_S),_S,_T3));}else{var _14a=E(_148),_14b=new T(function(){var _14c=B(_H4(46,_149.a,_149.b));return new T2(0,_14c.a,_14c.b);});if(E(_14a)==46){return B(_ZJ(_S,new T2(1,new T(function(){return E(E(_14b).a);}),new T(function(){return E(E(_14b).b);})),_T3));}else{return B(_ZJ(new T2(1,_14a,new T(function(){return E(E(_14b).a);})),new T(function(){return E(E(_14b).b);}),_T3));}}}}}),_14d=B(_Gc(B(_sx(_13f,_145))));if(!_14d._){return E(_13e);}else{if(!E(_14d.b)._){return B(_pN(3,B(_A(0,E(_14d.a)+(imul(E(_141),E(_140)-1|0)|0)|0,_S))));}else{return E(_13d);}}}),_14e=B(_Gc(B(_sx(_13f,_144))));if(!_14e._){return E(_13e);}else{if(!E(_14e.b)._){return E(_14e.a);}else{return E(_13d);}}});return new T2(0,new T(function(){return B(_au(_143,_140));}),_143);},_14f=function(_14g,_14h){while(1){var _14i=E(_14h);if(!_14i._){return __Z;}else{var _14j=_14i.b,_14k=E(_14g);if(_14k==1){return E(_14j);}else{_14g=_14k-1|0;_14h=_14j;continue;}}}},_14l=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_14m=new T(function(){return B(err(_14l));}),_14n=0,_14o=function(_14p,_14q,_14r){return new F(function(){return _A(E(_14p),E(_14q),_14r);});},_14s=function(_14t,_14u){return new F(function(){return _A(0,E(_14t),_14u);});},_14v=function(_14w,_14x){return new F(function(){return _2v(_14s,_14w,_14x);});},_14y=new T3(0,_14o,_6A,_14v),_14z=0,_14A=new T(function(){return B(unCStr(" out of range "));}),_14B=new T(function(){return B(unCStr("}.index: Index "));}),_14C=new T(function(){return B(unCStr("Ix{"));}),_14D=new T2(1,_y,_S),_14E=new T2(1,_y,_14D),_14F=0,_14G=function(_14H){return E(E(_14H).a);},_14I=function(_14J,_14K,_14L,_14M,_14N){var _14O=new T(function(){var _14P=new T(function(){var _14Q=new T(function(){var _14R=new T(function(){var _14S=new T(function(){return B(A3(_sc,_6w,new T2(1,new T(function(){return B(A3(_14G,_14L,_14F,_14M));}),new T2(1,new T(function(){return B(A3(_14G,_14L,_14F,_14N));}),_S)),_14E));});return B(_q(_14A,new T2(1,_z,new T2(1,_z,_14S))));});return B(A(_14G,[_14L,_14z,_14K,new T2(1,_y,_14R)]));});return B(_q(_14B,new T2(1,_z,_14Q)));},1);return B(_q(_14J,_14P));},1);return new F(function(){return err(B(_q(_14C,_14O)));});},_14T=function(_14U,_14V,_14W,_14X,_14Y){return new F(function(){return _14I(_14U,_14V,_14Y,_14W,_14X);});},_14Z=function(_150,_151,_152,_153){var _154=E(_152);return new F(function(){return _14T(_150,_151,_154.a,_154.b,_153);});},_155=function(_156,_157,_158,_159){return new F(function(){return _14Z(_159,_158,_157,_156);});},_15a=new T(function(){return B(unCStr("Int"));}),_15b=function(_15c,_15d,_15e){return new F(function(){return _155(_14y,new T2(0,_15d,_15e),_15c,_15a);});},_15f=new T(function(){return B(unCStr("Negative range size"));}),_15g=new T(function(){return B(err(_15f));}),_15h=function(_15i){var _15j=B(A1(_15i,_));return E(_15j);},_15k=function(_15l,_15m,_15n,_){var _15o=E(_15l);if(!_15o){return new T2(0,_S,_15m);}else{var _15p=new T(function(){return B(_ms(_15n,0))-1|0;}),_15q=B(_13Z(new T(function(){return E(_15p)+1|0;}),_15m,_)),_15r=E(_15q),_15s=_15r.a,_15t=_15r.b,_15u=new T(function(){var _15v=E(_15s);if(B(_ms(_15n,0))>=(_15v+1|0)){var _15w=new T(function(){var _15x=_15v+1|0;if(_15x>0){return B(_14f(_15x,_15n));}else{return E(_15n);}});if(0>=_15v){return E(_15w);}else{var _15y=function(_15z,_15A){var _15B=E(_15z);if(!_15B._){return E(_15w);}else{var _15C=_15B.a,_15D=E(_15A);return (_15D==1)?new T2(1,_15C,_15w):new T2(1,_15C,new T(function(){return B(_15y(_15B.b,_15D-1|0));}));}};return B(_15y(_15n,_15v));}}else{return E(_15n);}}),_15E=B(_15k(_15o-1|0,_15t,_15u,_)),_15F=new T(function(){var _15G=function(_){var _15H=E(_15p),_15I=function(_15J){if(_15J>=0){var _15K=newArr(_15J,_14m),_15L=_15K,_15M=E(_15J);if(!_15M){return new T4(0,E(_14n),E(_15H),0,_15L);}else{var _15N=function(_15O,_15P,_){while(1){var _15Q=E(_15O);if(!_15Q._){return E(_);}else{var _=_15L[_15P]=_15Q.a;if(_15P!=(_15M-1|0)){var _15R=_15P+1|0;_15O=_15Q.b;_15P=_15R;continue;}else{return E(_);}}}},_=B(_15N(_15n,0,_));return new T4(0,E(_14n),E(_15H),_15M,_15L);}}else{return E(_15g);}};if(0>_15H){return new F(function(){return _15I(0);});}else{return new F(function(){return _15I(_15H+1|0);});}},_15S=B(_15h(_15G)),_15T=E(_15S.a),_15U=E(_15S.b),_15V=E(_15s);if(_15T>_15V){return B(_15b(_15V,_15T,_15U));}else{if(_15V>_15U){return B(_15b(_15V,_15T,_15U));}else{return E(_15S.d[_15V-_15T|0]);}}});return new T2(0,new T2(1,_15F,new T(function(){return B(_si(_15E));})),_15t);}},_15W=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_15X=function(_15Y,_15Z,_160,_161,_){var _162=__app1(E(_gG),_161),_163=__app3(E(_15W),_161,E(_15Y),E(_15Z)),_164=B(A2(_160,_161,_)),_165=__app1(E(_gF),_161);return new F(function(){return _gE(_);});},_166=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_167=function(_168,_169,_16a,_16b,_){var _16c=__app4(E(_166),_16b,_168,_169,_16a);return new F(function(){return _gE(_);});},_16d=2,_16e=function(_16f,_16g,_16h,_16i,_16j,_16k,_){var _16l=function(_16m,_){return new F(function(){return _15X(_16d,_16d,function(_16n,_){return new F(function(){return _167(B(_6Q(_16g,E(_16k))),0,0,E(_16n),_);});},E(_16m),_);});};return new F(function(){return _gR(new T(function(){return E(_16h)-E(_16i)*16;},1),new T(function(){return E(_16j)*20;},1),_16l,_16f,_);});},_16o=function(_16p){return E(_16p).c;},_16q=function(_16r,_16s,_16t,_16u,_16v,_16w,_){var _16x=new T(function(){return E(E(_16w).q);}),_16y=new T(function(){return E(E(_16x).a);}),_16z=new T(function(){if(!B(_an(E(_16w).r,8))){var _16A=E(E(_16x).b);if(!(_16A%2)){return _16A+1|0;}else{return _16A-1|0;}}else{return E(E(_16x).b);}}),_16B=new T(function(){var _16C=E(_16w);return {_:0,a:E(_16C.a),b:E(_16C.b),c:E(_16C.c),d:E(_16C.d),e:E(_16C.e),f:E(_16C.f),g:E(_16C.g),h:E(_16C.h),i:_16C.i,j:_16C.j,k:_16C.k,l:_16C.l,m:E(_16C.m),n:_16C.n,o:E(_16C.o),p:E(_16C.p),q:E(new T2(0,_16y,_16z)),r:_16C.r,s:E(_16C.s),t:E(_16C.t)};}),_16D=new T(function(){return E(E(_16B).a);}),_16E=new T(function(){return E(E(_16B).b);}),_16F=new T(function(){return E(E(_16E).a);}),_16G=new T(function(){var _16H=E(_16t)/16,_16I=_16H&4294967295;if(_16H>=_16I){return _16I-2|0;}else{return (_16I-1|0)-2|0;}}),_16J=B(_np(_16r,_16s,new T(function(){return B(_b3(_16G,_16F));}),_nO,new T(function(){return E(E(_16D).b);}),_)),_16K=new T(function(){return E(E(E(_16B).a).a);}),_16L=B(A(_mN,[_16r,new T(function(){if(E(E(_16D).d)==32){return E(_nM);}else{return E(_nN);}}),new T(function(){return ((E(E(_16K).a)+E(_16G)|0)-E(_16F)|0)+1|0;},1),new T(function(){return (E(E(_16K).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_16o(_16D));}),_S),_])),_16M=function(_){var _16N=B(_16e(_16r,new T(function(){return E(E(_16v).b);},1),_16t,new T(function(){return E(_16F)+7|0;},1),_nO,new T(function(){return (imul(E(_16y),8)|0)+E(_16z)|0;},1),_));return _16B;};if(!E(E(E(_16w).s).c)){var _16O=new T(function(){return (2+E(E(_16E).b)|0)+3|0;}),_16P=B(_j9(new T2(0,_16r,_16s),_16u,0,_16O,new T(function(){var _16Q=E(_16t)/28,_16R=_16Q&4294967295;if(_16Q>=_16R){return (_16R-1|0)+E(_16B).k|0;}else{return ((_16R-1|0)-1|0)+E(_16B).k|0;}}),_16O,B(_US(_16B)),_));return new F(function(){return _16M(_);});}else{return new F(function(){return _16M(_);});}},_16S=function(_16T,_16U){while(1){var _16V=E(_16T);if(!_16V._){return E(_16U);}else{_16T=_16V.b;_16U=_16V.a;continue;}}},_16W=function(_16X,_16Y,_16Z){return new F(function(){return _16S(_16Y,_16X);});},_170=function(_171,_172){while(1){var _173=E(_171);if(!_173._){return E(_172);}else{_171=_173.b;_172=_173.a;continue;}}},_174=function(_175,_176,_177){return new F(function(){return _170(_176,_175);});},_178=function(_179,_17a){while(1){var _17b=E(_17a);if(!_17b._){return __Z;}else{var _17c=_17b.b,_17d=E(_179);if(_17d==1){return E(_17c);}else{_179=_17d-1|0;_17a=_17c;continue;}}}},_17e=function(_17f,_17g){var _17h=new T(function(){var _17i=_17f+1|0;if(_17i>0){return B(_178(_17i,_17g));}else{return E(_17g);}});if(0>=_17f){return E(_17h);}else{var _17j=function(_17k,_17l){var _17m=E(_17k);if(!_17m._){return E(_17h);}else{var _17n=_17m.a,_17o=E(_17l);return (_17o==1)?new T2(1,_17n,_17h):new T2(1,_17n,new T(function(){return B(_17j(_17m.b,_17o-1|0));}));}};return new F(function(){return _17j(_17g,_17f);});}},_17p=new T(function(){return B(unCStr(":"));}),_17q=function(_17r){var _17s=E(_17r);if(!_17s._){return __Z;}else{var _17t=new T(function(){return B(_q(_17p,new T(function(){return B(_17q(_17s.b));},1)));},1);return new F(function(){return _q(_17s.a,_17t);});}},_17u=function(_17v,_17w){var _17x=new T(function(){return B(_q(_17p,new T(function(){return B(_17q(_17w));},1)));},1);return new F(function(){return _q(_17v,_17x);});},_17y=function(_17z){return new F(function(){return _La("Check.hs:173:7-35|(co : na : xs)");});},_17A=new T(function(){return B(_17y(_));}),_17B=new T(function(){return B(err(_sq));}),_17C=new T(function(){return B(err(_ss));}),_17D=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_17E=0,_17F=new T(function(){return B(unCStr("!"));}),_17G=function(_17H,_17I){var _17J=E(_17I);if(!_17J._){return E(_17A);}else{var _17K=E(_17J.b);if(!_17K._){return E(_17A);}else{var _17L=E(_17J.a),_17M=new T(function(){var _17N=B(_H4(58,_17K.a,_17K.b));return new T2(0,_17N.a,_17N.b);}),_17O=function(_17P,_17Q,_17R){var _17S=function(_17T){if((_17H+1|0)!=_17T){return new T3(0,_17H+1|0,_17Q,_17J);}else{var _17U=E(_17R);return (_17U._==0)?new T3(0,_17E,_17Q,_S):new T3(0,_17E,_17Q,new T(function(){var _17V=B(_17u(_17U.a,_17U.b));if(!_17V._){return E(_RC);}else{return B(_Rx(_17V.a,_17V.b));}}));}};if(!B(_qN(_17P,_17F))){var _17W=B(_Gc(B(_sx(_17D,_17P))));if(!_17W._){return E(_17B);}else{if(!E(_17W.b)._){return new F(function(){return _17S(E(_17W.a));});}else{return E(_17C);}}}else{return new F(function(){return _17S( -1);});}};if(E(_17L)==58){return new F(function(){return _17O(_S,new T(function(){return E(E(_17M).a);}),new T(function(){return E(E(_17M).b);}));});}else{var _17X=E(_17M),_17Y=E(_17X.b);if(!_17Y._){return E(_17A);}else{return new F(function(){return _17O(new T2(1,_17L,_17X.a),_17Y.a,_17Y.b);});}}}}},_17Z=function(_180,_181){while(1){var _182=E(_181);if(!_182._){return __Z;}else{var _183=_182.b,_184=E(_180);if(_184==1){return E(_183);}else{_180=_184-1|0;_181=_183;continue;}}}},_185=function(_186,_187,_188){var _189=new T2(1,_187,new T(function(){var _18a=_186+1|0;if(_18a>0){return B(_17Z(_18a,_188));}else{return E(_188);}}));if(0>=_186){return E(_189);}else{var _18b=function(_18c,_18d){var _18e=E(_18c);if(!_18e._){return E(_189);}else{var _18f=_18e.a,_18g=E(_18d);return (_18g==1)?new T2(1,_18f,_189):new T2(1,_18f,new T(function(){return B(_18b(_18e.b,_18g-1|0));}));}};return new F(function(){return _18b(_188,_186);});}},_18h=new T2(0,_Rf,_E8),_18i=function(_18j,_18k,_18l){while(1){var _18m=E(_18l);if(!_18m._){return E(_18h);}else{var _18n=_18m.b,_18o=E(_18m.a),_18p=E(_18o.a);if(_18j!=E(_18p.a)){_18l=_18n;continue;}else{if(_18k!=E(_18p.b)){_18l=_18n;continue;}else{return E(_18o.b);}}}}},_18q=function(_18r,_18s){while(1){var _18t=E(_18s);if(!_18t._){return __Z;}else{var _18u=_18t.b,_18v=E(_18r);if(_18v==1){return E(_18u);}else{_18r=_18v-1|0;_18s=_18u;continue;}}}},_18w=function(_18x,_18y,_18z){var _18A=E(_18x);if(_18A==1){return E(_18z);}else{return new F(function(){return _18q(_18A-1|0,_18z);});}},_18B=function(_18C,_18D,_18E){return new T2(1,new T(function(){if(0>=_18C){return __Z;}else{return B(_pN(_18C,new T2(1,_18D,_18E)));}}),new T(function(){if(_18C>0){return B(_18F(_18C,B(_18w(_18C,_18D,_18E))));}else{return B(_18B(_18C,_18D,_18E));}}));},_18F=function(_18G,_18H){var _18I=E(_18H);if(!_18I._){return __Z;}else{var _18J=_18I.a,_18K=_18I.b;return new T2(1,new T(function(){if(0>=_18G){return __Z;}else{return B(_pN(_18G,_18I));}}),new T(function(){if(_18G>0){return B(_18F(_18G,B(_18w(_18G,_18J,_18K))));}else{return B(_18B(_18G,_18J,_18K));}}));}},_18L=function(_18M,_18N,_18O){var _18P=_18N-1|0;if(0<=_18P){var _18Q=E(_18M),_18R=function(_18S){var _18T=new T(function(){if(_18S!=_18P){return B(_18R(_18S+1|0));}else{return __Z;}}),_18U=function(_18V){var _18W=E(_18V);return (_18W._==0)?E(_18T):new T2(1,new T(function(){var _18X=E(_18O);if(!_18X._){return E(_18h);}else{var _18Y=_18X.b,_18Z=E(_18X.a),_190=E(_18Z.a),_191=E(_18W.a);if(_191!=E(_190.a)){return B(_18i(_191,_18S,_18Y));}else{if(_18S!=E(_190.b)){return B(_18i(_191,_18S,_18Y));}else{return E(_18Z.b);}}}}),new T(function(){return B(_18U(_18W.b));}));};return new F(function(){return _18U(B(_8r(0,_18Q-1|0)));});};return new F(function(){return _18F(_18Q,B(_18R(0)));});}else{return __Z;}},_192=function(_193){return new F(function(){return _La("Check.hs:72:21-47|(l : r : _)");});},_194=new T(function(){return B(_192(_));}),_195=61,_196=function(_197,_198){while(1){var _199=E(_197);if(!_199._){return E(_198);}else{_197=_199.b;_198=_199.a;continue;}}},_19a=function(_19b,_19c,_19d){return new F(function(){return _196(_19c,_19b);});},_19e=function(_19f,_19g){var _19h=E(_19g);if(!_19h._){return new T2(0,_S,_S);}else{var _19i=_19h.a;if(!B(A1(_19f,_19i))){var _19j=new T(function(){var _19k=B(_19e(_19f,_19h.b));return new T2(0,_19k.a,_19k.b);});return new T2(0,new T2(1,_19i,new T(function(){return E(E(_19j).a);})),new T(function(){return E(E(_19j).b);}));}else{return new T2(0,_S,_19h);}}},_19l=function(_19m,_19n){while(1){var _19o=E(_19n);if(!_19o._){return __Z;}else{if(!B(A1(_19m,_19o.a))){return E(_19o);}else{_19n=_19o.b;continue;}}}},_19p=function(_19q){var _19r=_19q>>>0;if(_19r>887){var _19s=u_iswspace(_19q);return (E(_19s)==0)?false:true;}else{var _19t=E(_19r);return (_19t==32)?true:(_19t-9>>>0>4)?(E(_19t)==160)?true:false:true;}},_19u=function(_19v){return new F(function(){return _19p(E(_19v));});},_19w=function(_19x){var _19y=B(_19l(_19u,_19x));if(!_19y._){return __Z;}else{var _19z=new T(function(){var _19A=B(_19e(_19u,_19y));return new T2(0,_19A.a,_19A.b);});return new T2(1,new T(function(){return E(E(_19z).a);}),new T(function(){return B(_19w(E(_19z).b));}));}},_19B=function(_19C){if(!B(_4A(_h6,_195,_19C))){return new T2(0,_19C,_S);}else{var _19D=new T(function(){var _19E=E(_19C);if(!_19E._){return E(_194);}else{var _19F=E(_19E.b);if(!_19F._){return E(_194);}else{var _19G=_19F.a,_19H=_19F.b,_19I=E(_19E.a);if(E(_19I)==61){return new T2(0,_S,new T(function(){return E(B(_H4(61,_19G,_19H)).a);}));}else{var _19J=B(_H4(61,_19G,_19H)),_19K=E(_19J.b);if(!_19K._){return E(_194);}else{return new T2(0,new T2(1,_19I,_19J.a),_19K.a);}}}}});return new T2(0,new T(function(){var _19L=B(_19w(E(_19D).a));if(!_19L._){return __Z;}else{return B(_19a(_19L.a,_19L.b,_T3));}}),new T(function(){var _19M=B(_19w(E(_19D).b));if(!_19M._){return __Z;}else{return E(_19M.a);}}));}},_19N=function(_19O,_19P){return new F(function(){return _17e(E(_19O),_19P);});},_19Q=function(_19R){var _19S=E(_19R);if(!_19S._){return new T2(0,_S,_S);}else{var _19T=E(_19S.a),_19U=new T(function(){var _19V=B(_19Q(_19S.b));return new T2(0,_19V.a,_19V.b);});return new T2(0,new T2(1,_19T.a,new T(function(){return E(E(_19U).a);})),new T2(1,_19T.b,new T(function(){return E(E(_19U).b);})));}},_19W=new T(function(){return B(unCStr("\u306d\u3048 \u8d77\u304d\u3066\u3088\u30fb\u30fb\u30fb\u3002 {ch.\u8d77\u304d\u308b,s0.\u8d77\u304d\u306a\u3044,initMsg}"));}),_19X=new T(function(){return B(unCStr("nubatama"));}),_19Y=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_19Z=new T2(0,_19X,_19Y),_1a0=new T(function(){return B(unCStr("s1"));}),_1a1=new T(function(){return B(unCStr("\n\u3082\u306e\u3092 \u304b\u305e\u3078\u308b\u306e\u304c \u6578\uff1a\u304b\u305a\uff1a\u3067\u3059\u3002\n\u3082\u3057 \u79c1\u305f\u3061\u304c \u3053\u306e\u4e16\u754c\u3092 \u5206\uff1a\u308f\uff1a\u3051\u3066\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u306a\u3044\u306a\u3089 \u6578\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3084\u3046\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u5206\u3051\u3089\u308c\u3066\u3090\u308b\u304b\u3089 \u6578\u3078\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059 {da}{e.b0.m0:s100}"));}),_1a2=new T2(0,_1a0,_1a1),_1a3=new T(function(){return B(unCStr("s100"));}),_1a4=new T(function(){return B(unCStr("\n\u3053\u308c\u306f \u5206\u3051\u3089\u308c\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_0.\u3044\u3044\u3048,s1_1}"));}),_1a5=new T2(0,_1a3,_1a4),_1a6=new T(function(){return B(unCStr("s1_0"));}),_1a7=new T(function(){return B(unCStr("\n\u3067\u306f \u5206\u3051\u3066\u304f\u3060\u3055\u3044 {ct.0.Fr}{d.b0}{e.e0.m0:s101}"));}),_1a8=new T2(0,_1a6,_1a7),_1a9=new T(function(){return B(unCStr("s4"));}),_1aa=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_1ab=new T2(0,_1a9,_1aa),_1ac=new T2(1,_1ab,_S),_1ad=new T(function(){return B(unCStr("s3"));}),_1ae=new T(function(){return B(unCStr("\n\u3053\u306e\u4e16\u754c\u306b\u907a\uff1a\u306e\u3053\uff1a\u3055\u308c\u305f\u8a00\uff1a\u3053\u3068\uff1a\u8449\uff1a\u3070\uff1a \u305d\u308c\u304c \u53f2\uff1a\u3075\u307f\uff1a \u3067\u3059\u3002\n\u79c1\u305f\u3061\u306f \u305d\u308c\u306b\u3088\u3063\u3066 \u4eba\uff1a\u3058\u3093\uff1a\u751f\uff1a\u305b\u3044\uff1a\u306e\u9577\u3055\u3092\u306f\u308b\u304b\u306b\u8d8a\uff1a\u3053\uff1a\u3048\u305f \u8a18\uff1a\u304d\uff1a\u61b6\uff1a\u304a\u304f\uff1a\u3092\u8fbf\uff1a\u305f\u3069\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1af=new T2(0,_1ad,_1ae),_1ag=new T2(1,_1af,_1ac),_1ah=new T(function(){return B(unCStr("s2"));}),_1ai=new T(function(){return B(unCStr("\n\u3082\u306e\u3054\u3068\u306e\u7b4b\uff1a\u3059\u3058\uff1a\u9053\uff1a\u307f\u3061\uff1a\u304c \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u3067\u3059\u3002\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306e\u3053\u3068 \u5618\uff1a\u3046\u305d\uff1a\u306e\u3053\u3068\u3002\n\u6b63\uff1a\u305f\u3060\uff1a\u3057\u3044\u3053\u3068 \u9593\uff1a\u307e\uff1a\u9055\uff1a\u3061\u304c\uff1a\u3063\u3066\u3090\u308b\u3053\u3068\u3002\n\u305d\u308c\u3092 \u306f\u3063\u304d\u308a\u3055\u305b\u308b\u306e\u304c \u7406 \u3067\u3059"));}),_1aj=new T2(0,_1ah,_1ai),_1ak=new T2(1,_1aj,_1ag),_1al=new T(function(){return B(unCStr("s1c"));}),_1am=new T(function(){return B(unCStr("\n\u6249\u304c\u958b\u304b\u308c\u305f\u3084\u3046\u3067\u3059 {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"));}),_1an=new T2(0,_1al,_1am),_1ao=new T2(1,_1an,_1ak),_1ap=new T(function(){return B(unCStr("s104"));}),_1aq=new T(function(){return B(unCStr("\n\u706b\uff1a\u3072\uff1a(\uff11)\u3068\u6c34\uff1a\u307f\u3065\uff1a(\uff12)\u3092\u5408\u306f\u305b\u308b\u3068 \u3072\u307f\u3064(\uff13) \u306b\u306a\u308a\u307e\u3059\u3002\n\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u306f \u307e\u3046\u958b\uff1a\u3072\u3089\uff1a\u304b\u308c\u308b\u3067\u305b\u3046\u3002\n\u9375\uff1a\u304b\u304e\uff1a\u3092\u624b\u306b\u5165\u308c\u305f\u306e\u3067\u3059\u304b\u3089 {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"));}),_1ar=new T2(0,_1ap,_1aq),_1as=new T2(1,_1ar,_1ao),_1at=new T(function(){return B(unCStr("s103"));}),_1au=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u304c\u5b58\u5728\u3059\u308b\u9650\uff1a\u304b\u304e\uff1a\u308a \u6578\u306f\u7121\uff1a\u3080\uff1a\u9650\uff1a\u3052\u3093\uff1a\u306b\u3064\u304f\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3053\u308c\u3089\u304c\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u306b\u7f6e\uff1a\u304a\uff1a\u304b\u308c\u3066\u3090\u305f\u4f4d\uff1a\u3044\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u5165\uff1a\u3044\uff1a\u308c\u66ff\uff1a\u304b\uff1a\u3078\u305f\u3089 \u4f55\uff1a\u306a\u306b\uff1a\u304b\u8d77\uff1a\u304a\uff1a\u3053\u308a\u3055\u3046\u3067\u3059 {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"));}),_1av=new T2(0,_1at,_1au),_1aw=new T2(1,_1av,_1as),_1ax=new T(function(){return B(unCStr("s102"));}),_1ay=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u3068\u3044\u3075\u5b58\u5728\u3068 \uff1c\u7121\u3044\uff1e\u3068\u3044\u3075\u5b58\u5728\u304c\u3067\u304d\u307e\u3057\u305f\u3002\n\uff1c\u5b58\u5728\uff1e\u3092 1 \u3068\u3059\u308b\u306a\u3089 \u3053\u308c\u3089\u3092\u5408\u306f\u305b\u305f\u540d\u524d\u3092\u3064\u304f\u308a\u307e\u305b\u3046 {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"));}),_1az=new T2(0,_1ax,_1ay),_1aA=new T2(1,_1az,_1aw),_1aB=new T(function(){return B(unCStr("s1_3"));}),_1aC=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u5206\u3051\u305f\u3068\u601d\uff1a\u304a\u3082\uff1a\u306f\u306a\u3044\u306e\u3067\u3042\u308c\u3070\u3002\n\u305d\u308c\u306f \u5206\u304b\u308c\u3066\u3090\u307e\u305b\u3093"));}),_1aD=new T2(0,_1aB,_1aC),_1aE=new T2(1,_1aD,_1aA),_1aF=new T(function(){return B(unCStr("s1_2"));}),_1aG=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u4e16\u754c\u3092 \u5206\u3051\u3066\n\u300c\u5728\uff1a\u3042\uff1a\u308b\u3002\n\u300c\u7121\uff1a\u306a\uff1a\u3044\u3002\n\u3092\u3064\u304f\u308a\u307e\u3057\u305f\u3002\n\u305d\u308c\u3067\u306f \u3053\u306e \uff1c\u5728\u308b\uff1e\u3092 1 \u3068\u547c\uff1a\u3088\uff1a\u3073\u307e\u305b\u3046 {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"));}),_1aH=new T2(0,_1aF,_1aG),_1aI=new T2(1,_1aH,_1aE),_1aJ=new T(function(){return B(unCStr("s101"));}),_1aK=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u3053\u308c\u3092\u53d6\uff1a\u3068\uff1a\u3063\u305f\u306e\u3067 \u305d\u308c\u306f \u307e\u3046\u3053\u3053\u306b\u3042\u308a\u307e\u305b\u3093\u3002\n\u3053\u308c\u306f \u5206\u3051\u305f\u3053\u3068\u306b\u306a\u308a\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_2.\u3044\u3044\u3048,s1_3}"));}),_1aL=new T2(0,_1aJ,_1aK),_1aM=new T2(1,_1aL,_1aI),_1aN=new T(function(){return B(unCStr("s1_1"));}),_1aO=new T(function(){return B(unCStr("\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306b\u5206\u3051\u3089\u308c\u306a\u3044\u306e\u3067\u305b\u3046\u304b"));}),_1aP=new T2(0,_1aN,_1aO),_1aQ=new T2(1,_1aP,_1aM),_1aR=new T2(1,_1a8,_1aQ),_1aS=new T2(1,_1a5,_1aR),_1aT=new T2(1,_1a2,_1aS),_1aU=new T2(1,_19Z,_1aT),_1aV=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1aW=new T(function(){return B(unCStr("msgW"));}),_1aX=new T2(0,_1aW,_1aV),_1aY=new T2(1,_1aX,_1aU),_1aZ=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_1b0=new T(function(){return B(unCStr("msgR"));}),_1b1=new T2(0,_1b0,_1aZ),_1b2=new T2(1,_1b1,_1aY),_1b3=new T(function(){return B(unCStr("sc0"));}),_1b4=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002"));}),_1b5=new T2(0,_1b3,_1b4),_1b6=new T2(1,_1b5,_1b2),_1b7=new T(function(){return B(unCStr("s0"));}),_1b8=new T(function(){return B(unCStr("\n{sm}\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066 {rk.1.z.abc.sc0}"));}),_1b9=new T2(0,_1b7,_1b8),_1ba=new T2(1,_1b9,_1b6),_1bb=new T(function(){return B(unCStr("initMsg"));}),_1bc=function(_1bd,_1be){var _1bf=new T(function(){var _1bg=B(_19Q(_1bd));return new T2(0,_1bg.a,_1bg.b);}),_1bh=function(_1bi){var _1bj=E(_1bi);if(!_1bj._){return E(_1bf);}else{var _1bk=E(_1bj.a),_1bl=new T(function(){return B(_1bh(_1bj.b));});return new T2(0,new T2(1,_1bk.a,new T(function(){return E(E(_1bl).a);})),new T2(1,_1bk.b,new T(function(){return E(E(_1bl).b);})));}},_1bm=function(_1bn,_1bo,_1bp){var _1bq=new T(function(){return B(_1bh(_1bp));});return new T2(0,new T2(1,_1bn,new T(function(){return E(E(_1bq).a);})),new T2(1,_1bo,new T(function(){return E(E(_1bq).b);})));},_1br=B(_1bm(_1bb,_19W,_1ba)),_1bs=_1br.a;if(!B(_4A(_qd,_1be,_1bs))){return __Z;}else{return new F(function(){return _6Q(_1br.b,B(_Mt(_qd,_1be,_1bs)));});}},_1bt=7,_1bu=new T2(0,_1bt,_1bt),_1bv=new T2(1,_1bu,_S),_1bw=5,_1bx=new T2(0,_1bw,_1bt),_1by=new T2(1,_1bx,_1bv),_1bz=new T2(0,_1bw,_1bw),_1bA=new T2(1,_1bz,_1by),_1bB=new T2(1,_1bz,_1bA),_1bC=new T2(1,_1bz,_1bB),_1bD=2,_1bE=4,_1bF=new T2(0,_1bE,_1bD),_1bG=new T2(1,_1bF,_S),_1bH=new T2(0,_1bD,_1bD),_1bI=new T2(1,_1bH,_1bG),_1bJ=new T2(1,_1bH,_1bI),_1bK=new T2(1,_1bH,_1bJ),_1bL=new T2(1,_1bH,_1bK),_1bM=new T(function(){return B(unCStr("Int"));}),_1bN=function(_1bO,_1bP,_1bQ){return new F(function(){return _155(_14y,new T2(0,_1bP,_1bQ),_1bO,_1bM);});},_1bR=new T(function(){return B(unCStr("msgR"));}),_1bS=new T(function(){return B(_1bc(_S,_1bR));}),_1bT=new T(function(){return B(unCStr("msgW"));}),_1bU=new T(function(){return B(_1bc(_S,_1bT));}),_1bV=function(_1bW){var _1bX=E(_1bW);return 0;},_1bY=new T(function(){return B(unCStr("@@@@@"));}),_1bZ=new T(function(){var _1c0=E(_1bY);if(!_1c0._){return E(_ng);}else{return E(_1c0.a);}}),_1c1=122,_1c2=new T2(0,_1c1,_Ee),_1c3=0,_1c4=new T2(0,_1c3,_1c3),_1c5=new T2(0,_1c4,_1c2),_1c6=61,_1c7=new T2(0,_1c6,_Ee),_1c8=1,_1c9=new T2(0,_1c8,_1c3),_1ca=new T2(0,_1c9,_1c7),_1cb=99,_1cc=new T2(0,_1cb,_E8),_1cd=new T2(0,_1bE,_1bE),_1ce=new T2(0,_1cd,_1cc),_1cf=new T2(1,_1ce,_S),_1cg=98,_1ch=new T2(0,_1cg,_E8),_1ci=new T2(0,_1bD,_1bE),_1cj=new T2(0,_1ci,_1ch),_1ck=new T2(1,_1cj,_1cf),_1cl=97,_1cm=new T2(0,_1cl,_E8),_1cn=new T2(0,_1c3,_1bE),_1co=new T2(0,_1cn,_1cm),_1cp=new T2(1,_1co,_1ck),_1cq=new T2(1,_1ca,_1cp),_1cr=new T2(1,_1c5,_1cq),_1cs=new T(function(){return B(_18L(_1bw,5,_1cr));}),_1ct=new T(function(){return B(_La("Check.hs:142:22-33|(ch : po)"));}),_1cu=new T(function(){return B(_e6("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1cv=48,_1cw=new T2(0,_1cv,_Ee),_1cx=new T2(0,_1bD,_1c3),_1cy=new T2(0,_1cx,_1cw),_1cz=new T2(1,_1cy,_S),_1cA=6,_1cB=new T2(0,_1c3,_1cA),_1cC=new T2(0,_1cB,_1cm),_1cD=new T2(0,_1bD,_1cA),_1cE=new T2(0,_1cD,_1ch),_1cF=new T2(0,_1bE,_1cA),_1cG=new T2(0,_1cF,_1cc),_1cH=new T2(1,_1cG,_S),_1cI=new T2(1,_1cE,_1cH),_1cJ=new T2(1,_1cC,_1cI),_1cK=new T2(1,_1ca,_1cJ),_1cL=new T2(1,_1c5,_1cK),_1cM=new T2(1,_S,_S),_1cN=new T2(1,_1cL,_1cM),_1cO=new T2(1,_S,_1cN),_1cP=new T2(1,_1cz,_1cO),_1cQ=new T2(1,_1cr,_1cP),_1cR=function(_1cS){var _1cT=E(_1cS);if(!_1cT._){return __Z;}else{var _1cU=_1cT.b,_1cV=E(_1cT.a),_1cW=_1cV.b,_1cX=E(_1cV.a),_1cY=function(_1cZ){if(E(_1cX)==32){return new T2(1,_1cV,new T(function(){return B(_1cR(_1cU));}));}else{switch(E(_1cW)){case 0:return new T2(1,new T2(0,_1cX,_E8),new T(function(){return B(_1cR(_1cU));}));case 1:return new T2(1,new T2(0,_1cX,_EJ),new T(function(){return B(_1cR(_1cU));}));case 2:return new T2(1,new T2(0,_1cX,_Ek),new T(function(){return B(_1cR(_1cU));}));case 3:return new T2(1,new T2(0,_1cX,_Eq),new T(function(){return B(_1cR(_1cU));}));case 4:return new T2(1,new T2(0,_1cX,_Ew),new T(function(){return B(_1cR(_1cU));}));case 5:return new T2(1,new T2(0,_1cX,_EX),new T(function(){return B(_1cR(_1cU));}));case 6:return new T2(1,new T2(0,_1cX,_EQ),new T(function(){return B(_1cR(_1cU));}));case 7:return new T2(1,new T2(0,_1cX,_EJ),new T(function(){return B(_1cR(_1cU));}));default:return new T2(1,new T2(0,_1cX,_EC),new T(function(){return B(_1cR(_1cU));}));}}};if(E(_1cX)==32){return new F(function(){return _1cY(_);});}else{switch(E(_1cW)){case 0:return new T2(1,new T2(0,_1cX,_EC),new T(function(){return B(_1cR(_1cU));}));case 1:return new F(function(){return _1cY(_);});break;case 2:return new F(function(){return _1cY(_);});break;case 3:return new F(function(){return _1cY(_);});break;case 4:return new F(function(){return _1cY(_);});break;case 5:return new F(function(){return _1cY(_);});break;case 6:return new F(function(){return _1cY(_);});break;case 7:return new F(function(){return _1cY(_);});break;default:return new F(function(){return _1cY(_);});}}}},_1d0=function(_1d1){var _1d2=E(_1d1);return (_1d2._==0)?__Z:new T2(1,new T(function(){return B(_1cR(_1d2.a));}),new T(function(){return B(_1d0(_1d2.b));}));},_1d3=function(_1d4){var _1d5=E(_1d4);if(!_1d5._){return __Z;}else{var _1d6=_1d5.b,_1d7=E(_1d5.a),_1d8=_1d7.b,_1d9=E(_1d7.a),_1da=function(_1db){if(E(_1d9)==32){return new T2(1,_1d7,new T(function(){return B(_1d3(_1d6));}));}else{switch(E(_1d8)){case 0:return new T2(1,new T2(0,_1d9,_E8),new T(function(){return B(_1d3(_1d6));}));case 1:return new T2(1,new T2(0,_1d9,_Ee),new T(function(){return B(_1d3(_1d6));}));case 2:return new T2(1,new T2(0,_1d9,_Ek),new T(function(){return B(_1d3(_1d6));}));case 3:return new T2(1,new T2(0,_1d9,_Eq),new T(function(){return B(_1d3(_1d6));}));case 4:return new T2(1,new T2(0,_1d9,_Ew),new T(function(){return B(_1d3(_1d6));}));case 5:return new T2(1,new T2(0,_1d9,_EX),new T(function(){return B(_1d3(_1d6));}));case 6:return new T2(1,new T2(0,_1d9,_EQ),new T(function(){return B(_1d3(_1d6));}));case 7:return new T2(1,new T2(0,_1d9,_Ee),new T(function(){return B(_1d3(_1d6));}));default:return new T2(1,new T2(0,_1d9,_EC),new T(function(){return B(_1d3(_1d6));}));}}};if(E(_1d9)==32){return new F(function(){return _1da(_);});}else{if(E(_1d8)==8){return new T2(1,new T2(0,_1d9,_E8),new T(function(){return B(_1d3(_1d6));}));}else{return new F(function(){return _1da(_);});}}}},_1dc=function(_1dd){var _1de=E(_1dd);return (_1de._==0)?__Z:new T2(1,new T(function(){return B(_1d3(_1de.a));}),new T(function(){return B(_1dc(_1de.b));}));},_1df=function(_1dg,_1dh,_1di,_1dj,_1dk,_1dl,_1dm,_1dn,_1do,_1dp,_1dq,_1dr,_1ds,_1dt,_1du,_1dv,_1dw,_1dx,_1dy,_1dz,_1dA,_1dB,_1dC,_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_1dN,_1dO,_1dP,_1dQ,_1dR){var _1dS=E(_1dh);if(!_1dS._){return E(_1cu);}else{var _1dT=_1dS.b,_1dU=E(_1dS.a),_1dV=new T(function(){var _1dW=function(_){var _1dX=B(_ms(_1dw,0))-1|0,_1dY=function(_1dZ){if(_1dZ>=0){var _1e0=newArr(_1dZ,_14m),_1e1=_1e0,_1e2=E(_1dZ);if(!_1e2){return new T4(0,E(_17E),E(_1dX),0,_1e1);}else{var _1e3=function(_1e4,_1e5,_){while(1){var _1e6=E(_1e4);if(!_1e6._){return E(_);}else{var _=_1e1[_1e5]=_1e6.a;if(_1e5!=(_1e2-1|0)){var _1e7=_1e5+1|0;_1e4=_1e6.b;_1e5=_1e7;continue;}else{return E(_);}}}},_=B(_1e3(_1dw,0,_));return new T4(0,E(_17E),E(_1dX),_1e2,_1e1);}}else{return E(_15g);}};if(0>_1dX){return new F(function(){return _1dY(0);});}else{return new F(function(){return _1dY(_1dX+1|0);});}},_1e8=B(_15h(_1dW)),_1e9=E(_1e8.a),_1ea=E(_1e8.b),_1eb=E(_1dg);if(_1e9>_1eb){return B(_1bN(_1eb,_1e9,_1ea));}else{if(_1eb>_1ea){return B(_1bN(_1eb,_1e9,_1ea));}else{return E(_1e8.d[_1eb-_1e9|0]);}}});switch(E(_1dU)){case 97:var _1ec=new T(function(){var _1ed=E(_1dT);if(!_1ed._){return E(_1ct);}else{return new T2(0,_1ed.a,_1ed.b);}}),_1ee=new T(function(){var _1ef=B(_19B(E(_1ec).b));return new T2(0,_1ef.a,_1ef.b);}),_1eg=B(_Gc(B(_sx(_17D,new T(function(){return E(E(_1ee).b);})))));if(!_1eg._){return E(_17B);}else{if(!E(_1eg.b)._){var _1eh=new T(function(){var _1ei=B(_Gc(B(_sx(_17D,new T(function(){return E(E(_1ee).a);})))));if(!_1ei._){return E(_17B);}else{if(!E(_1ei.b)._){return E(_1ei.a);}else{return E(_17C);}}},1);return {_:0,a:E({_:0,a:E(_1di),b:E(B(_KJ(_1eh,E(_1eg.a),new T(function(){return E(E(_1ec).a);}),_E8,_1dj))),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};}else{return E(_17C);}}break;case 104:return {_:0,a:E({_:0,a:E(_1di),b:E(B(_1d0(_1dj))),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};case 106:var _1ej=E(_1dT);if(!_1ej._){return {_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l: -1,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};}else{if(E(_1ej.a)==108){var _1ek=E(_1dg),_1el=B(_Gc(B(_sx(_17D,_1ej.b))));return (_1el._==0)?E(_17B):(E(_1el.b)._==0)?{_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(B(_17e(_1ek,_1dv))),f:E(B(_17e(_1ek,_1dw))),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:E(_1el.a),m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_wt),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)}:E(_17C);}else{var _1em=B(_Gc(B(_sx(_17D,_1ej))));return (_1em._==0)?E(_17B):(E(_1em.b)._==0)?{_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:E(_1em.a),m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)}:E(_17C);}}break;case 108:var _1en=E(_1dg);return {_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(B(_17e(_1en,_1dv))),f:E(B(_17e(_1en,_1dw))),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_wt),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};case 109:var _1eo=B(_17G(E(_1dV),_1dT)),_1ep=_1eo.c,_1eq=B(_qN(_1ep,_S));if(!E(_1eq)){var _1er=E(_1dg),_1es=new T(function(){var _1et=function(_){var _1eu=B(_ms(_1dv,0))-1|0,_1ev=function(_1ew){if(_1ew>=0){var _1ex=newArr(_1ew,_14m),_1ey=_1ex,_1ez=E(_1ew);if(!_1ez){return new T4(0,E(_17E),E(_1eu),0,_1ey);}else{var _1eA=function(_1eB,_1eC,_){while(1){var _1eD=E(_1eB);if(!_1eD._){return E(_);}else{var _=_1ey[_1eC]=_1eD.a;if(_1eC!=(_1ez-1|0)){var _1eE=_1eC+1|0;_1eB=_1eD.b;_1eC=_1eE;continue;}else{return E(_);}}}},_=B(_1eA(_1dv,0,_));return new T4(0,E(_17E),E(_1eu),_1ez,_1ey);}}else{return E(_15g);}};if(0>_1eu){return new F(function(){return _1ev(0);});}else{return new F(function(){return _1ev(_1eu+1|0);});}},_1eF=B(_15h(_1et)),_1eG=E(_1eF.a),_1eH=E(_1eF.b);if(_1eG>_1er){return B(_1bN(_1er,_1eG,_1eH));}else{if(_1er>_1eH){return B(_1bN(_1er,_1eG,_1eH));}else{return E(E(_1eF.d[_1er-_1eG|0]).a);}}}),_1eI=B(_185(_1er,new T2(0,_1es,new T2(1,_1dU,_1ep)),_1dv));}else{var _1eI=B(_19N(_1dg,_1dv));}if(!E(_1eq)){var _1eJ=B(_185(E(_1dg),_1eo.a,_1dw));}else{var _1eJ=B(_19N(_1dg,_1dw));}return {_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(B(_1bc(_1du,_1eo.b))),d:E(_1du),e:E(_1eI),f:E(_1eJ),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_wt),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};case 114:var _1eK=B(_6Q(_1bC,_1dm));return {_:0,a:E({_:0,a:E(B(_6Q(_1bL,_1dm))),b:E(B(_18L(_1eK.a,E(_1eK.b),new T(function(){return B(_6Q(_1cQ,_1dm));})))),c:B(_6Q(_1bY,_1dm)),d:32,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1eK),c:E(_1bS),d:E(_1du),e:E(_1dv),f:E(B(_6d(_1bV,_1dw))),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_wt),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};case 115:return {_:0,a:E({_:0,a:E(_1di),b:E(B(_1dc(_1dj))),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};case 116:var _1eL=E(_1dV),_1eM=B(_17G(_1eL,_1dT)),_1eN=E(_1eM.a);if(!E(_1eN)){var _1eO=true;}else{var _1eO=false;}if(!E(_1eO)){var _1eP=B(_185(E(_1dg),_1eN,_1dw));}else{var _1eP=B(_185(E(_1dg),_1eL+1|0,_1dw));}if(!E(_1eO)){var _1eQ=__Z;}else{var _1eQ=E(_1eM.b);}if(!B(_qN(_1eQ,_S))){var _1eR=B(_1df(_1dg,_1eQ,_1di,_1dj,_1dk,_1dl,_1dm,_1dn,_1do,_1dp,_1dq,_1dr,_1ds,_1dt,_1du,_1dv,_1eP,_1dx,_1dy,_1dz,_1dA,_1dB,_1dC,_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_1dN,_1dO,_1dP,_1dQ,_1dR)),_1eS=E(_1eR.a);return {_:0,a:E({_:0,a:E(_1eS.a),b:E(_1eS.b),c:_1eS.c,d:_1eS.d,e:_1eS.e,f:E(_1eS.f),g:_1eS.g,h:E(B(_q(_1dp,_1dS))),i:E(_1eS.i),j:E(_1eS.j)}),b:E(_1eR.b),c:E(_1eR.c),d:E(_1eR.d),e:E(_1eR.e),f:E(_1eR.f),g:E(_1eR.g),h:E(_1eR.h),i:_1eR.i,j:_1eR.j,k:_1eR.k,l:_1eR.l,m:E(_1eR.m),n:_1eR.n,o:E(_1eR.o),p:E(_1eR.p),q:E(_1eR.q),r:_1eR.r,s:E(_1eR.s),t:E(_1eR.t)};}else{return {_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1eP),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};}break;case 119:return {_:0,a:E({_:0,a:E(_1bH),b:E(_1cs),c:E(_1bZ),d:32,e:0,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1bz),c:E(_1bU),d:E(_1du),e:E(_1dv),f:E(B(_6d(_1bV,_1dw))),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_wt),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};default:return {_:0,a:E({_:0,a:E(_1di),b:E(_1dj),c:_1dk,d:_1dl,e:_1dm,f:E(_1dn),g:_1do,h:E(B(_q(_1dp,_1dS))),i:E(_1dq),j:E(_1dr)}),b:E(_1ds),c:E(_1dt),d:E(_1du),e:E(_1dv),f:E(_1dw),g:E(_1dx),h:E(_1dy),i:_1dz,j:_1dA,k:_1dB,l:_1dC,m:E(_1dD),n:_1dE,o:E(_1dF),p:E(_1dG),q:E(_1dH),r:_1dI,s:E({_:0,a:E(_1dJ),b:E(_1dK),c:E(_1dL),d:E(_1dM),e:E(_1dN),f:E(_1dO),g:E(_1dP),h:E(_1dQ)}),t:E(_1dR)};}}},_1eT=function(_1eU,_1eV){while(1){var _1eW=E(_1eV);if(!_1eW._){return __Z;}else{var _1eX=_1eW.b,_1eY=E(_1eU);if(_1eY==1){return E(_1eX);}else{_1eU=_1eY-1|0;_1eV=_1eX;continue;}}}},_1eZ=new T(function(){return B(unCStr("X"));}),_1f0=new T(function(){return B(_e6("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1f1=38,_1f2=function(_1f3,_1f4,_1f5,_1f6,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_1fd,_1fe,_1ff,_1fg,_1fh,_1fi,_1fj,_1fk,_1fl,_1fm,_1fn,_1fo,_1fp){var _1fq=E(_1f5);if(!_1fq._){return {_:0,a:_1f6,b:_1f7,c:_1f8,d:_1f9,e:_1fa,f:_1fb,g:_1fc,h:_1fd,i:_1fe,j:_1ff,k:_1fg,l:_1fh,m:_1fi,n:_1fj,o:_1fk,p:_1fl,q:_1fm,r:_1fn,s:_1fo,t:_1fp};}else{var _1fr=_1fq.b,_1fs=E(_1fq.a),_1ft=_1fs.a,_1fu=_1fs.b,_1fv=function(_1fw,_1fx,_1fy){var _1fz=function(_1fA,_1fB){if(!B(_qN(_1fA,_S))){var _1fC=E(_1f6),_1fD=E(_1fo),_1fE=B(_1df(_1fB,_1fA,_1fC.a,_1fC.b,_1fC.c,_1fC.d,_1fC.e,_1fC.f,_1fC.g,_1fC.h,_1fC.i,_1fC.j,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_1fd,_1fe,_1ff,_1fg,_1fh,_1fi,_1fj,_1fk,_1fl,_1fm,_1fn,_1fD.a,_1fD.b,_1fD.c,_1fD.d,_1fD.e,_1fD.f,_1fD.g,_1fD.h,_1fp)),_1fF=_1fE.a,_1fG=_1fE.b,_1fH=_1fE.c,_1fI=_1fE.d,_1fJ=_1fE.e,_1fK=_1fE.f,_1fL=_1fE.g,_1fM=_1fE.h,_1fN=_1fE.i,_1fO=_1fE.j,_1fP=_1fE.k,_1fQ=_1fE.l,_1fR=_1fE.m,_1fS=_1fE.n,_1fT=_1fE.o,_1fU=_1fE.p,_1fV=_1fE.q,_1fW=_1fE.r,_1fX=_1fE.s,_1fY=_1fE.t;if(B(_ms(_1fK,0))!=B(_ms(_1fb,0))){return {_:0,a:_1fF,b:_1fG,c:_1fH,d:_1fI,e:_1fJ,f:_1fK,g:_1fL,h:_1fM,i:_1fN,j:_1fO,k:_1fP,l:_1fQ,m:_1fR,n:_1fS,o:_1fT,p:_1fU,q:_1fV,r:_1fW,s:_1fX,t:_1fY};}else{return new F(function(){return _1f2(new T(function(){return E(_1f3)+1|0;}),_1f4,_1fr,_1fF,_1fG,_1fH,_1fI,_1fJ,_1fK,_1fL,_1fM,_1fN,_1fO,_1fP,_1fQ,_1fR,_1fS,_1fT,_1fU,_1fV,_1fW,_1fX,_1fY);});}}else{return new F(function(){return _1f2(new T(function(){return E(_1f3)+1|0;}),_1f4,_1fr,_1f6,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_1fd,_1fe,_1ff,_1fg,_1fh,_1fi,_1fj,_1fk,_1fl,_1fm,_1fn,_1fo,_1fp);});}},_1fZ=B(_ms(_1f4,0))-B(_ms(new T2(1,_1fw,_1fx),0))|0;if(_1fZ>0){var _1g0=B(_1eT(_1fZ,_1f4));}else{var _1g0=E(_1f4);}if(E(B(_16W(_1fw,_1fx,_T3)))==63){var _1g1=B(_Rx(_1fw,_1fx));}else{var _1g1=new T2(1,_1fw,_1fx);}var _1g2=function(_1g3){if(!B(_4A(_h6,_1f1,_1ft))){return new T2(0,_1fu,_1f3);}else{var _1g4=function(_1g5){while(1){var _1g6=B((function(_1g7){var _1g8=E(_1g7);if(!_1g8._){return true;}else{var _1g9=_1g8.b,_1ga=E(_1g8.a);if(!_1ga._){return E(_1f0);}else{switch(E(_1ga.a)){case 99:var _1gb=E(_1f6);if(!E(_1gb.j)){return false;}else{var _1gc=function(_1gd){while(1){var _1ge=E(_1gd);if(!_1ge._){return true;}else{var _1gf=_1ge.b,_1gg=E(_1ge.a);if(!_1gg._){return E(_1f0);}else{if(E(_1gg.a)==115){var _1gh=B(_Gc(B(_sx(_17D,_1gg.b))));if(!_1gh._){return E(_17B);}else{if(!E(_1gh.b)._){if(_1gb.e!=E(_1gh.a)){return false;}else{_1gd=_1gf;continue;}}else{return E(_17C);}}}else{_1gd=_1gf;continue;}}}}};return new F(function(){return _1gc(_1g9);});}break;case 115:var _1gi=E(_1f6),_1gj=_1gi.e,_1gk=B(_Gc(B(_sx(_17D,_1ga.b))));if(!_1gk._){return E(_17B);}else{if(!E(_1gk.b)._){if(_1gj!=E(_1gk.a)){return false;}else{var _1gl=function(_1gm){while(1){var _1gn=E(_1gm);if(!_1gn._){return true;}else{var _1go=_1gn.b,_1gp=E(_1gn.a);if(!_1gp._){return E(_1f0);}else{switch(E(_1gp.a)){case 99:if(!E(_1gi.j)){return false;}else{_1gm=_1go;continue;}break;case 115:var _1gq=B(_Gc(B(_sx(_17D,_1gp.b))));if(!_1gq._){return E(_17B);}else{if(!E(_1gq.b)._){if(_1gj!=E(_1gq.a)){return false;}else{_1gm=_1go;continue;}}else{return E(_17C);}}break;default:_1gm=_1go;continue;}}}}};return new F(function(){return _1gl(_1g9);});}}else{return E(_17C);}}break;default:_1g5=_1g9;return __continue;}}}})(_1g5));if(_1g6!=__continue){return _1g6;}}};return (!B(_1g4(_1fy)))?(!B(_qN(_1g1,_1eZ)))?new T2(0,_S,_1f3):new T2(0,_1fu,_1f3):new T2(0,_1fu,_1f3);}};if(E(B(_174(_1fw,_1fx,_T3)))==63){if(!B(_68(_1g0,_S))){var _1gr=E(_1g0);if(!_1gr._){return E(_RC);}else{if(!B(_qN(_1g1,B(_Rx(_1gr.a,_1gr.b))))){if(!B(_qN(_1g1,_1eZ))){return new F(function(){return _1fz(_S,_1f3);});}else{return new F(function(){return _1fz(_1fu,_1f3);});}}else{var _1gs=B(_1g2(_));return new F(function(){return _1fz(_1gs.a,_1gs.b);});}}}else{if(!B(_qN(_1g1,_1g0))){if(!B(_qN(_1g1,_1eZ))){return new F(function(){return _1fz(_S,_1f3);});}else{return new F(function(){return _1fz(_1fu,_1f3);});}}else{var _1gt=B(_1g2(_));return new F(function(){return _1fz(_1gt.a,_1gt.b);});}}}else{if(!B(_qN(_1g1,_1g0))){if(!B(_qN(_1g1,_1eZ))){return new F(function(){return _1fz(_S,_1f3);});}else{return new F(function(){return _1fz(_1fu,_1f3);});}}else{var _1gu=B(_1g2(_));return new F(function(){return _1fz(_1gu.a,_1gu.b);});}}},_1gv=E(_1ft);if(!_1gv._){return E(_T3);}else{var _1gw=_1gv.a,_1gx=E(_1gv.b);if(!_1gx._){return new F(function(){return _1fv(_1gw,_S,_S);});}else{var _1gy=E(_1gw),_1gz=new T(function(){var _1gA=B(_H4(38,_1gx.a,_1gx.b));return new T2(0,_1gA.a,_1gA.b);});if(E(_1gy)==38){return E(_T3);}else{return new F(function(){return _1fv(_1gy,new T(function(){return E(E(_1gz).a);}),new T(function(){return E(E(_1gz).b);}));});}}}}},_1gB="]",_1gC="}",_1gD=":",_1gE=",",_1gF=new T(function(){return eval("JSON.stringify");}),_1gG="false",_1gH="null",_1gI="[",_1gJ="{",_1gK="\"",_1gL="true",_1gM=function(_1gN,_1gO){var _1gP=E(_1gO);switch(_1gP._){case 0:return new T2(0,new T(function(){return jsShow(_1gP.a);}),_1gN);case 1:return new T2(0,new T(function(){var _1gQ=__app1(E(_1gF),_1gP.a);return String(_1gQ);}),_1gN);case 2:return (!E(_1gP.a))?new T2(0,_1gG,_1gN):new T2(0,_1gL,_1gN);case 3:var _1gR=E(_1gP.a);if(!_1gR._){return new T2(0,_1gI,new T2(1,_1gB,_1gN));}else{var _1gS=new T(function(){var _1gT=new T(function(){var _1gU=function(_1gV){var _1gW=E(_1gV);if(!_1gW._){return E(new T2(1,_1gB,_1gN));}else{var _1gX=new T(function(){var _1gY=B(_1gM(new T(function(){return B(_1gU(_1gW.b));}),_1gW.a));return new T2(1,_1gY.a,_1gY.b);});return new T2(1,_1gE,_1gX);}};return B(_1gU(_1gR.b));}),_1gZ=B(_1gM(_1gT,_1gR.a));return new T2(1,_1gZ.a,_1gZ.b);});return new T2(0,_1gI,_1gS);}break;case 4:var _1h0=E(_1gP.a);if(!_1h0._){return new T2(0,_1gJ,new T2(1,_1gC,_1gN));}else{var _1h1=E(_1h0.a),_1h2=new T(function(){var _1h3=new T(function(){var _1h4=function(_1h5){var _1h6=E(_1h5);if(!_1h6._){return E(new T2(1,_1gC,_1gN));}else{var _1h7=E(_1h6.a),_1h8=new T(function(){var _1h9=B(_1gM(new T(function(){return B(_1h4(_1h6.b));}),_1h7.b));return new T2(1,_1h9.a,_1h9.b);});return new T2(1,_1gE,new T2(1,_1gK,new T2(1,_1h7.a,new T2(1,_1gK,new T2(1,_1gD,_1h8)))));}};return B(_1h4(_1h0.b));}),_1ha=B(_1gM(_1h3,_1h1.b));return new T2(1,_1ha.a,_1ha.b);});return new T2(0,_1gJ,new T2(1,new T(function(){var _1hb=__app1(E(_1gF),E(_1h1.a));return String(_1hb);}),new T2(1,_1gD,_1h2)));}break;default:return new T2(0,_1gH,_1gN);}},_1hc=new T(function(){return toJSStr(_S);}),_1hd=function(_1he){var _1hf=B(_1gM(_S,_1he)),_1hg=jsCat(new T2(1,_1hf.a,_1hf.b),E(_1hc));return E(_1hg);},_1hh=function(_1hi){var _1hj=E(_1hi);if(!_1hj._){return new T2(0,_S,_S);}else{var _1hk=E(_1hj.a),_1hl=new T(function(){var _1hm=B(_1hh(_1hj.b));return new T2(0,_1hm.a,_1hm.b);});return new T2(0,new T2(1,_1hk.a,new T(function(){return E(E(_1hl).a);})),new T2(1,_1hk.b,new T(function(){return E(E(_1hl).b);})));}},_1hn=new T(function(){return B(unCStr("Rk"));}),_1ho=function(_1hp,_1hq,_1hr,_1hs,_1ht,_1hu,_1hv,_1hw,_1hx,_1hy,_1hz,_1hA,_1hB,_1hC,_1hD,_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ){while(1){var _1hK=B((function(_1hL,_1hM,_1hN,_1hO,_1hP,_1hQ,_1hR,_1hS,_1hT,_1hU,_1hV,_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5){var _1i6=E(_1hL);if(!_1i6._){return {_:0,a:_1hM,b:_1hN,c:_1hO,d:_1hP,e:_1hQ,f:_1hR,g:_1hS,h:_1hT,i:_1hU,j:_1hV,k:_1hW,l:_1hX,m:_1hY,n:_1hZ,o:_1i0,p:_1i1,q:_1i2,r:_1i3,s:_1i4,t:_1i5};}else{var _1i7=_1i6.a,_1i8=B(_RV(B(unAppCStr("e.e",new T2(1,_1i7,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1i7,_1hn)));})))),_1hM,_1hN,_1hO,_1hP,_1hQ,_1hR,_1hS,_1hT,_1hU,_1hV,_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5));_1hp=_1i6.b;_1hq=_1i8.a;_1hr=_1i8.b;_1hs=_1i8.c;_1ht=_1i8.d;_1hu=_1i8.e;_1hv=_1i8.f;_1hw=_1i8.g;_1hx=_1i8.h;_1hy=_1i8.i;_1hz=_1i8.j;_1hA=_1i8.k;_1hB=_1i8.l;_1hC=_1i8.m;_1hD=_1i8.n;_1hE=_1i8.o;_1hF=_1i8.p;_1hG=_1i8.q;_1hH=_1i8.r;_1hI=_1i8.s;_1hJ=_1i8.t;return __continue;}})(_1hp,_1hq,_1hr,_1hs,_1ht,_1hu,_1hv,_1hw,_1hx,_1hy,_1hz,_1hA,_1hB,_1hC,_1hD,_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ));if(_1hK!=__continue){return _1hK;}}},_1i9=function(_1ia){var _1ib=E(_1ia);switch(_1ib){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1ib>>>0>1114111){return new F(function(){return _wD(_1ib);});}else{return _1ib;}}},_1ic=function(_1id,_1ie,_1if){while(1){var _1ig=E(_1ie);if(!_1ig._){return (E(_1if)._==0)?true:false;}else{var _1ih=E(_1if);if(!_1ih._){return false;}else{if(!B(A3(_4y,_1id,_1ig.a,_1ih.a))){return false;}else{_1ie=_1ig.b;_1if=_1ih.b;continue;}}}}},_1ii=function(_1ij,_1ik){return (!B(_1ic(_rk,_1ij,_1ik)))?true:false;},_1il=function(_1im,_1in){return new F(function(){return _1ic(_rk,_1im,_1in);});},_1io=new T2(0,_1il,_1ii),_1ip=function(_1iq){var _1ir=E(_1iq);if(!_1ir._){return new T2(0,_S,_S);}else{var _1is=E(_1ir.a),_1it=new T(function(){var _1iu=B(_1ip(_1ir.b));return new T2(0,_1iu.a,_1iu.b);});return new T2(0,new T2(1,_1is.a,new T(function(){return E(E(_1it).a);})),new T2(1,_1is.b,new T(function(){return E(E(_1it).b);})));}},_1iv=function(_1iw,_1ix){while(1){var _1iy=E(_1ix);if(!_1iy._){return __Z;}else{var _1iz=_1iy.b,_1iA=E(_1iw);if(_1iA==1){return E(_1iz);}else{_1iw=_1iA-1|0;_1ix=_1iz;continue;}}}},_1iB=function(_1iC,_1iD){while(1){var _1iE=E(_1iD);if(!_1iE._){return __Z;}else{var _1iF=_1iE.b,_1iG=E(_1iC);if(_1iG==1){return E(_1iF);}else{_1iC=_1iG-1|0;_1iD=_1iF;continue;}}}},_1iH=function(_1iI){return new F(function(){return _Gj(_1iI,_S);});},_1iJ=function(_1iK,_1iL,_1iM,_1iN){var _1iO=new T(function(){return B(_Mt(_h6,_1iL,_1iM));}),_1iP=new T(function(){var _1iQ=E(_1iO),_1iR=new T(function(){var _1iS=_1iQ+1|0;if(_1iS>0){return B(_1iB(_1iS,_1iM));}else{return E(_1iM);}});if(0>=_1iQ){return E(_1iR);}else{var _1iT=function(_1iU,_1iV){var _1iW=E(_1iU);if(!_1iW._){return E(_1iR);}else{var _1iX=_1iW.a,_1iY=E(_1iV);return (_1iY==1)?new T2(1,_1iX,_1iR):new T2(1,_1iX,new T(function(){return B(_1iT(_1iW.b,_1iY-1|0));}));}};return B(_1iT(_1iM,_1iQ));}}),_1iZ=new T(function(){var _1j0=E(_1iO),_1j1=new T(function(){if(E(_1iL)==94){return B(A2(_1iK,new T(function(){return B(_6Q(_1iN,_1j0+1|0));}),new T(function(){return B(_6Q(_1iN,_1j0));})));}else{return B(A2(_1iK,new T(function(){return B(_6Q(_1iN,_1j0));}),new T(function(){return B(_6Q(_1iN,_1j0+1|0));})));}}),_1j2=new T2(1,_1j1,new T(function(){var _1j3=_1j0+2|0;if(_1j3>0){return B(_1iv(_1j3,_1iN));}else{return E(_1iN);}}));if(0>=_1j0){return E(_1j2);}else{var _1j4=function(_1j5,_1j6){var _1j7=E(_1j5);if(!_1j7._){return E(_1j2);}else{var _1j8=_1j7.a,_1j9=E(_1j6);return (_1j9==1)?new T2(1,_1j8,_1j2):new T2(1,_1j8,new T(function(){return B(_1j4(_1j7.b,_1j9-1|0));}));}};return B(_1j4(_1iN,_1j0));}});return (E(_1iL)==94)?new T2(0,new T(function(){return B(_1iH(_1iP));}),new T(function(){return B(_1iH(_1iZ));})):new T2(0,_1iP,_1iZ);},_1ja=new T(function(){return B(_cm(_oL,_oK));}),_1jb=function(_1jc,_1jd,_1je){while(1){if(!E(_1ja)){if(!B(_cm(B(_11l(_1jd,_oL)),_oK))){if(!B(_cm(_1jd,_aU))){var _1jf=B(_oe(_1jc,_1jc)),_1jg=B(_116(B(_eN(_1jd,_aU)),_oL)),_1jh=B(_oe(_1jc,_1je));_1jc=_1jf;_1jd=_1jg;_1je=_1jh;continue;}else{return new F(function(){return _oe(_1jc,_1je);});}}else{var _1jf=B(_oe(_1jc,_1jc)),_1jg=B(_116(_1jd,_oL));_1jc=_1jf;_1jd=_1jg;continue;}}else{return E(_9T);}}},_1ji=function(_1jj,_1jk){while(1){if(!E(_1ja)){if(!B(_cm(B(_11l(_1jk,_oL)),_oK))){if(!B(_cm(_1jk,_aU))){return new F(function(){return _1jb(B(_oe(_1jj,_1jj)),B(_116(B(_eN(_1jk,_aU)),_oL)),_1jj);});}else{return E(_1jj);}}else{var _1jl=B(_oe(_1jj,_1jj)),_1jm=B(_116(_1jk,_oL));_1jj=_1jl;_1jk=_1jm;continue;}}else{return E(_9T);}}},_1jn=function(_1jo,_1jp){if(!B(_d6(_1jp,_oK))){if(!B(_cm(_1jp,_oK))){return new F(function(){return _1ji(_1jo,_1jp);});}else{return E(_aU);}}else{return E(_pq);}},_1jq=94,_1jr=45,_1js=43,_1jt=42,_1ju=function(_1jv,_1jw){while(1){var _1jx=B((function(_1jy,_1jz){var _1jA=E(_1jz);if(!_1jA._){return __Z;}else{if((B(_ms(_1jy,0))+1|0)==B(_ms(_1jA,0))){if(!B(_4A(_h6,_1jq,_1jy))){if(!B(_4A(_h6,_1jt,_1jy))){if(!B(_4A(_h6,_1js,_1jy))){if(!B(_4A(_h6,_1jr,_1jy))){return E(_1jA);}else{var _1jB=B(_1iJ(_eN,45,_1jy,_1jA));_1jv=_1jB.a;_1jw=_1jB.b;return __continue;}}else{var _1jC=B(_1iJ(_cu,43,_1jy,_1jA));_1jv=_1jC.a;_1jw=_1jC.b;return __continue;}}else{var _1jD=B(_1iJ(_oe,42,_1jy,_1jA));_1jv=_1jD.a;_1jw=_1jD.b;return __continue;}}else{var _1jE=B(_1iJ(_1jn,94,new T(function(){return B(_1iH(_1jy));}),new T(function(){return B(_Gj(_1jA,_S));})));_1jv=_1jE.a;_1jw=_1jE.b;return __continue;}}else{return __Z;}}})(_1jv,_1jw));if(_1jx!=__continue){return _1jx;}}},_1jF=function(_1jG){var _1jH=E(_1jG);if(!_1jH._){return new T2(0,_S,_S);}else{var _1jI=E(_1jH.a),_1jJ=new T(function(){var _1jK=B(_1jF(_1jH.b));return new T2(0,_1jK.a,_1jK.b);});return new T2(0,new T2(1,_1jI.a,new T(function(){return E(E(_1jJ).a);})),new T2(1,_1jI.b,new T(function(){return E(E(_1jJ).b);})));}},_1jL=new T(function(){return B(unCStr("0123456789+-"));}),_1jM=function(_1jN){while(1){var _1jO=E(_1jN);if(!_1jO._){return true;}else{if(!B(_4A(_h6,_1jO.a,_1jL))){return false;}else{_1jN=_1jO.b;continue;}}}},_1jP=new T(function(){return B(err(_sq));}),_1jQ=new T(function(){return B(err(_ss));}),_1jR=function(_1jS,_1jT){var _1jU=function(_1jV,_1jW){var _1jX=function(_1jY){return new F(function(){return A1(_1jW,new T(function(){return B(_fs(_1jY));}));});},_1jZ=new T(function(){return B(_D6(function(_1k0){return new F(function(){return A3(_1jS,_1k0,_1jV,_1jX);});}));}),_1k1=function(_1k2){return E(_1jZ);},_1k3=function(_1k4){return new F(function(){return A2(_BN,_1k4,_1k1);});},_1k5=new T(function(){return B(_D6(function(_1k6){var _1k7=E(_1k6);if(_1k7._==4){var _1k8=E(_1k7.a);if(!_1k8._){return new F(function(){return A3(_1jS,_1k7,_1jV,_1jW);});}else{if(E(_1k8.a)==45){if(!E(_1k8.b)._){return E(new T1(1,_1k3));}else{return new F(function(){return A3(_1jS,_1k7,_1jV,_1jW);});}}else{return new F(function(){return A3(_1jS,_1k7,_1jV,_1jW);});}}}else{return new F(function(){return A3(_1jS,_1k7,_1jV,_1jW);});}}));}),_1k9=function(_1ka){return E(_1k5);};return new T1(1,function(_1kb){return new F(function(){return A2(_BN,_1kb,_1k9);});});};return new F(function(){return _DX(_1jU,_1jT);});},_1kc=function(_1kd){var _1ke=E(_1kd);if(_1ke._==5){var _1kf=B(_FV(_1ke.a));return (_1kf._==0)?E(_G0):function(_1kg,_1kh){return new F(function(){return A1(_1kh,_1kf.a);});};}else{return E(_G0);}},_1ki=new T(function(){return B(A3(_1jR,_1kc,_DD,_Fq));}),_1kj=function(_1kk,_1kl){var _1km=E(_1kl);if(!_1km._){return __Z;}else{var _1kn=_1km.a,_1ko=_1km.b,_1kp=function(_1kq){var _1kr=B(_1jF(_1kk)),_1ks=_1kr.a;return (!B(_4A(_qd,_1kn,_1ks)))?__Z:new T2(1,new T(function(){return B(_6Q(_1kr.b,B(_Mt(_qd,_1kn,_1ks))));}),new T(function(){return B(_1kj(_1kk,_1ko));}));};if(!B(_68(_1kn,_S))){if(!B(_1jM(_1kn))){return new F(function(){return _1kp(_);});}else{return new T2(1,new T(function(){var _1kt=B(_Gc(B(_sx(_1ki,_1kn))));if(!_1kt._){return E(_1jP);}else{if(!E(_1kt.b)._){return E(_1kt.a);}else{return E(_1jQ);}}}),new T(function(){return B(_1kj(_1kk,_1ko));}));}}else{return new F(function(){return _1kp(_);});}}},_1ku=new T(function(){return B(unCStr("+-*^"));}),_1kv=new T(function(){return B(unCStr("0123456789"));}),_1kw=new T(function(){return B(_La("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1kx=new T2(1,_S,_S),_1ky=function(_1kz){var _1kA=E(_1kz);if(!_1kA._){return new T2(0,_1kx,_S);}else{var _1kB=_1kA.a,_1kC=new T(function(){var _1kD=B(_1ky(_1kA.b)),_1kE=E(_1kD.a);if(!_1kE._){return E(_1kw);}else{return new T3(0,_1kE.a,_1kE.b,_1kD.b);}});return (!B(_4A(_h6,_1kB,_1kv)))?(!B(_4A(_h6,_1kB,_1ku)))?new T2(0,new T2(1,new T2(1,_1kB,new T(function(){return E(E(_1kC).a);})),new T(function(){return E(E(_1kC).b);})),new T(function(){return E(E(_1kC).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1kC).a);}),new T(function(){return E(E(_1kC).b);}))),new T2(1,_1kB,new T(function(){return E(E(_1kC).c);}))):new T2(0,new T2(1,new T2(1,_1kB,new T(function(){return E(E(_1kC).a);})),new T(function(){return E(E(_1kC).b);})),new T(function(){return E(E(_1kC).c);}));}},_1kF=function(_1kG,_1kH){var _1kI=new T(function(){var _1kJ=B(_1ky(_1kH)),_1kK=E(_1kJ.a);if(!_1kK._){return E(_1kw);}else{return new T3(0,_1kK.a,_1kK.b,_1kJ.b);}});return (!B(_4A(_h6,_1kG,_1kv)))?(!B(_4A(_h6,_1kG,_1ku)))?new T2(0,new T2(1,new T2(1,_1kG,new T(function(){return E(E(_1kI).a);})),new T(function(){return E(E(_1kI).b);})),new T(function(){return E(E(_1kI).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1kI).a);}),new T(function(){return E(E(_1kI).b);}))),new T2(1,_1kG,new T(function(){return E(E(_1kI).c);}))):new T2(0,new T2(1,new T2(1,_1kG,new T(function(){return E(E(_1kI).a);})),new T(function(){return E(E(_1kI).b);})),new T(function(){return E(E(_1kI).c);}));},_1kL=function(_1kM,_1kN){while(1){var _1kO=E(_1kM);if(!_1kO._){return E(_1kN);}else{_1kM=_1kO.b;_1kN=_1kO.a;continue;}}},_1kP=function(_1kQ,_1kR,_1kS){return new F(function(){return _1kL(_1kR,_1kQ);});},_1kT=function(_1kU,_1kV){var _1kW=E(_1kV);if(!_1kW._){return __Z;}else{var _1kX=B(_1kF(_1kW.a,_1kW.b)),_1kY=B(_1ju(_1kX.b,B(_1kj(_1kU,_1kX.a))));if(!_1kY._){return E(_1kW);}else{return new F(function(){return _13p(0,B(_1kP(_1kY.a,_1kY.b,_T3)),_S);});}}},_1kZ=function(_1l0,_1l1){var _1l2=function(_1l3,_1l4){while(1){var _1l5=B((function(_1l6,_1l7){var _1l8=E(_1l7);if(!_1l8._){return (!B(_qN(_1l6,_S)))?new T2(0,_wt,_1l6):new T2(0,_ws,_S);}else{var _1l9=_1l8.b,_1la=B(_1ip(_1l8.a)).a;if(!B(_4A(_h6,_195,_1la))){var _1lb=_1l6;_1l3=_1lb;_1l4=_1l9;return __continue;}else{var _1lc=B(_19B(_1la)),_1ld=_1lc.a,_1le=_1lc.b;if(!B(_68(_1le,_S))){if(!B(_qN(B(_1kT(_1l0,_1ld)),B(_1kT(_1l0,_1le))))){return new T2(0,_ws,_S);}else{var _1lf=new T(function(){if(!B(_qN(_1l6,_S))){return B(_q(_1l6,new T(function(){return B(unAppCStr(" ",_1ld));},1)));}else{return E(_1ld);}});_1l3=_1lf;_1l4=_1l9;return __continue;}}else{return new T2(0,_ws,_S);}}}})(_1l3,_1l4));if(_1l5!=__continue){return _1l5;}}};return new F(function(){return _1l2(_S,_1l1);});},_1lg=function(_1lh,_1li){var _1lj=new T(function(){var _1lk=B(_Gc(B(_sx(_13f,new T(function(){return B(_pN(3,B(_A(0,imul(E(_1li),E(_1lh)-1|0)|0,_S))));})))));if(!_1lk._){return E(_13e);}else{if(!E(_1lk.b)._){return E(_1lk.a);}else{return E(_13d);}}});return new T2(0,new T(function(){return B(_au(_1lj,_1lh));}),_1lj);},_1ll=function(_1lm,_1ln){while(1){var _1lo=E(_1ln);if(!_1lo._){return __Z;}else{var _1lp=_1lo.b,_1lq=E(_1lm);if(_1lq==1){return E(_1lp);}else{_1lm=_1lq-1|0;_1ln=_1lp;continue;}}}},_1lr=function(_1ls,_1lt){while(1){var _1lu=E(_1lt);if(!_1lu._){return __Z;}else{var _1lv=_1lu.b,_1lw=E(_1ls);if(_1lw==1){return E(_1lv);}else{_1ls=_1lw-1|0;_1lt=_1lv;continue;}}}},_1lx=64,_1ly=new T2(1,_1lx,_S),_1lz=function(_1lA,_1lB,_1lC,_1lD){return (!B(_qN(_1lA,_1lC)))?true:(!B(_cm(_1lB,_1lD)))?true:false;},_1lE=function(_1lF,_1lG){var _1lH=E(_1lF),_1lI=E(_1lG);return new F(function(){return _1lz(_1lH.a,_1lH.b,_1lI.a,_1lI.b);});},_1lJ=function(_1lK,_1lL,_1lM,_1lN){if(!B(_qN(_1lK,_1lM))){return false;}else{return new F(function(){return _cm(_1lL,_1lN);});}},_1lO=function(_1lP,_1lQ){var _1lR=E(_1lP),_1lS=E(_1lQ);return new F(function(){return _1lJ(_1lR.a,_1lR.b,_1lS.a,_1lS.b);});},_1lT=new T2(0,_1lO,_1lE),_1lU=function(_1lV){var _1lW=E(_1lV);if(!_1lW._){return new T2(0,_S,_S);}else{var _1lX=E(_1lW.a),_1lY=new T(function(){var _1lZ=B(_1lU(_1lW.b));return new T2(0,_1lZ.a,_1lZ.b);});return new T2(0,new T2(1,_1lX.a,new T(function(){return E(E(_1lY).a);})),new T2(1,_1lX.b,new T(function(){return E(E(_1lY).b);})));}},_1m0=function(_1m1){var _1m2=E(_1m1);if(!_1m2._){return new T2(0,_S,_S);}else{var _1m3=E(_1m2.a),_1m4=new T(function(){var _1m5=B(_1m0(_1m2.b));return new T2(0,_1m5.a,_1m5.b);});return new T2(0,new T2(1,_1m3.a,new T(function(){return E(E(_1m4).a);})),new T2(1,_1m3.b,new T(function(){return E(E(_1m4).b);})));}},_1m6=function(_1m7){var _1m8=E(_1m7);if(!_1m8._){return new T2(0,_S,_S);}else{var _1m9=E(_1m8.a),_1ma=new T(function(){var _1mb=B(_1m6(_1m8.b));return new T2(0,_1mb.a,_1mb.b);});return new T2(0,new T2(1,_1m9.a,new T(function(){return E(E(_1ma).a);})),new T2(1,_1m9.b,new T(function(){return E(E(_1ma).b);})));}},_1mc=function(_1md,_1me){return (_1md<=_1me)?new T2(1,_1md,new T(function(){return B(_1mc(_1md+1|0,_1me));})):__Z;},_1mf=new T(function(){return B(_1mc(65,90));}),_1mg=function(_1mh){return (_1mh<=122)?new T2(1,_1mh,new T(function(){return B(_1mg(_1mh+1|0));})):E(_1mf);},_1mi=new T(function(){return B(_1mg(97));}),_1mj=function(_1mk){while(1){var _1ml=E(_1mk);if(!_1ml._){return true;}else{if(!B(_4A(_h6,_1ml.a,_1mi))){return false;}else{_1mk=_1ml.b;continue;}}}},_1mm=new T2(0,_S,_S),_1mn=new T(function(){return B(err(_sq));}),_1mo=new T(function(){return B(err(_ss));}),_1mp=new T(function(){return B(A3(_1jR,_1kc,_DD,_Fq));}),_1mq=function(_1mr,_1ms,_1mt){while(1){var _1mu=B((function(_1mv,_1mw,_1mx){var _1my=E(_1mx);if(!_1my._){return __Z;}else{var _1mz=_1my.b,_1mA=B(_1m0(_1mw)),_1mB=_1mA.a,_1mC=B(_1lU(_1mB)),_1mD=_1mC.a,_1mE=new T(function(){return E(B(_1m6(_1my.a)).a);}),_1mF=new T(function(){return B(_4A(_h6,_195,_1mE));}),_1mG=new T(function(){if(!E(_1mF)){return E(_1mm);}else{var _1mH=B(_19B(_1mE));return new T2(0,_1mH.a,_1mH.b);}}),_1mI=new T(function(){return E(E(_1mG).a);}),_1mJ=new T(function(){return B(_Mt(_qd,_1mI,_1mD));}),_1mK=new T(function(){var _1mL=function(_){var _1mM=B(_ms(_1mw,0))-1|0,_1mN=function(_1mO){if(_1mO>=0){var _1mP=newArr(_1mO,_14m),_1mQ=_1mP,_1mR=E(_1mO);if(!_1mR){return new T4(0,E(_17E),E(_1mM),0,_1mQ);}else{var _1mS=function(_1mT,_1mU,_){while(1){var _1mV=E(_1mT);if(!_1mV._){return E(_);}else{var _=_1mQ[_1mU]=_1mV.a;if(_1mU!=(_1mR-1|0)){var _1mW=_1mU+1|0;_1mT=_1mV.b;_1mU=_1mW;continue;}else{return E(_);}}}},_=B(_1mS(_1mA.b,0,_));return new T4(0,E(_17E),E(_1mM),_1mR,_1mQ);}}else{return E(_15g);}};if(0>_1mM){return new F(function(){return _1mN(0);});}else{return new F(function(){return _1mN(_1mM+1|0);});}};return B(_15h(_1mL));});if(!B(_4A(_qd,_1mI,_1mD))){var _1mX=false;}else{var _1mY=E(_1mK),_1mZ=E(_1mY.a),_1n0=E(_1mY.b),_1n1=E(_1mJ);if(_1mZ>_1n1){var _1n2=B(_1bN(_1n1,_1mZ,_1n0));}else{if(_1n1>_1n0){var _1n3=B(_1bN(_1n1,_1mZ,_1n0));}else{var _1n3=E(_1mY.d[_1n1-_1mZ|0])==E(_1mv);}var _1n2=_1n3;}var _1mX=_1n2;}var _1n4=new T(function(){return E(E(_1mG).b);}),_1n5=new T(function(){return B(_Mt(_qd,_1n4,_1mD));}),_1n6=new T(function(){if(!B(_4A(_qd,_1n4,_1mD))){return false;}else{var _1n7=E(_1mK),_1n8=E(_1n7.a),_1n9=E(_1n7.b),_1na=E(_1n5);if(_1n8>_1na){return B(_1bN(_1na,_1n8,_1n9));}else{if(_1na>_1n9){return B(_1bN(_1na,_1n8,_1n9));}else{return E(_1n7.d[_1na-_1n8|0])==E(_1mv);}}}}),_1nb=new T(function(){var _1nc=function(_){var _1nd=B(_ms(_1mB,0))-1|0,_1ne=function(_1nf){if(_1nf>=0){var _1ng=newArr(_1nf,_14m),_1nh=_1ng,_1ni=E(_1nf);if(!_1ni){return new T4(0,E(_17E),E(_1nd),0,_1nh);}else{var _1nj=function(_1nk,_1nl,_){while(1){var _1nm=E(_1nk);if(!_1nm._){return E(_);}else{var _=_1nh[_1nl]=_1nm.a;if(_1nl!=(_1ni-1|0)){var _1nn=_1nl+1|0;_1nk=_1nm.b;_1nl=_1nn;continue;}else{return E(_);}}}},_=B(_1nj(_1mC.b,0,_));return new T4(0,E(_17E),E(_1nd),_1ni,_1nh);}}else{return E(_15g);}};if(0>_1nd){return new F(function(){return _1ne(0);});}else{return new F(function(){return _1ne(_1nd+1|0);});}};return B(_15h(_1nc));}),_1no=function(_1np){var _1nq=function(_1nr){return (!E(_1mX))?__Z:(!E(_1n6))?__Z:new T2(1,new T2(0,_1mI,new T(function(){var _1ns=E(_1nb),_1nt=E(_1ns.a),_1nu=E(_1ns.b),_1nv=E(_1mJ);if(_1nt>_1nv){return B(_1bN(_1nv,_1nt,_1nu));}else{if(_1nv>_1nu){return B(_1bN(_1nv,_1nt,_1nu));}else{return E(_1ns.d[_1nv-_1nt|0]);}}})),new T2(1,new T2(0,_1n4,new T(function(){var _1nw=E(_1nb),_1nx=E(_1nw.a),_1ny=E(_1nw.b),_1nz=E(_1n5);if(_1nx>_1nz){return B(_1bN(_1nz,_1nx,_1ny));}else{if(_1nz>_1ny){return B(_1bN(_1nz,_1nx,_1ny));}else{return E(_1nw.d[_1nz-_1nx|0]);}}})),_S));};if(!E(_1mX)){if(!E(_1n6)){return new F(function(){return _1nq(_);});}else{return new T2(1,new T2(0,_1n4,new T(function(){var _1nA=E(_1nb),_1nB=E(_1nA.a),_1nC=E(_1nA.b),_1nD=E(_1n5);if(_1nB>_1nD){return B(_1bN(_1nD,_1nB,_1nC));}else{if(_1nD>_1nC){return B(_1bN(_1nD,_1nB,_1nC));}else{return E(_1nA.d[_1nD-_1nB|0]);}}})),_S);}}else{return new F(function(){return _1nq(_);});}};if(!E(_1mX)){var _1nE=B(_1no(_));}else{if(!E(_1n6)){var _1nF=new T2(1,new T2(0,_1mI,new T(function(){var _1nG=E(_1nb),_1nH=E(_1nG.a),_1nI=E(_1nG.b),_1nJ=E(_1mJ);if(_1nH>_1nJ){return B(_1bN(_1nJ,_1nH,_1nI));}else{if(_1nJ>_1nI){return B(_1bN(_1nJ,_1nH,_1nI));}else{return E(_1nG.d[_1nJ-_1nH|0]);}}})),_S);}else{var _1nF=B(_1no(_));}var _1nE=_1nF;}if(!B(_1ic(_1lT,_1nE,_S))){return new F(function(){return _q(_1nE,new T(function(){return B(_1mq(_1mv,_1mw,_1mz));},1));});}else{if(!E(_1mF)){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{if(!B(_1mj(_1mI))){if(!B(_1mj(_1n4))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{if(!E(_1mX)){if(!E(_1n6)){if(!B(_68(_1mI,_S))){if(!B(_1jM(_1mI))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{return new T2(1,new T2(0,_1n4,new T(function(){var _1nM=B(_Gc(B(_sx(_1mp,_1mI))));if(!_1nM._){return E(_1mn);}else{if(!E(_1nM.b)._){return E(_1nM.a);}else{return E(_1mo);}}})),new T(function(){return B(_1mq(_1mv,_1mw,_1mz));}));}}else{var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}else{var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}else{var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}}else{if(!E(_1mX)){if(!E(_1n6)){if(!B(_68(_1n4,_S))){if(!B(_1jM(_1n4))){if(!B(_1mj(_1n4))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{if(!B(_68(_1mI,_S))){if(!B(_1jM(_1mI))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{return new T2(1,new T2(0,_1n4,new T(function(){var _1nN=B(_Gc(B(_sx(_1mp,_1mI))));if(!_1nN._){return E(_1mn);}else{if(!E(_1nN.b)._){return E(_1nN.a);}else{return E(_1mo);}}})),new T(function(){return B(_1mq(_1mv,_1mw,_1mz));}));}}else{var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}}else{return new T2(1,new T2(0,_1mI,new T(function(){var _1nO=B(_Gc(B(_sx(_1mp,_1n4))));if(!_1nO._){return E(_1mn);}else{if(!E(_1nO.b)._){return E(_1nO.a);}else{return E(_1mo);}}})),new T(function(){return B(_1mq(_1mv,_1mw,_1mz));}));}}else{if(!B(_1mj(_1n4))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{if(!B(_68(_1mI,_S))){if(!B(_1jM(_1mI))){var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}else{return new T2(1,new T2(0,_1n4,new T(function(){var _1nP=B(_Gc(B(_sx(_1mp,_1mI))));if(!_1nP._){return E(_1mn);}else{if(!E(_1nP.b)._){return E(_1nP.a);}else{return E(_1mo);}}})),new T(function(){return B(_1mq(_1mv,_1mw,_1mz));}));}}else{var _1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}}}else{var _1nQ=B(_1mj(_1n4)),_1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}else{var _1nR=B(_1mj(_1n4)),_1nK=_1mv,_1nL=_1mw;_1mr=_1nK;_1ms=_1nL;_1mt=_1mz;return __continue;}}}}}})(_1mr,_1ms,_1mt));if(_1mu!=__continue){return _1mu;}}},_1nS=102,_1nT=101,_1nU=new T(function(){return B(unCStr("=="));}),_1nV=new T(function(){return B(_e6("Action.hs:(103,17)-(107,70)|case"));}),_1nW=new T(function(){return B(_e6("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1nX=5,_1nY=117,_1nZ=98,_1o0=110,_1o1=118,_1o2=function(_1o3,_1o4,_1o5,_1o6,_1o7,_1o8,_1o9,_1oa,_1ob,_1oc,_1od,_1oe,_1of){var _1og=B(_6Q(B(_6Q(_1o7,_1o4)),_1o3)),_1oh=_1og.a,_1oi=_1og.b;if(E(_1o9)==32){if(!B(_4A(_h6,_1oh,_1ly))){var _1oj=false;}else{switch(E(_1oi)){case 0:var _1ok=true;break;case 1:var _1ok=false;break;case 2:var _1ok=false;break;case 3:var _1ok=false;break;case 4:var _1ok=false;break;case 5:var _1ok=false;break;case 6:var _1ok=false;break;case 7:var _1ok=false;break;default:var _1ok=false;}var _1oj=_1ok;}var _1ol=_1oj;}else{var _1ol=false;}if(E(_1o9)==32){if(E(_1oh)==32){var _1om=false;}else{switch(E(_1oi)){case 0:if(!E(_1ol)){var _1on=true;}else{var _1on=false;}var _1oo=_1on;break;case 1:var _1oo=false;break;case 2:var _1oo=false;break;case 3:var _1oo=false;break;case 4:var _1oo=false;break;case 5:var _1oo=false;break;case 6:var _1oo=false;break;case 7:var _1oo=false;break;default:if(!E(_1ol)){var _1op=true;}else{var _1op=false;}var _1oo=_1op;}var _1om=_1oo;}var _1oq=_1om;}else{var _1oq=false;}var _1or=new T(function(){return B(_KJ(_1o3,_1o4,new T(function(){if(!E(_1oq)){if(!E(_1ol)){return E(_1oh);}else{return _1o8;}}else{return E(_Ur);}}),_1oi,_1o7));});switch(E(_1oi)){case 3:var _1os=true;break;case 4:if(E(_1o9)==32){var _1ot=true;}else{var _1ot=false;}var _1os=_1ot;break;default:var _1os=false;}if(!E(_1os)){var _1ou=E(_1or);}else{var _1ov=E(_1o5),_1ow=new T(function(){return B(_6Q(_1or,_1o4));}),_1ox=function(_1oy,_1oz){var _1oA=E(_1oy);if(_1oA==( -1)){return E(_1or);}else{var _1oB=new T(function(){return B(_KJ(_1o3,_1o4,_Ur,_E8,_1or));}),_1oC=E(_1oz);if(_1oC==( -1)){var _1oD=__Z;}else{var _1oD=B(_6Q(_1oB,_1oC));}if(E(B(_6Q(_1oD,_1oA)).a)==32){var _1oE=new T(function(){var _1oF=new T(function(){return B(_6Q(_1ow,_1o3));}),_1oG=new T2(1,new T2(0,new T(function(){return E(E(_1oF).a);}),new T(function(){return E(E(_1oF).b);})),new T(function(){var _1oH=_1oA+1|0;if(_1oH>0){return B(_1lr(_1oH,_1oD));}else{return E(_1oD);}}));if(0>=_1oA){return E(_1oG);}else{var _1oI=function(_1oJ,_1oK){var _1oL=E(_1oJ);if(!_1oL._){return E(_1oG);}else{var _1oM=_1oL.a,_1oN=E(_1oK);return (_1oN==1)?new T2(1,_1oM,_1oG):new T2(1,_1oM,new T(function(){return B(_1oI(_1oL.b,_1oN-1|0));}));}};return B(_1oI(_1oD,_1oA));}}),_1oO=new T2(1,_1oE,new T(function(){var _1oP=_1oz+1|0;if(_1oP>0){return B(_1ll(_1oP,_1oB));}else{return E(_1oB);}}));if(0>=_1oz){return E(_1oO);}else{var _1oQ=function(_1oR,_1oS){var _1oT=E(_1oR);if(!_1oT._){return E(_1oO);}else{var _1oU=_1oT.a,_1oV=E(_1oS);return (_1oV==1)?new T2(1,_1oU,_1oO):new T2(1,_1oU,new T(function(){return B(_1oQ(_1oT.b,_1oV-1|0));}));}};return new F(function(){return _1oQ(_1oB,_1oz);});}}else{return E(_1or);}}};if(_1o3<=_1ov){if(_1ov<=_1o3){var _1oW=E(_1o6);if(_1o4<=_1oW){if(_1oW<=_1o4){var _1oX=E(_1nV);}else{var _1oY=E(_1o4);if(!_1oY){var _1oZ=B(_1ox( -1, -1));}else{var _1oZ=B(_1ox(_1o3,_1oY-1|0));}var _1oX=_1oZ;}var _1p0=_1oX;}else{if(_1o4!=(B(_ms(_1or,0))-1|0)){var _1p1=B(_1ox(_1o3,_1o4+1|0));}else{var _1p1=B(_1ox( -1, -1));}var _1p0=_1p1;}var _1p2=_1p0;}else{var _1p3=E(_1o3);if(!_1p3){var _1p4=B(_1ox( -1, -1));}else{var _1p4=B(_1ox(_1p3-1|0,_1o4));}var _1p2=_1p4;}var _1p5=_1p2;}else{if(_1o3!=(B(_ms(_1ow,0))-1|0)){var _1p6=B(_1ox(_1o3+1|0,_1o4));}else{var _1p6=B(_1ox( -1, -1));}var _1p5=_1p6;}var _1ou=_1p5;}if(!E(_1oe)){var _1p7=E(_1ou);}else{var _1p8=new T(function(){var _1p9=E(_1ou);if(!_1p9._){return E(_ng);}else{return B(_ms(_1p9.a,0));}}),_1pa=new T(function(){return B(_ms(_1ou,0));}),_1pb=function(_1pc,_1pd,_1pe,_1pf,_1pg,_1ph,_1pi){while(1){var _1pj=B((function(_1pk,_1pl,_1pm,_1pn,_1po,_1pp,_1pq){var _1pr=E(_1pq);if(!_1pr._){return E(_1pn);}else{var _1ps=_1pr.b,_1pt=E(_1pr.a);if(!_1pt._){return E(_1nW);}else{var _1pu=_1pt.b,_1pv=E(_1pt.a);if(E(_1pv.b)==5){var _1pw=new T(function(){var _1px=B(_1lg(_1nX,_1pk));return new T2(0,_1px.a,_1px.b);}),_1py=new T(function(){var _1pz=function(_1pA,_1pB){var _1pC=function(_1pD){return new F(function(){return _KJ(_1pl,_1pm,_Ur,_E8,new T(function(){return B(_KJ(_1pA,_1pB,_1pv.a,_EX,_1pn));}));});};if(_1pA!=_1pl){return new F(function(){return _1pC(_);});}else{if(_1pB!=_1pm){return new F(function(){return _1pC(_);});}else{return E(_1pn);}}};switch(E(E(_1pw).a)){case 1:var _1pE=_1pl-1|0;if(_1pE<0){return B(_1pz(_1pl,_1pm));}else{if(_1pE>=E(_1p8)){return B(_1pz(_1pl,_1pm));}else{if(_1pm<0){return B(_1pz(_1pl,_1pm));}else{if(_1pm>=E(_1pa)){return B(_1pz(_1pl,_1pm));}else{if(_1pE!=_1po){if(E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pE)).a)==32){return B(_1pz(_1pE,_1pm));}else{return B(_1pz(_1pl,_1pm));}}else{if(_1pm!=_1pp){if(E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pE)).a)==32){return B(_1pz(_1pE,_1pm));}else{return B(_1pz(_1pl,_1pm));}}else{return B(_1pz(_1pl,_1pm));}}}}}}break;case 2:if(_1pl<0){return B(_1pz(_1pl,_1pm));}else{if(_1pl>=E(_1p8)){return B(_1pz(_1pl,_1pm));}else{var _1pF=_1pm-1|0;if(_1pF<0){return B(_1pz(_1pl,_1pm));}else{if(_1pF>=E(_1pa)){return B(_1pz(_1pl,_1pm));}else{if(_1pl!=_1po){if(E(B(_6Q(B(_6Q(_1pn,_1pF)),_1pl)).a)==32){return B(_1pz(_1pl,_1pF));}else{return B(_1pz(_1pl,_1pm));}}else{if(_1pF!=_1pp){if(E(B(_6Q(B(_6Q(_1pn,_1pF)),_1pl)).a)==32){return B(_1pz(_1pl,_1pF));}else{return B(_1pz(_1pl,_1pm));}}else{return B(_1pz(_1pl,_1pm));}}}}}}break;case 3:var _1pG=_1pl+1|0;if(_1pG<0){return B(_1pz(_1pl,_1pm));}else{if(_1pG>=E(_1p8)){return B(_1pz(_1pl,_1pm));}else{if(_1pm<0){return B(_1pz(_1pl,_1pm));}else{if(_1pm>=E(_1pa)){return B(_1pz(_1pl,_1pm));}else{if(_1pG!=_1po){if(E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pG)).a)==32){return B(_1pz(_1pG,_1pm));}else{return B(_1pz(_1pl,_1pm));}}else{if(_1pm!=_1pp){if(E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pG)).a)==32){return B(_1pz(_1pG,_1pm));}else{return B(_1pz(_1pl,_1pm));}}else{return B(_1pz(_1pl,_1pm));}}}}}}break;case 4:if(_1pl<0){return B(_1pz(_1pl,_1pm));}else{if(_1pl>=E(_1p8)){return B(_1pz(_1pl,_1pm));}else{var _1pH=_1pm+1|0;if(_1pH<0){return B(_1pz(_1pl,_1pm));}else{if(_1pH>=E(_1pa)){return B(_1pz(_1pl,_1pm));}else{if(_1pl!=_1po){if(E(B(_6Q(B(_6Q(_1pn,_1pH)),_1pl)).a)==32){return B(_1pz(_1pl,_1pH));}else{return B(_1pz(_1pl,_1pm));}}else{if(_1pH!=_1pp){if(E(B(_6Q(B(_6Q(_1pn,_1pH)),_1pl)).a)==32){return B(_1pz(_1pl,_1pH));}else{return B(_1pz(_1pl,_1pm));}}else{return B(_1pz(_1pl,_1pm));}}}}}}break;default:if(_1pl<0){return B(_1pz(_1pl,_1pm));}else{if(_1pl>=E(_1p8)){return B(_1pz(_1pl,_1pm));}else{if(_1pm<0){return B(_1pz(_1pl,_1pm));}else{if(_1pm>=E(_1pa)){return B(_1pz(_1pl,_1pm));}else{if(_1pl!=_1po){var _1pI=E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pl)).a);return B(_1pz(_1pl,_1pm));}else{if(_1pm!=_1pp){var _1pJ=E(B(_6Q(B(_6Q(_1pn,_1pm)),_1pl)).a);return B(_1pz(_1pl,_1pm));}else{return B(_1pz(_1pl,_1pm));}}}}}}}}),_1pK=E(_1pu);if(!_1pK._){var _1pL=_1pm+1|0,_1pM=_1po,_1pN=_1pp;_1pc=new T(function(){return E(E(_1pw).b);},1);_1pd=0;_1pe=_1pL;_1pf=_1py;_1pg=_1pM;_1ph=_1pN;_1pi=_1ps;return __continue;}else{return new F(function(){return _1pO(new T(function(){return E(E(_1pw).b);},1),_1pl+1|0,_1pm,_1py,_1po,_1pp,_1pK.a,_1pK.b,_1ps);});}}else{var _1pP=E(_1pu);if(!_1pP._){var _1pQ=_1pk,_1pL=_1pm+1|0,_1pR=_1pn,_1pM=_1po,_1pN=_1pp;_1pc=_1pQ;_1pd=0;_1pe=_1pL;_1pf=_1pR;_1pg=_1pM;_1ph=_1pN;_1pi=_1ps;return __continue;}else{return new F(function(){return _1pO(_1pk,_1pl+1|0,_1pm,_1pn,_1po,_1pp,_1pP.a,_1pP.b,_1ps);});}}}}})(_1pc,_1pd,_1pe,_1pf,_1pg,_1ph,_1pi));if(_1pj!=__continue){return _1pj;}}},_1pO=function(_1pS,_1pT,_1pU,_1pV,_1pW,_1pX,_1pY,_1pZ,_1q0){while(1){var _1q1=B((function(_1q2,_1q3,_1q4,_1q5,_1q6,_1q7,_1q8,_1q9,_1qa){var _1qb=E(_1q8);if(E(_1qb.b)==5){var _1qc=new T(function(){var _1qd=B(_1lg(_1nX,_1q2));return new T2(0,_1qd.a,_1qd.b);}),_1qe=new T(function(){var _1qf=function(_1qg,_1qh){var _1qi=function(_1qj){return new F(function(){return _KJ(_1q3,_1q4,_Ur,_E8,new T(function(){return B(_KJ(_1qg,_1qh,_1qb.a,_EX,_1q5));}));});};if(_1qg!=_1q3){return new F(function(){return _1qi(_);});}else{if(_1qh!=_1q4){return new F(function(){return _1qi(_);});}else{return E(_1q5);}}};switch(E(E(_1qc).a)){case 1:var _1qk=_1q3-1|0;if(_1qk<0){return B(_1qf(_1q3,_1q4));}else{if(_1qk>=E(_1p8)){return B(_1qf(_1q3,_1q4));}else{if(_1q4<0){return B(_1qf(_1q3,_1q4));}else{if(_1q4>=E(_1pa)){return B(_1qf(_1q3,_1q4));}else{if(_1qk!=_1q6){if(E(B(_6Q(B(_6Q(_1q5,_1q4)),_1qk)).a)==32){return B(_1qf(_1qk,_1q4));}else{return B(_1qf(_1q3,_1q4));}}else{if(_1q4!=_1q7){if(E(B(_6Q(B(_6Q(_1q5,_1q4)),_1qk)).a)==32){return B(_1qf(_1qk,_1q4));}else{return B(_1qf(_1q3,_1q4));}}else{return B(_1qf(_1q3,_1q4));}}}}}}break;case 2:if(_1q3<0){return B(_1qf(_1q3,_1q4));}else{if(_1q3>=E(_1p8)){return B(_1qf(_1q3,_1q4));}else{var _1ql=_1q4-1|0;if(_1ql<0){return B(_1qf(_1q3,_1q4));}else{if(_1ql>=E(_1pa)){return B(_1qf(_1q3,_1q4));}else{if(_1q3!=_1q6){if(E(B(_6Q(B(_6Q(_1q5,_1ql)),_1q3)).a)==32){return B(_1qf(_1q3,_1ql));}else{return B(_1qf(_1q3,_1q4));}}else{if(_1ql!=_1q7){if(E(B(_6Q(B(_6Q(_1q5,_1ql)),_1q3)).a)==32){return B(_1qf(_1q3,_1ql));}else{return B(_1qf(_1q3,_1q4));}}else{return B(_1qf(_1q3,_1q4));}}}}}}break;case 3:var _1qm=_1q3+1|0;if(_1qm<0){return B(_1qf(_1q3,_1q4));}else{if(_1qm>=E(_1p8)){return B(_1qf(_1q3,_1q4));}else{if(_1q4<0){return B(_1qf(_1q3,_1q4));}else{if(_1q4>=E(_1pa)){return B(_1qf(_1q3,_1q4));}else{if(_1qm!=_1q6){if(E(B(_6Q(B(_6Q(_1q5,_1q4)),_1qm)).a)==32){return B(_1qf(_1qm,_1q4));}else{return B(_1qf(_1q3,_1q4));}}else{if(_1q4!=_1q7){if(E(B(_6Q(B(_6Q(_1q5,_1q4)),_1qm)).a)==32){return B(_1qf(_1qm,_1q4));}else{return B(_1qf(_1q3,_1q4));}}else{return B(_1qf(_1q3,_1q4));}}}}}}break;case 4:if(_1q3<0){return B(_1qf(_1q3,_1q4));}else{if(_1q3>=E(_1p8)){return B(_1qf(_1q3,_1q4));}else{var _1qn=_1q4+1|0;if(_1qn<0){return B(_1qf(_1q3,_1q4));}else{if(_1qn>=E(_1pa)){return B(_1qf(_1q3,_1q4));}else{if(_1q3!=_1q6){if(E(B(_6Q(B(_6Q(_1q5,_1qn)),_1q3)).a)==32){return B(_1qf(_1q3,_1qn));}else{return B(_1qf(_1q3,_1q4));}}else{if(_1qn!=_1q7){if(E(B(_6Q(B(_6Q(_1q5,_1qn)),_1q3)).a)==32){return B(_1qf(_1q3,_1qn));}else{return B(_1qf(_1q3,_1q4));}}else{return B(_1qf(_1q3,_1q4));}}}}}}break;default:if(_1q3<0){return B(_1qf(_1q3,_1q4));}else{if(_1q3>=E(_1p8)){return B(_1qf(_1q3,_1q4));}else{if(_1q4<0){return B(_1qf(_1q3,_1q4));}else{if(_1q4>=E(_1pa)){return B(_1qf(_1q3,_1q4));}else{if(_1q3!=_1q6){var _1qo=E(B(_6Q(B(_6Q(_1q5,_1q4)),_1q3)).a);return B(_1qf(_1q3,_1q4));}else{if(_1q4!=_1q7){var _1qp=E(B(_6Q(B(_6Q(_1q5,_1q4)),_1q3)).a);return B(_1qf(_1q3,_1q4));}else{return B(_1qf(_1q3,_1q4));}}}}}}}}),_1qq=E(_1q9);if(!_1qq._){return new F(function(){return _1pb(new T(function(){return E(E(_1qc).b);},1),0,_1q4+1|0,_1qe,_1q6,_1q7,_1qa);});}else{var _1qr=_1q3+1|0,_1qs=_1q4,_1qt=_1q6,_1qu=_1q7,_1qv=_1qa;_1pS=new T(function(){return E(E(_1qc).b);},1);_1pT=_1qr;_1pU=_1qs;_1pV=_1qe;_1pW=_1qt;_1pX=_1qu;_1pY=_1qq.a;_1pZ=_1qq.b;_1q0=_1qv;return __continue;}}else{var _1qw=E(_1q9);if(!_1qw._){return new F(function(){return _1pb(_1q2,0,_1q4+1|0,_1q5,_1q6,_1q7,_1qa);});}else{var _1qx=_1q2,_1qr=_1q3+1|0,_1qs=_1q4,_1qy=_1q5,_1qt=_1q6,_1qu=_1q7,_1qv=_1qa;_1pS=_1qx;_1pT=_1qr;_1pU=_1qs;_1pV=_1qy;_1pW=_1qt;_1pX=_1qu;_1pY=_1qw.a;_1pZ=_1qw.b;_1q0=_1qv;return __continue;}}})(_1pS,_1pT,_1pU,_1pV,_1pW,_1pX,_1pY,_1pZ,_1q0));if(_1q1!=__continue){return _1q1;}}},_1p7=B(_1pb(_1oc,0,0,_1ou,_1o3,_1o4,_1ou));}var _1qz=function(_1qA){var _1qB=function(_1qC){var _1qD=new T(function(){switch(E(_1oi)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1qE=new T(function(){if(!E(_1os)){if(!E(_1qD)){return new T2(0,_1o3,_1o4);}else{return new T2(0,_1o5,_1o6);}}else{if(!B(_1ic(_1io,_1p7,_1or))){if(!E(_1qD)){return new T2(0,_1o3,_1o4);}else{return new T2(0,_1o5,_1o6);}}else{return new T2(0,_1o5,_1o6);}}}),_1qF=new T(function(){return E(E(_1qE).b);}),_1qG=new T(function(){return E(E(_1qE).a);});if(!E(_1os)){var _1qH=E(_1of);}else{var _1qH=E(B(_1kZ(new T(function(){return B(_1mq(_1oa,_1ob,_1p7));}),_1p7)).a);}var _1qI=new T(function(){if(!E(_1oq)){if(!E(_1ol)){var _1qJ=function(_1qK){var _1qL=function(_1qM){var _1qN=E(_1oi);if(_1qN==4){return new T2(1,_1o0,new T2(1,_1oh,_S));}else{if(!E(_1qD)){return (E(_1qN)==2)?new T2(1,_1nY,new T2(1,_1oh,_S)):__Z;}else{var _1qO=E(_1oh);return (E(_1qO)==61)?new T2(1,_1nZ,new T2(1,_1qO,new T(function(){return B(_A(0,_1o4,_S));}))):new T2(1,_1nZ,new T2(1,_1qO,_S));}}};if(!E(_1os)){return new F(function(){return _1qL(_);});}else{if(E(_1o5)!=E(_1qG)){return new T2(1,_1o1,new T2(1,_1oh,_S));}else{if(E(_1o6)!=E(_1qF)){return new T2(1,_1o1,new T2(1,_1oh,_S));}else{return new F(function(){return _1qL(_);});}}}};if(!E(_1os)){return B(_1qJ(_));}else{if(!E(_1qH)){return B(_1qJ(_));}else{return E(_1nU);}}}else{return new T2(1,_1nS,new T2(1,_1oh,_S));}}else{return new T2(1,_1nT,new T2(1,_1oh,_S));}},1);return {_:0,a:new T2(0,_1qG,_1qF),b:_1p7,c:_1qA,d:_1qC,e:_1oa,f:_1ob,g:_1oc,h:B(_q(_1od,_1qI)),i:_1oe,j:E(_1qH)};};if(!E(_1oq)){return new F(function(){return _1qB(_1o9);});}else{return new F(function(){return _1qB(E(_1oh));});}};if(!E(_1ol)){return new F(function(){return _1qz(_1o8);});}else{return new F(function(){return _1qz(E(_1oh));});}},_1qP=new T2(1,_5U,_S),_1qQ=5,_1qR=new T2(1,_1qQ,_S),_1qS=function(_1qT,_1qU){while(1){var _1qV=E(_1qT);if(!_1qV._){return E(_1qU);}else{_1qT=_1qV.b;_1qU=_1qV.a;continue;}}},_1qW=57,_1qX=48,_1qY=new T2(1,_1lx,_S),_1qZ=new T(function(){return B(err(_ss));}),_1r0=new T(function(){return B(err(_sq));}),_1r1=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_1r2=function(_1r3,_1r4){if((_1r4-48|0)>>>0>9){var _1r5=_1r4+_1r3|0,_1r6=function(_1r7){if(!B(_4A(_h6,_1r7,_1qY))){return E(_1r7);}else{return new F(function(){return _1r2(_1r3,_1r7);});}};if(_1r5<=122){if(_1r5>=97){if(_1r5>>>0>1114111){return new F(function(){return _wD(_1r5);});}else{return new F(function(){return _1r6(_1r5);});}}else{if(_1r5<=90){if(_1r5>>>0>1114111){return new F(function(){return _wD(_1r5);});}else{return new F(function(){return _1r6(_1r5);});}}else{var _1r8=65+(_1r5-90|0)|0;if(_1r8>>>0>1114111){return new F(function(){return _wD(_1r8);});}else{return new F(function(){return _1r6(_1r8);});}}}}else{var _1r9=97+(_1r5-122|0)|0;if(_1r9>>>0>1114111){return new F(function(){return _wD(_1r9);});}else{return new F(function(){return _1r6(_1r9);});}}}else{var _1ra=B(_Gc(B(_sx(_1r1,new T2(1,_1r4,_S)))));if(!_1ra._){return E(_1r0);}else{if(!E(_1ra.b)._){var _1rb=E(_1ra.a)+_1r3|0;switch(_1rb){case  -1:return E(_1qX);case 10:return E(_1qW);default:return new F(function(){return _1qS(B(_A(0,_1rb,_S)),_T3);});}}else{return E(_1qZ);}}}},_1rc=function(_1rd,_1re){if((_1rd-48|0)>>>0>9){return _1re;}else{var _1rf=B(_Gc(B(_sx(_1r1,new T2(1,_1rd,_S)))));if(!_1rf._){return E(_1r0);}else{if(!E(_1rf.b)._){return new F(function(){return _1r2(E(_1rf.a),_1re);});}else{return E(_1qZ);}}}},_1rg=function(_1rh,_1ri){return new F(function(){return _1rc(E(_1rh),E(_1ri));});},_1rj=new T2(1,_1rg,_S),_1rk=112,_1rl=111,_1rm=function(_1rn,_1ro,_1rp,_1rq,_1rr,_1rs,_1rt,_1ru,_1rv,_1rw,_1rx){var _1ry=new T(function(){return B(_6Q(B(_6Q(_1rp,_1ro)),E(_1rn)));}),_1rz=new T(function(){return E(E(_1ry).b);}),_1rA=new T(function(){if(E(_1rz)==4){return true;}else{return false;}}),_1rB=new T(function(){return E(E(_1ry).a);});if(E(_1rr)==32){var _1rC=false;}else{if(E(_1rB)==32){var _1rD=true;}else{var _1rD=false;}var _1rC=_1rD;}var _1rE=new T(function(){var _1rF=new T(function(){return B(A3(_6Q,_1qP,B(_Mt(_h6,_1rq,_1ly)),_1rr));});if(!E(_1rC)){if(!E(_1rA)){return E(_1rB);}else{if(!B(_4A(_3L,_1rs,_1qR))){return E(_1rB);}else{return B(A(_6Q,[_1rj,B(_Mt(_3L,_1rs,_1qR)),_1rF,_1rB]));}}}else{return E(_1rF);}}),_1rG=B(_KJ(_1rn,_1ro,_1rE,_1rz,_1rp));if(!E(_1rC)){var _1rH=B(_1kZ(new T(function(){return B(_1mq(_1rs,_1rt,_1rG));}),_1rG)).a;return {_:0,a:new T2(0,_1rn,_1ro),b:_1rG,c:_1rq,d:_1rr,e:_1rs,f:_1rt,g:_1ru,h:B(_q(_1rv,new T(function(){if(!E(_1rH)){if(!E(_1rA)){return __Z;}else{return new T2(1,_1rk,new T2(1,_1rE,_S));}}else{return E(_1nU);}},1))),i:_1rw,j:E(_1rH)};}else{var _1rI=B(_1kZ(new T(function(){return B(_1mq(_1rs,_1rt,_1rG));}),_1rG)).a;return {_:0,a:new T2(0,_1rn,_1ro),b:_1rG,c:_1rq,d:32,e:_1rs,f:_1rt,g:_1ru,h:B(_q(_1rv,new T(function(){if(!E(_1rI)){return new T2(1,_1rl,new T2(1,_1rE,_S));}else{return E(_1nU);}},1))),i:_1rw,j:E(_1rI)};}},_1rJ=new T(function(){return B(_e6("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1rK=function(_1rL,_1rM){while(1){var _1rN=E(_1rM);if(!_1rN._){return false;}else{var _1rO=_1rN.b,_1rP=E(_1rL),_1rQ=_1rP.a,_1rR=_1rP.b,_1rS=E(_1rN.a);if(!_1rS._){return E(_1rJ);}else{var _1rT=E(_1rS.a),_1rU=_1rT.a,_1rV=_1rT.b,_1rW=E(_1rS.b);if(!_1rW._){var _1rX=E(_1rQ),_1rY=E(_1rX);if(_1rY==32){switch(E(_1rR)){case 0:if(!E(_1rV)){return true;}else{_1rL=new T2(0,_1rX,_E8);_1rM=_1rO;continue;}break;case 1:if(E(_1rV)==1){return true;}else{_1rL=new T2(0,_1rX,_Ee);_1rM=_1rO;continue;}break;case 2:if(E(_1rV)==2){return true;}else{_1rL=new T2(0,_1rX,_Ek);_1rM=_1rO;continue;}break;case 3:if(E(_1rV)==3){return true;}else{_1rL=new T2(0,_1rX,_Eq);_1rM=_1rO;continue;}break;case 4:if(E(_1rV)==4){return true;}else{_1rL=new T2(0,_1rX,_Ew);_1rM=_1rO;continue;}break;case 5:if(E(_1rV)==5){return true;}else{_1rL=new T2(0,_1rX,_EX);_1rM=_1rO;continue;}break;case 6:if(E(_1rV)==6){return true;}else{_1rL=new T2(0,_1rX,_EQ);_1rM=_1rO;continue;}break;case 7:if(E(_1rV)==7){return true;}else{_1rL=new T2(0,_1rX,_EJ);_1rM=_1rO;continue;}break;default:if(E(_1rV)==8){return true;}else{_1rL=new T2(0,_1rX,_EC);_1rM=_1rO;continue;}}}else{if(_1rY!=E(_1rU)){_1rL=_1rP;_1rM=_1rO;continue;}else{switch(E(_1rR)){case 0:if(!E(_1rV)){return true;}else{_1rL=new T2(0,_1rX,_E8);_1rM=_1rO;continue;}break;case 1:if(E(_1rV)==1){return true;}else{_1rL=new T2(0,_1rX,_Ee);_1rM=_1rO;continue;}break;case 2:if(E(_1rV)==2){return true;}else{_1rL=new T2(0,_1rX,_Ek);_1rM=_1rO;continue;}break;case 3:if(E(_1rV)==3){return true;}else{_1rL=new T2(0,_1rX,_Eq);_1rM=_1rO;continue;}break;case 4:if(E(_1rV)==4){return true;}else{_1rL=new T2(0,_1rX,_Ew);_1rM=_1rO;continue;}break;case 5:if(E(_1rV)==5){return true;}else{_1rL=new T2(0,_1rX,_EX);_1rM=_1rO;continue;}break;case 6:if(E(_1rV)==6){return true;}else{_1rL=new T2(0,_1rX,_EQ);_1rM=_1rO;continue;}break;case 7:if(E(_1rV)==7){return true;}else{_1rL=new T2(0,_1rX,_EJ);_1rM=_1rO;continue;}break;default:if(E(_1rV)==8){return true;}else{_1rL=new T2(0,_1rX,_EC);_1rM=_1rO;continue;}}}}}else{var _1rZ=E(_1rQ),_1s0=E(_1rZ);if(_1s0==32){switch(E(_1rR)){case 0:if(!E(_1rV)){return true;}else{_1rL=new T2(0,_1rZ,_E8);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 1:if(E(_1rV)==1){return true;}else{_1rL=new T2(0,_1rZ,_Ee);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 2:if(E(_1rV)==2){return true;}else{_1rL=new T2(0,_1rZ,_Ek);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 3:if(E(_1rV)==3){return true;}else{_1rL=new T2(0,_1rZ,_Eq);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 4:if(E(_1rV)==4){return true;}else{_1rL=new T2(0,_1rZ,_Ew);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 5:if(E(_1rV)==5){return true;}else{_1rL=new T2(0,_1rZ,_EX);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 6:if(E(_1rV)==6){return true;}else{_1rL=new T2(0,_1rZ,_EQ);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 7:if(E(_1rV)==7){return true;}else{_1rL=new T2(0,_1rZ,_EJ);_1rM=new T2(1,_1rW,_1rO);continue;}break;default:if(E(_1rV)==8){return true;}else{_1rL=new T2(0,_1rZ,_EC);_1rM=new T2(1,_1rW,_1rO);continue;}}}else{if(_1s0!=E(_1rU)){_1rL=_1rP;_1rM=new T2(1,_1rW,_1rO);continue;}else{switch(E(_1rR)){case 0:if(!E(_1rV)){return true;}else{_1rL=new T2(0,_1rZ,_E8);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 1:if(E(_1rV)==1){return true;}else{_1rL=new T2(0,_1rZ,_Ee);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 2:if(E(_1rV)==2){return true;}else{_1rL=new T2(0,_1rZ,_Ek);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 3:if(E(_1rV)==3){return true;}else{_1rL=new T2(0,_1rZ,_Eq);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 4:if(E(_1rV)==4){return true;}else{_1rL=new T2(0,_1rZ,_Ew);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 5:if(E(_1rV)==5){return true;}else{_1rL=new T2(0,_1rZ,_EX);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 6:if(E(_1rV)==6){return true;}else{_1rL=new T2(0,_1rZ,_EQ);_1rM=new T2(1,_1rW,_1rO);continue;}break;case 7:if(E(_1rV)==7){return true;}else{_1rL=new T2(0,_1rZ,_EJ);_1rM=new T2(1,_1rW,_1rO);continue;}break;default:if(E(_1rV)==8){return true;}else{_1rL=new T2(0,_1rZ,_EC);_1rM=new T2(1,_1rW,_1rO);continue;}}}}}}}}},_1s1=function(_1s2,_1s3){var _1s4=E(_1s2);if(!_1s4._){return __Z;}else{var _1s5=E(_1s3);return (_1s5._==0)?__Z:new T2(1,new T(function(){return new T2(0,new T2(1,_1s5.a,_1hn),E(_1s4.a).b);}),new T(function(){return B(_1s1(_1s4.b,_1s5.b));}));}},_1s6=new T(function(){return B(unCStr("\n"));}),_1s7=function(_1s8,_1s9,_){var _1sa=jsWriteHandle(E(_1s8),toJSStr(E(_1s9)));return _gD;},_1sb=function(_1sc,_1sd,_){var _1se=E(_1sc),_1sf=jsWriteHandle(_1se,toJSStr(E(_1sd)));return new F(function(){return _1s7(_1se,_1s6,_);});},_1sg=function(_1sh){var _1si=E(_1sh);if(!_1si._){return __Z;}else{return new F(function(){return _q(_1si.a,new T(function(){return B(_1sg(_1si.b));},1));});}},_1sj=0,_1sk= -1,_1sl= -2,_1sm=new T(function(){return B(unCStr("removed"));}),_1sn=new T(function(){return B(unCStr("loadError"));}),_1so=new T(function(){return B(unCStr("saved"));}),_1sp=new T(function(){var _1sq=E(_1bY);if(!_1sq._){return E(_ng);}else{return E(_1sq.a);}}),_1sr=new T(function(){return B(_18L(_1bw,5,_1cr));}),_1ss=new T(function(){return B(unCStr("Thank you for playing!"));}),_1st=17,_1su=2,_1sv=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1sw=10,_1sx=3,_1sy=new T(function(){return B(unCStr("Coding : yokoP"));}),_1sz=8,_1sA=new T(function(){return B(unCStr("Congratulations!"));}),_1sB=5,_1sC=32,_1sD=new T2(0,_1sC,_EX),_1sE=99,_1sF=64,_1sG=new T(function(){return B(_ms(_1cQ,0));}),_1sH=new T(function(){return B(unCStr("loadError"));}),_1sI=new T(function(){return B(unCStr(","));}),_1sJ=new T(function(){return B(unCStr("~"));}),_1sK=new T(function(){return B(unCStr("savedata"));}),_1sL=new T(function(){return B(unCStr("---"));}),_1sM=0,_1sN=new T1(0,333),_1sO=new T(function(){return B(_8r(1,2147483647));}),_1sP=new T(function(){return B(unCStr("choice"));}),_1sQ=new T2(1,_6C,_S),_1sR=new T(function(){return B(_8j(_1sP,_1sQ));}),_1sS=new T2(1,_6C,_1sR),_1sT=new T(function(){return B(unAppCStr("[]",_S));}),_1sU=new T(function(){return B(unCStr("\""));}),_1sV=new T2(1,_S,_S),_1sW=new T(function(){return B(_6d(_Z1,_1sV));}),_1sX=new T2(1,_6C,_S),_1sY=function(_1sZ,_1t0){var _1t1=E(_1t0);return (_1t1._==0)?__Z:new T2(1,_1sZ,new T2(1,_1t1.a,new T(function(){return B(_1sY(_1sZ,_1t1.b));})));},_1t2=new T(function(){return B(unCStr("noContent"));}),_1t3=new T(function(){return B(unCStr("noHint"));}),_1t4=new T(function(){return B(err(_ss));}),_1t5=new T(function(){return B(err(_sq));}),_1t6=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_1t7=function(_1t8,_1t9){var _1ta=E(_1t9);if(!_1ta._){var _1tb=B(_Gc(B(_sx(_1t6,_1t8))));return (_1tb._==0)?E(_1t5):(E(_1tb.b)._==0)?new T4(0,E(_1tb.a),_S,_S,_S):E(_1t4);}else{var _1tc=_1ta.a,_1td=E(_1ta.b);if(!_1td._){var _1te=B(_Gc(B(_sx(_1t6,_1t8))));return (_1te._==0)?E(_1t5):(E(_1te.b)._==0)?new T4(0,E(_1te.a),E(_1tc),E(_1t3),E(_1t2)):E(_1t4);}else{var _1tf=_1td.a,_1tg=E(_1td.b);if(!_1tg._){var _1th=B(_Gc(B(_sx(_1t6,_1t8))));return (_1th._==0)?E(_1t5):(E(_1th.b)._==0)?new T4(0,E(_1th.a),E(_1tc),E(_1tf),E(_1t2)):E(_1t4);}else{if(!E(_1tg.b)._){var _1ti=B(_Gc(B(_sx(_1t6,_1t8))));return (_1ti._==0)?E(_1t5):(E(_1ti.b)._==0)?new T4(0,E(_1ti.a),E(_1tc),E(_1tf),E(_1tg.a)):E(_1t4);}else{return new T4(0,0,_S,_S,_S);}}}}},_1tj=function(_1tk){var _1tl=E(_1tk);if(!_1tl._){return new F(function(){return _1t7(_S,_S);});}else{var _1tm=_1tl.a,_1tn=E(_1tl.b);if(!_1tn._){return new F(function(){return _1t7(new T2(1,_1tm,_S),_S);});}else{var _1to=E(_1tm),_1tp=new T(function(){var _1tq=B(_H4(44,_1tn.a,_1tn.b));return new T2(0,_1tq.a,_1tq.b);});if(E(_1to)==44){return new F(function(){return _1t7(_S,new T2(1,new T(function(){return E(E(_1tp).a);}),new T(function(){return E(E(_1tp).b);})));});}else{var _1tr=E(_1tp);return new F(function(){return _1t7(new T2(1,_1to,_1tr.a),_1tr.b);});}}}},_1ts=function(_1tt){var _1tu=B(_1tj(_1tt));return new T4(0,_1tu.a,E(_1tu.b),E(_1tu.c),E(_1tu.d));},_1tv=function(_1tw){return (E(_1tw)==10)?true:false;},_1tx=function(_1ty){var _1tz=E(_1ty);if(!_1tz._){return __Z;}else{var _1tA=new T(function(){var _1tB=B(_19e(_1tv,_1tz));return new T2(0,_1tB.a,new T(function(){var _1tC=E(_1tB.b);if(!_1tC._){return __Z;}else{return B(_1tx(_1tC.b));}}));});return new T2(1,new T(function(){return E(E(_1tA).a);}),new T(function(){return E(E(_1tA).b);}));}},_1tD=new T(function(){return B(unCStr("57,\u5974\u56fd\u738b\u304c\u5f8c\u6f22\u304b\u3089\u91d1\u5370,\u300c\u5f8c\u6f22\u66f8\u300d\u306b\u8a18\u8f09\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\u8cc0\u5cf6\u306b\u3066\u300c\u6f22\u59d4\u5974\u570b\u738b\u300d\u3068\u523b\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\u898b\u3055\u308c\u308b**\u5927\u548c\u671d\u5ef7\u3068\u306e\u95dc\u4fc2\u306f\u4e0d\u660e\n239,\u300c\u5351\u5f25\u547c\u300d\u304c\u9b4f\u306b\u9063\u4f7f,\u652f\u90a3\u306e\u6b74\u53f2\u66f8\u300c\u9b4f\u5fd7\u300d\u306b\u8a18\u8f09\u3055\u308c\u3066\u3090\u308b\u5deb\u5973,\u300c\u9b4f\u5fd7\u300d\u502d\u4eba\u4f1d\u306b\u8a18\u3055\u308c\u3066\u3090\u308b\u300c\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)\u300d\u3082\u300c\u5351\u5f25\u547c\u300d\u3082\u65e5\u672c\u306b\u6b98\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\u5fb3\u5929\u7687 \u7a0e\u3092\u514d\u9664,\u300c\u53e4\u4e8b\u8a18\u300d\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u8a18\u8f09\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c\u300c\u6c11\u306e\u304b\u307e\u3069\u3088\u308a\u7159\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\u3057\u304f\u3066\u708a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b\u300d\u3068\u3057\u3066 \u5bae\u4e2d\u306e\u4fee\u7e55\u3092\u5f8c\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\u304b\u306b\u3059\u308b\u8a71\u304c\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u3042\u308b\n478,\u300c\u502d\u300d\u306e\u6b66\u738b \u5357\u671d\u306e\u5b8b\u3078\u9063\u4f7f,\u96c4\u7565\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\u8aac,\u300c\u5b8b\u66f8\u300d\u502d\u570b\u50b3\u306b\u8a18\u8f09\u304c\u3042\u308b**\u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\u6559\u516c\u4f1d,\u6b3d\u660e\u5929\u7687\u5fa1\u4ee3\u306b\u767e\u6e08\u306e\u8056\u660e\u738b\u304b\u3089\u4f1d\u6765\u3057\u305f\u3068\u306e\u6587\u732e\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\u8aac\u3042\u308b\n604,\u5341\u4e03\u6761\u61b2\u6cd5\u5236\u5b9a,\u8056\u5fb3\u592a\u5b50\u304c\u5236\u5b9a\u3057\u305f\u3068\u3055\u308c\u308b,\u300c\u548c\u3092\u4ee5\u3066\u8cb4\u3057\u3068\u70ba\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\u304d\u3092\u5b97\u3068\u305b\u3088\u300d\n607,\u6cd5\u9686\u5bfa\u304c\u5275\u5efa\u3055\u308c\u308b,\u8056\u5fb3\u592a\u5b50\u3086\u304b\u308a\u306e\u5bfa\u9662,\u897f\u9662\u4f3d\u85cd\u306f\u73fe\u5b58\u3059\u308b\u4e16\u754c\u6700\u53e4\u306e\u6728\u9020\u5efa\u7bc9\u7269\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\u5df3\u306e\u5909,\u3053\u306e\u5f8c\u3059\u3050\u5927\u5316\u306e\u6539\u65b0\u306a\u308b,\u4e2d\u5927\u5144\u7687\u5b50(\u5f8c\u306e38\u4ee3\u5929\u667a\u5929\u7687)\u304c\u8607\u6211\u6c0f\u3092\u4ea1\u307c\u3059\n663,\u767d\u6751\u6c5f\u306e\u6226,\u5510\u3068\u65b0\u7f85\u306b\u6ec5\u307c\u3055\u308c\u305f\u767e\u6e08\u3092\u518d\u8208\u3059\u308b\u76ee\u7684,\u5510\u30fb\u65b0\u7f85\u9023\u5408\u8ecd\u306b\u6557\u308c\u308b\n672,\u58ec\u7533\u306e\u4e71,\u5929\u667a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\u7d99\u8005\u4e89\u3072,\u5f8c\u7d99\u8005\u3067\u3042\u3063\u305f\u5927\u53cb\u7687\u5b50\u306b\u53d4\u7236\u306e\u5927\u6d77\u4eba\u7687\u5b50\u304c\u53cd\u65d7\u3092\u7ffb\u3057 \u5927\u53cb\u7687\u5b50\u3092\u5012\u3057\u3066\u5929\u6b66\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f\u300c\u306a\u3089\u300d\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b\u300c\u82b1\u306e\u5fa1\u6240\u300d\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089\u300c\u5ba4\u753a\u5e55\u5e9c\u300d\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075\u300c\u4e0b\u524b\u4e0a\u300d\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d \u300c\u5929\u4e0b\u5e03\u6b66\u300d\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b\u300c\u9396\u56fd\u300d\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c\u300c\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4\u300d\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1tE=new T(function(){return B(_1tx(_1tD));}),_1tF=new T(function(){return B(_6d(_1ts,_1tE));}),_1tG=new T(function(){return B(_8O(1,2));}),_1tH=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b\u300c\u4e0d\u5e73\u7b49\u300d\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,\u300c\u6276\u6e05\u6ec5\u6d0b\u300d\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***\u300c\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287\u300d\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b\u300c\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42\u300d,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059\u300d\u30fc\u30fc\u5f8c\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059\u300d"));}),_1tI=new T(function(){return B(_1tx(_1tH));}),_1tJ=new T(function(){return B(_6d(_1ts,_1tI));}),_1tK=function(_1tL,_1tM){var _1tN=E(_1tL);if(!_1tN._){return __Z;}else{var _1tO=E(_1tM);return (_1tO._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1tN.a).a;}),_1tO.a),new T(function(){return B(_1tK(_1tN.b,_1tO.b));}));}},_1tP=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1tQ=new T(function(){return B(unCStr("tail"));}),_1tR=new T(function(){return B(_nd(_1tQ));}),_1tS=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1tT=new T2(1,_2t,_S),_1tU=function(_1tV,_1tW){return new T2(1,_6C,new T(function(){return B(_8j(_1tV,new T2(1,_6C,_1tW)));}));},_1tX=function(_1tY){var _1tZ=E(_1tY);if(!_1tZ._){return E(_1tT);}else{var _1u0=new T(function(){var _1u1=E(_1tZ.a),_1u2=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1u3){return new F(function(){return _1tU(_1u1.a,_1u3);});},new T2(1,function(_1u4){return new F(function(){return _1tU(_1u1.b,_1u4);});},_S)),new T2(1,_y,new T(function(){return B(_1tX(_1tZ.b));}))));});return new T2(1,_z,_1u2);});return new T2(1,_2s,_1u0);}},_1u5=function(_1u6){var _1u7=E(_1u6);if(!_1u7._){return E(_1tT);}else{var _1u8=new T(function(){return B(_A(0,E(_1u7.a),new T(function(){return B(_1u5(_1u7.b));})));});return new T2(1,_2s,_1u8);}},_1u9=function(_1ua){var _1ub=E(_1ua);if(!_1ub._){return E(_1tT);}else{var _1uc=new T(function(){var _1ud=E(_1ub.a),_1ue=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1uf){return new F(function(){return _1tU(_1ud.a,_1uf);});},new T2(1,function(_1ug){return new F(function(){return _1tU(_1ud.b,_1ug);});},_S)),new T2(1,_y,new T(function(){return B(_1u9(_1ub.b));}))));});return new T2(1,_z,_1ue);});return new T2(1,_2s,_1uc);}},_1uh=new T(function(){return B(unCStr("True"));}),_1ui=new T(function(){return B(unCStr("False"));}),_1uj=function(_1uk){return E(E(_1uk).b);},_1ul=function(_1um,_1un,_1uo){var _1up=new T(function(){var _1uq=E(_1uo);if(!_1uq._){return __Z;}else{var _1ur=_1uq.b,_1us=E(_1uq.a),_1ut=E(_1us.a);if(_1ut<_1um){var _1uu=function(_1uv){while(1){var _1uw=B((function(_1ux){var _1uy=E(_1ux);if(!_1uy._){return __Z;}else{var _1uz=_1uy.b,_1uA=E(_1uy.a);if(E(_1uA.a)<_1um){_1uv=_1uz;return __continue;}else{return new T2(1,_1uA,new T(function(){return B(_1uu(_1uz));}));}}})(_1uv));if(_1uw!=__continue){return _1uw;}}};return B(_1uB(B(_1uu(_1ur))));}else{var _1uC=new T(function(){var _1uD=function(_1uE){while(1){var _1uF=B((function(_1uG){var _1uH=E(_1uG);if(!_1uH._){return __Z;}else{var _1uI=_1uH.b,_1uJ=E(_1uH.a);if(E(_1uJ.a)<_1um){_1uE=_1uI;return __continue;}else{return new T2(1,_1uJ,new T(function(){return B(_1uD(_1uI));}));}}})(_1uE));if(_1uF!=__continue){return _1uF;}}};return B(_1uD(_1ur));});return B(_1ul(_1ut,_1us.b,_1uC));}}}),_1uK=E(_1uo);if(!_1uK._){return new F(function(){return _q(_S,new T2(1,new T2(0,_1um,_1un),_1up));});}else{var _1uL=_1uK.b,_1uM=E(_1uK.a),_1uN=E(_1uM.a);if(_1uN>=_1um){var _1uO=function(_1uP){while(1){var _1uQ=B((function(_1uR){var _1uS=E(_1uR);if(!_1uS._){return __Z;}else{var _1uT=_1uS.b,_1uU=E(_1uS.a);if(E(_1uU.a)>=_1um){_1uP=_1uT;return __continue;}else{return new T2(1,_1uU,new T(function(){return B(_1uO(_1uT));}));}}})(_1uP));if(_1uQ!=__continue){return _1uQ;}}};return new F(function(){return _q(B(_1uB(B(_1uO(_1uL)))),new T2(1,new T2(0,_1um,_1un),_1up));});}else{var _1uV=new T(function(){var _1uW=function(_1uX){while(1){var _1uY=B((function(_1uZ){var _1v0=E(_1uZ);if(!_1v0._){return __Z;}else{var _1v1=_1v0.b,_1v2=E(_1v0.a);if(E(_1v2.a)>=_1um){_1uX=_1v1;return __continue;}else{return new T2(1,_1v2,new T(function(){return B(_1uW(_1v1));}));}}})(_1uX));if(_1uY!=__continue){return _1uY;}}};return B(_1uW(_1uL));});return new F(function(){return _q(B(_1ul(_1uN,_1uM.b,_1uV)),new T2(1,new T2(0,_1um,_1un),_1up));});}}},_1uB=function(_1v3){var _1v4=E(_1v3);if(!_1v4._){return __Z;}else{var _1v5=_1v4.b,_1v6=E(_1v4.a),_1v7=_1v6.a,_1v8=new T(function(){var _1v9=E(_1v5);if(!_1v9._){return __Z;}else{var _1va=_1v9.b,_1vb=E(_1v9.a),_1vc=E(_1vb.a),_1vd=E(_1v7);if(_1vc<_1vd){var _1ve=function(_1vf){while(1){var _1vg=B((function(_1vh){var _1vi=E(_1vh);if(!_1vi._){return __Z;}else{var _1vj=_1vi.b,_1vk=E(_1vi.a);if(E(_1vk.a)<_1vd){_1vf=_1vj;return __continue;}else{return new T2(1,_1vk,new T(function(){return B(_1ve(_1vj));}));}}})(_1vf));if(_1vg!=__continue){return _1vg;}}};return B(_1uB(B(_1ve(_1va))));}else{var _1vl=new T(function(){var _1vm=function(_1vn){while(1){var _1vo=B((function(_1vp){var _1vq=E(_1vp);if(!_1vq._){return __Z;}else{var _1vr=_1vq.b,_1vs=E(_1vq.a);if(E(_1vs.a)<_1vd){_1vn=_1vr;return __continue;}else{return new T2(1,_1vs,new T(function(){return B(_1vm(_1vr));}));}}})(_1vn));if(_1vo!=__continue){return _1vo;}}};return B(_1vm(_1va));});return B(_1ul(_1vc,_1vb.b,_1vl));}}}),_1vt=E(_1v5);if(!_1vt._){return new F(function(){return _q(_S,new T2(1,_1v6,_1v8));});}else{var _1vu=_1vt.b,_1vv=E(_1vt.a),_1vw=E(_1vv.a),_1vx=E(_1v7);if(_1vw>=_1vx){var _1vy=function(_1vz){while(1){var _1vA=B((function(_1vB){var _1vC=E(_1vB);if(!_1vC._){return __Z;}else{var _1vD=_1vC.b,_1vE=E(_1vC.a);if(E(_1vE.a)>=_1vx){_1vz=_1vD;return __continue;}else{return new T2(1,_1vE,new T(function(){return B(_1vy(_1vD));}));}}})(_1vz));if(_1vA!=__continue){return _1vA;}}};return new F(function(){return _q(B(_1uB(B(_1vy(_1vu)))),new T2(1,_1v6,_1v8));});}else{var _1vF=new T(function(){var _1vG=function(_1vH){while(1){var _1vI=B((function(_1vJ){var _1vK=E(_1vJ);if(!_1vK._){return __Z;}else{var _1vL=_1vK.b,_1vM=E(_1vK.a);if(E(_1vM.a)>=_1vx){_1vH=_1vL;return __continue;}else{return new T2(1,_1vM,new T(function(){return B(_1vG(_1vL));}));}}})(_1vH));if(_1vI!=__continue){return _1vI;}}};return B(_1vG(_1vu));});return new F(function(){return _q(B(_1ul(_1vw,_1vv.b,_1vF)),new T2(1,_1v6,_1v8));});}}}},_1vN=function(_){return new F(function(){return jsMkStdout();});},_1vO=new T(function(){return B(_36(_1vN));}),_1vP=new T(function(){return B(_La("Browser.hs:82:24-56|(Right j)"));}),_1vQ=function(_1vR){var _1vS=jsParseJSON(toJSStr(E(_1vR)));return (_1vS._==0)?E(_1vP):E(_1vS.a);},_1vT=function(_1vU,_1vV,_1vW,_1vX,_1vY,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1w9,_1wa,_1wb,_1wc,_1wd,_1we,_1wf,_1wg,_1wh,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_1wo,_1wp,_1wq,_1wr,_1ws,_1wt,_1wu,_1wv,_1ww,_1wx,_1wy,_1wz,_1wA,_){var _1wB={_:0,a:E(_1ws),b:E(_1wt),c:E(_1wu),d:E(_1wv),e:E(_1ww),f:E(_1wx),g:E(_1wy),h:E(_1wz)},_1wC=new T2(0,_1wg,_1wh),_1wD=new T2(0,_1w9,_1wa),_1wE={_:0,a:E(_1vZ),b:E(_1w0),c:_1w1,d:_1w2,e:_1w3,f:E(_1w4),g:_1w5,h:E(_1w6),i:E(_1w7),j:E(_1w8)};if(!E(_1wx)){var _1wF=function(_1wG){if(!E(_1wv)){if(!E(_1wz)){return {_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)};}else{var _1wH=function(_,_1wI,_1wJ,_1wK,_1wL,_1wM,_1wN,_1wO,_1wP,_1wQ,_1wR,_1wS,_1wT,_1wU,_1wV,_1wW,_1wX,_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3,_1x4,_1x5,_1x6,_1x7,_1x8,_1x9,_1xa){var _1xb=function(_){var _1xc=function(_){var _1xd=function(_){var _1xe=B(_1sb(_1vO,new T2(1,_6C,new T(function(){return B(_8j(_1wP,_1sX));})),_)),_1xf=function(_){var _1xg=B(_1sb(_1vO,B(_A(0,_1wl,_S)),_)),_1xh=B(_13Z(_1sB,_1wO,_)),_1xi=E(_1xh).b,_1xj=E(_1vU),_1xk=_1xj.a,_1xl=_1xj.b,_1xm=new T(function(){return B(_1i9(E(_1vY)));}),_1xn=new T(function(){var _1xo=E(_1xm),_1xp=E(_1wI),_1xq=_1xp.a,_1xr=_1xp.b,_1xs=function(_1xt,_1xu,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_1xB,_1xC){var _1xD=E(_1xt);if(E(_1xo)==32){var _1xE=B(_1rm(_1xD.a,E(_1xD.b),_1xu,_1xv,_1xw,_1xx,_1xy,_1xz,_1xA,_1xB,_1xC)),_1xF=_1xE.h,_1xG=B(_1f2(_1sM,_1xF,_1wV,{_:0,a:E(_1xE.a),b:E(_1xE.b),c:_1xE.c,d:_1xE.d,e:_1xE.e,f:E(_1xE.f),g:E(_1xi),h:E(_1xF),i:E(_1xE.i),j:E(_1xE.j)},_1wS,_1wT,_1wU,_1wV,_1wW,_1wX,_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3,_1x4,_1x5,_1x6,_1x7,_1x8,_1x9,_1xa));return {_:0,a:E(_1xG.a),b:E(_1xG.b),c:E(_1xG.c),d:E(_1xG.d),e:E(_1xG.e),f:E(_1xG.f),g:E(_1xG.g),h:E(_1xG.h),i:_1xG.i,j:_1xG.j,k:_1xG.k,l:_1xG.l,m:E(_1xG.m),n:_1xG.n,o:E(_1xG.o),p:E(_1xG.p),q:E(_1xG.q),r:_1xG.r,s:E(_1xG.s),t:E(_1xG.t)};}else{var _1xH=B(_1f2(_1sM,_1xA,_1wV,{_:0,a:E(_1xD),b:E(_1xu),c:_1xv,d:_1xw,e:_1xx,f:E(_1xy),g:E(_1xi),h:E(_1xA),i:E(_1xB),j:E(_1xC)},_1wS,_1wT,_1wU,_1wV,_1wW,_1wX,_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3,_1x4,_1x5,_1x6,_1x7,_1x8,_1x9,_1xa));return {_:0,a:E(_1xH.a),b:E(_1xH.b),c:E(_1xH.c),d:E(_1xH.d),e:E(_1xH.e),f:E(_1xH.f),g:E(_1xH.g),h:E(_1xH.h),i:_1xH.i,j:_1xH.j,k:_1xH.k,l:_1xH.l,m:E(_1xH.m),n:_1xH.n,o:E(_1xH.o),p:E(_1xH.p),q:E(_1xH.q),r:_1xH.r,s:E(_1xH.s),t:E(_1xH.t)};}},_1xI=function(_1xJ,_1xK){return new F(function(){return _1o2(_1xJ,_1xK,_1xq,_1xr,_1wJ,_1wK,_1wL,_1wM,_1wN,_1wO,_1wP,_1wQ,_1wR);});};switch(E(_1xo)){case 72:var _1xL=E(_1xr);if(0<=(_1xL-1|0)){var _1xM=B(_1xI(E(_1xq),_1xL-1|0));return B(_1xs(_1xM.a,_1xM.b,_1xM.c,_1xM.d,_1xM.e,_1xM.f,_1xM.g,_1xM.h,_1xM.i,_1xM.j));}else{var _1xN=B(_1xI(E(_1xq),_1xL));return B(_1xs(_1xN.a,_1xN.b,_1xN.c,_1xN.d,_1xN.e,_1xN.f,_1xN.g,_1xN.h,_1xN.i,_1xN.j));}break;case 75:var _1xO=E(_1xq);if(0<=(_1xO-1|0)){var _1xP=B(_1xI(_1xO-1|0,E(_1xr)));return B(_1xs(_1xP.a,_1xP.b,_1xP.c,_1xP.d,_1xP.e,_1xP.f,_1xP.g,_1xP.h,_1xP.i,_1xP.j));}else{var _1xQ=B(_1xI(_1xO,E(_1xr)));return B(_1xs(_1xQ.a,_1xQ.b,_1xQ.c,_1xQ.d,_1xQ.e,_1xQ.f,_1xQ.g,_1xQ.h,_1xQ.i,_1xQ.j));}break;case 77:var _1xR=E(_1xq);if(E(_1w9)!=(_1xR+1|0)){var _1xS=B(_1xI(_1xR+1|0,E(_1xr)));return B(_1xs(_1xS.a,_1xS.b,_1xS.c,_1xS.d,_1xS.e,_1xS.f,_1xS.g,_1xS.h,_1xS.i,_1xS.j));}else{var _1xT=B(_1xI(_1xR,E(_1xr)));return B(_1xs(_1xT.a,_1xT.b,_1xT.c,_1xT.d,_1xT.e,_1xT.f,_1xT.g,_1xT.h,_1xT.i,_1xT.j));}break;case 80:var _1xU=E(_1xr);if(E(_1wa)!=(_1xU+1|0)){var _1xV=B(_1xI(E(_1xq),_1xU+1|0));return B(_1xs(_1xV.a,_1xV.b,_1xV.c,_1xV.d,_1xV.e,_1xV.f,_1xV.g,_1xV.h,_1xV.i,_1xV.j));}else{var _1xW=B(_1xI(E(_1xq),_1xU));return B(_1xs(_1xW.a,_1xW.b,_1xW.c,_1xW.d,_1xW.e,_1xW.f,_1xW.g,_1xW.h,_1xW.i,_1xW.j));}break;case 104:var _1xX=E(_1xq);if(0<=(_1xX-1|0)){var _1xY=B(_1xI(_1xX-1|0,E(_1xr)));return B(_1xs(_1xY.a,_1xY.b,_1xY.c,_1xY.d,_1xY.e,_1xY.f,_1xY.g,_1xY.h,_1xY.i,_1xY.j));}else{var _1xZ=B(_1xI(_1xX,E(_1xr)));return B(_1xs(_1xZ.a,_1xZ.b,_1xZ.c,_1xZ.d,_1xZ.e,_1xZ.f,_1xZ.g,_1xZ.h,_1xZ.i,_1xZ.j));}break;case 106:var _1y0=E(_1xr);if(E(_1wa)!=(_1y0+1|0)){var _1y1=B(_1xI(E(_1xq),_1y0+1|0));return B(_1xs(_1y1.a,_1y1.b,_1y1.c,_1y1.d,_1y1.e,_1y1.f,_1y1.g,_1y1.h,_1y1.i,_1y1.j));}else{var _1y2=B(_1xI(E(_1xq),_1y0));return B(_1xs(_1y2.a,_1y2.b,_1y2.c,_1y2.d,_1y2.e,_1y2.f,_1y2.g,_1y2.h,_1y2.i,_1y2.j));}break;case 107:var _1y3=E(_1xr);if(0<=(_1y3-1|0)){var _1y4=B(_1xI(E(_1xq),_1y3-1|0));return B(_1xs(_1y4.a,_1y4.b,_1y4.c,_1y4.d,_1y4.e,_1y4.f,_1y4.g,_1y4.h,_1y4.i,_1y4.j));}else{var _1y5=B(_1xI(E(_1xq),_1y3));return B(_1xs(_1y5.a,_1y5.b,_1y5.c,_1y5.d,_1y5.e,_1y5.f,_1y5.g,_1y5.h,_1y5.i,_1y5.j));}break;case 108:var _1y6=E(_1xq);if(E(_1w9)!=(_1y6+1|0)){var _1y7=B(_1xI(_1y6+1|0,E(_1xr)));return B(_1xs(_1y7.a,_1y7.b,_1y7.c,_1y7.d,_1y7.e,_1y7.f,_1y7.g,_1y7.h,_1y7.i,_1y7.j));}else{var _1y8=B(_1xI(_1y6,E(_1xr)));return B(_1xs(_1y8.a,_1y8.b,_1y8.c,_1y8.d,_1y8.e,_1y8.f,_1y8.g,_1y8.h,_1y8.i,_1y8.j));}break;default:var _1y9=B(_1xI(E(_1xq),E(_1xr)));return B(_1xs(_1y9.a,_1y9.b,_1y9.c,_1y9.d,_1y9.e,_1y9.f,_1y9.g,_1y9.h,_1y9.i,_1y9.j));}}),_1ya=B(_16q(_1xk,_1xl,_1vV,_1vW,_1vX,_1xn,_)),_1yb=_1ya,_1yc=E(_1xm),_1yd=function(_,_1ye){var _1yf=function(_1yg){var _1yh=B(_1sb(_1vO,B(_8p(_1ye)),_)),_1yi=E(_1yb),_1yj=_1yi.d,_1yk=_1yi.e,_1yl=_1yi.f,_1ym=_1yi.g,_1yn=_1yi.i,_1yo=_1yi.j,_1yp=_1yi.k,_1yq=_1yi.l,_1yr=_1yi.m,_1ys=_1yi.n,_1yt=_1yi.o,_1yu=_1yi.p,_1yv=_1yi.q,_1yw=_1yi.r,_1yx=_1yi.t,_1yy=E(_1yi.s),_1yz=_1yy.a,_1yA=_1yy.d,_1yB=_1yy.e,_1yC=_1yy.f,_1yD=_1yy.g,_1yE=_1yy.h,_1yF=E(_1yi.a),_1yG=_1yF.e,_1yH=_1yF.f,_1yI=_1yF.g,_1yJ=E(_1yi.h),_1yK=function(_1yL){var _1yM=function(_1yN){if(_1yN!=E(_1sG)){var _1yO=B(_6Q(_1bC,_1yN)),_1yP=_1yO.a,_1yQ=E(_1yO.b),_1yR=B(_18L(_1yP,_1yQ,new T(function(){return B(_6Q(_1cQ,_1yN));})));return new F(function(){return _1vT(_1xj,_1vV,_1vW,_1vX,_1sF,B(_6Q(_1bL,_1yN)),_1yR,B(_6Q(_1bY,_1yN)),32,_1yN,_1yH,_1yI,B(_q(_1yF.h,new T2(1,_1sE,new T(function(){return B(_A(0,_1yG,_S));})))),B(_1rK(_1sD,_1yR)),_ws,_1yP,_1yQ,_S,_1yj,_1yk,_1yl,_1ym,_1yJ.a,_1yJ.b,_1yn,_1yo,_1yp, -1,_1yr,_1ys,_1yt,_1yu,_1yv,_1yw,_ws,_ws,_ws,_1yA,_1yB,_1yC,_1yD,_1yE,_1yx,_);});}else{var _1yS=__app1(E(_nh),_1xl),_1yT=B(A2(_ni,_1xk,_)),_1yU=B(A(_mN,[_1xk,_j2,_1su,_1sB,_1sA,_])),_1yV=B(A(_mN,[_1xk,_j2,_1sx,_1sz,_1sy,_])),_1yW=B(A(_mN,[_1xk,_j2,_1sx,_1sw,_1sv,_])),_1yX=B(A(_mN,[_1xk,_j2,_1su,_1st,_1ss,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1bH),b:E(_1sr),c:E(_1sp),d:32,e:0,f:E(_1yH),g:_1yI,h:E(_S),i:E(_1yF.i),j:E(_ws)}),b:E(_1bz),c:E(_1yi.c),d:E(_1yj),e:E(_1yk),f:E(_1yl),g:E(_1ym),h:E(_1yJ),i:_1yn,j:_1yo,k:_1yp,l:_1yq,m:E(_1yr),n:_1ys,o:E(_1yt),p:E(_1yu),q:E(_1yv),r:_1yw,s:E({_:0,a:E(_1yz),b:E(_ws),c:E(_ws),d:E(_1yA),e:E(_1yB),f:E(_1yC),g:E(_1yD),h:E(_1yE)}),t:E(_1yx)};});}};if(_1yq>=0){return new F(function(){return _1yM(_1yq);});}else{return new F(function(){return _1yM(_1yG+1|0);});}};if(!E(_1yz)){if(E(_1yc)==110){return new F(function(){return _1yK(_);});}else{return _1yi;}}else{return new F(function(){return _1yK(_);});}};if(E(_1yc)==114){if(!B(_68(_1ye,_1sH))){var _1yY=E(_1ye);if(!_1yY._){return _1yb;}else{var _1yZ=_1yY.b;return new T(function(){var _1z0=E(_1yb),_1z1=E(_1z0.a),_1z2=E(_1yY.a),_1z3=E(_1z2);if(_1z3==34){var _1z4=B(_Rx(_1z2,_1yZ));if(!_1z4._){var _1z5=E(_1tR);}else{var _1z6=E(_1z4.b);if(!_1z6._){var _1z7=E(_1sV);}else{var _1z8=_1z6.a,_1z9=E(_1z6.b);if(!_1z9._){var _1za=new T2(1,new T2(1,_1z8,_S),_S);}else{var _1zb=E(_1z8),_1zc=new T(function(){var _1zd=B(_H4(126,_1z9.a,_1z9.b));return new T2(0,_1zd.a,_1zd.b);});if(E(_1zb)==126){var _1ze=new T2(1,_S,new T2(1,new T(function(){return E(E(_1zc).a);}),new T(function(){return E(E(_1zc).b);})));}else{var _1ze=new T2(1,new T2(1,_1zb,new T(function(){return E(E(_1zc).a);})),new T(function(){return E(E(_1zc).b);}));}var _1za=_1ze;}var _1z7=_1za;}var _1z5=_1z7;}var _1zf=_1z5;}else{var _1zg=E(_1yZ);if(!_1zg._){var _1zh=new T2(1,new T2(1,_1z2,_S),_S);}else{var _1zi=new T(function(){var _1zj=B(_H4(126,_1zg.a,_1zg.b));return new T2(0,_1zj.a,_1zj.b);});if(E(_1z3)==126){var _1zk=new T2(1,_S,new T2(1,new T(function(){return E(E(_1zi).a);}),new T(function(){return E(E(_1zi).b);})));}else{var _1zk=new T2(1,new T2(1,_1z2,new T(function(){return E(E(_1zi).a);})),new T(function(){return E(E(_1zi).b);}));}var _1zh=_1zk;}var _1zf=_1zh;}var _1zl=B(_Gc(B(_sx(_Z0,new T(function(){return B(_Jd(_1zf));})))));if(!_1zl._){return E(_YY);}else{if(!E(_1zl.b)._){var _1zm=E(_1zl.a),_1zn=B(_6Q(_1bC,_1zm)),_1zo=B(_6Q(_1zf,1));if(!_1zo._){var _1zp=__Z;}else{var _1zq=E(_1zo.b);if(!_1zq._){var _1zr=__Z;}else{var _1zs=E(_1zo.a),_1zt=new T(function(){var _1zu=B(_H4(44,_1zq.a,_1zq.b));return new T2(0,_1zu.a,_1zu.b);});if(E(_1zs)==44){var _1zv=B(_YQ(_S,new T(function(){return E(E(_1zt).a);}),new T(function(){return E(E(_1zt).b);})));}else{var _1zv=B(_YU(new T2(1,_1zs,new T(function(){return E(E(_1zt).a);})),new T(function(){return E(E(_1zt).b);})));}var _1zr=_1zv;}var _1zp=_1zr;}var _1zw=B(_6Q(_1zf,2));if(!_1zw._){var _1zx=E(_1sW);}else{var _1zy=_1zw.a,_1zz=E(_1zw.b);if(!_1zz._){var _1zA=B(_6d(_Z1,new T2(1,new T2(1,_1zy,_S),_S)));}else{var _1zB=E(_1zy),_1zC=new T(function(){var _1zD=B(_H4(44,_1zz.a,_1zz.b));return new T2(0,_1zD.a,_1zD.b);});if(E(_1zB)==44){var _1zE=B(_6d(_Z1,new T2(1,_S,new T2(1,new T(function(){return E(E(_1zC).a);}),new T(function(){return E(E(_1zC).b);})))));}else{var _1zE=B(_6d(_Z1,new T2(1,new T2(1,_1zB,new T(function(){return E(E(_1zC).a);})),new T(function(){return E(E(_1zC).b);}))));}var _1zA=_1zE;}var _1zx=_1zA;}return {_:0,a:E({_:0,a:E(B(_6Q(_1bL,_1zm))),b:E(B(_18L(_1zn.a,E(_1zn.b),new T(function(){return B(_6Q(_1cQ,_1zm));})))),c:B(_6Q(_1bY,_1zm)),d:32,e:_1zm,f:E(_1z1.f),g:_1z1.g,h:E(_1z1.h),i:E(_1z1.i),j:E(_1z1.j)}),b:E(_1zn),c:E(_1z0.c),d:E(_1z0.d),e:E(_1zp),f:E(_1zx),g:E(_1z0.g),h:E(_1z0.h),i:_1z0.i,j:_1z0.j,k:_1z0.k,l:_1z0.l,m:E(_1z0.m),n:_1z0.n,o:E(_1z0.o),p:E(_1z0.p),q:E(_1z0.q),r:_1z0.r,s:E(_1z0.s),t:E(_1z0.t)};}else{return E(_YZ);}}});}}else{return new F(function(){return _1yf(_);});}}else{return new F(function(){return _1yf(_);});}};switch(E(_1yc)){case 100:var _1zF=__app1(E(_1tP),toJSStr(E(_1sK)));return new F(function(){return _1yd(_,_1sm);});break;case 114:var _1zG=B(_Zb(_6v,toJSStr(E(_1sK)),_));return new F(function(){return _1yd(_,new T(function(){var _1zH=E(_1zG);if(!_1zH._){return E(_1sn);}else{return fromJSStr(B(_1hd(_1zH.a)));}}));});break;case 115:var _1zI=new T(function(){var _1zJ=new T(function(){var _1zK=new T(function(){var _1zL=B(_6d(_6A,_1we));if(!_1zL._){return __Z;}else{return B(_1sg(new T2(1,_1zL.a,new T(function(){return B(_1sY(_1sI,_1zL.b));}))));}}),_1zM=new T(function(){var _1zN=function(_1zO){var _1zP=E(_1zO);if(!_1zP._){return __Z;}else{var _1zQ=E(_1zP.a);return new T2(1,_1zQ.a,new T2(1,_1zQ.b,new T(function(){return B(_1zN(_1zP.b));})));}},_1zR=B(_1zN(_1wd));if(!_1zR._){return __Z;}else{return B(_1sg(new T2(1,_1zR.a,new T(function(){return B(_1sY(_1sI,_1zR.b));}))));}});return B(_1sY(_1sJ,new T2(1,_1zM,new T2(1,_1zK,_S))));});return B(_q(B(_1sg(new T2(1,new T(function(){return B(_A(0,_1w3,_S));}),_1zJ))),_1sU));}),_1zS=__app2(E(_1tS),toJSStr(E(_1sK)),B(_1hd(B(_1vQ(B(unAppCStr("\"",_1zI)))))));return new F(function(){return _1yd(_,_1so);});break;default:return new F(function(){return _1yd(_,_1sL);});}};if(!E(_1wR)){var _1zT=B(_1sb(_1vO,_1ui,_));return new F(function(){return _1xf(_);});}else{var _1zU=B(_1sb(_1vO,_1uh,_));return new F(function(){return _1xf(_);});}},_1zV=E(_1wf);if(!_1zV._){var _1zW=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1xd(_);});}else{var _1zX=new T(function(){var _1zY=E(_1zV.a),_1zZ=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1A0){return new F(function(){return _1tU(_1zY.a,_1A0);});},new T2(1,function(_1A1){return new F(function(){return _1tU(_1zY.b,_1A1);});},_S)),new T2(1,_y,new T(function(){return B(_1tX(_1zV.b));}))));});return new T2(1,_z,_1zZ);}),_1A2=B(_1sb(_1vO,new T2(1,_2u,_1zX),_));return new F(function(){return _1xd(_);});}},_1A3=E(_1we);if(!_1A3._){var _1A4=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1xc(_);});}else{var _1A5=new T(function(){return B(_A(0,E(_1A3.a),new T(function(){return B(_1u5(_1A3.b));})));}),_1A6=B(_1sb(_1vO,new T2(1,_2u,_1A5),_));return new F(function(){return _1xc(_);});}},_1A7=E(_1wd);if(!_1A7._){var _1A8=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1xb(_);});}else{var _1A9=new T(function(){var _1Aa=E(_1A7.a),_1Ab=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1Ac){return new F(function(){return _1tU(_1Aa.a,_1Ac);});},new T2(1,function(_1Ad){return new F(function(){return _1tU(_1Aa.b,_1Ad);});},_S)),new T2(1,_y,new T(function(){return B(_1u9(_1A7.b));}))));});return new T2(1,_z,_1Ab);}),_1Ae=B(_1sb(_1vO,new T2(1,_2u,_1A9),_));return new F(function(){return _1xb(_);});}},_1Af=E(_1wo);if(!_1Af._){return new F(function(){return _1wH(_,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1wD,_1wb,_1wc,_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA);});}else{var _1Ag=E(_1Af.b);if(!_1Ag._){return new F(function(){return _1wH(_,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1wD,_1wb,_1wc,_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA);});}else{var _1Ah=E(_1Ag.b);if(!_1Ah._){return new F(function(){return _1wH(_,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1wD,_1wb,_1wc,_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA);});}else{var _1Ai=_1Ah.a,_1Aj=E(_1Ah.b);if(!_1Aj._){return new F(function(){return _1wH(_,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1wD,_1wb,_1wc,_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA);});}else{if(!E(_1Aj.b)._){var _1Ak=B(_15k(B(_ms(_1Ai,0)),_1w5,new T(function(){var _1Al=B(_Gc(B(_sx(_Z0,_1Af.a))));if(!_1Al._){return E(_1tF);}else{if(!E(_1Al.b)._){if(E(_1Al.a)==2){return E(_1tJ);}else{return E(_1tF);}}else{return E(_1tF);}}}),_)),_1Am=E(_1Ak),_1An=_1Am.a,_1Ao=new T(function(){var _1Ap=new T(function(){return B(_6d(function(_1Aq){var _1Ar=B(_sk(_3L,_1Aq,B(_Go(_1sO,_1Ai))));return (_1Ar._==0)?E(_1sC):E(_1Ar.a);},B(_6d(_1uj,B(_1uB(B(_1tK(_1An,_1tG))))))));}),_1As=B(_RV(B(unAppCStr("e.==.m1:",_1Aj.a)),{_:0,a:E(_1vZ),b:E(_1w0),c:_1w1,d:_1w2,e:_1w3,f:E(B(_q(_1w4,new T2(1,new T2(0,new T2(0,_1Ag.a,_1sN),_1w3),new T2(1,new T2(0,new T2(0,_1Ap,_1sN),_1w3),_S))))),g:E(_1Am.b),h:E(_1w6),i:E(_1w7),j:E(_1w8)},_1wD,_1wb,B(_q(_1wc,new T(function(){return B(_1s1(_1An,_1Ai));},1))),_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA)),_1At=B(_1ho(_1Ai,_1As.a,_1As.b,_1As.c,_1As.d,_1As.e,_1As.f,_1As.g,_1As.h,_1As.i,_1As.j,_1As.k,_1As.l,_1As.m,_1As.n,_1As.o,_1As.p,_1As.q,_1As.r,_1As.s,_1As.t));return {_:0,a:E(_1At.a),b:E(_1At.b),c:E(_1At.c),d:E(_1At.d),e:E(_1At.e),f:E(_1At.f),g:E(_1At.g),h:E(_1At.h),i:_1At.i,j:_1At.j,k:_1At.k,l:_1At.l,m:E(_1At.m),n:_1At.n,o:E(_1At.o),p:E(_1At.p),q:E(_1At.q),r:_1At.r,s:E(_1At.s),t:E(_1At.t)};}),_1Au=function(_){var _1Av=function(_){var _1Aw=function(_){var _1Ax=new T(function(){var _1Ay=E(E(_1Ao).a);return new T5(0,_1Ay,_1Ay.a,_1Ay.g,_1Ay.h,_1Ay.j);}),_1Az=B(_1sb(_1vO,new T2(1,_6C,new T(function(){return B(_8j(E(_1Ax).d,_1sX));})),_)),_1AA=E(_1Ax),_1AB=function(_){var _1AC=B(_1sb(_1vO,B(_A(0,_1wl,_S)),_)),_1AD=B(_13Z(_1sB,_1AA.c,_)),_1AE=E(_1AD).b,_1AF=E(_1vU),_1AG=_1AF.a,_1AH=_1AF.b,_1AI=new T(function(){return B(_1i9(E(_1vY)));}),_1AJ=new T(function(){var _1AK=E(_1Ao),_1AL=_1AK.b,_1AM=_1AK.c,_1AN=_1AK.d,_1AO=_1AK.e,_1AP=_1AK.f,_1AQ=_1AK.g,_1AR=_1AK.h,_1AS=_1AK.i,_1AT=_1AK.j,_1AU=_1AK.k,_1AV=_1AK.l,_1AW=_1AK.m,_1AX=_1AK.n,_1AY=_1AK.o,_1AZ=_1AK.p,_1B0=_1AK.q,_1B1=_1AK.r,_1B2=_1AK.s,_1B3=_1AK.t,_1B4=E(_1AI),_1B5=E(_1AA.b),_1B6=_1B5.a,_1B7=_1B5.b,_1B8=function(_1B9,_1Ba,_1Bb,_1Bc,_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi){var _1Bj=E(_1B9);if(E(_1B4)==32){var _1Bk=B(_1rm(_1Bj.a,E(_1Bj.b),_1Ba,_1Bb,_1Bc,_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi)),_1Bl=_1Bk.h,_1Bm=B(_1f2(_1sM,_1Bl,_1AO,{_:0,a:E(_1Bk.a),b:E(_1Bk.b),c:_1Bk.c,d:_1Bk.d,e:_1Bk.e,f:E(_1Bk.f),g:E(_1AE),h:E(_1Bl),i:E(_1Bk.i),j:E(_1Bk.j)},_1AL,_1AM,_1AN,_1AO,_1AP,_1AQ,_1AR,_1AS,_1AT,_1AU,_1AV,_1AW,_1AX,_1AY,_1AZ,_1B0,_1B1,_1B2,_1B3));return {_:0,a:E(_1Bm.a),b:E(_1Bm.b),c:E(_1Bm.c),d:E(_1Bm.d),e:E(_1Bm.e),f:E(_1Bm.f),g:E(_1Bm.g),h:E(_1Bm.h),i:_1Bm.i,j:_1Bm.j,k:_1Bm.k,l:_1Bm.l,m:E(_1Bm.m),n:_1Bm.n,o:E(_1Bm.o),p:E(_1Bm.p),q:E(_1Bm.q),r:_1Bm.r,s:E(_1Bm.s),t:E(_1Bm.t)};}else{var _1Bn=B(_1f2(_1sM,_1Bg,_1AO,{_:0,a:E(_1Bj),b:E(_1Ba),c:_1Bb,d:_1Bc,e:_1Bd,f:E(_1Be),g:E(_1AE),h:E(_1Bg),i:E(_1Bh),j:E(_1Bi)},_1AL,_1AM,_1AN,_1AO,_1AP,_1AQ,_1AR,_1AS,_1AT,_1AU,_1AV,_1AW,_1AX,_1AY,_1AZ,_1B0,_1B1,_1B2,_1B3));return {_:0,a:E(_1Bn.a),b:E(_1Bn.b),c:E(_1Bn.c),d:E(_1Bn.d),e:E(_1Bn.e),f:E(_1Bn.f),g:E(_1Bn.g),h:E(_1Bn.h),i:_1Bn.i,j:_1Bn.j,k:_1Bn.k,l:_1Bn.l,m:E(_1Bn.m),n:_1Bn.n,o:E(_1Bn.o),p:E(_1Bn.p),q:E(_1Bn.q),r:_1Bn.r,s:E(_1Bn.s),t:E(_1Bn.t)};}},_1Bo=function(_1Bp,_1Bq){var _1Br=E(_1AA.a),_1Bs=E(_1Br.a);return new F(function(){return _1o2(_1Bp,_1Bq,_1Bs.a,_1Bs.b,_1Br.b,_1Br.c,_1Br.d,_1Br.e,_1Br.f,_1Br.g,_1Br.h,_1Br.i,_1Br.j);});};switch(E(_1B4)){case 72:var _1Bt=E(_1B7);if(0<=(_1Bt-1|0)){var _1Bu=B(_1Bo(E(_1B6),_1Bt-1|0));return B(_1B8(_1Bu.a,_1Bu.b,_1Bu.c,_1Bu.d,_1Bu.e,_1Bu.f,_1Bu.g,_1Bu.h,_1Bu.i,_1Bu.j));}else{var _1Bv=B(_1Bo(E(_1B6),_1Bt));return B(_1B8(_1Bv.a,_1Bv.b,_1Bv.c,_1Bv.d,_1Bv.e,_1Bv.f,_1Bv.g,_1Bv.h,_1Bv.i,_1Bv.j));}break;case 75:var _1Bw=E(_1B6);if(0<=(_1Bw-1|0)){var _1Bx=B(_1Bo(_1Bw-1|0,E(_1B7)));return B(_1B8(_1Bx.a,_1Bx.b,_1Bx.c,_1Bx.d,_1Bx.e,_1Bx.f,_1Bx.g,_1Bx.h,_1Bx.i,_1Bx.j));}else{var _1By=B(_1Bo(_1Bw,E(_1B7)));return B(_1B8(_1By.a,_1By.b,_1By.c,_1By.d,_1By.e,_1By.f,_1By.g,_1By.h,_1By.i,_1By.j));}break;case 77:var _1Bz=E(_1B6);if(E(_1w9)!=(_1Bz+1|0)){var _1BA=B(_1Bo(_1Bz+1|0,E(_1B7)));return B(_1B8(_1BA.a,_1BA.b,_1BA.c,_1BA.d,_1BA.e,_1BA.f,_1BA.g,_1BA.h,_1BA.i,_1BA.j));}else{var _1BB=B(_1Bo(_1Bz,E(_1B7)));return B(_1B8(_1BB.a,_1BB.b,_1BB.c,_1BB.d,_1BB.e,_1BB.f,_1BB.g,_1BB.h,_1BB.i,_1BB.j));}break;case 80:var _1BC=E(_1B7);if(E(_1wa)!=(_1BC+1|0)){var _1BD=B(_1Bo(E(_1B6),_1BC+1|0));return B(_1B8(_1BD.a,_1BD.b,_1BD.c,_1BD.d,_1BD.e,_1BD.f,_1BD.g,_1BD.h,_1BD.i,_1BD.j));}else{var _1BE=B(_1Bo(E(_1B6),_1BC));return B(_1B8(_1BE.a,_1BE.b,_1BE.c,_1BE.d,_1BE.e,_1BE.f,_1BE.g,_1BE.h,_1BE.i,_1BE.j));}break;case 104:var _1BF=E(_1B6);if(0<=(_1BF-1|0)){var _1BG=B(_1Bo(_1BF-1|0,E(_1B7)));return B(_1B8(_1BG.a,_1BG.b,_1BG.c,_1BG.d,_1BG.e,_1BG.f,_1BG.g,_1BG.h,_1BG.i,_1BG.j));}else{var _1BH=B(_1Bo(_1BF,E(_1B7)));return B(_1B8(_1BH.a,_1BH.b,_1BH.c,_1BH.d,_1BH.e,_1BH.f,_1BH.g,_1BH.h,_1BH.i,_1BH.j));}break;case 106:var _1BI=E(_1B7);if(E(_1wa)!=(_1BI+1|0)){var _1BJ=B(_1Bo(E(_1B6),_1BI+1|0));return B(_1B8(_1BJ.a,_1BJ.b,_1BJ.c,_1BJ.d,_1BJ.e,_1BJ.f,_1BJ.g,_1BJ.h,_1BJ.i,_1BJ.j));}else{var _1BK=B(_1Bo(E(_1B6),_1BI));return B(_1B8(_1BK.a,_1BK.b,_1BK.c,_1BK.d,_1BK.e,_1BK.f,_1BK.g,_1BK.h,_1BK.i,_1BK.j));}break;case 107:var _1BL=E(_1B7);if(0<=(_1BL-1|0)){var _1BM=B(_1Bo(E(_1B6),_1BL-1|0));return B(_1B8(_1BM.a,_1BM.b,_1BM.c,_1BM.d,_1BM.e,_1BM.f,_1BM.g,_1BM.h,_1BM.i,_1BM.j));}else{var _1BN=B(_1Bo(E(_1B6),_1BL));return B(_1B8(_1BN.a,_1BN.b,_1BN.c,_1BN.d,_1BN.e,_1BN.f,_1BN.g,_1BN.h,_1BN.i,_1BN.j));}break;case 108:var _1BO=E(_1B6);if(E(_1w9)!=(_1BO+1|0)){var _1BP=B(_1Bo(_1BO+1|0,E(_1B7)));return B(_1B8(_1BP.a,_1BP.b,_1BP.c,_1BP.d,_1BP.e,_1BP.f,_1BP.g,_1BP.h,_1BP.i,_1BP.j));}else{var _1BQ=B(_1Bo(_1BO,E(_1B7)));return B(_1B8(_1BQ.a,_1BQ.b,_1BQ.c,_1BQ.d,_1BQ.e,_1BQ.f,_1BQ.g,_1BQ.h,_1BQ.i,_1BQ.j));}break;default:var _1BR=B(_1Bo(E(_1B6),E(_1B7)));return B(_1B8(_1BR.a,_1BR.b,_1BR.c,_1BR.d,_1BR.e,_1BR.f,_1BR.g,_1BR.h,_1BR.i,_1BR.j));}}),_1BS=B(_16q(_1AG,_1AH,_1vV,_1vW,_1vX,_1AJ,_)),_1BT=_1BS,_1BU=E(_1AI),_1BV=function(_,_1BW){var _1BX=function(_1BY){var _1BZ=B(_1sb(_1vO,B(_8p(_1BW)),_)),_1C0=E(_1BT),_1C1=_1C0.d,_1C2=_1C0.e,_1C3=_1C0.f,_1C4=_1C0.g,_1C5=_1C0.i,_1C6=_1C0.j,_1C7=_1C0.k,_1C8=_1C0.l,_1C9=_1C0.m,_1Ca=_1C0.n,_1Cb=_1C0.o,_1Cc=_1C0.p,_1Cd=_1C0.q,_1Ce=_1C0.r,_1Cf=_1C0.t,_1Cg=E(_1C0.s),_1Ch=_1Cg.a,_1Ci=_1Cg.d,_1Cj=_1Cg.e,_1Ck=_1Cg.f,_1Cl=_1Cg.g,_1Cm=_1Cg.h,_1Cn=E(_1C0.a),_1Co=_1Cn.e,_1Cp=_1Cn.f,_1Cq=_1Cn.g,_1Cr=E(_1C0.h),_1Cs=function(_1Ct){var _1Cu=function(_1Cv){if(_1Cv!=E(_1sG)){var _1Cw=B(_6Q(_1bC,_1Cv)),_1Cx=_1Cw.a,_1Cy=E(_1Cw.b),_1Cz=B(_18L(_1Cx,_1Cy,new T(function(){return B(_6Q(_1cQ,_1Cv));})));return new F(function(){return _1vT(_1AF,_1vV,_1vW,_1vX,_1sF,B(_6Q(_1bL,_1Cv)),_1Cz,B(_6Q(_1bY,_1Cv)),32,_1Cv,_1Cp,_1Cq,B(_q(_1Cn.h,new T2(1,_1sE,new T(function(){return B(_A(0,_1Co,_S));})))),B(_1rK(_1sD,_1Cz)),_ws,_1Cx,_1Cy,_S,_1C1,_1C2,_1C3,_1C4,_1Cr.a,_1Cr.b,_1C5,_1C6,_1C7, -1,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_ws,_ws,_ws,_1Ci,_1Cj,_1Ck,_1Cl,_1Cm,_1Cf,_);});}else{var _1CA=__app1(E(_nh),_1AH),_1CB=B(A2(_ni,_1AG,_)),_1CC=B(A(_mN,[_1AG,_j2,_1su,_1sB,_1sA,_])),_1CD=B(A(_mN,[_1AG,_j2,_1sx,_1sz,_1sy,_])),_1CE=B(A(_mN,[_1AG,_j2,_1sx,_1sw,_1sv,_])),_1CF=B(A(_mN,[_1AG,_j2,_1su,_1st,_1ss,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1bH),b:E(_1sr),c:E(_1sp),d:32,e:0,f:E(_1Cp),g:_1Cq,h:E(_S),i:E(_1Cn.i),j:E(_ws)}),b:E(_1bz),c:E(_1C0.c),d:E(_1C1),e:E(_1C2),f:E(_1C3),g:E(_1C4),h:E(_1Cr),i:_1C5,j:_1C6,k:_1C7,l:_1C8,m:E(_1C9),n:_1Ca,o:E(_1Cb),p:E(_1Cc),q:E(_1Cd),r:_1Ce,s:E({_:0,a:E(_1Ch),b:E(_ws),c:E(_ws),d:E(_1Ci),e:E(_1Cj),f:E(_1Ck),g:E(_1Cl),h:E(_1Cm)}),t:E(_1Cf)};});}};if(_1C8>=0){return new F(function(){return _1Cu(_1C8);});}else{return new F(function(){return _1Cu(_1Co+1|0);});}};if(!E(_1Ch)){if(E(_1BU)==110){return new F(function(){return _1Cs(_);});}else{return _1C0;}}else{return new F(function(){return _1Cs(_);});}};if(E(_1BU)==114){if(!B(_68(_1BW,_1sH))){var _1CG=E(_1BW);if(!_1CG._){return _1BT;}else{var _1CH=_1CG.b;return new T(function(){var _1CI=E(_1BT),_1CJ=E(_1CI.a),_1CK=E(_1CG.a),_1CL=E(_1CK);if(_1CL==34){var _1CM=B(_Rx(_1CK,_1CH));if(!_1CM._){var _1CN=E(_1tR);}else{var _1CO=E(_1CM.b);if(!_1CO._){var _1CP=E(_1sV);}else{var _1CQ=_1CO.a,_1CR=E(_1CO.b);if(!_1CR._){var _1CS=new T2(1,new T2(1,_1CQ,_S),_S);}else{var _1CT=E(_1CQ),_1CU=new T(function(){var _1CV=B(_H4(126,_1CR.a,_1CR.b));return new T2(0,_1CV.a,_1CV.b);});if(E(_1CT)==126){var _1CW=new T2(1,_S,new T2(1,new T(function(){return E(E(_1CU).a);}),new T(function(){return E(E(_1CU).b);})));}else{var _1CW=new T2(1,new T2(1,_1CT,new T(function(){return E(E(_1CU).a);})),new T(function(){return E(E(_1CU).b);}));}var _1CS=_1CW;}var _1CP=_1CS;}var _1CN=_1CP;}var _1CX=_1CN;}else{var _1CY=E(_1CH);if(!_1CY._){var _1CZ=new T2(1,new T2(1,_1CK,_S),_S);}else{var _1D0=new T(function(){var _1D1=B(_H4(126,_1CY.a,_1CY.b));return new T2(0,_1D1.a,_1D1.b);});if(E(_1CL)==126){var _1D2=new T2(1,_S,new T2(1,new T(function(){return E(E(_1D0).a);}),new T(function(){return E(E(_1D0).b);})));}else{var _1D2=new T2(1,new T2(1,_1CK,new T(function(){return E(E(_1D0).a);})),new T(function(){return E(E(_1D0).b);}));}var _1CZ=_1D2;}var _1CX=_1CZ;}var _1D3=B(_Gc(B(_sx(_Z0,new T(function(){return B(_Jd(_1CX));})))));if(!_1D3._){return E(_YY);}else{if(!E(_1D3.b)._){var _1D4=E(_1D3.a),_1D5=B(_6Q(_1bC,_1D4)),_1D6=B(_6Q(_1CX,1));if(!_1D6._){var _1D7=__Z;}else{var _1D8=E(_1D6.b);if(!_1D8._){var _1D9=__Z;}else{var _1Da=E(_1D6.a),_1Db=new T(function(){var _1Dc=B(_H4(44,_1D8.a,_1D8.b));return new T2(0,_1Dc.a,_1Dc.b);});if(E(_1Da)==44){var _1Dd=B(_YQ(_S,new T(function(){return E(E(_1Db).a);}),new T(function(){return E(E(_1Db).b);})));}else{var _1Dd=B(_YU(new T2(1,_1Da,new T(function(){return E(E(_1Db).a);})),new T(function(){return E(E(_1Db).b);})));}var _1D9=_1Dd;}var _1D7=_1D9;}var _1De=B(_6Q(_1CX,2));if(!_1De._){var _1Df=E(_1sW);}else{var _1Dg=_1De.a,_1Dh=E(_1De.b);if(!_1Dh._){var _1Di=B(_6d(_Z1,new T2(1,new T2(1,_1Dg,_S),_S)));}else{var _1Dj=E(_1Dg),_1Dk=new T(function(){var _1Dl=B(_H4(44,_1Dh.a,_1Dh.b));return new T2(0,_1Dl.a,_1Dl.b);});if(E(_1Dj)==44){var _1Dm=B(_6d(_Z1,new T2(1,_S,new T2(1,new T(function(){return E(E(_1Dk).a);}),new T(function(){return E(E(_1Dk).b);})))));}else{var _1Dm=B(_6d(_Z1,new T2(1,new T2(1,_1Dj,new T(function(){return E(E(_1Dk).a);})),new T(function(){return E(E(_1Dk).b);}))));}var _1Di=_1Dm;}var _1Df=_1Di;}return {_:0,a:E({_:0,a:E(B(_6Q(_1bL,_1D4))),b:E(B(_18L(_1D5.a,E(_1D5.b),new T(function(){return B(_6Q(_1cQ,_1D4));})))),c:B(_6Q(_1bY,_1D4)),d:32,e:_1D4,f:E(_1CJ.f),g:_1CJ.g,h:E(_1CJ.h),i:E(_1CJ.i),j:E(_1CJ.j)}),b:E(_1D5),c:E(_1CI.c),d:E(_1CI.d),e:E(_1D7),f:E(_1Df),g:E(_1CI.g),h:E(_1CI.h),i:_1CI.i,j:_1CI.j,k:_1CI.k,l:_1CI.l,m:E(_1CI.m),n:_1CI.n,o:E(_1CI.o),p:E(_1CI.p),q:E(_1CI.q),r:_1CI.r,s:E(_1CI.s),t:E(_1CI.t)};}else{return E(_YZ);}}});}}else{return new F(function(){return _1BX(_);});}}else{return new F(function(){return _1BX(_);});}};switch(E(_1BU)){case 100:var _1Dn=__app1(E(_1tP),toJSStr(E(_1sK)));return new F(function(){return _1BV(_,_1sm);});break;case 114:var _1Do=B(_Zb(_6v,toJSStr(E(_1sK)),_));return new F(function(){return _1BV(_,new T(function(){var _1Dp=E(_1Do);if(!_1Dp._){return E(_1sn);}else{return fromJSStr(B(_1hd(_1Dp.a)));}}));});break;case 115:var _1Dq=new T(function(){var _1Dr=new T(function(){var _1Ds=new T(function(){var _1Dt=B(_6d(_6A,_1we));if(!_1Dt._){return __Z;}else{return B(_1sg(new T2(1,_1Dt.a,new T(function(){return B(_1sY(_1sI,_1Dt.b));}))));}}),_1Du=new T(function(){var _1Dv=function(_1Dw){var _1Dx=E(_1Dw);if(!_1Dx._){return __Z;}else{var _1Dy=E(_1Dx.a);return new T2(1,_1Dy.a,new T2(1,_1Dy.b,new T(function(){return B(_1Dv(_1Dx.b));})));}},_1Dz=B(_1Dv(_1wd));if(!_1Dz._){return __Z;}else{return B(_1sg(new T2(1,_1Dz.a,new T(function(){return B(_1sY(_1sI,_1Dz.b));}))));}});return B(_1sY(_1sJ,new T2(1,_1Du,new T2(1,_1Ds,_S))));});return B(_q(B(_1sg(new T2(1,new T(function(){return B(_A(0,_1w3,_S));}),_1Dr))),_1sU));}),_1DA=__app2(E(_1tS),toJSStr(E(_1sK)),B(_1hd(B(_1vQ(B(unAppCStr("\"",_1Dq)))))));return new F(function(){return _1BV(_,_1so);});break;default:return new F(function(){return _1BV(_,_1sL);});}};if(!E(_1AA.e)){var _1DB=B(_1sb(_1vO,_1ui,_));return new F(function(){return _1AB(_);});}else{var _1DC=B(_1sb(_1vO,_1uh,_));return new F(function(){return _1AB(_);});}},_1DD=E(_1wf);if(!_1DD._){var _1DE=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1Aw(_);});}else{var _1DF=new T(function(){var _1DG=E(_1DD.a),_1DH=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1DI){return new F(function(){return _1tU(_1DG.a,_1DI);});},new T2(1,function(_1DJ){return new F(function(){return _1tU(_1DG.b,_1DJ);});},_S)),new T2(1,_y,new T(function(){return B(_1tX(_1DD.b));}))));});return new T2(1,_z,_1DH);}),_1DK=B(_1sb(_1vO,new T2(1,_2u,_1DF),_));return new F(function(){return _1Aw(_);});}},_1DL=E(_1we);if(!_1DL._){var _1DM=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1Av(_);});}else{var _1DN=new T(function(){return B(_A(0,E(_1DL.a),new T(function(){return B(_1u5(_1DL.b));})));}),_1DO=B(_1sb(_1vO,new T2(1,_2u,_1DN),_));return new F(function(){return _1Av(_);});}},_1DP=E(_1wd);if(!_1DP._){var _1DQ=B(_1sb(_1vO,_1sT,_));return new F(function(){return _1Au(_);});}else{var _1DR=new T(function(){var _1DS=E(_1DP.a),_1DT=new T(function(){return B(A3(_sc,_6w,new T2(1,function(_1DU){return new F(function(){return _1tU(_1DS.a,_1DU);});},new T2(1,function(_1DV){return new F(function(){return _1tU(_1DS.b,_1DV);});},_S)),new T2(1,_y,new T(function(){return B(_1u9(_1DP.b));}))));});return new T2(1,_z,_1DT);}),_1DW=B(_1sb(_1vO,new T2(1,_2u,_1DR),_));return new F(function(){return _1Au(_);});}}else{return new F(function(){return _1wH(_,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1wD,_1wb,_1wc,_1wd,_1we,_1wf,_1wC,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_S,_1wp,_1wq,_1wr,_1wB,_1wA);});}}}}}}}else{if(!E(_1wy)){return {_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E({_:0,a:E(_1ws),b:E(_1wt),c:E(_1wu),d:E(_ws),e:E(_1ww),f:E(_ws),g:E(_ws),h:E(_1wz)}),t:E(_1wA)};}else{var _1DX=B(_1sb(_1vO,_1sS,_)),_1DY=new T(function(){var _1DZ=B(_1hh(_1wm));return new T2(0,_1DZ.a,_1DZ.b);}),_1E0=new T(function(){return E(E(_1DY).a);}),_1E1=function(_1E2,_1E3){var _1E4=E(_1E2);switch(_1E4){case  -2:return {_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)};case  -1:var _1E5=E(_1vU),_1E6=B(_nP(_1E5.a,_1E5.b,new T(function(){var _1E7=E(_1vV)/16,_1E8=_1E7&4294967295;if(_1E7>=_1E8){return _1E8-2|0;}else{return (_1E8-1|0)-2|0;}}),{_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)},_));return new T(function(){return {_:0,a:E(_1wE),b:E(_1wD),c:E(B(_1bc(_S,new T(function(){return B(_6Q(E(_1DY).b,_1wn));})))),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E({_:0,a:E(_1ws),b:E(_1wt),c:E(_wt),d:E(_ws),e:E(_1ww),f:E(_ws),g:E(_ws),h:E(_1wz)}),t:E(_1wA)};});default:var _1E9=E(_1vU),_1Ea=B(_nP(_1E9.a,_1E9.b,new T(function(){var _1Eb=E(_1vV)/16,_1Ec=_1Eb&4294967295;if(_1Eb>=_1Ec){return _1Ec-2|0;}else{return (_1Ec-1|0)-2|0;}}),{_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)},_)),_1Ed=new T(function(){if(!E(_1wz)){return E(_1su);}else{return 2+(E(_1wa)+3|0)|0;}}),_1Ee=B(_j9(_1E9,_1vW,0,_1Ed,new T(function(){var _1Ef=E(_1vV)/28,_1Eg=_1Ef&4294967295;if(_1Ef>=_1Eg){return (_1Eg-1|0)+_1wk|0;}else{return ((_1Eg-1|0)-1|0)+_1wk|0;}}),_1Ed,B(_UG(_1wb,_1E0,_1E3)),_));return {_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1E4,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)};}};switch(E(B(_1i9(E(_1vY))))){case 32:return new F(function(){return _1E1( -1,_1sk);});break;case 72:var _1Eh=E(_1wn);if(!_1Eh){var _1Ei=B(_ms(_1E0,0))-1|0;return new F(function(){return _1E1(_1Ei,_1Ei);});}else{var _1Ej=_1Eh-1|0;return new F(function(){return _1E1(_1Ej,_1Ej);});}break;case 75:if(_1wn!=(B(_ms(_1E0,0))-1|0)){var _1Ek=_1wn+1|0;return new F(function(){return _1E1(_1Ek,_1Ek);});}else{return new F(function(){return _1E1(0,_1sj);});}break;case 77:var _1El=E(_1wn);if(!_1El){var _1Em=B(_ms(_1E0,0))-1|0;return new F(function(){return _1E1(_1Em,_1Em);});}else{var _1En=_1El-1|0;return new F(function(){return _1E1(_1En,_1En);});}break;case 80:if(_1wn!=(B(_ms(_1E0,0))-1|0)){var _1Eo=_1wn+1|0;return new F(function(){return _1E1(_1Eo,_1Eo);});}else{return new F(function(){return _1E1(0,_1sj);});}break;case 104:if(_1wn!=(B(_ms(_1E0,0))-1|0)){var _1Ep=_1wn+1|0;return new F(function(){return _1E1(_1Ep,_1Ep);});}else{return new F(function(){return _1E1(0,_1sj);});}break;case 106:if(_1wn!=(B(_ms(_1E0,0))-1|0)){var _1Eq=_1wn+1|0;return new F(function(){return _1E1(_1Eq,_1Eq);});}else{return new F(function(){return _1E1(0,_1sj);});}break;case 107:var _1Er=E(_1wn);if(!_1Er){var _1Es=B(_ms(_1E0,0))-1|0;return new F(function(){return _1E1(_1Es,_1Es);});}else{var _1Et=_1Er-1|0;return new F(function(){return _1E1(_1Et,_1Et);});}break;case 108:var _1Eu=E(_1wn);if(!_1Eu){var _1Ev=B(_ms(_1E0,0))-1|0;return new F(function(){return _1E1(_1Ev,_1Ev);});}else{var _1Ew=_1Eu-1|0;return new F(function(){return _1E1(_1Ew,_1Ew);});}break;default:return new F(function(){return _1E1( -2,_1sl);});}}}};if(!E(_1wu)){return new F(function(){return _1wF(_);});}else{if(!E(_1wv)){return new F(function(){return _XF(_1vU,_1vV,_1vW,_1vZ,_1w0,_1w1,_1w2,_1w3,_1w4,_1w5,_1w6,_1w7,_1w8,_1w9,_1wa,_1wb,_1wc,_1wd,_1we,_1wf,_1wg,_1wh,_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_1wo,_1wp,_1wq,_1wr,_1ws,_1wt,_ws,_1ww,_wt,_1wy,_1wz,_1wA,_);});}else{return new F(function(){return _1wF(_);});}}}else{return {_:0,a:E(_1wE),b:E(_1wD),c:E(_1wb),d:E(_1wc),e:E(_1wd),f:E(_1we),g:E(_1wf),h:E(_1wC),i:_1wi,j:_1wj,k:_1wk,l:_1wl,m:E(_1wm),n:_1wn,o:E(_1wo),p:E(_1wp),q:E(_1wq),r:_1wr,s:E(_1wB),t:E(_1wA)};}},_1Ex=function(_1Ey,_1Ez,_1EA,_1EB,_1EC,_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL,_1EM,_1EN,_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_1F1,_1F2,_1F3,_1F4,_1F5,_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd,_1Fe,_){if(!E(_1Fd)){var _1Ff=function(_1Fg){return new F(function(){return _Vl(_1Ey,_1Ez,_1EA,_1EC,_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL,_1EM,_1EN,_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_1F1,_1F2,new T2(0,_1F3,_1F4),_1Fg,_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_ws,_1Fe,_);});};if(_1F5<=254){return new F(function(){return _1Ff(_1F5+1|0);});}else{return new F(function(){return _1Ff(0);});}}else{var _1Fh=function(_1Fi){if(!B(_an(_1Fi,8))){if(!E(_1F8)){var _1Fj=E(_1Ey);return new F(function(){return _16q(_1Fj.a,_1Fj.b,_1Ez,_1EA,_1EB,{_:0,a:E({_:0,a:E(_1EC),b:E(_1ED),c:_1EE,d:_1EF,e:_1EG,f:E(_1EH),g:_1EI,h:E(_1EJ),i:E(_1EK),j:E(_1EL)}),b:E(new T2(0,_1EM,_1EN)),c:E(_1EO),d:E(_1EP),e:E(_1EQ),f:E(_1ER),g:E(_1ES),h:E(new T2(0,_1ET,_1EU)),i:_1EV,j:_1EW,k:_1EX,l:_1EY,m:E(_1EZ),n:_1F0,o:E(_1F1),p:E(_1F2),q:E(new T2(0,_1F3,_1F4)),r:_1Fi,s:E({_:0,a:E(_1F6),b:E(_1F7),c:E(_ws),d:E(_1F9),e:E(_1Fa),f:E(_1Fb),g:E(_1Fc),h:E(_wt)}),t:E(_1Fe)},_);});}else{return new F(function(){return _Vl(_1Ey,_1Ez,_1EA,_1EC,_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL,_1EM,_1EN,_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_1F1,_1F2,new T2(0,_1F3,_1F4),_1Fi,_1F6,_1F7,_wt,_1F9,_1Fa,_1Fb,_1Fc,_wt,_1Fe,_);});}}else{return new F(function(){return _Vl(_1Ey,_1Ez,_1EA,_1EC,_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL,_1EM,_1EN,_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_1F1,_1F2,new T2(0,_1F3,_1F4),_1Fi,_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_wt,_1Fe,_);});}};if(_1F5<=254){return new F(function(){return _1Fh(_1F5+1|0);});}else{return new F(function(){return _1Fh(0);});}}},_1Fk=function(_1Fl,_1Fm,_1Fn){var _1Fo=E(_1Fn);if(!_1Fo._){return 0;}else{var _1Fp=_1Fo.b,_1Fq=E(_1Fo.a),_1Fr=_1Fq.a,_1Fs=_1Fq.b;return (_1Fl<=_1Fr)?1+B(_1Fk(_1Fl,_1Fm,_1Fp))|0:(_1Fl>=_1Fr+_1Fq.c)?1+B(_1Fk(_1Fl,_1Fm,_1Fp))|0:(_1Fm<=_1Fs)?1+B(_1Fk(_1Fl,_1Fm,_1Fp))|0:(_1Fm>=_1Fs+_1Fq.d)?1+B(_1Fk(_1Fl,_1Fm,_1Fp))|0:1;}},_1Ft=function(_1Fu,_1Fv,_1Fw){var _1Fx=E(_1Fw);if(!_1Fx._){return 0;}else{var _1Fy=_1Fx.b,_1Fz=E(_1Fx.a),_1FA=_1Fz.a,_1FB=_1Fz.b;if(_1Fu<=_1FA){return 1+B(_1Ft(_1Fu,_1Fv,_1Fy))|0;}else{if(_1Fu>=_1FA+_1Fz.c){return 1+B(_1Ft(_1Fu,_1Fv,_1Fy))|0;}else{var _1FC=E(_1Fv);return (_1FC<=_1FB)?1+B(_1Fk(_1Fu,_1FC,_1Fy))|0:(_1FC>=_1FB+_1Fz.d)?1+B(_1Fk(_1Fu,_1FC,_1Fy))|0:1;}}}},_1FD=function(_1FE,_1FF,_1FG){var _1FH=E(_1FG);if(!_1FH._){return 0;}else{var _1FI=_1FH.b,_1FJ=E(_1FH.a),_1FK=_1FJ.a,_1FL=_1FJ.b,_1FM=E(_1FE);if(_1FM<=_1FK){return 1+B(_1Ft(_1FM,_1FF,_1FI))|0;}else{if(_1FM>=_1FK+_1FJ.c){return 1+B(_1Ft(_1FM,_1FF,_1FI))|0;}else{var _1FN=E(_1FF);return (_1FN<=_1FL)?1+B(_1Fk(_1FM,_1FN,_1FI))|0:(_1FN>=_1FL+_1FJ.d)?1+B(_1Fk(_1FM,_1FN,_1FI))|0:1;}}}},_1FO=function(_1FP,_1FQ){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1FQ)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1FQ)-100,E(_1FP),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1FP),100);}),new T2(1,new T(function(){return new T4(0,E(_1FP)-100,100,100,E(_1FQ)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1FP)-200,E(_1FQ)-200);}),_S)))));},_1FR=32,_1FS=76,_1FT=75,_1FU=74,_1FV=72,_1FW=64,_1FX=function(_1FY,_1FZ,_1G0,_1G1,_1G2){var _1G3=new T(function(){var _1G4=E(_1FZ),_1G5=E(_1G4.a),_1G6=_1G5.a,_1G7=_1G5.b,_1G8=B(_1FO(_1G6,_1G7)),_1G9=new T(function(){var _1Ga=E(_1G4.b);return new T2(0,new T(function(){return B(_g7(_1G6,_1Ga.a));}),new T(function(){return B(_g7(_1G7,_1Ga.b));}));});switch(B(_1FD(new T(function(){return E(_1G1)*E(E(_1G9).a);},1),new T(function(){return E(_1G2)*E(E(_1G9).b);},1),new T2(1,_1G8.a,_1G8.b)))){case 1:return E(_1FV);break;case 2:return E(_1FU);break;case 3:return E(_1FT);break;case 4:return E(_1FS);break;case 5:return E(_1FR);break;default:return E(_1FW);}});return function(_1Gb,_){var _1Gc=E(E(_1FZ).a),_1Gd=E(_1Gb),_1Ge=E(_1Gd.a),_1Gf=E(_1Gd.b),_1Gg=E(_1Gd.h),_1Gh=E(_1Gd.s);return new F(function(){return _1vT(_1FY,_1Gc.a,_1Gc.b,_1G0,_1G3,_1Ge.a,_1Ge.b,_1Ge.c,_1Ge.d,_1Ge.e,_1Ge.f,_1Ge.g,_1Ge.h,_1Ge.i,_1Ge.j,_1Gf.a,_1Gf.b,_1Gd.c,_1Gd.d,_1Gd.e,_1Gd.f,_1Gd.g,_1Gg.a,_1Gg.b,_1Gd.i,_1Gd.j,_1Gd.k,_1Gd.l,_1Gd.m,_1Gd.n,_1Gd.o,_1Gd.p,_1Gd.q,_1Gd.r,_1Gh.a,_1Gh.b,_1Gh.c,_1Gh.d,_1Gh.e,_1Gh.f,_1Gh.g,_1Gh.h,_1Gd.t,_);});};},_1Gi=0,_1Gj=2,_1Gk=2,_1Gl=0,_1Gm=new T(function(){return eval("document");}),_1Gn=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Go=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1Gp=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1Gq=function(_1Gr){return E(E(_1Gr).b);},_1Gs=function(_1Gt,_1Gu){return new F(function(){return A2(_1Gq,_1Gt,function(_){var _1Gv=E(_1Gu),_1Gw=__app1(E(_1Gp),_1Gv);if(!_1Gw){return _2N;}else{var _1Gx=__app1(E(_1Go),_1Gv);return new T1(1,new T2(0,_1Gx,_1Gv));}});});},_1Gy=new T(function(){var _1Gz=E(_1bY);if(!_1Gz._){return E(_ng);}else{return {_:0,a:E(_1bH),b:E(B(_18L(_1bw,5,_1cr))),c:E(_1Gz.a),d:32,e:0,f:E(_S),g:0,h:E(_S),i:E(_ws),j:E(_ws)};}}),_1GA=0,_1GB=4,_1GC=new T2(0,_1GB,_1GA),_1GD=new T2(0,_1GA,_1GA),_1GE={_:0,a:E(_ws),b:E(_ws),c:E(_wt),d:E(_ws),e:E(_ws),f:E(_ws),g:E(_ws),h:E(_ws)},_1GF=new T(function(){return {_:0,a:E(_1Gy),b:E(_1bz),c:E(_19W),d:E(_S),e:E(_S),f:E(_S),g:E(_S),h:E(_1GD),i:0,j:0,k:0,l: -1,m:E(_S),n:0,o:E(_S),p:E(_S),q:E(_1GC),r:0,s:E(_1GE),t:E(_S)};}),_1GG=new T1(0,100),_1GH=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1GI=new T6(0,_2N,_2O,_S,_1GH,_2N,_2N),_1GJ=new T(function(){return B(_2L(_1GI));}),_1GK=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1GL=new T6(0,_2N,_2O,_S,_1GK,_2N,_2N),_1GM=new T(function(){return B(_2L(_1GL));}),_1GN=new T1(1,50),_1GO=function(_1GP){return E(E(_1GP).a);},_1GQ=function(_1GR){return E(E(_1GR).a);},_1GS=function(_1GT){return E(E(_1GT).b);},_1GU=function(_1GV){return E(E(_1GV).b);},_1GW=function(_1GX){return E(E(_1GX).a);},_1GY=function(_){return new F(function(){return nMV(_2N);});},_1GZ=new T(function(){return B(_36(_1GY));}),_1H0=function(_1H1){return E(E(_1H1).b);},_1H2=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1H3=function(_1H4){return E(E(_1H4).d);},_1H5=function(_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb){var _1Hc=B(_1GO(_1H6)),_1Hd=B(_1GQ(_1Hc)),_1He=new T(function(){return B(_1Gq(_1Hc));}),_1Hf=new T(function(){return B(_1H3(_1Hd));}),_1Hg=new T(function(){return B(A1(_1H7,_1H9));}),_1Hh=new T(function(){return B(A2(_1GW,_1H8,_1Ha));}),_1Hi=function(_1Hj){return new F(function(){return A1(_1Hf,new T3(0,_1Hh,_1Hg,_1Hj));});},_1Hk=function(_1Hl){var _1Hm=new T(function(){var _1Hn=new T(function(){var _1Ho=__createJSFunc(2,function(_1Hp,_){var _1Hq=B(A2(E(_1Hl),_1Hp,_));return _3a;}),_1Hr=_1Ho;return function(_){return new F(function(){return __app3(E(_1H2),E(_1Hg),E(_1Hh),_1Hr);});};});return B(A1(_1He,_1Hn));});return new F(function(){return A3(_1GS,_1Hd,_1Hm,_1Hi);});},_1Hs=new T(function(){var _1Ht=new T(function(){return B(_1Gq(_1Hc));}),_1Hu=function(_1Hv){var _1Hw=new T(function(){return B(A1(_1Ht,function(_){var _=wMV(E(_1GZ),new T1(1,_1Hv));return new F(function(){return A(_1GU,[_1H8,_1Ha,_1Hv,_]);});}));});return new F(function(){return A3(_1GS,_1Hd,_1Hw,_1Hb);});};return B(A2(_1H0,_1H6,_1Hu));});return new F(function(){return A3(_1GS,_1Hd,_1Hs,_1Hk);});},_1Hx=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1Hy=function(_){var _1Hz=rMV(E(_1GZ)),_1HA=E(_1Hz);if(!_1HA._){var _1HB=__app1(E(_1Hx),E(_3a));return new F(function(){return _gE(_);});}else{var _1HC=__app1(E(_1Hx),E(_1HA.a));return new F(function(){return _gE(_);});}},_1HD="src",_1HE=new T(function(){return B(unCStr("img"));}),_1HF=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1HG=function(_1HH,_1HI){return new F(function(){return A2(_1Gq,_1HH,function(_){var _1HJ=__app1(E(_1HF),toJSStr(E(_1HE))),_1HK=__app3(E(_i0),_1HJ,E(_1HD),E(_1HI));return _1HJ;});});},_1HL=new T(function(){return B(unCStr(".png"));}),_1HM=function(_1HN,_1HO){var _1HP=E(_1HN);if(_1HP==( -1)){return __Z;}else{var _1HQ=new T(function(){var _1HR=new T(function(){return toJSStr(B(_q(_1HO,new T(function(){return B(_q(B(_A(0,_1HP,_S)),_1HL));},1))));});return B(_1HG(_5W,_1HR));});return new F(function(){return _q(B(_1HM(_1HP-1|0,_1HO)),new T2(1,_1HQ,_S));});}},_1HS=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1HT=new T(function(){return B(_1HM(120,_1HS));}),_1HU=function(_1HV,_){var _1HW=E(_1HV);if(!_1HW._){return _S;}else{var _1HX=B(A1(_1HW.a,_)),_1HY=B(_1HU(_1HW.b,_));return new T2(1,_1HX,_1HY);}},_1HZ=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1I0=new T(function(){return B(_1HM(56,_1HZ));}),_1I1=function(_1I2,_){var _1I3=E(_1I2);if(!_1I3._){return _S;}else{var _1I4=B(A1(_1I3.a,_)),_1I5=B(_1I1(_1I3.b,_));return new T2(1,_1I4,_1I5);}},_1I6=new T(function(){return B(unCStr("Images/img"));}),_1I7=new T(function(){return B(_1HM(5,_1I6));}),_1I8=function(_1I9,_){var _1Ia=E(_1I9);if(!_1Ia._){return _S;}else{var _1Ib=B(A1(_1Ia.a,_)),_1Ic=B(_1I8(_1Ia.b,_));return new T2(1,_1Ib,_1Ic);}},_1Id=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1Ie=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1If=function(_1Ig,_1Ih,_1Ii){var _1Ij=B(_1GO(_1Ig)),_1Ik=new T(function(){return B(_1Gq(_1Ij));}),_1Il=function(_1Im){var _1In=function(_){var _1Io=E(_1Ih);if(!_1Io._){var _1Ip=B(A1(_1Im,_gD)),_1Iq=__createJSFunc(0,function(_){var _1Ir=B(A1(_1Ip,_));return _3a;}),_1Is=__app2(E(_1Ie),_1Io.a,_1Iq);return new T(function(){var _1It=Number(_1Is),_1Iu=jsTrunc(_1It);return new T2(0,_1Iu,E(_1Io));});}else{var _1Iv=B(A1(_1Im,_gD)),_1Iw=__createJSFunc(0,function(_){var _1Ix=B(A1(_1Iv,_));return _3a;}),_1Iy=__app2(E(_1Id),_1Io.a,_1Iw);return new T(function(){var _1Iz=Number(_1Iy),_1IA=jsTrunc(_1Iz);return new T2(0,_1IA,E(_1Io));});}};return new F(function(){return A1(_1Ik,_1In);});},_1IB=new T(function(){return B(A2(_1H0,_1Ig,function(_1IC){return E(_1Ii);}));});return new F(function(){return A3(_1GS,B(_1GQ(_1Ij)),_1IB,_1Il);});},_1ID=function(_){var _1IE=B(_1I8(_1I7,_)),_1IF=B(_1I1(_1I0,_)),_1IG=B(_1HU(_1HT,_)),_1IH=__app1(E(_1Gn),"canvas"),_1II=__eq(_1IH,E(_3a));if(!E(_1II)){var _1IJ=__isUndef(_1IH);if(!E(_1IJ)){var _1IK=B(A3(_1Gs,_5W,_1IH,_)),_1IL=E(_1IK);if(!_1IL._){return new F(function(){return die(_1GM);});}else{var _1IM=E(_1IL.a),_1IN=B(_62(_1IM.b,_)),_1IO=_1IN,_1IP=nMV(_1GF),_1IQ=_1IP,_1IR=new T3(0,_1IE,_1IF,_1IG),_1IS=B(A(_1H5,[_5X,_3D,_m,_1Gm,_1Gj,function(_1IT,_){var _1IU=B(_1Hy(_)),_1IV=rMV(_1IQ),_1IW=E(E(_1IO).a),_1IX=E(_1IV),_1IY=E(_1IX.a),_1IZ=E(_1IX.b),_1J0=E(_1IX.h),_1J1=E(_1IX.s),_1J2=B(_1vT(_1IM,_1IW.a,_1IW.b,_1IR,E(_1IT).a,_1IY.a,_1IY.b,_1IY.c,_1IY.d,_1IY.e,_1IY.f,_1IY.g,_1IY.h,_1IY.i,_1IY.j,_1IZ.a,_1IZ.b,_1IX.c,_1IX.d,_1IX.e,_1IX.f,_1IX.g,_1J0.a,_1J0.b,_1IX.i,_1IX.j,_1IX.k,_1IX.l,_1IX.m,_1IX.n,_1IX.o,_1IX.p,_1IX.q,_1IX.r,_1J1.a,_1J1.b,_1J1.c,_1J1.d,_1J1.e,_1J1.f,_1J1.g,_1J1.h,_1IX.t,_)),_=wMV(_1IQ,_1J2);return _gD;},_])),_1J3=B(A(_1H5,[_5X,_3D,_3C,_1IH,_1Gi,function(_1J4,_){var _1J5=E(E(_1J4).a),_1J6=rMV(_1IQ),_1J7=B(A(_1FX,[_1IM,_1IO,_1IR,_1J5.a,_1J5.b,_1J6,_])),_=wMV(_1IQ,_1J7);return _gD;},_])),_1J8=B(A(_1H5,[_5X,_3D,_5c,_1IH,_1Gl,function(_1J9,_){var _1Ja=E(_1J9),_1Jb=rMV(_1IQ),_1Jc=E(_1Jb);if(!E(E(_1Jc.s).e)){var _=wMV(_1IQ,_1Jc);return _gD;}else{var _1Jd=B(_1Hy(_)),_=wMV(_1IQ,_1Jc);return _gD;}},_])),_1Je=function(_){var _1Jf=rMV(_1IQ),_=wMV(_1IQ,new T(function(){var _1Jg=E(_1Jf),_1Jh=E(_1Jg.s);return {_:0,a:E(_1Jg.a),b:E(_1Jg.b),c:E(_1Jg.c),d:E(_1Jg.d),e:E(_1Jg.e),f:E(_1Jg.f),g:E(_1Jg.g),h:E(_1Jg.h),i:_1Jg.i,j:_1Jg.j,k:_1Jg.k,l:_1Jg.l,m:E(_1Jg.m),n:_1Jg.n,o:E(_1Jg.o),p:E(_1Jg.p),q:E(_1Jg.q),r:_1Jg.r,s:E({_:0,a:E(_1Jh.a),b:E(_1Jh.b),c:E(_1Jh.c),d:E(_1Jh.d),e:E(_ws),f:E(_1Jh.f),g:E(_1Jh.g),h:E(_1Jh.h)}),t:E(_1Jg.t)};}));return _gD;},_1Ji=function(_1Jj,_){var _1Jk=E(_1Jj),_1Jl=rMV(_1IQ),_=wMV(_1IQ,new T(function(){var _1Jm=E(_1Jl),_1Jn=E(_1Jm.s);return {_:0,a:E(_1Jm.a),b:E(_1Jm.b),c:E(_1Jm.c),d:E(_1Jm.d),e:E(_1Jm.e),f:E(_1Jm.f),g:E(_1Jm.g),h:E(_1Jm.h),i:_1Jm.i,j:_1Jm.j,k:_1Jm.k,l:_1Jm.l,m:E(_1Jm.m),n:_1Jm.n,o:E(_1Jm.o),p:E(_1Jm.p),q:E(_1Jm.q),r:_1Jm.r,s:E({_:0,a:E(_1Jn.a),b:E(_1Jn.b),c:E(_1Jn.c),d:E(_1Jn.d),e:E(_wt),f:E(_1Jn.f),g:E(_1Jn.g),h:E(_1Jn.h)}),t:E(_1Jm.t)};})),_1Jo=B(A(_1If,[_5X,_1GG,_1Je,_]));return _gD;},_1Jp=B(A(_1H5,[_5X,_3D,_5c,_1IH,_1Gk,_1Ji,_])),_1Jq=B(A(_1If,[_5X,_1GN,function(_){var _1Jr=rMV(_1IQ),_1Js=E(E(_1IO).a),_1Jt=E(_1Jr),_1Ju=E(_1Jt.a),_1Jv=E(_1Jt.b),_1Jw=E(_1Jt.h),_1Jx=E(_1Jt.q),_1Jy=E(_1Jt.s),_1Jz=B(_1Ex(_1IM,_1Js.a,_1Js.b,_1IR,_1Ju.a,_1Ju.b,_1Ju.c,_1Ju.d,_1Ju.e,_1Ju.f,_1Ju.g,_1Ju.h,_1Ju.i,_1Ju.j,_1Jv.a,_1Jv.b,_1Jt.c,_1Jt.d,_1Jt.e,_1Jt.f,_1Jt.g,_1Jw.a,_1Jw.b,_1Jt.i,_1Jt.j,_1Jt.k,_1Jt.l,_1Jt.m,_1Jt.n,_1Jt.o,_1Jt.p,_1Jx.a,_1Jx.b,_1Jt.r,_1Jy.a,_1Jy.b,_1Jy.c,_1Jy.d,_1Jy.e,_1Jy.f,_1Jy.g,_1Jy.h,_1Jt.t,_)),_=wMV(_1IQ,_1Jz);return _gD;},_]));return _gD;}}else{return new F(function(){return die(_1GJ);});}}else{return new F(function(){return die(_1GJ);});}},_1JA=function(_){return new F(function(){return _1ID(_);});};
var hasteMain = function() {B(A(_1JA, [0]));};window.onload = hasteMain;