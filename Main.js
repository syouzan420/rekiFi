"use strict";
var __haste_prog_id = '61129b60d45a893412881920c4c9668ea17b2e143d53123fec699a63fc78788c';
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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n="deltaZ",_o="deltaY",_p="deltaX",_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v,_w){var _x=jsShowI(_v);return new F(function(){return _q(fromJSStr(_x),_w);});},_y=41,_z=40,_A=function(_B,_C,_D){if(_C>=0){return new F(function(){return _u(_C,_D);});}else{if(_B<=6){return new F(function(){return _u(_C,_D);});}else{return new T2(1,_z,new T(function(){var _E=jsShowI(_C);return B(_q(fromJSStr(_E),new T2(1,_y,_D)));}));}}},_F=new T(function(){return B(unCStr(")"));}),_G=new T(function(){return B(_A(0,2,_F));}),_H=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_G));}),_I=function(_J){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_A(0,_J,_H));}))));});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L)),_N=jsTrunc(_M);if(_N<0){return B(_I(_N));}else{if(_N>2){return B(_I(_N));}else{return _N;}}});},_O=0,_P=new T3(0,_O,_O,_O),_Q="button",_R=new T(function(){return eval("jsGetMouseCoords");}),_S=__Z,_T=function(_U,_){var _V=E(_U);if(!_V._){return _S;}else{var _W=B(_T(_V.b,_));return new T2(1,new T(function(){var _X=Number(E(_V.a));return jsTrunc(_X);}),_W);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _T(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return new T(function(){var _15=Number(E(_14));return jsTrunc(_15);});},_16=new T2(0,_13,_11),_17=function(_18,_){var _19=E(_18);if(!_19._){return _S;}else{var _1a=B(_17(_19.b,_));return new T2(1,_19.a,_1a);}},_1b=new T(function(){return B(unCStr("base"));}),_1c=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1d=new T(function(){return B(unCStr("IOException"));}),_1e=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1b,_1c,_1d),_1f=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1e,_S,_S),_1g=function(_1h){return E(_1f);},_1i=function(_1j){return E(E(_1j).a);},_1k=function(_1l,_1m,_1n){var _1o=B(A1(_1l,_)),_1p=B(A1(_1m,_)),_1q=hs_eqWord64(_1o.a,_1p.a);if(!_1q){return __Z;}else{var _1r=hs_eqWord64(_1o.b,_1p.b);return (!_1r)?__Z:new T1(1,_1n);}},_1s=function(_1t){var _1u=E(_1t);return new F(function(){return _1k(B(_1i(_1u.a)),_1g,_1u.b);});},_1v=new T(function(){return B(unCStr(": "));}),_1w=new T(function(){return B(unCStr(")"));}),_1x=new T(function(){return B(unCStr(" ("));}),_1y=new T(function(){return B(unCStr("interrupted"));}),_1z=new T(function(){return B(unCStr("system error"));}),_1A=new T(function(){return B(unCStr("unsatisified constraints"));}),_1B=new T(function(){return B(unCStr("user error"));}),_1C=new T(function(){return B(unCStr("permission denied"));}),_1D=new T(function(){return B(unCStr("illegal operation"));}),_1E=new T(function(){return B(unCStr("end of file"));}),_1F=new T(function(){return B(unCStr("resource exhausted"));}),_1G=new T(function(){return B(unCStr("resource busy"));}),_1H=new T(function(){return B(unCStr("does not exist"));}),_1I=new T(function(){return B(unCStr("already exists"));}),_1J=new T(function(){return B(unCStr("resource vanished"));}),_1K=new T(function(){return B(unCStr("timeout"));}),_1L=new T(function(){return B(unCStr("unsupported operation"));}),_1M=new T(function(){return B(unCStr("hardware fault"));}),_1N=new T(function(){return B(unCStr("inappropriate type"));}),_1O=new T(function(){return B(unCStr("invalid argument"));}),_1P=new T(function(){return B(unCStr("failed"));}),_1Q=new T(function(){return B(unCStr("protocol error"));}),_1R=function(_1S,_1T){switch(E(_1S)){case 0:return new F(function(){return _q(_1I,_1T);});break;case 1:return new F(function(){return _q(_1H,_1T);});break;case 2:return new F(function(){return _q(_1G,_1T);});break;case 3:return new F(function(){return _q(_1F,_1T);});break;case 4:return new F(function(){return _q(_1E,_1T);});break;case 5:return new F(function(){return _q(_1D,_1T);});break;case 6:return new F(function(){return _q(_1C,_1T);});break;case 7:return new F(function(){return _q(_1B,_1T);});break;case 8:return new F(function(){return _q(_1A,_1T);});break;case 9:return new F(function(){return _q(_1z,_1T);});break;case 10:return new F(function(){return _q(_1Q,_1T);});break;case 11:return new F(function(){return _q(_1P,_1T);});break;case 12:return new F(function(){return _q(_1O,_1T);});break;case 13:return new F(function(){return _q(_1N,_1T);});break;case 14:return new F(function(){return _q(_1M,_1T);});break;case 15:return new F(function(){return _q(_1L,_1T);});break;case 16:return new F(function(){return _q(_1K,_1T);});break;case 17:return new F(function(){return _q(_1J,_1T);});break;default:return new F(function(){return _q(_1y,_1T);});}},_1U=new T(function(){return B(unCStr("}"));}),_1V=new T(function(){return B(unCStr("{handle: "));}),_1W=function(_1X,_1Y,_1Z,_20,_21,_22){var _23=new T(function(){var _24=new T(function(){var _25=new T(function(){var _26=E(_20);if(!_26._){return E(_22);}else{var _27=new T(function(){return B(_q(_26,new T(function(){return B(_q(_1w,_22));},1)));},1);return B(_q(_1x,_27));}},1);return B(_1R(_1Y,_25));}),_28=E(_1Z);if(!_28._){return E(_24);}else{return B(_q(_28,new T(function(){return B(_q(_1v,_24));},1)));}}),_29=E(_21);if(!_29._){var _2a=E(_1X);if(!_2a._){return E(_23);}else{var _2b=E(_2a.a);if(!_2b._){var _2c=new T(function(){var _2d=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2d));},1);return new F(function(){return _q(_1V,_2c);});}else{var _2e=new T(function(){var _2f=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2f));},1);return new F(function(){return _q(_1V,_2e);});}}}else{return new F(function(){return _q(_29.a,new T(function(){return B(_q(_1v,_23));},1));});}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _1W(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_S);});},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1W(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1W(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2g,_2G),_2K=new T(function(){return new T5(0,_1g,_2J,_2L,_1s,_2g);}),_2L=function(_2M){return new T2(0,_2K,_2M);},_2N=__Z,_2O=7,_2P=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2Q=new T6(0,_2N,_2O,_S,_2P,_2N,_2N),_2R=new T(function(){return B(_2L(_2Q));}),_2S=function(_){return new F(function(){return die(_2R);});},_2T=function(_2U){return E(E(_2U).a);},_2V=function(_2W,_2X,_2Y,_){var _2Z=__arr2lst(0,_2Y),_30=B(_17(_2Z,_)),_31=E(_30);if(!_31._){return new F(function(){return _2S(_);});}else{var _32=E(_31.b);if(!_32._){return new F(function(){return _2S(_);});}else{if(!E(_32.b)._){var _33=B(A3(_2T,_2W,_31.a,_)),_34=B(A3(_2T,_2X,_32.a,_));return new T2(0,_33,_34);}else{return new F(function(){return _2S(_);});}}}},_35=function(_){return new F(function(){return __jsNull();});},_36=function(_37){var _38=B(A1(_37,_));return E(_38);},_39=new T(function(){return B(_36(_35));}),_3a=new T(function(){return E(_39);}),_3b=function(_3c,_3d,_){if(E(_3c)==7){var _3e=__app1(E(_R),_3d),_3f=B(_2V(_16,_16,_3e,_)),_3g=__get(_3d,E(_p)),_3h=__get(_3d,E(_o)),_3i=__get(_3d,E(_n));return new T(function(){return new T3(0,E(_3f),E(_2N),E(new T3(0,_3g,_3h,_3i)));});}else{var _3j=__app1(E(_R),_3d),_3k=B(_2V(_16,_16,_3j,_)),_3l=__get(_3d,E(_Q)),_3m=__eq(_3l,E(_3a));if(!E(_3m)){var _3n=__isUndef(_3l);if(!E(_3n)){var _3o=B(_K(_3l,_));return new T(function(){return new T3(0,E(_3k),E(new T1(1,_3o)),E(_P));});}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}},_3p=function(_3q,_3r,_){return new F(function(){return _3b(_3q,E(_3r),_);});},_3s="mouseout",_3t="mouseover",_3u="mousemove",_3v="mouseup",_3w="mousedown",_3x="dblclick",_3y="click",_3z="wheel",_3A=function(_3B){switch(E(_3B)){case 0:return E(_3y);case 1:return E(_3x);case 2:return E(_3w);case 3:return E(_3v);case 4:return E(_3u);case 5:return E(_3t);case 6:return E(_3s);default:return E(_3z);}},_3C=new T2(0,_3A,_3p),_3D=function(_3E){return E(_3E);},_3F=function(_3G,_3H){return E(_3G)==E(_3H);},_3I=function(_3J,_3K){return E(_3J)!=E(_3K);},_3L=new T2(0,_3F,_3I),_3M="screenY",_3N="screenX",_3O="clientY",_3P="clientX",_3Q="pageY",_3R="pageX",_3S="target",_3T="identifier",_3U=function(_3V,_){var _3W=__get(_3V,E(_3T)),_3X=__get(_3V,E(_3S)),_3Y=__get(_3V,E(_3R)),_3Z=__get(_3V,E(_3Q)),_40=__get(_3V,E(_3P)),_41=__get(_3V,E(_3O)),_42=__get(_3V,E(_3N)),_43=__get(_3V,E(_3M));return new T(function(){var _44=Number(_3W),_45=jsTrunc(_44);return new T5(0,_45,_3X,E(new T2(0,new T(function(){var _46=Number(_3Y);return jsTrunc(_46);}),new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}))),E(new T2(0,new T(function(){var _48=Number(_40);return jsTrunc(_48);}),new T(function(){var _49=Number(_41);return jsTrunc(_49);}))),E(new T2(0,new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}),new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}))));});},_4c=function(_4d,_){var _4e=E(_4d);if(!_4e._){return _S;}else{var _4f=B(_3U(E(_4e.a),_)),_4g=B(_4c(_4e.b,_));return new T2(1,_4f,_4g);}},_4h="touches",_4i=function(_4j){return E(E(_4j).b);},_4k=function(_4l,_4m,_){var _4n=__arr2lst(0,_4m),_4o=new T(function(){return B(_4i(_4l));}),_4p=function(_4q,_){var _4r=E(_4q);if(!_4r._){return _S;}else{var _4s=B(A2(_4o,_4r.a,_)),_4t=B(_4p(_4r.b,_));return new T2(1,_4s,_4t);}};return new F(function(){return _4p(_4n,_);});},_4u=function(_4v,_){return new F(function(){return _4k(_16,E(_4v),_);});},_4w=new T2(0,_11,_4u),_4x=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4y=function(_4z){return E(E(_4z).a);},_4A=function(_4B,_4C,_4D){while(1){var _4E=E(_4D);if(!_4E._){return false;}else{if(!B(A3(_4y,_4B,_4C,_4E.a))){_4D=_4E.b;continue;}else{return true;}}}},_4F=function(_4G,_4H){while(1){var _4I=B((function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return __Z;}else{var _4M=_4L.a,_4N=_4L.b;if(!B(A1(_4J,_4M))){var _4O=_4J;_4G=_4O;_4H=_4N;return __continue;}else{return new T2(1,_4M,new T(function(){return B(_4F(_4J,_4N));}));}}})(_4G,_4H));if(_4I!=__continue){return _4I;}}},_4P=function(_4Q,_){var _4R=__get(_4Q,E(_4h)),_4S=__arr2lst(0,_4R),_4T=B(_4c(_4S,_)),_4U=__app1(E(_4x),_4Q),_4V=B(_2V(_4w,_4w,_4U,_)),_4W=E(_4V),_4X=new T(function(){var _4Y=function(_4Z){return new F(function(){return _4A(_3L,new T(function(){return E(_4Z).a;}),_4W.a);});};return B(_4F(_4Y,_4T));}),_50=new T(function(){var _51=function(_52){return new F(function(){return _4A(_3L,new T(function(){return E(_52).a;}),_4W.b);});};return B(_4F(_51,_4T));});return new T3(0,_4T,_50,_4X);},_53=function(_54,_55,_){return new F(function(){return _4P(E(_55),_);});},_56="touchcancel",_57="touchend",_58="touchmove",_59="touchstart",_5a=function(_5b){switch(E(_5b)){case 0:return E(_59);case 1:return E(_58);case 2:return E(_57);default:return E(_56);}},_5c=new T2(0,_5a,_53),_5d=function(_5e,_5f,_){var _5g=B(A1(_5e,_)),_5h=B(A1(_5f,_));return _5g;},_5i=function(_5j,_5k,_){var _5l=B(A1(_5j,_)),_5m=B(A1(_5k,_));return new T(function(){return B(A1(_5l,_5m));});},_5n=function(_5o,_5p,_){var _5q=B(A1(_5p,_));return _5o;},_5r=function(_5s,_5t,_){var _5u=B(A1(_5t,_));return new T(function(){return B(A1(_5s,_5u));});},_5v=new T2(0,_5r,_5n),_5w=function(_5x,_){return _5x;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5z,_));return new F(function(){return A1(_5A,_);});},_5C=new T5(0,_5v,_5w,_5i,_5y,_5d),_5D=new T(function(){return E(_2K);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H){return new T6(0,_2N,_2O,_S,_5H,_2N,_2N);},_5I=function(_5J,_){var _5K=new T(function(){return B(A2(_5E,_5D,new T(function(){return B(A1(_5G,_5J));})));});return new F(function(){return die(_5K);});},_5L=function(_5M,_){return new F(function(){return _5I(_5M,_);});},_5N=function(_5O){return new F(function(){return A1(_5L,_5O);});},_5P=function(_5Q,_5R,_){var _5S=B(A1(_5Q,_));return new F(function(){return A2(_5R,_5S,_);});},_5T=new T5(0,_5C,_5P,_5y,_5w,_5N),_5U=function(_5V){return E(_5V);},_5W=new T2(0,_5T,_5U),_5X=new T2(0,_5W,_5w),_5Y=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_60=new T(function(){return eval("(function(cv){return cv.height})");}),_61=new T(function(){return eval("(function(cv){return cv.width})");}),_62=function(_63,_){var _64=__app1(E(_61),_63),_65=__app1(E(_60),_63),_66=__app1(E(_5Z),_63),_67=__app1(E(_5Y),_63);return new T2(0,new T2(0,_64,_65),new T2(0,_66,_67));},_68=function(_69,_6a){while(1){var _6b=B((function(_6c,_6d){var _6e=E(_6d);if(!_6e._){_69=new T2(1,new T2(0,_6e.b,_6e.c),new T(function(){return B(_68(_6c,_6e.e));}));_6a=_6e.d;return __continue;}else{return E(_6c);}})(_69,_6a));if(_6b!=__continue){return _6b;}}},_6f=function(_6g,_6h){while(1){var _6i=E(_6g);if(!_6i._){return (E(_6h)._==0)?true:false;}else{var _6j=E(_6h);if(!_6j._){return false;}else{if(E(_6i.a)!=E(_6j.a)){return false;}else{_6g=_6i.b;_6h=_6j.b;continue;}}}}},_6k=function(_6l,_6m){var _6n=E(_6m);return (_6n._==0)?__Z:new T2(1,new T(function(){return B(A1(_6l,_6n.a));}),new T(function(){return B(_6k(_6l,_6n.b));}));},_6o=function(_6p){return new T1(3,E(B(_6k(_5U,_6p))));},_6q="Tried to deserialie a non-array to a list!",_6r=new T1(0,_6q),_6s=new T1(1,_S),_6t=function(_6u){var _6v=E(_6u);if(!_6v._){return E(_6s);}else{var _6w=B(_6t(_6v.b));return (_6w._==0)?new T1(0,_6w.a):new T1(1,new T2(1,_6v.a,_6w.a));}},_6x=function(_6y){var _6z=E(_6y);if(_6z._==3){return new F(function(){return _6t(_6z.a);});}else{return E(_6r);}},_6A=function(_6B){return new T1(1,_6B);},_6C=new T4(0,_5U,_6o,_6A,_6x),_6D=function(_6E,_6F,_6G){return new F(function(){return A1(_6E,new T2(1,_2s,new T(function(){return B(A1(_6F,_6G));})));});},_6H=function(_6I){return new F(function(){return _A(0,E(_6I),_S);});},_6J=34,_6K=new T2(1,_6J,_S),_6L=new T(function(){return B(unCStr("!!: negative index"));}),_6M=new T(function(){return B(unCStr("Prelude."));}),_6N=new T(function(){return B(_q(_6M,_6L));}),_6O=new T(function(){return B(err(_6N));}),_6P=new T(function(){return B(unCStr("!!: index too large"));}),_6Q=new T(function(){return B(_q(_6M,_6P));}),_6R=new T(function(){return B(err(_6Q));}),_6S=function(_6T,_6U){while(1){var _6V=E(_6T);if(!_6V._){return E(_6R);}else{var _6W=E(_6U);if(!_6W){return E(_6V.a);}else{_6T=_6V.b;_6U=_6W-1|0;continue;}}}},_6X=function(_6Y,_6Z){if(_6Z>=0){return new F(function(){return _6S(_6Y,_6Z);});}else{return E(_6O);}},_70=new T(function(){return B(unCStr("ACK"));}),_71=new T(function(){return B(unCStr("BEL"));}),_72=new T(function(){return B(unCStr("BS"));}),_73=new T(function(){return B(unCStr("SP"));}),_74=new T2(1,_73,_S),_75=new T(function(){return B(unCStr("US"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("RS"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("GS"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("FS"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("ESC"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("SUB"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("EM"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("CAN"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("ETB"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("SYN"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("NAK"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("DC4"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DC3"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("DC2"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("DC1"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("DLE"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("SI"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("SO"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("CR"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("FF"));}),_7I=new T2(1,_7H,_7G),_7J=new T(function(){return B(unCStr("VT"));}),_7K=new T2(1,_7J,_7I),_7L=new T(function(){return B(unCStr("LF"));}),_7M=new T2(1,_7L,_7K),_7N=new T(function(){return B(unCStr("HT"));}),_7O=new T2(1,_7N,_7M),_7P=new T2(1,_72,_7O),_7Q=new T2(1,_71,_7P),_7R=new T2(1,_70,_7Q),_7S=new T(function(){return B(unCStr("ENQ"));}),_7T=new T2(1,_7S,_7R),_7U=new T(function(){return B(unCStr("EOT"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("ETX"));}),_7X=new T2(1,_7W,_7V),_7Y=new T(function(){return B(unCStr("STX"));}),_7Z=new T2(1,_7Y,_7X),_80=new T(function(){return B(unCStr("SOH"));}),_81=new T2(1,_80,_7Z),_82=new T(function(){return B(unCStr("NUL"));}),_83=new T2(1,_82,_81),_84=92,_85=new T(function(){return B(unCStr("\\DEL"));}),_86=new T(function(){return B(unCStr("\\a"));}),_87=new T(function(){return B(unCStr("\\\\"));}),_88=new T(function(){return B(unCStr("\\SO"));}),_89=new T(function(){return B(unCStr("\\r"));}),_8a=new T(function(){return B(unCStr("\\f"));}),_8b=new T(function(){return B(unCStr("\\v"));}),_8c=new T(function(){return B(unCStr("\\n"));}),_8d=new T(function(){return B(unCStr("\\t"));}),_8e=new T(function(){return B(unCStr("\\b"));}),_8f=function(_8g,_8h){if(_8g<=127){var _8i=E(_8g);switch(_8i){case 92:return new F(function(){return _q(_87,_8h);});break;case 127:return new F(function(){return _q(_85,_8h);});break;default:if(_8i<32){var _8j=E(_8i);switch(_8j){case 7:return new F(function(){return _q(_86,_8h);});break;case 8:return new F(function(){return _q(_8e,_8h);});break;case 9:return new F(function(){return _q(_8d,_8h);});break;case 10:return new F(function(){return _q(_8c,_8h);});break;case 11:return new F(function(){return _q(_8b,_8h);});break;case 12:return new F(function(){return _q(_8a,_8h);});break;case 13:return new F(function(){return _q(_89,_8h);});break;case 14:return new F(function(){return _q(_88,new T(function(){var _8k=E(_8h);if(!_8k._){return __Z;}else{if(E(_8k.a)==72){return B(unAppCStr("\\&",_8k));}else{return E(_8k);}}},1));});break;default:return new F(function(){return _q(new T2(1,_84,new T(function(){return B(_6X(_83,_8j));})),_8h);});}}else{return new T2(1,_8i,_8h);}}}else{var _8l=new T(function(){var _8m=jsShowI(_8g);return B(_q(fromJSStr(_8m),new T(function(){var _8n=E(_8h);if(!_8n._){return __Z;}else{var _8o=E(_8n.a);if(_8o<48){return E(_8n);}else{if(_8o>57){return E(_8n);}else{return B(unAppCStr("\\&",_8n));}}}},1)));});return new T2(1,_84,_8l);}},_8p=new T(function(){return B(unCStr("\\\""));}),_8q=function(_8r,_8s){var _8t=E(_8r);if(!_8t._){return E(_8s);}else{var _8u=_8t.b,_8v=E(_8t.a);if(_8v==34){return new F(function(){return _q(_8p,new T(function(){return B(_8q(_8u,_8s));},1));});}else{return new F(function(){return _8f(_8v,new T(function(){return B(_8q(_8u,_8s));}));});}}},_8w=function(_8x){return new T2(1,_6J,new T(function(){return B(_8q(_8x,_6K));}));},_8y=function(_8z,_8A){if(_8z<=_8A){var _8B=function(_8C){return new T2(1,_8C,new T(function(){if(_8C!=_8A){return B(_8B(_8C+1|0));}else{return __Z;}}));};return new F(function(){return _8B(_8z);});}else{return __Z;}},_8D=function(_8E){return new F(function(){return _8y(E(_8E),2147483647);});},_8F=function(_8G,_8H,_8I){if(_8I<=_8H){var _8J=new T(function(){var _8K=_8H-_8G|0,_8L=function(_8M){return (_8M>=(_8I-_8K|0))?new T2(1,_8M,new T(function(){return B(_8L(_8M+_8K|0));})):new T2(1,_8M,_S);};return B(_8L(_8H));});return new T2(1,_8G,_8J);}else{return (_8I<=_8G)?new T2(1,_8G,_S):__Z;}},_8N=function(_8O,_8P,_8Q){if(_8Q>=_8P){var _8R=new T(function(){var _8S=_8P-_8O|0,_8T=function(_8U){return (_8U<=(_8Q-_8S|0))?new T2(1,_8U,new T(function(){return B(_8T(_8U+_8S|0));})):new T2(1,_8U,_S);};return B(_8T(_8P));});return new T2(1,_8O,_8R);}else{return (_8Q>=_8O)?new T2(1,_8O,_S):__Z;}},_8V=function(_8W,_8X){if(_8X<_8W){return new F(function(){return _8F(_8W,_8X, -2147483648);});}else{return new F(function(){return _8N(_8W,_8X,2147483647);});}},_8Y=function(_8Z,_90){return new F(function(){return _8V(E(_8Z),E(_90));});},_91=function(_92,_93,_94){if(_93<_92){return new F(function(){return _8F(_92,_93,_94);});}else{return new F(function(){return _8N(_92,_93,_94);});}},_95=function(_96,_97,_98){return new F(function(){return _91(E(_96),E(_97),E(_98));});},_99=function(_9a,_9b){return new F(function(){return _8y(E(_9a),E(_9b));});},_9c=function(_9d){return E(_9d);},_9e=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_9f=new T(function(){return B(err(_9e));}),_9g=function(_9h){var _9i=E(_9h);return (_9i==( -2147483648))?E(_9f):_9i-1|0;},_9j=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9k=new T(function(){return B(err(_9j));}),_9l=function(_9m){var _9n=E(_9m);return (_9n==2147483647)?E(_9k):_9n+1|0;},_9o={_:0,a:_9l,b:_9g,c:_9c,d:_9c,e:_8D,f:_8Y,g:_99,h:_95},_9p=function(_9q,_9r){if(_9q<=0){if(_9q>=0){return new F(function(){return quot(_9q,_9r);});}else{if(_9r<=0){return new F(function(){return quot(_9q,_9r);});}else{return quot(_9q+1|0,_9r)-1|0;}}}else{if(_9r>=0){if(_9q>=0){return new F(function(){return quot(_9q,_9r);});}else{if(_9r<=0){return new F(function(){return quot(_9q,_9r);});}else{return quot(_9q+1|0,_9r)-1|0;}}}else{return quot(_9q-1|0,_9r)-1|0;}}},_9s=new T(function(){return B(unCStr("base"));}),_9t=new T(function(){return B(unCStr("GHC.Exception"));}),_9u=new T(function(){return B(unCStr("ArithException"));}),_9v=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9s,_9t,_9u),_9w=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9v,_S,_S),_9x=function(_9y){return E(_9w);},_9z=function(_9A){var _9B=E(_9A);return new F(function(){return _1k(B(_1i(_9B.a)),_9x,_9B.b);});},_9C=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9D=new T(function(){return B(unCStr("denormal"));}),_9E=new T(function(){return B(unCStr("divide by zero"));}),_9F=new T(function(){return B(unCStr("loss of precision"));}),_9G=new T(function(){return B(unCStr("arithmetic underflow"));}),_9H=new T(function(){return B(unCStr("arithmetic overflow"));}),_9I=function(_9J,_9K){switch(E(_9J)){case 0:return new F(function(){return _q(_9H,_9K);});break;case 1:return new F(function(){return _q(_9G,_9K);});break;case 2:return new F(function(){return _q(_9F,_9K);});break;case 3:return new F(function(){return _q(_9E,_9K);});break;case 4:return new F(function(){return _q(_9D,_9K);});break;default:return new F(function(){return _q(_9C,_9K);});}},_9L=function(_9M){return new F(function(){return _9I(_9M,_S);});},_9N=function(_9O,_9P,_9Q){return new F(function(){return _9I(_9P,_9Q);});},_9R=function(_9S,_9T){return new F(function(){return _2v(_9I,_9S,_9T);});},_9U=new T3(0,_9N,_9L,_9R),_9V=new T(function(){return new T5(0,_9x,_9U,_9W,_9z,_9L);}),_9W=function(_9X){return new T2(0,_9V,_9X);},_9Y=3,_9Z=new T(function(){return B(_9W(_9Y));}),_a0=new T(function(){return die(_9Z);}),_a1=0,_a2=new T(function(){return B(_9W(_a1));}),_a3=new T(function(){return die(_a2);}),_a4=function(_a5,_a6){var _a7=E(_a6);switch(_a7){case  -1:var _a8=E(_a5);if(_a8==( -2147483648)){return E(_a3);}else{return new F(function(){return _9p(_a8, -1);});}break;case 0:return E(_a0);default:return new F(function(){return _9p(_a5,_a7);});}},_a9=function(_aa,_ab){return new F(function(){return _a4(E(_aa),E(_ab));});},_ac=0,_ad=new T2(0,_a3,_ac),_ae=function(_af,_ag){var _ah=E(_af),_ai=E(_ag);switch(_ai){case  -1:var _aj=E(_ah);if(_aj==( -2147483648)){return E(_ad);}else{if(_aj<=0){if(_aj>=0){var _ak=quotRemI(_aj, -1);return new T2(0,_ak.a,_ak.b);}else{var _al=quotRemI(_aj, -1);return new T2(0,_al.a,_al.b);}}else{var _am=quotRemI(_aj-1|0, -1);return new T2(0,_am.a-1|0,(_am.b+( -1)|0)+1|0);}}break;case 0:return E(_a0);default:if(_ah<=0){if(_ah>=0){var _an=quotRemI(_ah,_ai);return new T2(0,_an.a,_an.b);}else{if(_ai<=0){var _ao=quotRemI(_ah,_ai);return new T2(0,_ao.a,_ao.b);}else{var _ap=quotRemI(_ah+1|0,_ai);return new T2(0,_ap.a-1|0,(_ap.b+_ai|0)-1|0);}}}else{if(_ai>=0){if(_ah>=0){var _aq=quotRemI(_ah,_ai);return new T2(0,_aq.a,_aq.b);}else{if(_ai<=0){var _ar=quotRemI(_ah,_ai);return new T2(0,_ar.a,_ar.b);}else{var _as=quotRemI(_ah+1|0,_ai);return new T2(0,_as.a-1|0,(_as.b+_ai|0)-1|0);}}}else{var _at=quotRemI(_ah-1|0,_ai);return new T2(0,_at.a-1|0,(_at.b+_ai|0)+1|0);}}}},_au=function(_av,_aw){var _ax=_av%_aw;if(_av<=0){if(_av>=0){return E(_ax);}else{if(_aw<=0){return E(_ax);}else{var _ay=E(_ax);return (_ay==0)?0:_ay+_aw|0;}}}else{if(_aw>=0){if(_av>=0){return E(_ax);}else{if(_aw<=0){return E(_ax);}else{var _az=E(_ax);return (_az==0)?0:_az+_aw|0;}}}else{var _aA=E(_ax);return (_aA==0)?0:_aA+_aw|0;}}},_aB=function(_aC,_aD){var _aE=E(_aD);switch(_aE){case  -1:return E(_ac);case 0:return E(_a0);default:return new F(function(){return _au(E(_aC),_aE);});}},_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=E(_aH);switch(_aJ){case  -1:var _aK=E(_aI);if(_aK==( -2147483648)){return E(_a3);}else{return new F(function(){return quot(_aK, -1);});}break;case 0:return E(_a0);default:return new F(function(){return quot(_aI,_aJ);});}},_aL=function(_aM,_aN){var _aO=E(_aM),_aP=E(_aN);switch(_aP){case  -1:var _aQ=E(_aO);if(_aQ==( -2147483648)){return E(_ad);}else{var _aR=quotRemI(_aQ, -1);return new T2(0,_aR.a,_aR.b);}break;case 0:return E(_a0);default:var _aS=quotRemI(_aO,_aP);return new T2(0,_aS.a,_aS.b);}},_aT=function(_aU,_aV){var _aW=E(_aV);switch(_aW){case  -1:return E(_ac);case 0:return E(_a0);default:return E(_aU)%_aW;}},_aX=function(_aY){return new T1(0,_aY);},_aZ=function(_b0){return new F(function(){return _aX(E(_b0));});},_b1=new T1(0,1),_b2=function(_b3){return new T2(0,E(B(_aX(E(_b3)))),E(_b1));},_b4=function(_b5,_b6){return imul(E(_b5),E(_b6))|0;},_b7=function(_b8,_b9){return E(_b8)+E(_b9)|0;},_ba=function(_bb,_bc){return E(_bb)-E(_bc)|0;},_bd=function(_be){var _bf=E(_be);return (_bf<0)? -_bf:E(_bf);},_bg=function(_bh){var _bi=E(_bh);if(!_bi._){return E(_bi.a);}else{return new F(function(){return I_toInt(_bi.a);});}},_bj=function(_bk){return new F(function(){return _bg(_bk);});},_bl=function(_bm){return  -E(_bm);},_bn= -1,_bo=0,_bp=1,_bq=function(_br){var _bs=E(_br);return (_bs>=0)?(E(_bs)==0)?E(_bo):E(_bp):E(_bn);},_bt={_:0,a:_b7,b:_ba,c:_b4,d:_bl,e:_bd,f:_bq,g:_bj},_bu=function(_bv,_bw){var _bx=E(_bv),_by=E(_bw);return (_bx>_by)?E(_bx):E(_by);},_bz=function(_bA,_bB){var _bC=E(_bA),_bD=E(_bB);return (_bC>_bD)?E(_bD):E(_bC);},_bE=function(_bF,_bG){return (_bF>=_bG)?(_bF!=_bG)?2:1:0;},_bH=function(_bI,_bJ){return new F(function(){return _bE(E(_bI),E(_bJ));});},_bK=function(_bL,_bM){return E(_bL)>=E(_bM);},_bN=function(_bO,_bP){return E(_bO)>E(_bP);},_bQ=function(_bR,_bS){return E(_bR)<=E(_bS);},_bT=function(_bU,_bV){return E(_bU)<E(_bV);},_bW={_:0,a:_3L,b:_bH,c:_bT,d:_bQ,e:_bN,f:_bK,g:_bu,h:_bz},_bX=new T3(0,_bt,_bW,_b2),_bY={_:0,a:_bX,b:_9o,c:_aF,d:_aT,e:_a9,f:_aB,g:_aL,h:_ae,i:_aZ},_bZ=function(_c0){var _c1=E(_c0);return new F(function(){return Math.log(_c1+(_c1+1)*Math.sqrt((_c1-1)/(_c1+1)));});},_c2=function(_c3){var _c4=E(_c3);return new F(function(){return Math.log(_c4+Math.sqrt(1+_c4*_c4));});},_c5=function(_c6){var _c7=E(_c6);return 0.5*Math.log((1+_c7)/(1-_c7));},_c8=function(_c9,_ca){return Math.log(E(_ca))/Math.log(E(_c9));},_cb=3.141592653589793,_cc=new T1(0,1),_cd=function(_ce,_cf){var _cg=E(_ce);if(!_cg._){var _ch=_cg.a,_ci=E(_cf);if(!_ci._){var _cj=_ci.a;return (_ch!=_cj)?(_ch>_cj)?2:0:1;}else{var _ck=I_compareInt(_ci.a,_ch);return (_ck<=0)?(_ck>=0)?1:2:0;}}else{var _cl=_cg.a,_cm=E(_cf);if(!_cm._){var _cn=I_compareInt(_cl,_cm.a);return (_cn>=0)?(_cn<=0)?1:2:0;}else{var _co=I_compare(_cl,_cm.a);return (_co>=0)?(_co<=0)?1:2:0;}}},_cp=function(_cq,_cr){var _cs=E(_cq);return (_cs._==0)?_cs.a*Math.pow(2,_cr):I_toNumber(_cs.a)*Math.pow(2,_cr);},_ct=function(_cu,_cv){var _cw=E(_cu);if(!_cw._){var _cx=_cw.a,_cy=E(_cv);return (_cy._==0)?_cx==_cy.a:(I_compareInt(_cy.a,_cx)==0)?true:false;}else{var _cz=_cw.a,_cA=E(_cv);return (_cA._==0)?(I_compareInt(_cz,_cA.a)==0)?true:false:(I_compare(_cz,_cA.a)==0)?true:false;}},_cB=function(_cC,_cD){while(1){var _cE=E(_cC);if(!_cE._){var _cF=_cE.a,_cG=E(_cD);if(!_cG._){var _cH=_cG.a,_cI=addC(_cF,_cH);if(!E(_cI.b)){return new T1(0,_cI.a);}else{_cC=new T1(1,I_fromInt(_cF));_cD=new T1(1,I_fromInt(_cH));continue;}}else{_cC=new T1(1,I_fromInt(_cF));_cD=_cG;continue;}}else{var _cJ=E(_cD);if(!_cJ._){_cC=_cE;_cD=new T1(1,I_fromInt(_cJ.a));continue;}else{return new T1(1,I_add(_cE.a,_cJ.a));}}}},_cK=function(_cL,_cM){while(1){var _cN=E(_cL);if(!_cN._){var _cO=E(_cN.a);if(_cO==( -2147483648)){_cL=new T1(1,I_fromInt( -2147483648));continue;}else{var _cP=E(_cM);if(!_cP._){var _cQ=_cP.a;return new T2(0,new T1(0,quot(_cO,_cQ)),new T1(0,_cO%_cQ));}else{_cL=new T1(1,I_fromInt(_cO));_cM=_cP;continue;}}}else{var _cR=E(_cM);if(!_cR._){_cL=_cN;_cM=new T1(1,I_fromInt(_cR.a));continue;}else{var _cS=I_quotRem(_cN.a,_cR.a);return new T2(0,new T1(1,_cS.a),new T1(1,_cS.b));}}}},_cT=new T1(0,0),_cU=function(_cV,_cW){while(1){var _cX=E(_cV);if(!_cX._){_cV=new T1(1,I_fromInt(_cX.a));continue;}else{return new T1(1,I_shiftLeft(_cX.a,_cW));}}},_cY=function(_cZ,_d0,_d1){if(!B(_ct(_d1,_cT))){var _d2=B(_cK(_d0,_d1)),_d3=_d2.a;switch(B(_cd(B(_cU(_d2.b,1)),_d1))){case 0:return new F(function(){return _cp(_d3,_cZ);});break;case 1:if(!(B(_bg(_d3))&1)){return new F(function(){return _cp(_d3,_cZ);});}else{return new F(function(){return _cp(B(_cB(_d3,_cc)),_cZ);});}break;default:return new F(function(){return _cp(B(_cB(_d3,_cc)),_cZ);});}}else{return E(_a0);}},_d4=function(_d5,_d6){var _d7=E(_d5);if(!_d7._){var _d8=_d7.a,_d9=E(_d6);return (_d9._==0)?_d8>_d9.a:I_compareInt(_d9.a,_d8)<0;}else{var _da=_d7.a,_db=E(_d6);return (_db._==0)?I_compareInt(_da,_db.a)>0:I_compare(_da,_db.a)>0;}},_dc=new T1(0,1),_dd=function(_de,_df){var _dg=E(_de);if(!_dg._){var _dh=_dg.a,_di=E(_df);return (_di._==0)?_dh<_di.a:I_compareInt(_di.a,_dh)>0;}else{var _dj=_dg.a,_dk=E(_df);return (_dk._==0)?I_compareInt(_dj,_dk.a)<0:I_compare(_dj,_dk.a)<0;}},_dl=new T(function(){return B(unCStr("base"));}),_dm=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dn=new T(function(){return B(unCStr("PatternMatchFail"));}),_do=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dl,_dm,_dn),_dp=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_do,_S,_S),_dq=function(_dr){return E(_dp);},_ds=function(_dt){var _du=E(_dt);return new F(function(){return _1k(B(_1i(_du.a)),_dq,_du.b);});},_dv=function(_dw){return E(E(_dw).a);},_dx=function(_dy){return new T2(0,_dz,_dy);},_dA=function(_dB,_dC){return new F(function(){return _q(E(_dB).a,_dC);});},_dD=function(_dE,_dF){return new F(function(){return _2v(_dA,_dE,_dF);});},_dG=function(_dH,_dI,_dJ){return new F(function(){return _q(E(_dI).a,_dJ);});},_dK=new T3(0,_dG,_dv,_dD),_dz=new T(function(){return new T5(0,_dq,_dK,_dx,_ds,_dv);}),_dL=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dM=function(_dN,_dO){return new F(function(){return die(new T(function(){return B(A2(_5E,_dO,_dN));}));});},_dP=function(_dQ,_9X){return new F(function(){return _dM(_dQ,_9X);});},_dR=function(_dS,_dT){var _dU=E(_dT);if(!_dU._){return new T2(0,_S,_S);}else{var _dV=_dU.a;if(!B(A1(_dS,_dV))){return new T2(0,_S,_dU);}else{var _dW=new T(function(){var _dX=B(_dR(_dS,_dU.b));return new T2(0,_dX.a,_dX.b);});return new T2(0,new T2(1,_dV,new T(function(){return E(E(_dW).a);})),new T(function(){return E(E(_dW).b);}));}}},_dY=32,_dZ=new T(function(){return B(unCStr("\n"));}),_e0=function(_e1){return (E(_e1)==124)?false:true;},_e2=function(_e3,_e4){var _e5=B(_dR(_e0,B(unCStr(_e3)))),_e6=_e5.a,_e7=function(_e8,_e9){var _ea=new T(function(){var _eb=new T(function(){return B(_q(_e4,new T(function(){return B(_q(_e9,_dZ));},1)));});return B(unAppCStr(": ",_eb));},1);return new F(function(){return _q(_e8,_ea);});},_ec=E(_e5.b);if(!_ec._){return new F(function(){return _e7(_e6,_S);});}else{if(E(_ec.a)==124){return new F(function(){return _e7(_e6,new T2(1,_dY,_ec.b));});}else{return new F(function(){return _e7(_e6,_S);});}}},_ed=function(_ee){return new F(function(){return _dP(new T1(0,new T(function(){return B(_e2(_ee,_dL));})),_dz);});},_ef=function(_eg){var _eh=function(_ei,_ej){while(1){if(!B(_dd(_ei,_eg))){if(!B(_d4(_ei,_eg))){if(!B(_ct(_ei,_eg))){return new F(function(){return _ed("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ej);}}else{return _ej-1|0;}}else{var _ek=B(_cU(_ei,1)),_el=_ej+1|0;_ei=_ek;_ej=_el;continue;}}};return new F(function(){return _eh(_dc,0);});},_em=function(_en){var _eo=E(_en);if(!_eo._){var _ep=_eo.a>>>0;if(!_ep){return  -1;}else{var _eq=function(_er,_es){while(1){if(_er>=_ep){if(_er<=_ep){if(_er!=_ep){return new F(function(){return _ed("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_es);}}else{return _es-1|0;}}else{var _et=imul(_er,2)>>>0,_eu=_es+1|0;_er=_et;_es=_eu;continue;}}};return new F(function(){return _eq(1,0);});}}else{return new F(function(){return _ef(_eo);});}},_ev=function(_ew){var _ex=E(_ew);if(!_ex._){var _ey=_ex.a>>>0;if(!_ey){return new T2(0, -1,0);}else{var _ez=function(_eA,_eB){while(1){if(_eA>=_ey){if(_eA<=_ey){if(_eA!=_ey){return new F(function(){return _ed("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_eB);}}else{return _eB-1|0;}}else{var _eC=imul(_eA,2)>>>0,_eD=_eB+1|0;_eA=_eC;_eB=_eD;continue;}}};return new T2(0,B(_ez(1,0)),(_ey&_ey-1>>>0)>>>0&4294967295);}}else{var _eE=_ex.a;return new T2(0,B(_em(_ex)),I_compareInt(I_and(_eE,I_sub(_eE,I_fromInt(1))),0));}},_eF=function(_eG,_eH){var _eI=E(_eG);if(!_eI._){var _eJ=_eI.a,_eK=E(_eH);return (_eK._==0)?_eJ<=_eK.a:I_compareInt(_eK.a,_eJ)>=0;}else{var _eL=_eI.a,_eM=E(_eH);return (_eM._==0)?I_compareInt(_eL,_eM.a)<=0:I_compare(_eL,_eM.a)<=0;}},_eN=function(_eO,_eP){while(1){var _eQ=E(_eO);if(!_eQ._){var _eR=_eQ.a,_eS=E(_eP);if(!_eS._){return new T1(0,(_eR>>>0&_eS.a>>>0)>>>0&4294967295);}else{_eO=new T1(1,I_fromInt(_eR));_eP=_eS;continue;}}else{var _eT=E(_eP);if(!_eT._){_eO=_eQ;_eP=new T1(1,I_fromInt(_eT.a));continue;}else{return new T1(1,I_and(_eQ.a,_eT.a));}}}},_eU=function(_eV,_eW){while(1){var _eX=E(_eV);if(!_eX._){var _eY=_eX.a,_eZ=E(_eW);if(!_eZ._){var _f0=_eZ.a,_f1=subC(_eY,_f0);if(!E(_f1.b)){return new T1(0,_f1.a);}else{_eV=new T1(1,I_fromInt(_eY));_eW=new T1(1,I_fromInt(_f0));continue;}}else{_eV=new T1(1,I_fromInt(_eY));_eW=_eZ;continue;}}else{var _f2=E(_eW);if(!_f2._){_eV=_eX;_eW=new T1(1,I_fromInt(_f2.a));continue;}else{return new T1(1,I_sub(_eX.a,_f2.a));}}}},_f3=new T1(0,2),_f4=function(_f5,_f6){var _f7=E(_f5);if(!_f7._){var _f8=(_f7.a>>>0&(2<<_f6>>>0)-1>>>0)>>>0,_f9=1<<_f6>>>0;return (_f9<=_f8)?(_f9>=_f8)?1:2:0;}else{var _fa=B(_eN(_f7,B(_eU(B(_cU(_f3,_f6)),_dc)))),_fb=B(_cU(_dc,_f6));return (!B(_d4(_fb,_fa)))?(!B(_dd(_fb,_fa)))?1:2:0;}},_fc=function(_fd,_fe){while(1){var _ff=E(_fd);if(!_ff._){_fd=new T1(1,I_fromInt(_ff.a));continue;}else{return new T1(1,I_shiftRight(_ff.a,_fe));}}},_fg=function(_fh,_fi,_fj,_fk){var _fl=B(_ev(_fk)),_fm=_fl.a;if(!E(_fl.b)){var _fn=B(_em(_fj));if(_fn<((_fm+_fh|0)-1|0)){var _fo=_fm+(_fh-_fi|0)|0;if(_fo>0){if(_fo>_fn){if(_fo<=(_fn+1|0)){if(!E(B(_ev(_fj)).b)){return 0;}else{return new F(function(){return _cp(_cc,_fh-_fi|0);});}}else{return 0;}}else{var _fp=B(_fc(_fj,_fo));switch(B(_f4(_fj,_fo-1|0))){case 0:return new F(function(){return _cp(_fp,_fh-_fi|0);});break;case 1:if(!(B(_bg(_fp))&1)){return new F(function(){return _cp(_fp,_fh-_fi|0);});}else{return new F(function(){return _cp(B(_cB(_fp,_cc)),_fh-_fi|0);});}break;default:return new F(function(){return _cp(B(_cB(_fp,_cc)),_fh-_fi|0);});}}}else{return new F(function(){return _cp(_fj,(_fh-_fi|0)-_fo|0);});}}else{if(_fn>=_fi){var _fq=B(_fc(_fj,(_fn+1|0)-_fi|0));switch(B(_f4(_fj,_fn-_fi|0))){case 0:return new F(function(){return _cp(_fq,((_fn-_fm|0)+1|0)-_fi|0);});break;case 2:return new F(function(){return _cp(B(_cB(_fq,_cc)),((_fn-_fm|0)+1|0)-_fi|0);});break;default:if(!(B(_bg(_fq))&1)){return new F(function(){return _cp(_fq,((_fn-_fm|0)+1|0)-_fi|0);});}else{return new F(function(){return _cp(B(_cB(_fq,_cc)),((_fn-_fm|0)+1|0)-_fi|0);});}}}else{return new F(function(){return _cp(_fj, -_fm);});}}}else{var _fr=B(_em(_fj))-_fm|0,_fs=function(_ft){var _fu=function(_fv,_fw){if(!B(_eF(B(_cU(_fw,_fi)),_fv))){return new F(function(){return _cY(_ft-_fi|0,_fv,_fw);});}else{return new F(function(){return _cY((_ft-_fi|0)+1|0,_fv,B(_cU(_fw,1)));});}};if(_ft>=_fi){if(_ft!=_fi){return new F(function(){return _fu(_fj,new T(function(){return B(_cU(_fk,_ft-_fi|0));}));});}else{return new F(function(){return _fu(_fj,_fk);});}}else{return new F(function(){return _fu(new T(function(){return B(_cU(_fj,_fi-_ft|0));}),_fk);});}};if(_fh>_fr){return new F(function(){return _fs(_fh);});}else{return new F(function(){return _fs(_fr);});}}},_fx=new T1(0,2147483647),_fy=new T(function(){return B(_cB(_fx,_dc));}),_fz=function(_fA){var _fB=E(_fA);if(!_fB._){var _fC=E(_fB.a);return (_fC==( -2147483648))?E(_fy):new T1(0, -_fC);}else{return new T1(1,I_negate(_fB.a));}},_fD=new T(function(){return 0/0;}),_fE=new T(function(){return  -1/0;}),_fF=new T(function(){return 1/0;}),_fG=0,_fH=function(_fI,_fJ){if(!B(_ct(_fJ,_cT))){if(!B(_ct(_fI,_cT))){if(!B(_dd(_fI,_cT))){return new F(function(){return _fg( -1021,53,_fI,_fJ);});}else{return  -B(_fg( -1021,53,B(_fz(_fI)),_fJ));}}else{return E(_fG);}}else{return (!B(_ct(_fI,_cT)))?(!B(_dd(_fI,_cT)))?E(_fF):E(_fE):E(_fD);}},_fK=function(_fL){var _fM=E(_fL);return new F(function(){return _fH(_fM.a,_fM.b);});},_fN=function(_fO){return 1/E(_fO);},_fP=function(_fQ){var _fR=E(_fQ);return (_fR!=0)?(_fR<=0)? -_fR:E(_fR):E(_fG);},_fS=function(_fT){var _fU=E(_fT);if(!_fU._){return _fU.a;}else{return new F(function(){return I_toNumber(_fU.a);});}},_fV=function(_fW){return new F(function(){return _fS(_fW);});},_fX=1,_fY= -1,_fZ=function(_g0){var _g1=E(_g0);return (_g1<=0)?(_g1>=0)?E(_g1):E(_fY):E(_fX);},_g2=function(_g3,_g4){return E(_g3)-E(_g4);},_g5=function(_g6){return  -E(_g6);},_g7=function(_g8,_g9){return E(_g8)+E(_g9);},_ga=function(_gb,_gc){return E(_gb)*E(_gc);},_gd={_:0,a:_g7,b:_g2,c:_ga,d:_g5,e:_fP,f:_fZ,g:_fV},_ge=function(_gf,_gg){return E(_gf)/E(_gg);},_gh=new T4(0,_gd,_ge,_fN,_fK),_gi=function(_gj){return new F(function(){return Math.acos(E(_gj));});},_gk=function(_gl){return new F(function(){return Math.asin(E(_gl));});},_gm=function(_gn){return new F(function(){return Math.atan(E(_gn));});},_go=function(_gp){return new F(function(){return Math.cos(E(_gp));});},_gq=function(_gr){return new F(function(){return cosh(E(_gr));});},_gs=function(_gt){return new F(function(){return Math.exp(E(_gt));});},_gu=function(_gv){return new F(function(){return Math.log(E(_gv));});},_gw=function(_gx,_gy){return new F(function(){return Math.pow(E(_gx),E(_gy));});},_gz=function(_gA){return new F(function(){return Math.sin(E(_gA));});},_gB=function(_gC){return new F(function(){return sinh(E(_gC));});},_gD=function(_gE){return new F(function(){return Math.sqrt(E(_gE));});},_gF=function(_gG){return new F(function(){return Math.tan(E(_gG));});},_gH=function(_gI){return new F(function(){return tanh(E(_gI));});},_gJ={_:0,a:_gh,b:_cb,c:_gs,d:_gu,e:_gD,f:_gw,g:_c8,h:_gz,i:_go,j:_gF,k:_gk,l:_gi,m:_gm,n:_gB,o:_gq,p:_gH,q:_c2,r:_bZ,s:_c5},_gK=0,_gL=function(_){return _gK;},_gM=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gN=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gO=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gP=function(_gQ,_gR,_gS,_){var _gT=__app1(E(_gN),_gS),_gU=__app2(E(_gO),_gS,E(_gQ)),_gV=B(A2(_gR,_gS,_)),_gW=__app1(E(_gM),_gS);return new F(function(){return _gL(_);});},_gX=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gY=function(_gZ,_h0,_h1,_h2,_){var _h3=__app1(E(_gN),_h2),_h4=__app3(E(_gX),_h2,E(_gZ),E(_h0)),_h5=B(A2(_h1,_h2,_)),_h6=__app1(E(_gM),_h2);return new F(function(){return _gL(_);});},_h7=function(_h8,_h9){return E(_h8)!=E(_h9);},_ha=function(_hb,_hc){return E(_hb)==E(_hc);},_hd=new T2(0,_ha,_h7),_he=function(_hf){return E(E(_hf).a);},_hg=function(_hh){return E(E(_hh).a);},_hi=function(_hj){return E(E(_hj).b);},_hk=function(_hl){return E(E(_hl).g);},_hm=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hn=0,_ho=3.3333333333333335,_hp=16.666666666666668,_hq=function(_hr){return E(E(_hr).b);},_hs=new T1(0,0),_ht=new T1(0,2),_hu=function(_hv){return E(E(_hv).i);},_hw=function(_hx,_hy,_hz,_hA,_hB,_hC,_hD,_hE){var _hF=new T(function(){var _hG=E(_hE);if(_hG<=31){return B(_4A(_hd,_hG,_hm));}else{if(_hG>=128){return B(_4A(_hd,_hG,_hm));}else{return true;}}}),_hH=new T(function(){if(E(_hA)==8){return new T2(0,new T(function(){return B(_fS(B(A2(_hu,_hy,_hC))))*28+20;}),new T(function(){return B(_fS(B(A2(_hu,_hz,_hD))))*20+8*(E(_hB)-1);}));}else{return new T2(0,new T(function(){return B(_fS(B(A2(_hu,_hy,_hC))))*28;}),new T(function(){return B(_fS(B(A2(_hu,_hz,_hD))))*20;}));}}),_hI=new T(function(){var _hJ=B(_he(_hx));if(!E(_hF)){return B(A2(_hk,B(_hg(_hJ)),_hs));}else{return B(A3(_hi,_hJ,new T(function(){return B(_hq(_hx));}),new T(function(){return B(A2(_hk,B(_hg(_hJ)),_ht));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hH).a);}),new T(function(){return E(E(_hH).b);})),new T2(0,new T(function(){if(!E(_hF)){return E(_hn);}else{return E(_ho);}}),new T(function(){if(!E(_hF)){return E(_hn);}else{return E(_hp);}})),_hI);},_hK=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hL=function(_hM,_hN,_hO){var _hP=new T(function(){return toJSStr(E(_hO));});return function(_hQ,_){var _hR=__app4(E(_hK),E(_hQ),E(_hP),E(_hM),E(_hN));return new F(function(){return _gL(_);});};},_hS=0,_hT=",",_hU="rgba(",_hV=new T(function(){return toJSStr(_S);}),_hW="rgb(",_hX=")",_hY=new T2(1,_hX,_S),_hZ=function(_i0){var _i1=E(_i0);if(!_i1._){var _i2=jsCat(new T2(1,_hW,new T2(1,new T(function(){return String(_i1.a);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.b);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.c);}),_hY)))))),E(_hV));return E(_i2);}else{var _i3=jsCat(new T2(1,_hU,new T2(1,new T(function(){return String(_i1.a);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.b);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.c);}),new T2(1,_hT,new T2(1,new T(function(){return String(_i1.d);}),_hY)))))))),E(_hV));return E(_i3);}},_i4="strokeStyle",_i5="fillStyle",_i6=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i7=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i8=function(_i9,_ia){var _ib=new T(function(){return B(_hZ(_i9));});return function(_ic,_){var _id=E(_ic),_ie=E(_i5),_if=E(_i6),_ig=__app2(_if,_id,_ie),_ih=E(_i4),_ii=__app2(_if,_id,_ih),_ij=E(_ib),_ik=E(_i7),_il=__app3(_ik,_id,_ie,_ij),_im=__app3(_ik,_id,_ih,_ij),_in=B(A2(_ia,_id,_)),_io=String(_ig),_ip=__app3(_ik,_id,_ie,_io),_iq=String(_ii),_ir=__app3(_ik,_id,_ih,_iq);return new F(function(){return _gL(_);});};},_is="font",_it=function(_iu,_iv){var _iw=new T(function(){return toJSStr(E(_iu));});return function(_ix,_){var _iy=E(_ix),_iz=E(_is),_iA=__app2(E(_i6),_iy,_iz),_iB=E(_i7),_iC=__app3(_iB,_iy,_iz,E(_iw)),_iD=B(A2(_iv,_iy,_)),_iE=String(_iA),_iF=__app3(_iB,_iy,_iz,_iE);return new F(function(){return _gL(_);});};},_iG=new T(function(){return B(unCStr("px IPAGothic"));}),_iH=function(_iI,_iJ,_iK,_iL,_iM,_iN,_iO,_){var _iP=new T(function(){var _iQ=new T(function(){var _iR=B(_hw(_gJ,_bY,_bY,_iK,_iL,_iM,_iN,_iO)),_iS=E(_iR.a),_iT=E(_iR.b);return new T5(0,_iS.a,_iS.b,_iT.a,_iT.b,_iR.c);}),_iU=new T(function(){var _iV=E(_iQ);return E(_iV.a)+E(_iV.c);}),_iW=new T(function(){var _iX=E(_iQ);return E(_iX.b)-E(_iX.d);}),_iY=new T(function(){return E(E(_iQ).e);}),_iZ=new T(function(){return B(_hL(_hS,_hS,new T2(1,_iO,_S)));}),_j0=function(_j1,_){return new F(function(){return _gP(_iY,_iZ,E(_j1),_);});};return B(_it(new T(function(){return B(_q(B(_A(0,E(_iK),_S)),_iG));},1),function(_j2,_){return new F(function(){return _gY(_iU,_iW,_j0,E(_j2),_);});}));});return new F(function(){return A(_i8,[_iJ,_iP,_iI,_]);});},_j3=new T3(0,153,255,255),_j4=new T2(1,_j3,_S),_j5=new T3(0,255,153,204),_j6=new T2(1,_j5,_j4),_j7=new T3(0,255,204,153),_j8=new T2(1,_j7,_j6),_j9=new T3(0,200,255,200),_ja=new T2(1,_j9,_j8),_jb=20,_jc=64,_jd=1,_je=2,_jf=8,_jg=function(_jh,_ji,_jj,_jk,_jl,_jm,_jn,_){while(1){var _jo=B((function(_jp,_jq,_jr,_js,_jt,_ju,_jv,_){var _jw=E(_jv);if(!_jw._){return _gK;}else{var _jx=_jw.b,_jy=E(_jw.a),_jz=E(_jy);switch(_jz){case 10:var _jA=_jp,_jB=_jq,_jC=_js,_jD=_js;_jh=_jA;_ji=_jB;_jj=0;_jk=_jC;_jl=new T(function(){return E(_jt)-1|0;});_jm=_jD;_jn=_jx;return __continue;case 123:return new F(function(){return _jE(_jp,_jq,_jr,_js,_jt,_ju,_jx,_);});break;case 65306:var _jF=new T(function(){return B(_6X(_ja,_jr));}),_jG=function(_jH,_jI,_jJ,_jK,_jL,_jM,_){while(1){var _jN=B((function(_jO,_jP,_jQ,_jR,_jS,_jT,_){var _jU=E(_jT);if(!_jU._){return _gK;}else{var _jV=_jU.b,_jW=E(_jU.a);if(E(_jW)==65306){var _jX=new T(function(){var _jY=E(_jS);if((_jY+1)*20<=E(_jq)-10){return new T2(0,_jR,_jY+1|0);}else{return new T2(0,new T(function(){return E(_jR)-1|0;}),_jP);}});return new F(function(){return _jg(_jO,_jq,_jr,_jP,new T(function(){return E(E(_jX).a);}),new T(function(){return E(E(_jX).b);}),_jV,_);});}else{var _jZ=E(_jO),_k0=B(_iH(_jZ.a,_jF,_jf,_jQ,_jR,_jS,_jW,_)),_k1=_jP,_k2=_jQ+1,_k3=_jR,_k4=_jS;_jH=_jZ;_jI=_k1;_jJ=_k2;_jK=_k3;_jL=_k4;_jM=_jV;return __continue;}}})(_jH,_jI,_jJ,_jK,_jL,_jM,_));if(_jN!=__continue){return _jN;}}};return new F(function(){return _jG(_jp,_js,0,new T(function(){if(E(_js)!=E(_ju)){return E(_jt);}else{return E(_jt)+1|0;}}),new T(function(){var _k5=E(_ju);if(E(_js)!=_k5){return _k5-1|0;}else{var _k6=(E(_jq)-10)/20,_k7=_k6&4294967295;if(_k6>=_k7){return _k7;}else{return _k7-1|0;}}}),_jx,_);});break;default:var _k8=function(_k9,_ka){var _kb=new T(function(){switch(E(_jz)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return _jr;}}),_kc=new T(function(){var _kd=E(_ju);if((_kd+1)*20<=E(_jq)-10){return new T2(0,_jt,_kd+1|0);}else{return new T2(0,new T(function(){return E(_jt)-1|0;}),_js);}});if(E(_k9)==64){return new F(function(){return _ke(_jp,_jq,_kb,_js,new T(function(){return E(E(_kc).a);}),new T(function(){return E(E(_kc).b);}),_jx,_);});}else{var _kf=E(_jp),_kg=B(_iH(_kf.a,new T(function(){return B(_6X(_ja,E(_kb)));},1),_jb,_hS,_jt,_ju,_ka,_));return new F(function(){return _ke(_kf,_jq,_kb,_js,new T(function(){return E(E(_kc).a);}),new T(function(){return E(E(_kc).b);}),_jx,_);});}},_kh=E(_jz);switch(_kh){case 42:return new F(function(){return _k8(64,_jc);});break;case 12289:return new F(function(){return _k8(64,_jc);});break;case 12290:return new F(function(){return _k8(64,_jc);});break;default:return new F(function(){return _k8(_kh,_jy);});}}}})(_jh,_ji,_jj,_jk,_jl,_jm,_jn,_));if(_jo!=__continue){return _jo;}}},_ke=function(_ki,_kj,_kk,_kl,_km,_kn,_ko,_){var _kp=E(_ko);if(!_kp._){return _gK;}else{var _kq=_kp.b,_kr=E(_kp.a),_ks=E(_kr);switch(_ks){case 10:return new F(function(){return _jg(_ki,_kj,0,_kl,new T(function(){return E(_km)-1|0;}),_kl,_kq,_);});break;case 123:return new F(function(){return _jE(_ki,_kj,_kk,_kl,_km,_kn,_kq,_);});break;case 65306:var _kt=new T(function(){return B(_6X(_ja,E(_kk)));}),_ku=function(_kv,_kw,_kx,_ky,_kz,_kA,_){while(1){var _kB=B((function(_kC,_kD,_kE,_kF,_kG,_kH,_){var _kI=E(_kH);if(!_kI._){return _gK;}else{var _kJ=_kI.b,_kK=E(_kI.a);if(E(_kK)==65306){var _kL=new T(function(){var _kM=E(_kG);if((_kM+1)*20<=E(_kj)-10){return new T2(0,_kF,_kM+1|0);}else{return new T2(0,new T(function(){return E(_kF)-1|0;}),_kD);}});return new F(function(){return _ke(_kC,_kj,_kk,_kD,new T(function(){return E(E(_kL).a);}),new T(function(){return E(E(_kL).b);}),_kJ,_);});}else{var _kN=E(_kC),_kO=B(_iH(_kN.a,_kt,_jf,_kE,_kF,_kG,_kK,_)),_kP=_kD,_kQ=_kE+1,_kR=_kF,_kS=_kG;_kv=_kN;_kw=_kP;_kx=_kQ;_ky=_kR;_kz=_kS;_kA=_kJ;return __continue;}}})(_kv,_kw,_kx,_ky,_kz,_kA,_));if(_kB!=__continue){return _kB;}}};return new F(function(){return _ku(_ki,_kl,0,new T(function(){if(E(_kl)!=E(_kn)){return E(_km);}else{return E(_km)+1|0;}}),new T(function(){var _kT=E(_kn);if(E(_kl)!=_kT){return _kT-1|0;}else{var _kU=(E(_kj)-10)/20,_kV=_kU&4294967295;if(_kU>=_kV){return _kV;}else{return _kV-1|0;}}}),_kq,_);});break;default:var _kW=function(_kX,_kY){var _kZ=new T(function(){switch(E(_ks)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return E(_kk);}}),_l0=new T(function(){var _l1=E(_kn);if((_l1+1)*20<=E(_kj)-10){return new T2(0,_km,_l1+1|0);}else{return new T2(0,new T(function(){return E(_km)-1|0;}),_kl);}});if(E(_kX)==64){return new F(function(){return _ke(_ki,_kj,_kZ,_kl,new T(function(){return E(E(_l0).a);}),new T(function(){return E(E(_l0).b);}),_kq,_);});}else{var _l2=E(_ki),_l3=B(_iH(_l2.a,new T(function(){return B(_6X(_ja,E(_kZ)));},1),_jb,_hS,_km,_kn,_kY,_));return new F(function(){return _ke(_l2,_kj,_kZ,_kl,new T(function(){return E(E(_l0).a);}),new T(function(){return E(E(_l0).b);}),_kq,_);});}},_l4=E(_ks);switch(_l4){case 42:return new F(function(){return _kW(64,_jc);});break;case 12289:return new F(function(){return _kW(64,_jc);});break;case 12290:return new F(function(){return _kW(64,_jc);});break;default:return new F(function(){return _kW(_l4,_kr);});}}}},_jE=function(_l5,_l6,_l7,_l8,_l9,_la,_lb,_){while(1){var _lc=B((function(_ld,_le,_lf,_lg,_lh,_li,_lj,_){var _lk=E(_lj);if(!_lk._){return _gK;}else{var _ll=_lk.b;if(E(_lk.a)==125){var _lm=new T(function(){var _ln=E(_li);if((_ln+1)*20<=E(_le)-10){return new T2(0,_lh,_ln+1|0);}else{return new T2(0,new T(function(){return E(_lh)-1|0;}),_lg);}});return new F(function(){return _ke(_ld,_le,_lf,_lg,new T(function(){return E(E(_lm).a);}),new T(function(){return E(E(_lm).b);}),_ll,_);});}else{var _lo=_ld,_lp=_le,_lq=_lf,_lr=_lg,_ls=_lh,_lt=_li;_l5=_lo;_l6=_lp;_l7=_lq;_l8=_lr;_l9=_ls;_la=_lt;_lb=_ll;return __continue;}}})(_l5,_l6,_l7,_l8,_l9,_la,_lb,_));if(_lc!=__continue){return _lc;}}},_lu=function(_lv,_lw,_lx,_ly,_lz,_lA,_lB,_lC,_){while(1){var _lD=B((function(_lE,_lF,_lG,_lH,_lI,_lJ,_lK,_lL,_){var _lM=E(_lL);if(!_lM._){return _gK;}else{var _lN=_lM.b,_lO=E(_lM.a),_lP=E(_lO);switch(_lP){case 10:var _lQ=_lE,_lR=_lF,_lS=_lG,_lT=_lI,_lU=_lI;_lv=_lQ;_lw=_lR;_lx=_lS;_ly=0;_lz=_lT;_lA=new T(function(){return E(_lJ)-1|0;});_lB=_lU;_lC=_lN;return __continue;case 123:return new F(function(){return _jE(new T2(0,_lE,_lF),_lG,_lH,_lI,_lJ,_lK,_lN,_);});break;case 65306:var _lV=new T(function(){return B(_6X(_ja,_lH));}),_lW=function(_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_){while(1){var _m4=B((function(_m5,_m6,_m7,_m8,_m9,_ma,_mb,_){var _mc=E(_mb);if(!_mc._){return _gK;}else{var _md=_mc.b,_me=E(_mc.a);if(E(_me)==65306){var _mf=new T(function(){var _mg=E(_ma);if((_mg+1)*20<=E(_lG)-10){return new T2(0,_m9,_mg+1|0);}else{return new T2(0,new T(function(){return E(_m9)-1|0;}),_m7);}});return new F(function(){return _lu(_m5,_m6,_lG,_lH,_m7,new T(function(){return E(E(_mf).a);}),new T(function(){return E(E(_mf).b);}),_md,_);});}else{var _mh=B(_iH(_m5,_lV,_jf,_m8,_m9,_ma,_me,_)),_mi=_m5,_mj=_m6,_mk=_m7,_ml=_m8+1,_mm=_m9,_mn=_ma;_lX=_mi;_lY=_mj;_lZ=_mk;_m0=_ml;_m1=_mm;_m2=_mn;_m3=_md;return __continue;}}})(_lX,_lY,_lZ,_m0,_m1,_m2,_m3,_));if(_m4!=__continue){return _m4;}}};return new F(function(){return _lW(_lE,_lF,_lI,0,new T(function(){if(E(_lI)!=E(_lK)){return E(_lJ);}else{return E(_lJ)+1|0;}}),new T(function(){var _mo=E(_lK);if(E(_lI)!=_mo){return _mo-1|0;}else{var _mp=(E(_lG)-10)/20,_mq=_mp&4294967295;if(_mp>=_mq){return _mq;}else{return _mq-1|0;}}}),_lN,_);});break;default:var _mr=function(_ms,_mt){var _mu=new T(function(){switch(E(_lP)){case 42:return E(_je);break;case 12300:return E(_jd);break;default:return _lH;}}),_mv=new T(function(){var _mw=E(_lK);if((_mw+1)*20<=E(_lG)-10){return new T2(0,_lJ,_mw+1|0);}else{return new T2(0,new T(function(){return E(_lJ)-1|0;}),_lI);}});if(E(_ms)==64){return new F(function(){return _ke(new T2(0,_lE,_lF),_lG,_mu,_lI,new T(function(){return E(E(_mv).a);}),new T(function(){return E(E(_mv).b);}),_lN,_);});}else{var _mx=B(_iH(_lE,new T(function(){return B(_6X(_ja,E(_mu)));},1),_jb,_hS,_lJ,_lK,_mt,_));return new F(function(){return _ke(new T2(0,_lE,_lF),_lG,_mu,_lI,new T(function(){return E(E(_mv).a);}),new T(function(){return E(E(_mv).b);}),_lN,_);});}},_my=E(_lP);switch(_my){case 42:return new F(function(){return _mr(64,_jc);});break;case 12289:return new F(function(){return _mr(64,_jc);});break;case 12290:return new F(function(){return _mr(64,_jc);});break;default:return new F(function(){return _mr(_my,_lO);});}}}})(_lv,_lw,_lx,_ly,_lz,_lA,_lB,_lC,_));if(_lD!=__continue){return _lD;}}},_mz=function(_mA,_mB){while(1){var _mC=E(_mA);if(!_mC._){return E(_mB);}else{var _mD=_mB+1|0;_mA=_mC.b;_mB=_mD;continue;}}},_mE=function(_mF){return E(E(_mF).a);},_mG=function(_mH,_mI){var _mJ=E(_mI),_mK=new T(function(){var _mL=B(_hg(_mH)),_mM=B(_mG(_mH,B(A3(_mE,_mL,_mJ,new T(function(){return B(A2(_hk,_mL,_b1));})))));return new T2(1,_mM.a,_mM.b);});return new T2(0,_mJ,_mK);},_mN=new T(function(){var _mO=B(_mG(_gh,_hS));return new T2(1,_mO.a,_mO.b);}),_mP=new T(function(){return B(unCStr("px Courier"));}),_mQ=new T(function(){return B(_A(0,20,_S));}),_mR=new T(function(){return B(_q(_mQ,_mP));}),_mS=function(_mT,_){return _gK;},_mU=function(_mV,_mW,_mX,_mY,_mZ){var _n0=new T(function(){return E(_mX)*16;}),_n1=new T(function(){return E(_mY)*20;}),_n2=function(_n3,_n4){var _n5=E(_n3);if(!_n5._){return E(_mS);}else{var _n6=E(_n4);if(!_n6._){return E(_mS);}else{var _n7=new T(function(){return B(_n2(_n5.b,_n6.b));}),_n8=new T(function(){var _n9=new T(function(){var _na=new T(function(){return B(_hL(new T(function(){return E(_n0)+16*E(_n6.a);}),_n1,new T2(1,_n5.a,_S)));});return B(_it(_mR,_na));});return B(_i8(_mW,_n9));});return function(_nb,_){var _nc=B(A2(_n8,_nb,_));return new F(function(){return A2(_n7,_nb,_);});};}}};return new F(function(){return A3(_n2,_mZ,_mN,_mV);});},_nd=45,_ne=new T(function(){return B(unCStr("-"));}),_nf=new T2(1,_nd,_ne),_ng=function(_nh){var _ni=E(_nh);return (_ni==1)?E(_nf):new T2(1,_nd,new T(function(){return B(_ng(_ni-1|0));}));},_nj=new T(function(){return B(unCStr(": empty list"));}),_nk=function(_nl){return new F(function(){return err(B(_q(_6M,new T(function(){return B(_q(_nl,_nj));},1))));});},_nm=new T(function(){return B(unCStr("head"));}),_nn=new T(function(){return B(_nk(_nm));}),_no=new T(function(){return eval("(function(e){e.width = e.width;})");}),_np=new T(function(){return B(_hL(_hS,_hS,_S));}),_nq=32,_nr=new T(function(){return B(unCStr("|"));}),_ns=function(_nt){var _nu=E(_nt);return (_nu._==0)?E(_nr):new T2(1,new T(function(){var _nv=E(_nu.a);switch(E(_nv.b)){case 7:return E(_nq);break;case 8:return E(_nq);break;default:return E(_nv.a);}}),new T(function(){return B(_ns(_nu.b));}));},_nw=function(_nx,_ny,_nz,_nA,_nB,_){var _nC=__app1(E(_no),_ny),_nD=B(A2(_np,_nx,_)),_nE=B(unAppCStr("-",new T(function(){var _nF=E(_nB);if(!_nF._){return E(_nn);}else{var _nG=B(_mz(_nF.a,0));if(0>=_nG){return E(_ne);}else{return B(_ng(_nG));}}}))),_nH=B(A(_mU,[_nx,_j9,_nz,_nA,_nE,_])),_nI=function(_nJ,_nK,_nL,_){while(1){var _nM=B((function(_nN,_nO,_nP,_){var _nQ=E(_nP);if(!_nQ._){return new F(function(){return A(_mU,[_nx,_j9,_nN,_nO,_nE,_]);});}else{var _nR=B(A(_mU,[_nx,_j9,_nN,_nO,B(unAppCStr("|",new T(function(){return B(_ns(_nQ.a));}))),_])),_nS=_nN;_nJ=_nS;_nK=new T(function(){return E(_nO)+1|0;});_nL=_nQ.b;return __continue;}})(_nJ,_nK,_nL,_));if(_nM!=__continue){return _nM;}}};return new F(function(){return _nI(_nz,new T(function(){return E(_nA)+1|0;}),_nB,_);});},_nT=new T(function(){return B(_6X(_ja,1));}),_nU=new T(function(){return B(_6X(_ja,2));}),_nV=2,_nW=function(_nX,_nY,_nZ,_o0,_){var _o1=__app1(E(_no),_nY),_o2=B(A2(_np,_nX,_)),_o3=E(_o0),_o4=E(_o3.b).a,_o5=E(_o3.a),_o6=_o5.a;if(!E(E(_o3.u).h)){return _gK;}else{var _o7=B(_nw(_nX,_nY,new T(function(){return E(_nZ)-E(_o4)|0;}),_nV,_o5.b,_));return new F(function(){return A(_mU,[_nX,new T(function(){if(E(_o5.e)==32){return E(_nT);}else{return E(_nU);}}),new T(function(){return ((E(E(_o6).a)+1|0)+E(_nZ)|0)-E(_o4)|0;},1),new T(function(){return (E(E(_o6).b)+2|0)+1|0;},1),new T2(1,_o5.d,_S),_]);});}},_o8=function(_o9){return E(E(_o9).a);},_oa=function(_ob){return E(E(_ob).a);},_oc=function(_od,_oe){while(1){var _of=E(_od);if(!_of._){return E(_oe);}else{_od=_of.b;_oe=_of.a;continue;}}},_og=function(_oh,_oi,_oj){return new F(function(){return _oc(_oi,_oh);});},_ok=new T1(0,2),_ol=function(_om,_on){while(1){var _oo=E(_om);if(!_oo._){var _op=_oo.a,_oq=E(_on);if(!_oq._){var _or=_oq.a;if(!(imul(_op,_or)|0)){return new T1(0,imul(_op,_or)|0);}else{_om=new T1(1,I_fromInt(_op));_on=new T1(1,I_fromInt(_or));continue;}}else{_om=new T1(1,I_fromInt(_op));_on=_oq;continue;}}else{var _os=E(_on);if(!_os._){_om=_oo;_on=new T1(1,I_fromInt(_os.a));continue;}else{return new T1(1,I_mul(_oo.a,_os.a));}}}},_ot=function(_ou,_ov,_ow){while(1){if(!(_ov%2)){var _ox=B(_ol(_ou,_ou)),_oy=quot(_ov,2);_ou=_ox;_ov=_oy;continue;}else{var _oz=E(_ov);if(_oz==1){return new F(function(){return _ol(_ou,_ow);});}else{var _ox=B(_ol(_ou,_ou)),_oA=B(_ol(_ou,_ow));_ou=_ox;_ov=quot(_oz-1|0,2);_ow=_oA;continue;}}}},_oB=function(_oC,_oD){while(1){if(!(_oD%2)){var _oE=B(_ol(_oC,_oC)),_oF=quot(_oD,2);_oC=_oE;_oD=_oF;continue;}else{var _oG=E(_oD);if(_oG==1){return E(_oC);}else{return new F(function(){return _ot(B(_ol(_oC,_oC)),quot(_oG-1|0,2),_oC);});}}}},_oH=function(_oI){return E(E(_oI).c);},_oJ=function(_oK){return E(E(_oK).a);},_oL=function(_oM){return E(E(_oM).b);},_oN=function(_oO){return E(E(_oO).b);},_oP=function(_oQ){return E(E(_oQ).c);},_oR=new T1(0,0),_oS=new T1(0,2),_oT=function(_oU){return E(E(_oU).d);},_oV=function(_oW,_oX){var _oY=B(_o8(_oW)),_oZ=new T(function(){return B(_oa(_oY));}),_p0=new T(function(){return B(A3(_oT,_oW,_oX,new T(function(){return B(A2(_hk,_oZ,_oS));})));});return new F(function(){return A3(_4y,B(_oJ(B(_oL(_oY)))),_p0,new T(function(){return B(A2(_hk,_oZ,_oR));}));});},_p1=new T(function(){return B(unCStr("Negative exponent"));}),_p2=new T(function(){return B(err(_p1));}),_p3=function(_p4){return E(E(_p4).c);},_p5=function(_p6,_p7,_p8,_p9){var _pa=B(_o8(_p7)),_pb=new T(function(){return B(_oa(_pa));}),_pc=B(_oL(_pa));if(!B(A3(_oP,_pc,_p9,new T(function(){return B(A2(_hk,_pb,_oR));})))){if(!B(A3(_4y,B(_oJ(_pc)),_p9,new T(function(){return B(A2(_hk,_pb,_oR));})))){var _pd=new T(function(){return B(A2(_hk,_pb,_oS));}),_pe=new T(function(){return B(A2(_hk,_pb,_b1));}),_pf=B(_oJ(_pc)),_pg=function(_ph,_pi,_pj){while(1){var _pk=B((function(_pl,_pm,_pn){if(!B(_oV(_p7,_pm))){if(!B(A3(_4y,_pf,_pm,_pe))){var _po=new T(function(){return B(A3(_p3,_p7,new T(function(){return B(A3(_oN,_pb,_pm,_pe));}),_pd));});_ph=new T(function(){return B(A3(_oH,_p6,_pl,_pl));});_pi=_po;_pj=new T(function(){return B(A3(_oH,_p6,_pl,_pn));});return __continue;}else{return new F(function(){return A3(_oH,_p6,_pl,_pn);});}}else{var _pp=_pn;_ph=new T(function(){return B(A3(_oH,_p6,_pl,_pl));});_pi=new T(function(){return B(A3(_p3,_p7,_pm,_pd));});_pj=_pp;return __continue;}})(_ph,_pi,_pj));if(_pk!=__continue){return _pk;}}},_pq=function(_pr,_ps){while(1){var _pt=B((function(_pu,_pv){if(!B(_oV(_p7,_pv))){if(!B(A3(_4y,_pf,_pv,_pe))){var _pw=new T(function(){return B(A3(_p3,_p7,new T(function(){return B(A3(_oN,_pb,_pv,_pe));}),_pd));});return new F(function(){return _pg(new T(function(){return B(A3(_oH,_p6,_pu,_pu));}),_pw,_pu);});}else{return E(_pu);}}else{_pr=new T(function(){return B(A3(_oH,_p6,_pu,_pu));});_ps=new T(function(){return B(A3(_p3,_p7,_pv,_pd));});return __continue;}})(_pr,_ps));if(_pt!=__continue){return _pt;}}};return new F(function(){return _pq(_p8,_p9);});}else{return new F(function(){return A2(_hk,_p6,_b1);});}}else{return E(_p2);}},_px=new T(function(){return B(err(_p1));}),_py=function(_pz){var _pA=I_decodeDouble(_pz);return new T2(0,new T1(1,_pA.b),_pA.a);},_pB=function(_pC,_pD){var _pE=B(_py(_pD)),_pF=_pE.a,_pG=_pE.b,_pH=new T(function(){return B(_oa(new T(function(){return B(_o8(_pC));})));});if(_pG<0){var _pI= -_pG;if(_pI>=0){var _pJ=E(_pI);if(!_pJ){var _pK=E(_b1);}else{var _pK=B(_oB(_ok,_pJ));}if(!B(_ct(_pK,_cT))){var _pL=B(_cK(_pF,_pK));return new T2(0,new T(function(){return B(A2(_hk,_pH,_pL.a));}),new T(function(){return B(_cp(_pL.b,_pG));}));}else{return E(_a0);}}else{return E(_px);}}else{var _pM=new T(function(){var _pN=new T(function(){return B(_p5(_pH,_bY,new T(function(){return B(A2(_hk,_pH,_ok));}),_pG));});return B(A3(_oH,_pH,new T(function(){return B(A2(_hk,_pH,_pF));}),_pN));});return new T2(0,_pM,_fG);}},_pO=function(_pP,_pQ){while(1){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.b,_pT=E(_pP);if(_pT==1){return E(_pS);}else{_pP=_pT-1|0;_pQ=_pS;continue;}}}},_pU=function(_pV,_pW){var _pX=E(_pW);if(!_pX._){return __Z;}else{var _pY=_pX.a,_pZ=E(_pV);return (_pZ==1)?new T2(1,_pY,_S):new T2(1,_pY,new T(function(){return B(_pU(_pZ-1|0,_pX.b));}));}},_q0=function(_q1,_q2,_q3,_q4){while(1){if(B(_6X(new T2(1,_q3,_q4),_q2))!=_q1){var _q5=_q2+1|0;_q2=_q5;continue;}else{if(0>=_q2){return __Z;}else{return new F(function(){return _pU(_q2,new T2(1,_q3,_q4));});}}}},_q6=function(_q7,_q8,_q9){var _qa=E(_q9);if(!_qa._){return __Z;}else{var _qb=E(_q7);if(B(_6X(_qa,_q8))!=_qb){return new F(function(){return _q0(_qb,_q8+1|0,_qa.a,_qa.b);});}else{if(0>=_q8){return __Z;}else{return new F(function(){return _pU(_q8,_qa);});}}}},_qc=function(_qd,_qe,_qf){var _qg=_qe+1|0;if(_qg>0){return new F(function(){return _pO(_qg,B(_q6(_qd,_qg,_qf)));});}else{return new F(function(){return _q6(_qd,_qg,_qf);});}},_qh=function(_qi,_qj){return (!B(_6f(_qi,_qj)))?true:false;},_qk=new T2(0,_6f,_qh),_ql=0,_qm=new T(function(){return B(_ed("Event.hs:(81,1)-(82,68)|function addEvent"));}),_qn=function(_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF,_qG,_qH,_qI,_qJ,_qK){while(1){var _qL=E(_qo);if(!_qL._){return {_:0,a:_qp,b:_qq,c:_qr,d:_qs,e:_qt,f:_qu,g:_qv,h:_qw,i:_qx,j:_qy,k:_qz,l:_qA,m:_qB,n:_qC,o:_qD,p:_qE,q:_qF,r:_qG,s:_qH,t:_qI,u:_qJ,v:_qK};}else{var _qM=E(_qL.b);if(!_qM._){return E(_qm);}else{var _qN=new T2(1,new T2(0,_qL.a,_qM.a),_qt),_qO=new T2(1,_ql,_qu);_qo=_qM.b;_qt=_qN;_qu=_qO;continue;}}}},_qP=function(_qQ,_qR,_qS){var _qT=E(_qS);if(!_qT._){return __Z;}else{var _qU=_qT.a,_qV=_qT.b;return (!B(A2(_qQ,_qR,_qU)))?new T2(1,_qU,new T(function(){return B(_qP(_qQ,_qR,_qV));})):E(_qV);}},_qW=function(_qX,_qY){while(1){var _qZ=E(_qX);if(!_qZ._){return (E(_qY)._==0)?true:false;}else{var _r0=E(_qY);if(!_r0._){return false;}else{if(E(_qZ.a)!=E(_r0.a)){return false;}else{_qX=_qZ.b;_qY=_r0.b;continue;}}}}},_r1=function(_r2,_r3){while(1){var _r4=E(_r2);if(!_r4._){return (E(_r3)._==0)?true:false;}else{var _r5=E(_r3);if(!_r5._){return false;}else{if(!B(_6f(_r4.a,_r5.a))){return false;}else{_r2=_r4.b;_r3=_r5.b;continue;}}}}},_r6=function(_r7,_r8){switch(E(_r7)){case 0:return (E(_r8)==0)?true:false;case 1:return (E(_r8)==1)?true:false;case 2:return (E(_r8)==2)?true:false;case 3:return (E(_r8)==3)?true:false;case 4:return (E(_r8)==4)?true:false;case 5:return (E(_r8)==5)?true:false;case 6:return (E(_r8)==6)?true:false;case 7:return (E(_r8)==7)?true:false;default:return (E(_r8)==8)?true:false;}},_r9=function(_ra,_rb,_rc,_rd){if(_ra!=_rc){return false;}else{return new F(function(){return _r6(_rb,_rd);});}},_re=function(_rf,_rg){var _rh=E(_rf),_ri=E(_rg);return new F(function(){return _r9(E(_rh.a),_rh.b,E(_ri.a),_ri.b);});},_rj=function(_rk,_rl,_rm,_rn){if(_rk!=_rm){return true;}else{switch(E(_rl)){case 0:return (E(_rn)==0)?false:true;case 1:return (E(_rn)==1)?false:true;case 2:return (E(_rn)==2)?false:true;case 3:return (E(_rn)==3)?false:true;case 4:return (E(_rn)==4)?false:true;case 5:return (E(_rn)==5)?false:true;case 6:return (E(_rn)==6)?false:true;case 7:return (E(_rn)==7)?false:true;default:return (E(_rn)==8)?false:true;}}},_ro=function(_rp,_rq){var _rr=E(_rp),_rs=E(_rq);return new F(function(){return _rj(E(_rr.a),_rr.b,E(_rs.a),_rs.b);});},_rt=new T2(0,_re,_ro),_ru=0,_rv=function(_rw,_rx){var _ry=E(_rx);if(!_ry._){return 0;}else{var _rz=_ry.b,_rA=E(_rw),_rB=E(_ry.a),_rC=_rB.b;if(E(_rA.a)!=E(_rB.a)){return 1+B(_rv(_rA,_rz))|0;}else{switch(E(_rA.b)){case 0:return (E(_rC)==0)?0:1+B(_rv(_rA,_rz))|0;case 1:return (E(_rC)==1)?0:1+B(_rv(_rA,_rz))|0;case 2:return (E(_rC)==2)?0:1+B(_rv(_rA,_rz))|0;case 3:return (E(_rC)==3)?0:1+B(_rv(_rA,_rz))|0;case 4:return (E(_rC)==4)?0:1+B(_rv(_rA,_rz))|0;case 5:return (E(_rC)==5)?0:1+B(_rv(_rA,_rz))|0;case 6:return (E(_rC)==6)?0:1+B(_rv(_rA,_rz))|0;case 7:return (E(_rC)==7)?0:1+B(_rv(_rA,_rz))|0;default:return (E(_rC)==8)?0:1+B(_rv(_rA,_rz))|0;}}}},_rD=function(_rE,_rF){return new F(function(){return _rv(_rE,_rF);});},_rG=function(_rH,_rI){var _rJ=E(_rI);if(!_rJ._){return new T2(0,_ru,_ru);}else{var _rK=_rJ.a,_rL=_rJ.b;return (!B(_4A(_rt,_rH,_rK)))?new T2(0,new T(function(){return E(B(_rG(_rH,_rL)).a);}),new T(function(){return 1+E(B(_rG(_rH,_rL)).b)|0;})):new T2(0,new T(function(){return B(_rD(_rH,_rK));}),_ru);}},_rM=function(_rN,_rO){while(1){var _rP=E(_rO);if(!_rP._){return __Z;}else{var _rQ=_rP.b,_rR=E(_rN);if(_rR==1){return E(_rQ);}else{_rN=_rR-1|0;_rO=_rQ;continue;}}}},_rS=new T(function(){return B(unCStr("getch"));}),_rT=new T(function(){return B(unCStr("=="));}),_rU=new T(function(){return B(unCStr("&&"));}),_rV=new T(function(){return B(unCStr("||"));}),_rW=new T(function(){return B(unCStr("getpos"));}),_rX=new T(function(){return B(unCStr("ch"));}),_rY=new T(function(){return B(unCStr("tp"));}),_rZ=new T2(1,_rY,_S),_s0=new T2(1,_rX,_rZ),_s1=new T2(0,_rW,_s0),_s2=new T(function(){return B(unCStr("a"));}),_s3=new T(function(){return B(unCStr("b"));}),_s4=new T2(1,_s3,_S),_s5=new T2(1,_s2,_s4),_s6=new T2(0,_rT,_s5),_s7=new T2(0,_rU,_s5),_s8=new T2(0,_rV,_s5),_s9=new T2(1,_s8,_S),_sa=new T2(1,_s7,_s9),_sb=new T2(1,_s6,_sa),_sc=new T2(1,_s1,_sb),_sd=new T(function(){return B(unCStr("p"));}),_se=new T(function(){return B(unCStr("q"));}),_sf=new T2(1,_se,_S),_sg=new T2(1,_sd,_sf),_sh=new T2(0,_rS,_sg),_si=new T2(1,_sh,_sc),_sj=new T(function(){return B(unCStr("foldr1"));}),_sk=new T(function(){return B(_nk(_sj));}),_sl=function(_sm,_sn){var _so=E(_sn);if(!_so._){return E(_sk);}else{var _sp=_so.a,_sq=E(_so.b);if(!_sq._){return E(_sp);}else{return new F(function(){return A2(_sm,_sp,new T(function(){return B(_sl(_sm,_sq));}));});}}},_sr=function(_ss){return E(E(_ss).a);},_st=function(_su,_sv,_sw){while(1){var _sx=E(_sw);if(!_sx._){return __Z;}else{var _sy=E(_sx.a);if(!B(A3(_4y,_su,_sv,_sy.a))){_sw=_sx.b;continue;}else{return new T1(1,_sy.b);}}}},_sz=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sA=new T(function(){return B(err(_sz));}),_sB=new T(function(){return B(unCStr("T"));}),_sC=new T(function(){return B(unCStr("F"));}),_sD=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_sE=new T(function(){return B(err(_sD));}),_sF=new T(function(){return B(unCStr("empty"));}),_sG=new T2(1,_sF,_S),_sH=new T(function(){return B(_ed("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sI=function(_sJ,_sK){while(1){var _sL=B((function(_sM,_sN){var _sO=E(_sM);switch(_sO._){case 0:var _sP=E(_sN);if(!_sP._){return __Z;}else{_sJ=B(A1(_sO.a,_sP.a));_sK=_sP.b;return __continue;}break;case 1:var _sQ=B(A1(_sO.a,_sN)),_sR=_sN;_sJ=_sQ;_sK=_sR;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sO.a,_sN),new T(function(){return B(_sI(_sO.b,_sN));}));default:return E(_sO.a);}})(_sJ,_sK));if(_sL!=__continue){return _sL;}}},_sS=function(_sT,_sU){var _sV=function(_sW){var _sX=E(_sU);if(_sX._==3){return new T2(3,_sX.a,new T(function(){return B(_sS(_sT,_sX.b));}));}else{var _sY=E(_sT);if(_sY._==2){return E(_sX);}else{var _sZ=E(_sX);if(_sZ._==2){return E(_sY);}else{var _t0=function(_t1){var _t2=E(_sZ);if(_t2._==4){var _t3=function(_t4){return new T1(4,new T(function(){return B(_q(B(_sI(_sY,_t4)),_t2.a));}));};return new T1(1,_t3);}else{var _t5=E(_sY);if(_t5._==1){var _t6=_t5.a,_t7=E(_t2);if(!_t7._){return new T1(1,function(_t8){return new F(function(){return _sS(B(A1(_t6,_t8)),_t7);});});}else{var _t9=function(_ta){return new F(function(){return _sS(B(A1(_t6,_ta)),new T(function(){return B(A1(_t7.a,_ta));}));});};return new T1(1,_t9);}}else{var _tb=E(_t2);if(!_tb._){return E(_sH);}else{var _tc=function(_td){return new F(function(){return _sS(_t5,new T(function(){return B(A1(_tb.a,_td));}));});};return new T1(1,_tc);}}}},_te=E(_sY);switch(_te._){case 1:var _tf=E(_sZ);if(_tf._==4){var _tg=function(_th){return new T1(4,new T(function(){return B(_q(B(_sI(B(A1(_te.a,_th)),_th)),_tf.a));}));};return new T1(1,_tg);}else{return new F(function(){return _t0(_);});}break;case 4:var _ti=_te.a,_tj=E(_sZ);switch(_tj._){case 0:var _tk=function(_tl){var _tm=new T(function(){return B(_q(_ti,new T(function(){return B(_sI(_tj,_tl));},1)));});return new T1(4,_tm);};return new T1(1,_tk);case 1:var _tn=function(_to){var _tp=new T(function(){return B(_q(_ti,new T(function(){return B(_sI(B(A1(_tj.a,_to)),_to));},1)));});return new T1(4,_tp);};return new T1(1,_tn);default:return new T1(4,new T(function(){return B(_q(_ti,_tj.a));}));}break;default:return new F(function(){return _t0(_);});}}}}},_tq=E(_sT);switch(_tq._){case 0:var _tr=E(_sU);if(!_tr._){var _ts=function(_tt){return new F(function(){return _sS(B(A1(_tq.a,_tt)),new T(function(){return B(A1(_tr.a,_tt));}));});};return new T1(0,_ts);}else{return new F(function(){return _sV(_);});}break;case 3:return new T2(3,_tq.a,new T(function(){return B(_sS(_tq.b,_sU));}));default:return new F(function(){return _sV(_);});}},_tu=new T(function(){return B(unCStr("("));}),_tv=new T(function(){return B(unCStr(")"));}),_tw=function(_tx,_ty){var _tz=E(_tx);switch(_tz._){case 0:return new T1(0,function(_tA){return new F(function(){return _tw(B(A1(_tz.a,_tA)),_ty);});});case 1:return new T1(1,function(_tB){return new F(function(){return _tw(B(A1(_tz.a,_tB)),_ty);});});case 2:return new T0(2);case 3:return new F(function(){return _sS(B(A1(_ty,_tz.a)),new T(function(){return B(_tw(_tz.b,_ty));}));});break;default:var _tC=function(_tD){var _tE=E(_tD);if(!_tE._){return __Z;}else{var _tF=E(_tE.a);return new F(function(){return _q(B(_sI(B(A1(_ty,_tF.a)),_tF.b)),new T(function(){return B(_tC(_tE.b));},1));});}},_tG=B(_tC(_tz.a));return (_tG._==0)?new T0(2):new T1(4,_tG);}},_tH=new T0(2),_tI=function(_tJ){return new T2(3,_tJ,_tH);},_tK=function(_tL,_tM){var _tN=E(_tL);if(!_tN){return new F(function(){return A1(_tM,_gK);});}else{var _tO=new T(function(){return B(_tK(_tN-1|0,_tM));});return new T1(0,function(_tP){return E(_tO);});}},_tQ=function(_tR,_tS,_tT){var _tU=new T(function(){return B(A1(_tR,_tI));}),_tV=function(_tW,_tX,_tY,_tZ){while(1){var _u0=B((function(_u1,_u2,_u3,_u4){var _u5=E(_u1);switch(_u5._){case 0:var _u6=E(_u2);if(!_u6._){return new F(function(){return A1(_tS,_u4);});}else{var _u7=_u3+1|0,_u8=_u4;_tW=B(A1(_u5.a,_u6.a));_tX=_u6.b;_tY=_u7;_tZ=_u8;return __continue;}break;case 1:var _u9=B(A1(_u5.a,_u2)),_ua=_u2,_u7=_u3,_u8=_u4;_tW=_u9;_tX=_ua;_tY=_u7;_tZ=_u8;return __continue;case 2:return new F(function(){return A1(_tS,_u4);});break;case 3:var _ub=new T(function(){return B(_tw(_u5,_u4));});return new F(function(){return _tK(_u3,function(_uc){return E(_ub);});});break;default:return new F(function(){return _tw(_u5,_u4);});}})(_tW,_tX,_tY,_tZ));if(_u0!=__continue){return _u0;}}};return function(_ud){return new F(function(){return _tV(_tU,_ud,0,_tT);});};},_ue=function(_uf){return new F(function(){return A1(_uf,_S);});},_ug=function(_uh,_ui){var _uj=function(_uk){var _ul=E(_uk);if(!_ul._){return E(_ue);}else{var _um=_ul.a;if(!B(A1(_uh,_um))){return E(_ue);}else{var _un=new T(function(){return B(_uj(_ul.b));}),_uo=function(_up){var _uq=new T(function(){return B(A1(_un,function(_ur){return new F(function(){return A1(_up,new T2(1,_um,_ur));});}));});return new T1(0,function(_us){return E(_uq);});};return E(_uo);}}};return function(_ut){return new F(function(){return A2(_uj,_ut,_ui);});};},_uu=new T0(6),_uv=new T(function(){return B(unCStr("valDig: Bad base"));}),_uw=new T(function(){return B(err(_uv));}),_ux=function(_uy,_uz){var _uA=function(_uB,_uC){var _uD=E(_uB);if(!_uD._){var _uE=new T(function(){return B(A1(_uC,_S));});return function(_uF){return new F(function(){return A1(_uF,_uE);});};}else{var _uG=E(_uD.a),_uH=function(_uI){var _uJ=new T(function(){return B(_uA(_uD.b,function(_uK){return new F(function(){return A1(_uC,new T2(1,_uI,_uK));});}));}),_uL=function(_uM){var _uN=new T(function(){return B(A1(_uJ,_uM));});return new T1(0,function(_uO){return E(_uN);});};return E(_uL);};switch(E(_uy)){case 8:if(48>_uG){var _uP=new T(function(){return B(A1(_uC,_S));});return function(_uQ){return new F(function(){return A1(_uQ,_uP);});};}else{if(_uG>55){var _uR=new T(function(){return B(A1(_uC,_S));});return function(_uS){return new F(function(){return A1(_uS,_uR);});};}else{return new F(function(){return _uH(_uG-48|0);});}}break;case 10:if(48>_uG){var _uT=new T(function(){return B(A1(_uC,_S));});return function(_uU){return new F(function(){return A1(_uU,_uT);});};}else{if(_uG>57){var _uV=new T(function(){return B(A1(_uC,_S));});return function(_uW){return new F(function(){return A1(_uW,_uV);});};}else{return new F(function(){return _uH(_uG-48|0);});}}break;case 16:if(48>_uG){if(97>_uG){if(65>_uG){var _uX=new T(function(){return B(A1(_uC,_S));});return function(_uY){return new F(function(){return A1(_uY,_uX);});};}else{if(_uG>70){var _uZ=new T(function(){return B(A1(_uC,_S));});return function(_v0){return new F(function(){return A1(_v0,_uZ);});};}else{return new F(function(){return _uH((_uG-65|0)+10|0);});}}}else{if(_uG>102){if(65>_uG){var _v1=new T(function(){return B(A1(_uC,_S));});return function(_v2){return new F(function(){return A1(_v2,_v1);});};}else{if(_uG>70){var _v3=new T(function(){return B(A1(_uC,_S));});return function(_v4){return new F(function(){return A1(_v4,_v3);});};}else{return new F(function(){return _uH((_uG-65|0)+10|0);});}}}else{return new F(function(){return _uH((_uG-97|0)+10|0);});}}}else{if(_uG>57){if(97>_uG){if(65>_uG){var _v5=new T(function(){return B(A1(_uC,_S));});return function(_v6){return new F(function(){return A1(_v6,_v5);});};}else{if(_uG>70){var _v7=new T(function(){return B(A1(_uC,_S));});return function(_v8){return new F(function(){return A1(_v8,_v7);});};}else{return new F(function(){return _uH((_uG-65|0)+10|0);});}}}else{if(_uG>102){if(65>_uG){var _v9=new T(function(){return B(A1(_uC,_S));});return function(_va){return new F(function(){return A1(_va,_v9);});};}else{if(_uG>70){var _vb=new T(function(){return B(A1(_uC,_S));});return function(_vc){return new F(function(){return A1(_vc,_vb);});};}else{return new F(function(){return _uH((_uG-65|0)+10|0);});}}}else{return new F(function(){return _uH((_uG-97|0)+10|0);});}}}else{return new F(function(){return _uH(_uG-48|0);});}}break;default:return E(_uw);}}},_vd=function(_ve){var _vf=E(_ve);if(!_vf._){return new T0(2);}else{return new F(function(){return A1(_uz,_vf);});}};return function(_vg){return new F(function(){return A3(_uA,_vg,_5U,_vd);});};},_vh=16,_vi=8,_vj=function(_vk){var _vl=function(_vm){return new F(function(){return A1(_vk,new T1(5,new T2(0,_vi,_vm)));});},_vn=function(_vo){return new F(function(){return A1(_vk,new T1(5,new T2(0,_vh,_vo)));});},_vp=function(_vq){switch(E(_vq)){case 79:return new T1(1,B(_ux(_vi,_vl)));case 88:return new T1(1,B(_ux(_vh,_vn)));case 111:return new T1(1,B(_ux(_vi,_vl)));case 120:return new T1(1,B(_ux(_vh,_vn)));default:return new T0(2);}};return function(_vr){return (E(_vr)==48)?E(new T1(0,_vp)):new T0(2);};},_vs=function(_vt){return new T1(0,B(_vj(_vt)));},_vu=function(_vv){return new F(function(){return A1(_vv,_2N);});},_vw=function(_vx){return new F(function(){return A1(_vx,_2N);});},_vy=10,_vz=new T1(0,10),_vA=function(_vB){return new F(function(){return _aX(E(_vB));});},_vC=new T(function(){return B(unCStr("this should not happen"));}),_vD=new T(function(){return B(err(_vC));}),_vE=function(_vF,_vG){var _vH=E(_vG);if(!_vH._){return __Z;}else{var _vI=E(_vH.b);return (_vI._==0)?E(_vD):new T2(1,B(_cB(B(_ol(_vH.a,_vF)),_vI.a)),new T(function(){return B(_vE(_vF,_vI.b));}));}},_vJ=new T1(0,0),_vK=function(_vL,_vM,_vN){while(1){var _vO=B((function(_vP,_vQ,_vR){var _vS=E(_vR);if(!_vS._){return E(_vJ);}else{if(!E(_vS.b)._){return E(_vS.a);}else{var _vT=E(_vQ);if(_vT<=40){var _vU=function(_vV,_vW){while(1){var _vX=E(_vW);if(!_vX._){return E(_vV);}else{var _vY=B(_cB(B(_ol(_vV,_vP)),_vX.a));_vV=_vY;_vW=_vX.b;continue;}}};return new F(function(){return _vU(_vJ,_vS);});}else{var _vZ=B(_ol(_vP,_vP));if(!(_vT%2)){var _w0=B(_vE(_vP,_vS));_vL=_vZ;_vM=quot(_vT+1|0,2);_vN=_w0;return __continue;}else{var _w0=B(_vE(_vP,new T2(1,_vJ,_vS)));_vL=_vZ;_vM=quot(_vT+1|0,2);_vN=_w0;return __continue;}}}}})(_vL,_vM,_vN));if(_vO!=__continue){return _vO;}}},_w1=function(_w2,_w3){return new F(function(){return _vK(_w2,new T(function(){return B(_mz(_w3,0));},1),B(_6k(_vA,_w3)));});},_w4=function(_w5){var _w6=new T(function(){var _w7=new T(function(){var _w8=function(_w9){return new F(function(){return A1(_w5,new T1(1,new T(function(){return B(_w1(_vz,_w9));})));});};return new T1(1,B(_ux(_vy,_w8)));}),_wa=function(_wb){if(E(_wb)==43){var _wc=function(_wd){return new F(function(){return A1(_w5,new T1(1,new T(function(){return B(_w1(_vz,_wd));})));});};return new T1(1,B(_ux(_vy,_wc)));}else{return new T0(2);}},_we=function(_wf){if(E(_wf)==45){var _wg=function(_wh){return new F(function(){return A1(_w5,new T1(1,new T(function(){return B(_fz(B(_w1(_vz,_wh))));})));});};return new T1(1,B(_ux(_vy,_wg)));}else{return new T0(2);}};return B(_sS(B(_sS(new T1(0,_we),new T1(0,_wa))),_w7));});return new F(function(){return _sS(new T1(0,function(_wi){return (E(_wi)==101)?E(_w6):new T0(2);}),new T1(0,function(_wj){return (E(_wj)==69)?E(_w6):new T0(2);}));});},_wk=function(_wl){var _wm=function(_wn){return new F(function(){return A1(_wl,new T1(1,_wn));});};return function(_wo){return (E(_wo)==46)?new T1(1,B(_ux(_vy,_wm))):new T0(2);};},_wp=function(_wq){return new T1(0,B(_wk(_wq)));},_wr=function(_ws){var _wt=function(_wu){var _wv=function(_ww){return new T1(1,B(_tQ(_w4,_vu,function(_wx){return new F(function(){return A1(_ws,new T1(5,new T3(1,_wu,_ww,_wx)));});})));};return new T1(1,B(_tQ(_wp,_vw,_wv)));};return new F(function(){return _ux(_vy,_wt);});},_wy=function(_wz){return new T1(1,B(_wr(_wz)));},_wA=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wB=function(_wC){return new F(function(){return _4A(_hd,_wC,_wA);});},_wD=false,_wE=true,_wF=function(_wG){var _wH=new T(function(){return B(A1(_wG,_vi));}),_wI=new T(function(){return B(A1(_wG,_vh));});return function(_wJ){switch(E(_wJ)){case 79:return E(_wH);case 88:return E(_wI);case 111:return E(_wH);case 120:return E(_wI);default:return new T0(2);}};},_wK=function(_wL){return new T1(0,B(_wF(_wL)));},_wM=function(_wN){return new F(function(){return A1(_wN,_vy);});},_wO=function(_wP){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_A(9,_wP,_S));}))));});},_wQ=function(_wR){return new T0(2);},_wS=function(_wT){var _wU=E(_wT);if(!_wU._){return E(_wQ);}else{var _wV=_wU.a,_wW=E(_wU.b);if(!_wW._){return E(_wV);}else{var _wX=new T(function(){return B(_wS(_wW));}),_wY=function(_wZ){return new F(function(){return _sS(B(A1(_wV,_wZ)),new T(function(){return B(A1(_wX,_wZ));}));});};return E(_wY);}}},_x0=function(_x1,_x2){var _x3=function(_x4,_x5,_x6){var _x7=E(_x4);if(!_x7._){return new F(function(){return A1(_x6,_x1);});}else{var _x8=E(_x5);if(!_x8._){return new T0(2);}else{if(E(_x7.a)!=E(_x8.a)){return new T0(2);}else{var _x9=new T(function(){return B(_x3(_x7.b,_x8.b,_x6));});return new T1(0,function(_xa){return E(_x9);});}}}};return function(_xb){return new F(function(){return _x3(_x1,_xb,_x2);});};},_xc=new T(function(){return B(unCStr("SO"));}),_xd=14,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_x0(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("SOH"));}),_xj=1,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_x0(_xi,function(_xn){return E(_xm);})));},_xo=function(_xp){return new T1(1,B(_tQ(_xk,_xe,_xp)));},_xq=new T(function(){return B(unCStr("NUL"));}),_xr=0,_xs=function(_xt){var _xu=new T(function(){return B(A1(_xt,_xr));});return new T1(1,B(_x0(_xq,function(_xv){return E(_xu);})));},_xw=new T(function(){return B(unCStr("STX"));}),_xx=2,_xy=function(_xz){var _xA=new T(function(){return B(A1(_xz,_xx));});return new T1(1,B(_x0(_xw,function(_xB){return E(_xA);})));},_xC=new T(function(){return B(unCStr("ETX"));}),_xD=3,_xE=function(_xF){var _xG=new T(function(){return B(A1(_xF,_xD));});return new T1(1,B(_x0(_xC,function(_xH){return E(_xG);})));},_xI=new T(function(){return B(unCStr("EOT"));}),_xJ=4,_xK=function(_xL){var _xM=new T(function(){return B(A1(_xL,_xJ));});return new T1(1,B(_x0(_xI,function(_xN){return E(_xM);})));},_xO=new T(function(){return B(unCStr("ENQ"));}),_xP=5,_xQ=function(_xR){var _xS=new T(function(){return B(A1(_xR,_xP));});return new T1(1,B(_x0(_xO,function(_xT){return E(_xS);})));},_xU=new T(function(){return B(unCStr("ACK"));}),_xV=6,_xW=function(_xX){var _xY=new T(function(){return B(A1(_xX,_xV));});return new T1(1,B(_x0(_xU,function(_xZ){return E(_xY);})));},_y0=new T(function(){return B(unCStr("BEL"));}),_y1=7,_y2=function(_y3){var _y4=new T(function(){return B(A1(_y3,_y1));});return new T1(1,B(_x0(_y0,function(_y5){return E(_y4);})));},_y6=new T(function(){return B(unCStr("BS"));}),_y7=8,_y8=function(_y9){var _ya=new T(function(){return B(A1(_y9,_y7));});return new T1(1,B(_x0(_y6,function(_yb){return E(_ya);})));},_yc=new T(function(){return B(unCStr("HT"));}),_yd=9,_ye=function(_yf){var _yg=new T(function(){return B(A1(_yf,_yd));});return new T1(1,B(_x0(_yc,function(_yh){return E(_yg);})));},_yi=new T(function(){return B(unCStr("LF"));}),_yj=10,_yk=function(_yl){var _ym=new T(function(){return B(A1(_yl,_yj));});return new T1(1,B(_x0(_yi,function(_yn){return E(_ym);})));},_yo=new T(function(){return B(unCStr("VT"));}),_yp=11,_yq=function(_yr){var _ys=new T(function(){return B(A1(_yr,_yp));});return new T1(1,B(_x0(_yo,function(_yt){return E(_ys);})));},_yu=new T(function(){return B(unCStr("FF"));}),_yv=12,_yw=function(_yx){var _yy=new T(function(){return B(A1(_yx,_yv));});return new T1(1,B(_x0(_yu,function(_yz){return E(_yy);})));},_yA=new T(function(){return B(unCStr("CR"));}),_yB=13,_yC=function(_yD){var _yE=new T(function(){return B(A1(_yD,_yB));});return new T1(1,B(_x0(_yA,function(_yF){return E(_yE);})));},_yG=new T(function(){return B(unCStr("SI"));}),_yH=15,_yI=function(_yJ){var _yK=new T(function(){return B(A1(_yJ,_yH));});return new T1(1,B(_x0(_yG,function(_yL){return E(_yK);})));},_yM=new T(function(){return B(unCStr("DLE"));}),_yN=16,_yO=function(_yP){var _yQ=new T(function(){return B(A1(_yP,_yN));});return new T1(1,B(_x0(_yM,function(_yR){return E(_yQ);})));},_yS=new T(function(){return B(unCStr("DC1"));}),_yT=17,_yU=function(_yV){var _yW=new T(function(){return B(A1(_yV,_yT));});return new T1(1,B(_x0(_yS,function(_yX){return E(_yW);})));},_yY=new T(function(){return B(unCStr("DC2"));}),_yZ=18,_z0=function(_z1){var _z2=new T(function(){return B(A1(_z1,_yZ));});return new T1(1,B(_x0(_yY,function(_z3){return E(_z2);})));},_z4=new T(function(){return B(unCStr("DC3"));}),_z5=19,_z6=function(_z7){var _z8=new T(function(){return B(A1(_z7,_z5));});return new T1(1,B(_x0(_z4,function(_z9){return E(_z8);})));},_za=new T(function(){return B(unCStr("DC4"));}),_zb=20,_zc=function(_zd){var _ze=new T(function(){return B(A1(_zd,_zb));});return new T1(1,B(_x0(_za,function(_zf){return E(_ze);})));},_zg=new T(function(){return B(unCStr("NAK"));}),_zh=21,_zi=function(_zj){var _zk=new T(function(){return B(A1(_zj,_zh));});return new T1(1,B(_x0(_zg,function(_zl){return E(_zk);})));},_zm=new T(function(){return B(unCStr("SYN"));}),_zn=22,_zo=function(_zp){var _zq=new T(function(){return B(A1(_zp,_zn));});return new T1(1,B(_x0(_zm,function(_zr){return E(_zq);})));},_zs=new T(function(){return B(unCStr("ETB"));}),_zt=23,_zu=function(_zv){var _zw=new T(function(){return B(A1(_zv,_zt));});return new T1(1,B(_x0(_zs,function(_zx){return E(_zw);})));},_zy=new T(function(){return B(unCStr("CAN"));}),_zz=24,_zA=function(_zB){var _zC=new T(function(){return B(A1(_zB,_zz));});return new T1(1,B(_x0(_zy,function(_zD){return E(_zC);})));},_zE=new T(function(){return B(unCStr("EM"));}),_zF=25,_zG=function(_zH){var _zI=new T(function(){return B(A1(_zH,_zF));});return new T1(1,B(_x0(_zE,function(_zJ){return E(_zI);})));},_zK=new T(function(){return B(unCStr("SUB"));}),_zL=26,_zM=function(_zN){var _zO=new T(function(){return B(A1(_zN,_zL));});return new T1(1,B(_x0(_zK,function(_zP){return E(_zO);})));},_zQ=new T(function(){return B(unCStr("ESC"));}),_zR=27,_zS=function(_zT){var _zU=new T(function(){return B(A1(_zT,_zR));});return new T1(1,B(_x0(_zQ,function(_zV){return E(_zU);})));},_zW=new T(function(){return B(unCStr("FS"));}),_zX=28,_zY=function(_zZ){var _A0=new T(function(){return B(A1(_zZ,_zX));});return new T1(1,B(_x0(_zW,function(_A1){return E(_A0);})));},_A2=new T(function(){return B(unCStr("GS"));}),_A3=29,_A4=function(_A5){var _A6=new T(function(){return B(A1(_A5,_A3));});return new T1(1,B(_x0(_A2,function(_A7){return E(_A6);})));},_A8=new T(function(){return B(unCStr("RS"));}),_A9=30,_Aa=function(_Ab){var _Ac=new T(function(){return B(A1(_Ab,_A9));});return new T1(1,B(_x0(_A8,function(_Ad){return E(_Ac);})));},_Ae=new T(function(){return B(unCStr("US"));}),_Af=31,_Ag=function(_Ah){var _Ai=new T(function(){return B(A1(_Ah,_Af));});return new T1(1,B(_x0(_Ae,function(_Aj){return E(_Ai);})));},_Ak=new T(function(){return B(unCStr("SP"));}),_Al=32,_Am=function(_An){var _Ao=new T(function(){return B(A1(_An,_Al));});return new T1(1,B(_x0(_Ak,function(_Ap){return E(_Ao);})));},_Aq=new T(function(){return B(unCStr("DEL"));}),_Ar=127,_As=function(_At){var _Au=new T(function(){return B(A1(_At,_Ar));});return new T1(1,B(_x0(_Aq,function(_Av){return E(_Au);})));},_Aw=new T2(1,_As,_S),_Ax=new T2(1,_Am,_Aw),_Ay=new T2(1,_Ag,_Ax),_Az=new T2(1,_Aa,_Ay),_AA=new T2(1,_A4,_Az),_AB=new T2(1,_zY,_AA),_AC=new T2(1,_zS,_AB),_AD=new T2(1,_zM,_AC),_AE=new T2(1,_zG,_AD),_AF=new T2(1,_zA,_AE),_AG=new T2(1,_zu,_AF),_AH=new T2(1,_zo,_AG),_AI=new T2(1,_zi,_AH),_AJ=new T2(1,_zc,_AI),_AK=new T2(1,_z6,_AJ),_AL=new T2(1,_z0,_AK),_AM=new T2(1,_yU,_AL),_AN=new T2(1,_yO,_AM),_AO=new T2(1,_yI,_AN),_AP=new T2(1,_yC,_AO),_AQ=new T2(1,_yw,_AP),_AR=new T2(1,_yq,_AQ),_AS=new T2(1,_yk,_AR),_AT=new T2(1,_ye,_AS),_AU=new T2(1,_y8,_AT),_AV=new T2(1,_y2,_AU),_AW=new T2(1,_xW,_AV),_AX=new T2(1,_xQ,_AW),_AY=new T2(1,_xK,_AX),_AZ=new T2(1,_xE,_AY),_B0=new T2(1,_xy,_AZ),_B1=new T2(1,_xs,_B0),_B2=new T2(1,_xo,_B1),_B3=new T(function(){return B(_wS(_B2));}),_B4=34,_B5=new T1(0,1114111),_B6=92,_B7=39,_B8=function(_B9){var _Ba=new T(function(){return B(A1(_B9,_y1));}),_Bb=new T(function(){return B(A1(_B9,_y7));}),_Bc=new T(function(){return B(A1(_B9,_yd));}),_Bd=new T(function(){return B(A1(_B9,_yj));}),_Be=new T(function(){return B(A1(_B9,_yp));}),_Bf=new T(function(){return B(A1(_B9,_yv));}),_Bg=new T(function(){return B(A1(_B9,_yB));}),_Bh=new T(function(){return B(A1(_B9,_B6));}),_Bi=new T(function(){return B(A1(_B9,_B7));}),_Bj=new T(function(){return B(A1(_B9,_B4));}),_Bk=new T(function(){var _Bl=function(_Bm){var _Bn=new T(function(){return B(_aX(E(_Bm)));}),_Bo=function(_Bp){var _Bq=B(_w1(_Bn,_Bp));if(!B(_eF(_Bq,_B5))){return new T0(2);}else{return new F(function(){return A1(_B9,new T(function(){var _Br=B(_bg(_Bq));if(_Br>>>0>1114111){return B(_wO(_Br));}else{return _Br;}}));});}};return new T1(1,B(_ux(_Bm,_Bo)));},_Bs=new T(function(){var _Bt=new T(function(){return B(A1(_B9,_Af));}),_Bu=new T(function(){return B(A1(_B9,_A9));}),_Bv=new T(function(){return B(A1(_B9,_A3));}),_Bw=new T(function(){return B(A1(_B9,_zX));}),_Bx=new T(function(){return B(A1(_B9,_zR));}),_By=new T(function(){return B(A1(_B9,_zL));}),_Bz=new T(function(){return B(A1(_B9,_zF));}),_BA=new T(function(){return B(A1(_B9,_zz));}),_BB=new T(function(){return B(A1(_B9,_zt));}),_BC=new T(function(){return B(A1(_B9,_zn));}),_BD=new T(function(){return B(A1(_B9,_zh));}),_BE=new T(function(){return B(A1(_B9,_zb));}),_BF=new T(function(){return B(A1(_B9,_z5));}),_BG=new T(function(){return B(A1(_B9,_yZ));}),_BH=new T(function(){return B(A1(_B9,_yT));}),_BI=new T(function(){return B(A1(_B9,_yN));}),_BJ=new T(function(){return B(A1(_B9,_yH));}),_BK=new T(function(){return B(A1(_B9,_xd));}),_BL=new T(function(){return B(A1(_B9,_xV));}),_BM=new T(function(){return B(A1(_B9,_xP));}),_BN=new T(function(){return B(A1(_B9,_xJ));}),_BO=new T(function(){return B(A1(_B9,_xD));}),_BP=new T(function(){return B(A1(_B9,_xx));}),_BQ=new T(function(){return B(A1(_B9,_xj));}),_BR=new T(function(){return B(A1(_B9,_xr));}),_BS=function(_BT){switch(E(_BT)){case 64:return E(_BR);case 65:return E(_BQ);case 66:return E(_BP);case 67:return E(_BO);case 68:return E(_BN);case 69:return E(_BM);case 70:return E(_BL);case 71:return E(_Ba);case 72:return E(_Bb);case 73:return E(_Bc);case 74:return E(_Bd);case 75:return E(_Be);case 76:return E(_Bf);case 77:return E(_Bg);case 78:return E(_BK);case 79:return E(_BJ);case 80:return E(_BI);case 81:return E(_BH);case 82:return E(_BG);case 83:return E(_BF);case 84:return E(_BE);case 85:return E(_BD);case 86:return E(_BC);case 87:return E(_BB);case 88:return E(_BA);case 89:return E(_Bz);case 90:return E(_By);case 91:return E(_Bx);case 92:return E(_Bw);case 93:return E(_Bv);case 94:return E(_Bu);case 95:return E(_Bt);default:return new T0(2);}};return B(_sS(new T1(0,function(_BU){return (E(_BU)==94)?E(new T1(0,_BS)):new T0(2);}),new T(function(){return B(A1(_B3,_B9));})));});return B(_sS(new T1(1,B(_tQ(_wK,_wM,_Bl))),_Bs));});return new F(function(){return _sS(new T1(0,function(_BV){switch(E(_BV)){case 34:return E(_Bj);case 39:return E(_Bi);case 92:return E(_Bh);case 97:return E(_Ba);case 98:return E(_Bb);case 102:return E(_Bf);case 110:return E(_Bd);case 114:return E(_Bg);case 116:return E(_Bc);case 118:return E(_Be);default:return new T0(2);}}),_Bk);});},_BW=function(_BX){return new F(function(){return A1(_BX,_gK);});},_BY=function(_BZ){var _C0=E(_BZ);if(!_C0._){return E(_BW);}else{var _C1=E(_C0.a),_C2=_C1>>>0,_C3=new T(function(){return B(_BY(_C0.b));});if(_C2>887){var _C4=u_iswspace(_C1);if(!E(_C4)){return E(_BW);}else{var _C5=function(_C6){var _C7=new T(function(){return B(A1(_C3,_C6));});return new T1(0,function(_C8){return E(_C7);});};return E(_C5);}}else{var _C9=E(_C2);if(_C9==32){var _Ca=function(_Cb){var _Cc=new T(function(){return B(A1(_C3,_Cb));});return new T1(0,function(_Cd){return E(_Cc);});};return E(_Ca);}else{if(_C9-9>>>0>4){if(E(_C9)==160){var _Ce=function(_Cf){var _Cg=new T(function(){return B(A1(_C3,_Cf));});return new T1(0,function(_Ch){return E(_Cg);});};return E(_Ce);}else{return E(_BW);}}else{var _Ci=function(_Cj){var _Ck=new T(function(){return B(A1(_C3,_Cj));});return new T1(0,function(_Cl){return E(_Ck);});};return E(_Ci);}}}}},_Cm=function(_Cn){var _Co=new T(function(){return B(_Cm(_Cn));}),_Cp=function(_Cq){return (E(_Cq)==92)?E(_Co):new T0(2);},_Cr=function(_Cs){return E(new T1(0,_Cp));},_Ct=new T1(1,function(_Cu){return new F(function(){return A2(_BY,_Cu,_Cr);});}),_Cv=new T(function(){return B(_B8(function(_Cw){return new F(function(){return A1(_Cn,new T2(0,_Cw,_wE));});}));}),_Cx=function(_Cy){var _Cz=E(_Cy);if(_Cz==38){return E(_Co);}else{var _CA=_Cz>>>0;if(_CA>887){var _CB=u_iswspace(_Cz);return (E(_CB)==0)?new T0(2):E(_Ct);}else{var _CC=E(_CA);return (_CC==32)?E(_Ct):(_CC-9>>>0>4)?(E(_CC)==160)?E(_Ct):new T0(2):E(_Ct);}}};return new F(function(){return _sS(new T1(0,function(_CD){return (E(_CD)==92)?E(new T1(0,_Cx)):new T0(2);}),new T1(0,function(_CE){var _CF=E(_CE);if(E(_CF)==92){return E(_Cv);}else{return new F(function(){return A1(_Cn,new T2(0,_CF,_wD));});}}));});},_CG=function(_CH,_CI){var _CJ=new T(function(){return B(A1(_CI,new T1(1,new T(function(){return B(A1(_CH,_S));}))));}),_CK=function(_CL){var _CM=E(_CL),_CN=E(_CM.a);if(E(_CN)==34){if(!E(_CM.b)){return E(_CJ);}else{return new F(function(){return _CG(function(_CO){return new F(function(){return A1(_CH,new T2(1,_CN,_CO));});},_CI);});}}else{return new F(function(){return _CG(function(_CP){return new F(function(){return A1(_CH,new T2(1,_CN,_CP));});},_CI);});}};return new F(function(){return _Cm(_CK);});},_CQ=new T(function(){return B(unCStr("_\'"));}),_CR=function(_CS){var _CT=u_iswalnum(_CS);if(!E(_CT)){return new F(function(){return _4A(_hd,_CS,_CQ);});}else{return true;}},_CU=function(_CV){return new F(function(){return _CR(E(_CV));});},_CW=new T(function(){return B(unCStr(",;()[]{}`"));}),_CX=new T(function(){return B(unCStr("=>"));}),_CY=new T2(1,_CX,_S),_CZ=new T(function(){return B(unCStr("~"));}),_D0=new T2(1,_CZ,_CY),_D1=new T(function(){return B(unCStr("@"));}),_D2=new T2(1,_D1,_D0),_D3=new T(function(){return B(unCStr("->"));}),_D4=new T2(1,_D3,_D2),_D5=new T(function(){return B(unCStr("<-"));}),_D6=new T2(1,_D5,_D4),_D7=new T(function(){return B(unCStr("|"));}),_D8=new T2(1,_D7,_D6),_D9=new T(function(){return B(unCStr("\\"));}),_Da=new T2(1,_D9,_D8),_Db=new T(function(){return B(unCStr("="));}),_Dc=new T2(1,_Db,_Da),_Dd=new T(function(){return B(unCStr("::"));}),_De=new T2(1,_Dd,_Dc),_Df=new T(function(){return B(unCStr(".."));}),_Dg=new T2(1,_Df,_De),_Dh=function(_Di){var _Dj=new T(function(){return B(A1(_Di,_uu));}),_Dk=new T(function(){var _Dl=new T(function(){var _Dm=function(_Dn){var _Do=new T(function(){return B(A1(_Di,new T1(0,_Dn)));});return new T1(0,function(_Dp){return (E(_Dp)==39)?E(_Do):new T0(2);});};return B(_B8(_Dm));}),_Dq=function(_Dr){var _Ds=E(_Dr);switch(E(_Ds)){case 39:return new T0(2);case 92:return E(_Dl);default:var _Dt=new T(function(){return B(A1(_Di,new T1(0,_Ds)));});return new T1(0,function(_Du){return (E(_Du)==39)?E(_Dt):new T0(2);});}},_Dv=new T(function(){var _Dw=new T(function(){return B(_CG(_5U,_Di));}),_Dx=new T(function(){var _Dy=new T(function(){var _Dz=new T(function(){var _DA=function(_DB){var _DC=E(_DB),_DD=u_iswalpha(_DC);return (E(_DD)==0)?(E(_DC)==95)?new T1(1,B(_ug(_CU,function(_DE){return new F(function(){return A1(_Di,new T1(3,new T2(1,_DC,_DE)));});}))):new T0(2):new T1(1,B(_ug(_CU,function(_DF){return new F(function(){return A1(_Di,new T1(3,new T2(1,_DC,_DF)));});})));};return B(_sS(new T1(0,_DA),new T(function(){return new T1(1,B(_tQ(_vs,_wy,_Di)));})));}),_DG=function(_DH){return (!B(_4A(_hd,_DH,_wA)))?new T0(2):new T1(1,B(_ug(_wB,function(_DI){var _DJ=new T2(1,_DH,_DI);if(!B(_4A(_qk,_DJ,_Dg))){return new F(function(){return A1(_Di,new T1(4,_DJ));});}else{return new F(function(){return A1(_Di,new T1(2,_DJ));});}})));};return B(_sS(new T1(0,_DG),_Dz));});return B(_sS(new T1(0,function(_DK){if(!B(_4A(_hd,_DK,_CW))){return new T0(2);}else{return new F(function(){return A1(_Di,new T1(2,new T2(1,_DK,_S)));});}}),_Dy));});return B(_sS(new T1(0,function(_DL){return (E(_DL)==34)?E(_Dw):new T0(2);}),_Dx));});return B(_sS(new T1(0,function(_DM){return (E(_DM)==39)?E(new T1(0,_Dq)):new T0(2);}),_Dv));});return new F(function(){return _sS(new T1(1,function(_DN){return (E(_DN)._==0)?E(_Dj):new T0(2);}),_Dk);});},_DO=0,_DP=function(_DQ,_DR){var _DS=new T(function(){var _DT=new T(function(){var _DU=function(_DV){var _DW=new T(function(){var _DX=new T(function(){return B(A1(_DR,_DV));});return B(_Dh(function(_DY){var _DZ=E(_DY);return (_DZ._==2)?(!B(_qW(_DZ.a,_tv)))?new T0(2):E(_DX):new T0(2);}));}),_E0=function(_E1){return E(_DW);};return new T1(1,function(_E2){return new F(function(){return A2(_BY,_E2,_E0);});});};return B(A2(_DQ,_DO,_DU));});return B(_Dh(function(_E3){var _E4=E(_E3);return (_E4._==2)?(!B(_qW(_E4.a,_tu)))?new T0(2):E(_DT):new T0(2);}));}),_E5=function(_E6){return E(_DS);};return function(_E7){return new F(function(){return A2(_BY,_E7,_E5);});};},_E8=function(_E9,_Ea){var _Eb=function(_Ec){var _Ed=new T(function(){return B(A1(_E9,_Ec));}),_Ee=function(_Ef){return new F(function(){return _sS(B(A1(_Ed,_Ef)),new T(function(){return new T1(1,B(_DP(_Eb,_Ef)));}));});};return E(_Ee);},_Eg=new T(function(){return B(A1(_E9,_Ea));}),_Eh=function(_Ei){return new F(function(){return _sS(B(A1(_Eg,_Ei)),new T(function(){return new T1(1,B(_DP(_Eb,_Ei)));}));});};return E(_Eh);},_Ej=0,_Ek=function(_El,_Em){return new F(function(){return A1(_Em,_Ej);});},_En=new T(function(){return B(unCStr("Fr"));}),_Eo=new T2(0,_En,_Ek),_Ep=1,_Eq=function(_Er,_Es){return new F(function(){return A1(_Es,_Ep);});},_Et=new T(function(){return B(unCStr("Bl"));}),_Eu=new T2(0,_Et,_Eq),_Ev=2,_Ew=function(_Ex,_Ey){return new F(function(){return A1(_Ey,_Ev);});},_Ez=new T(function(){return B(unCStr("Ex"));}),_EA=new T2(0,_Ez,_Ew),_EB=3,_EC=function(_ED,_EE){return new F(function(){return A1(_EE,_EB);});},_EF=new T(function(){return B(unCStr("Mv"));}),_EG=new T2(0,_EF,_EC),_EH=4,_EI=function(_EJ,_EK){return new F(function(){return A1(_EK,_EH);});},_EL=new T(function(){return B(unCStr("Pn"));}),_EM=new T2(0,_EL,_EI),_EN=8,_EO=function(_EP,_EQ){return new F(function(){return A1(_EQ,_EN);});},_ER=new T(function(){return B(unCStr("DF"));}),_ES=new T2(0,_ER,_EO),_ET=new T2(1,_ES,_S),_EU=7,_EV=function(_EW,_EX){return new F(function(){return A1(_EX,_EU);});},_EY=new T(function(){return B(unCStr("DB"));}),_EZ=new T2(0,_EY,_EV),_F0=new T2(1,_EZ,_ET),_F1=6,_F2=function(_F3,_F4){return new F(function(){return A1(_F4,_F1);});},_F5=new T(function(){return B(unCStr("Cm"));}),_F6=new T2(0,_F5,_F2),_F7=new T2(1,_F6,_F0),_F8=5,_F9=function(_Fa,_Fb){return new F(function(){return A1(_Fb,_F8);});},_Fc=new T(function(){return B(unCStr("Wn"));}),_Fd=new T2(0,_Fc,_F9),_Fe=new T2(1,_Fd,_F7),_Ff=new T2(1,_EM,_Fe),_Fg=new T2(1,_EG,_Ff),_Fh=new T2(1,_EA,_Fg),_Fi=new T2(1,_Eu,_Fh),_Fj=new T2(1,_Eo,_Fi),_Fk=function(_Fl,_Fm,_Fn){var _Fo=E(_Fl);if(!_Fo._){return new T0(2);}else{var _Fp=E(_Fo.a),_Fq=_Fp.a,_Fr=new T(function(){return B(A2(_Fp.b,_Fm,_Fn));}),_Fs=new T(function(){return B(_Dh(function(_Ft){var _Fu=E(_Ft);switch(_Fu._){case 3:return (!B(_qW(_Fq,_Fu.a)))?new T0(2):E(_Fr);case 4:return (!B(_qW(_Fq,_Fu.a)))?new T0(2):E(_Fr);default:return new T0(2);}}));}),_Fv=function(_Fw){return E(_Fs);};return new F(function(){return _sS(new T1(1,function(_Fx){return new F(function(){return A2(_BY,_Fx,_Fv);});}),new T(function(){return B(_Fk(_Fo.b,_Fm,_Fn));}));});}},_Fy=function(_Fz,_FA){return new F(function(){return _Fk(_Fj,_Fz,_FA);});},_FB=function(_FC){var _FD=function(_FE){return E(new T2(3,_FC,_tH));};return new T1(1,function(_FF){return new F(function(){return A2(_BY,_FF,_FD);});});},_FG=new T(function(){return B(A3(_E8,_Fy,_DO,_FB));}),_FH=new T(function(){return B(err(_sz));}),_FI=new T(function(){return B(err(_sD));}),_FJ=function(_FK,_FL){var _FM=function(_FN,_FO){var _FP=function(_FQ){return new F(function(){return A1(_FO,new T(function(){return  -E(_FQ);}));});},_FR=new T(function(){return B(_Dh(function(_FS){return new F(function(){return A3(_FK,_FS,_FN,_FP);});}));}),_FT=function(_FU){return E(_FR);},_FV=function(_FW){return new F(function(){return A2(_BY,_FW,_FT);});},_FX=new T(function(){return B(_Dh(function(_FY){var _FZ=E(_FY);if(_FZ._==4){var _G0=E(_FZ.a);if(!_G0._){return new F(function(){return A3(_FK,_FZ,_FN,_FO);});}else{if(E(_G0.a)==45){if(!E(_G0.b)._){return E(new T1(1,_FV));}else{return new F(function(){return A3(_FK,_FZ,_FN,_FO);});}}else{return new F(function(){return A3(_FK,_FZ,_FN,_FO);});}}}else{return new F(function(){return A3(_FK,_FZ,_FN,_FO);});}}));}),_G1=function(_G2){return E(_FX);};return new T1(1,function(_G3){return new F(function(){return A2(_BY,_G3,_G1);});});};return new F(function(){return _E8(_FM,_FL);});},_G4=function(_G5){var _G6=E(_G5);if(!_G6._){var _G7=_G6.b,_G8=new T(function(){return B(_vK(new T(function(){return B(_aX(E(_G6.a)));}),new T(function(){return B(_mz(_G7,0));},1),B(_6k(_vA,_G7))));});return new T1(1,_G8);}else{return (E(_G6.b)._==0)?(E(_G6.c)._==0)?new T1(1,new T(function(){return B(_w1(_vz,_G6.a));})):__Z:__Z;}},_G9=function(_Ga,_Gb){return new T0(2);},_Gc=function(_Gd){var _Ge=E(_Gd);if(_Ge._==5){var _Gf=B(_G4(_Ge.a));if(!_Gf._){return E(_G9);}else{var _Gg=new T(function(){return B(_bg(_Gf.a));});return function(_Gh,_Gi){return new F(function(){return A1(_Gi,_Gg);});};}}else{return E(_G9);}},_Gj=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_Gk=new T2(1,_y,_S),_Gl=function(_Gm){while(1){var _Gn=B((function(_Go){var _Gp=E(_Go);if(!_Gp._){return __Z;}else{var _Gq=_Gp.b,_Gr=E(_Gp.a);if(!E(_Gr.b)._){return new T2(1,_Gr.a,new T(function(){return B(_Gl(_Gq));}));}else{_Gm=_Gq;return __continue;}}})(_Gm));if(_Gn!=__continue){return _Gn;}}},_Gs=function(_Gt,_Gu){while(1){var _Gv=E(_Gt);if(!_Gv._){return E(_Gu);}else{var _Gw=new T2(1,_Gv.a,_Gu);_Gt=_Gv.b;_Gu=_Gw;continue;}}},_Gx=function(_Gy,_Gz){var _GA=E(_Gy);if(!_GA._){return __Z;}else{var _GB=E(_Gz);return (_GB._==0)?__Z:new T2(1,new T2(0,_GA.a,_GB.a),new T(function(){return B(_Gx(_GA.b,_GB.b));}));}},_GC=function(_GD,_GE,_GF){while(1){var _GG=B((function(_GH,_GI,_GJ){var _GK=E(_GJ);if(!_GK._){return E(_GI);}else{var _GL=_GK.a,_GM=_GK.b,_GN=B(_st(_qk,_GL,_si));if(!_GN._){var _GO=E(_sG);}else{var _GO=E(_GN.a);}if(!B(_r1(_GO,_sG))){var _GP=B(_Gs(B(_Gx(B(_Gs(_GI,_S)),new T(function(){return B(_Gs(_GO,_S));},1))),_S)),_GQ=B(_mz(_GP,0)),_GR=new T(function(){var _GS=B(_6k(_sr,_GP));if(!_GS._){return __Z;}else{var _GT=_GS.a,_GU=E(_GS.b);if(!_GU._){return __Z;}else{var _GV=_GU.a;if(!E(_GU.b)._){if(!B(_qW(_GL,_rU))){if(!B(_qW(_GL,_rT))){if(!B(_qW(_GL,_rS))){if(!B(_qW(_GL,_rW))){if(!B(_qW(_GL,_rV))){return __Z;}else{if(!B(_qW(_GT,_sB))){if(!B(_qW(_GV,_sB))){return E(_sC);}else{return E(_sB);}}else{return E(_sB);}}}else{var _GW=B(_rG(new T2(0,new T(function(){var _GX=E(_GT);if(!_GX._){return E(_nn);}else{return E(_GX.a);}}),new T(function(){var _GY=B(_Gl(B(_sI(_FG,_GV))));if(!_GY._){return E(_sA);}else{if(!E(_GY.b)._){return E(_GY.a);}else{return E(_sE);}}})),E(E(_GH).a).b)),_GZ=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_H0){return new F(function(){return _A(0,E(_GW.a),_H0);});},new T2(1,function(_H1){return new F(function(){return _A(0,E(_GW.b),_H1);});},_S)),_Gk));});return new T2(1,_z,_GZ);}}else{return new T2(1,new T(function(){var _H2=B(_Gl(B(_sI(_Gj,_GT))));if(!_H2._){return E(_FH);}else{if(!E(_H2.b)._){var _H3=B(_Gl(B(_sI(_Gj,_GV))));if(!_H3._){return E(_FH);}else{if(!E(_H3.b)._){return E(B(_6X(B(_6X(E(E(_GH).a).b,E(_H3.a))),E(_H2.a))).a);}else{return E(_FI);}}}else{return E(_FI);}}}),_S);}}else{if(!B(_qW(_GT,_GV))){return E(_sC);}else{return E(_sB);}}}else{if(!B(_qW(_GT,_sB))){return E(_sC);}else{if(!B(_qW(_GV,_sB))){return E(_sC);}else{return E(_sB);}}}}else{return __Z;}}}});if(_GQ>0){var _H4=_GH,_H5=B(_q(B(_Gs(B(_rM(_GQ,B(_Gs(_GI,_S)))),_S)),new T2(1,_GR,_S)));_GD=_H4;_GE=_H5;_GF=_GM;return __continue;}else{var _H4=_GH,_H5=B(_q(B(_Gs(B(_Gs(_GI,_S)),_S)),new T2(1,_GR,_S)));_GD=_H4;_GE=_H5;_GF=_GM;return __continue;}}else{var _H4=_GH,_H5=B(_q(_GI,new T2(1,_GL,_S)));_GD=_H4;_GE=_H5;_GF=_GM;return __continue;}}})(_GD,_GE,_GF));if(_GG!=__continue){return _GG;}}},_H6=new T(function(){return B(_ed("Event.hs:(102,1)-(106,73)|function addMemory"));}),_H7=function(_H8,_H9){var _Ha=E(_H8),_Hb=E(_H9);if(!B(_qW(_Ha.a,_Hb.a))){return false;}else{return new F(function(){return _qW(_Ha.b,_Hb.b);});}},_Hc=new T2(1,_S,_S),_Hd=function(_He,_Hf,_Hg){var _Hh=E(_Hg);if(!_Hh._){return new T2(0,new T2(1,_Hf,_S),_S);}else{var _Hi=E(_Hf),_Hj=new T(function(){var _Hk=B(_Hd(_He,_Hh.a,_Hh.b));return new T2(0,_Hk.a,_Hk.b);});return (_He!=_Hi)?new T2(0,new T2(1,_Hi,new T(function(){return E(E(_Hj).a);})),new T(function(){return E(E(_Hj).b);})):new T2(0,_S,new T2(1,new T(function(){return E(E(_Hj).a);}),new T(function(){return E(E(_Hj).b);})));}},_Hl=32,_Hm=function(_Hn){var _Ho=E(_Hn);if(!_Ho._){return __Z;}else{var _Hp=new T(function(){return B(_q(_Ho.a,new T(function(){return B(_Hm(_Ho.b));},1)));});return new T2(1,_Hl,_Hp);}},_Hq=function(_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN){while(1){var _HO=B((function(_HP,_HQ,_HR,_HS,_HT,_HU,_HV,_HW,_HX,_HY,_HZ,_I0,_I1,_I2,_I3,_I4,_I5,_I6,_I7,_I8,_I9,_Ia,_Ib){var _Ic=E(_HP);if(!_Ic._){return {_:0,a:_HQ,b:_HR,c:_HS,d:_HT,e:_HU,f:_HV,g:_HW,h:_HX,i:_HY,j:_HZ,k:_I0,l:_I1,m:_I2,n:_I3,o:_I4,p:_I5,q:_I6,r:_I7,s:_I8,t:_I9,u:_Ia,v:_Ib};}else{var _Id=_Ic.a,_Ie=E(_Ic.b);if(!_Ie._){return E(_H6);}else{var _If=new T(function(){var _Ig=E(_Ie.a);if(!_Ig._){var _Ih=B(_GC({_:0,a:E(_HQ),b:E(_HR),c:E(_HS),d:E(_HT),e:E(_HU),f:E(_HV),g:E(_HW),h:E(_HX),i:_HY,j:_HZ,k:_I0,l:_I1,m:E(_I2),n:_I3,o:E(_I4),p:E(_I5),q:_I6,r:E(_I7),s:E(_I8),t:_I9,u:E(_Ia),v:E(_Ib)},_S,_Hc));if(!_Ih._){return __Z;}else{return B(_q(_Ih.a,new T(function(){return B(_Hm(_Ih.b));},1)));}}else{var _Ii=_Ig.a,_Ij=E(_Ig.b);if(!_Ij._){var _Ik=B(_GC({_:0,a:E(_HQ),b:E(_HR),c:E(_HS),d:E(_HT),e:E(_HU),f:E(_HV),g:E(_HW),h:E(_HX),i:_HY,j:_HZ,k:_I0,l:_I1,m:E(_I2),n:_I3,o:E(_I4),p:E(_I5),q:_I6,r:E(_I7),s:E(_I8),t:_I9,u:E(_Ia),v:E(_Ib)},_S,new T2(1,new T2(1,_Ii,_S),_S)));if(!_Ik._){return __Z;}else{return B(_q(_Ik.a,new T(function(){return B(_Hm(_Ik.b));},1)));}}else{var _Il=E(_Ii),_Im=new T(function(){var _In=B(_Hd(95,_Ij.a,_Ij.b));return new T2(0,_In.a,_In.b);});if(E(_Il)==95){var _Io=B(_GC({_:0,a:E(_HQ),b:E(_HR),c:E(_HS),d:E(_HT),e:E(_HU),f:E(_HV),g:E(_HW),h:E(_HX),i:_HY,j:_HZ,k:_I0,l:_I1,m:E(_I2),n:_I3,o:E(_I4),p:E(_I5),q:_I6,r:E(_I7),s:E(_I8),t:_I9,u:E(_Ia),v:E(_Ib)},_S,new T2(1,_S,new T2(1,new T(function(){return E(E(_Im).a);}),new T(function(){return E(E(_Im).b);})))));if(!_Io._){return __Z;}else{return B(_q(_Io.a,new T(function(){return B(_Hm(_Io.b));},1)));}}else{var _Ip=B(_GC({_:0,a:E(_HQ),b:E(_HR),c:E(_HS),d:E(_HT),e:E(_HU),f:E(_HV),g:E(_HW),h:E(_HX),i:_HY,j:_HZ,k:_I0,l:_I1,m:E(_I2),n:_I3,o:E(_I4),p:E(_I5),q:_I6,r:E(_I7),s:E(_I8),t:_I9,u:E(_Ia),v:E(_Ib)},_S,new T2(1,new T2(1,_Il,new T(function(){return E(E(_Im).a);})),new T(function(){return E(E(_Im).b);}))));if(!_Ip._){return __Z;}else{return B(_q(_Ip.a,new T(function(){return B(_Hm(_Ip.b));},1)));}}}}}),_Iq=_HQ,_Ir=_HR,_Is=_HS,_It=_HT,_Iu=_HU,_Iv=_HV,_Iw=_HX,_Ix=_HY,_Iy=_HZ,_Iz=_I0,_IA=_I1,_IB=_I2,_IC=_I3,_ID=_I4,_IE=_I5,_IF=_I6,_IG=_I7,_IH=_I8,_II=_I9,_IJ=_Ia,_IK=_Ib;_Hr=_Ie.b;_Hs=_Iq;_Ht=_Ir;_Hu=_Is;_Hv=_It;_Hw=_Iu;_Hx=_Iv;_Hy=new T2(1,new T2(0,_Id,_If),new T(function(){var _IL=B(_st(_qk,_Id,_HW));if(!_IL._){var _IM=__Z;}else{var _IM=E(_IL.a);}if(!B(_qW(_IM,_S))){return B(_qP(_H7,new T2(0,_Id,_IM),_HW));}else{return E(_HW);}}));_Hz=_Iw;_HA=_Ix;_HB=_Iy;_HC=_Iz;_HD=_IA;_HE=_IB;_HF=_IC;_HG=_ID;_HH=_IE;_HI=_IF;_HJ=_IG;_HK=_IH;_HL=_II;_HM=_IJ;_HN=_IK;return __continue;}}})(_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN));if(_HO!=__continue){return _HO;}}},_IN=function(_IO){var _IP=E(_IO);if(!_IP._){return new T2(0,_S,_S);}else{var _IQ=E(_IP.a),_IR=new T(function(){var _IS=B(_IN(_IP.b));return new T2(0,_IS.a,_IS.b);});return new T2(0,new T2(1,_IQ.a,new T(function(){return E(E(_IR).a);})),new T2(1,_IQ.b,new T(function(){return E(E(_IR).b);})));}},_IT=function(_IU,_IV,_IW){while(1){var _IX=B((function(_IY,_IZ,_J0){var _J1=E(_J0);if(!_J1._){return __Z;}else{var _J2=_J1.b;if(_IZ!=E(_J1.a)){var _J3=_IY+1|0,_J4=_IZ;_IU=_J3;_IV=_J4;_IW=_J2;return __continue;}else{return new T2(1,_IY,new T(function(){return B(_IT(_IY+1|0,_IZ,_J2));}));}}})(_IU,_IV,_IW));if(_IX!=__continue){return _IX;}}},_J5=function(_J6,_J7,_J8){var _J9=E(_J8);if(!_J9._){return __Z;}else{var _Ja=_J9.b,_Jb=E(_J7);if(_Jb!=E(_J9.a)){return new F(function(){return _IT(_J6+1|0,_Jb,_Ja);});}else{return new T2(1,_J6,new T(function(){return B(_IT(_J6+1|0,_Jb,_Ja));}));}}},_Jc=function(_Jd,_Je,_Jf,_Jg){var _Jh=E(_Jg);if(!_Jh._){return __Z;}else{var _Ji=_Jh.b;return (!B(_4A(_3L,_Jd,_Jf)))?new T2(1,_Jh.a,new T(function(){return B(_Jc(_Jd+1|0,_Je,_Jf,_Ji));})):new T2(1,_Je,new T(function(){return B(_Jc(_Jd+1|0,_Je,_Jf,_Ji));}));}},_Jj=function(_Jk,_Jl,_Jm){var _Jn=E(_Jm);if(!_Jn._){return __Z;}else{var _Jo=new T(function(){var _Jp=B(_IN(_Jn.a)),_Jq=_Jp.a,_Jr=new T(function(){return B(_Jc(0,_Jl,new T(function(){return B(_J5(0,_Jk,_Jq));}),_Jp.b));},1);return B(_Gx(_Jq,_Jr));});return new T2(1,_Jo,new T(function(){return B(_Jj(_Jk,_Jl,_Jn.b));}));}},_Js=function(_Jt){var _Ju=E(_Jt);return (_Ju._==0)?E(_nn):E(_Ju.a);},_Jv=new T(function(){return B(_ed("Event.hs:(75,1)-(78,93)|function changeType"));}),_Jw=new T(function(){return B(_ed("Event.hs:72:16-116|case"));}),_Jx=new T(function(){return B(unCStr("Wn"));}),_Jy=new T(function(){return B(unCStr("Pn"));}),_Jz=new T(function(){return B(unCStr("Mv"));}),_JA=new T(function(){return B(unCStr("Fr"));}),_JB=new T(function(){return B(unCStr("Ex"));}),_JC=new T(function(){return B(unCStr("DF"));}),_JD=new T(function(){return B(unCStr("DB"));}),_JE=new T(function(){return B(unCStr("Cm"));}),_JF=new T(function(){return B(unCStr("Bl"));}),_JG=function(_JH){return (!B(_qW(_JH,_JF)))?(!B(_qW(_JH,_JE)))?(!B(_qW(_JH,_JD)))?(!B(_qW(_JH,_JC)))?(!B(_qW(_JH,_JB)))?(!B(_qW(_JH,_JA)))?(!B(_qW(_JH,_Jz)))?(!B(_qW(_JH,_Jy)))?(!B(_qW(_JH,_Jx)))?E(_Jw):5:4:3:0:2:8:7:6:1;},_JI=function(_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0,_K1,_K2,_K3,_K4,_K5){while(1){var _K6=B((function(_K7,_K8,_K9,_Ka,_Kb,_Kc,_Kd,_Ke,_Kf,_Kg,_Kh,_Ki,_Kj,_Kk,_Kl,_Km,_Kn,_Ko,_Kp,_Kq,_Kr,_Ks,_Kt){var _Ku=E(_K7);if(!_Ku._){return {_:0,a:_K8,b:_K9,c:_Ka,d:_Kb,e:_Kc,f:_Kd,g:_Ke,h:_Kf,i:_Kg,j:_Kh,k:_Ki,l:_Kj,m:_Kk,n:_Kl,o:_Km,p:_Kn,q:_Ko,r:_Kp,s:_Kq,t:_Kr,u:_Ks,v:_Kt};}else{var _Kv=E(_Ku.b);if(!_Kv._){return E(_Jv);}else{var _Kw=E(_K8),_Kx=_K9,_Ky=_Ka,_Kz=_Kb,_KA=_Kc,_KB=_Kd,_KC=_Ke,_KD=_Kf,_KE=_Kg,_KF=_Kh,_KG=_Ki,_KH=_Kj,_KI=_Kk,_KJ=_Kl,_KK=_Km,_KL=_Kn,_KM=_Ko,_KN=_Kp,_KO=_Kq,_KP=_Kr,_KQ=_Ks,_KR=_Kt;_JJ=_Kv.b;_JK={_:0,a:E(_Kw.a),b:E(B(_Jj(new T(function(){return B(_Js(_Ku.a));}),new T(function(){return B(_JG(_Kv.a));}),_Kw.b))),c:E(_Kw.c),d:_Kw.d,e:_Kw.e,f:_Kw.f,g:E(_Kw.g),h:_Kw.h,i:E(_Kw.i),j:E(_Kw.j),k:E(_Kw.k)};_JL=_Kx;_JM=_Ky;_JN=_Kz;_JO=_KA;_JP=_KB;_JQ=_KC;_JR=_KD;_JS=_KE;_JT=_KF;_JU=_KG;_JV=_KH;_JW=_KI;_JX=_KJ;_JY=_KK;_JZ=_KL;_K0=_KM;_K1=_KN;_K2=_KO;_K3=_KP;_K4=_KQ;_K5=_KR;return __continue;}}})(_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0,_K1,_K2,_K3,_K4,_K5));if(_K6!=__continue){return _K6;}}},_KS=function(_KT,_KU){while(1){var _KV=E(_KU);if(!_KV._){return __Z;}else{var _KW=_KV.b,_KX=E(_KT);if(_KX==1){return E(_KW);}else{_KT=_KX-1|0;_KU=_KW;continue;}}}},_KY=function(_KZ,_L0){while(1){var _L1=E(_L0);if(!_L1._){return __Z;}else{var _L2=_L1.b,_L3=E(_KZ);if(_L3==1){return E(_L2);}else{_KZ=_L3-1|0;_L0=_L2;continue;}}}},_L4=function(_L5,_L6,_L7,_L8,_L9){var _La=new T(function(){var _Lb=E(_L5),_Lc=new T(function(){return B(_6X(_L9,_L6));}),_Ld=new T2(1,new T2(0,_L7,_L8),new T(function(){var _Le=_Lb+1|0;if(_Le>0){return B(_KY(_Le,_Lc));}else{return E(_Lc);}}));if(0>=_Lb){return E(_Ld);}else{var _Lf=function(_Lg,_Lh){var _Li=E(_Lg);if(!_Li._){return E(_Ld);}else{var _Lj=_Li.a,_Lk=E(_Lh);return (_Lk==1)?new T2(1,_Lj,_Ld):new T2(1,_Lj,new T(function(){return B(_Lf(_Li.b,_Lk-1|0));}));}};return B(_Lf(_Lc,_Lb));}}),_Ll=new T2(1,_La,new T(function(){var _Lm=_L6+1|0;if(_Lm>0){return B(_KS(_Lm,_L9));}else{return E(_L9);}}));if(0>=_L6){return E(_Ll);}else{var _Ln=function(_Lo,_Lp){var _Lq=E(_Lo);if(!_Lq._){return E(_Ll);}else{var _Lr=_Lq.a,_Ls=E(_Lp);return (_Ls==1)?new T2(1,_Lr,_Ll):new T2(1,_Lr,new T(function(){return B(_Ln(_Lq.b,_Ls-1|0));}));}};return new F(function(){return _Ln(_L9,_L6);});}},_Lt=32,_Lu=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Lv=function(_Lw){return new F(function(){return _dP(new T1(0,new T(function(){return B(_e2(_Lw,_Lu));})),_dz);});},_Lx=function(_Ly){return new F(function(){return _Lv("Event.hs:58:27-53|(x\' : y\' : _)");});},_Lz=new T(function(){return B(_Lx(_));}),_LA=function(_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO,_LP,_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX){while(1){var _LY=B((function(_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc,_Md,_Me,_Mf,_Mg,_Mh,_Mi,_Mj,_Mk,_Ml){var _Mm=E(_LZ);if(!_Mm._){return {_:0,a:_M0,b:_M1,c:_M2,d:_M3,e:_M4,f:_M5,g:_M6,h:_M7,i:_M8,j:_M9,k:_Ma,l:_Mb,m:_Mc,n:_Md,o:_Me,p:_Mf,q:_Mg,r:_Mh,s:_Mi,t:_Mj,u:_Mk,v:_Ml};}else{var _Mn=E(_M0),_Mo=new T(function(){var _Mp=E(_Mm.a);if(!_Mp._){return E(_Lz);}else{var _Mq=E(_Mp.b);if(!_Mq._){return E(_Lz);}else{var _Mr=_Mq.a,_Ms=_Mq.b,_Mt=E(_Mp.a);if(E(_Mt)==44){return new T2(0,_S,new T(function(){return E(B(_Hd(44,_Mr,_Ms)).a);}));}else{var _Mu=B(_Hd(44,_Mr,_Ms)),_Mv=E(_Mu.b);if(!_Mv._){return E(_Lz);}else{return new T2(0,new T2(1,_Mt,_Mu.a),_Mv.a);}}}}}),_Mw=B(_Gl(B(_sI(_Gj,new T(function(){return E(E(_Mo).b);})))));if(!_Mw._){return E(_FH);}else{if(!E(_Mw.b)._){var _Mx=new T(function(){var _My=B(_Gl(B(_sI(_Gj,new T(function(){return E(E(_Mo).a);})))));if(!_My._){return E(_FH);}else{if(!E(_My.b)._){return E(_My.a);}else{return E(_FI);}}},1),_Mz=_M1,_MA=_M2,_MB=_M3,_MC=_M4,_MD=_M5,_ME=_M6,_MF=_M7,_MG=_M8,_MH=_M9,_MI=_Ma,_MJ=_Mb,_MK=_Mc,_ML=_Md,_MM=_Me,_MN=_Mf,_MO=_Mg,_MP=_Mh,_MQ=_Mi,_MR=_Mj,_MS=_Mk,_MT=_Ml;_LB=_Mm.b;_LC={_:0,a:E(_Mn.a),b:E(B(_L4(_Mx,E(_Mw.a),_Lt,_Ej,_Mn.b))),c:E(_Mn.c),d:_Mn.d,e:_Mn.e,f:_Mn.f,g:E(_Mn.g),h:_Mn.h,i:E(_Mn.i),j:E(_Mn.j),k:E(_Mn.k)};_LD=_Mz;_LE=_MA;_LF=_MB;_LG=_MC;_LH=_MD;_LI=_ME;_LJ=_MF;_LK=_MG;_LL=_MH;_LM=_MI;_LN=_MJ;_LO=_MK;_LP=_ML;_LQ=_MM;_LR=_MN;_LS=_MO;_LT=_MP;_LU=_MQ;_LV=_MR;_LW=_MS;_LX=_MT;return __continue;}else{return E(_FI);}}}})(_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO,_LP,_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX));if(_LY!=__continue){return _LY;}}},_MU=function(_MV,_MW,_MX){var _MY=E(_MX);return (_MY._==0)?0:(!B(A3(_4y,_MV,_MW,_MY.a)))?1+B(_MU(_MV,_MW,_MY.b))|0:0;},_MZ=function(_N0,_N1){while(1){var _N2=E(_N1);if(!_N2._){return __Z;}else{var _N3=_N2.b,_N4=E(_N0);if(_N4==1){return E(_N3);}else{_N0=_N4-1|0;_N1=_N3;continue;}}}},_N5=function(_N6,_N7){var _N8=new T(function(){var _N9=_N6+1|0;if(_N9>0){return B(_MZ(_N9,_N7));}else{return E(_N7);}});if(0>=_N6){return E(_N8);}else{var _Na=function(_Nb,_Nc){var _Nd=E(_Nb);if(!_Nd._){return E(_N8);}else{var _Ne=_Nd.a,_Nf=E(_Nc);return (_Nf==1)?new T2(1,_Ne,_N8):new T2(1,_Ne,new T(function(){return B(_Na(_Nd.b,_Nf-1|0));}));}};return new F(function(){return _Na(_N7,_N6);});}},_Ng=function(_Nh,_Ni){return new F(function(){return _N5(E(_Nh),_Ni);});},_Nj= -1,_Nk=function(_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH){while(1){var _NI=B((function(_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5){var _O6=E(_NJ);if(!_O6._){return {_:0,a:_NK,b:_NL,c:_NM,d:_NN,e:_NO,f:_NP,g:_NQ,h:_NR,i:_NS,j:_NT,k:_NU,l:_NV,m:_NW,n:_NX,o:_NY,p:_NZ,q:_O0,r:_O1,s:_O2,t:_O3,u:_O4,v:_O5};}else{var _O7=_O6.a,_O8=B(_6k(_sr,_NO)),_O9=B(_4A(_qk,_O7,_O8)),_Oa=new T(function(){if(!E(_O9)){return E(_Nj);}else{return B(_MU(_qk,_O7,_O8));}});if(!E(_O9)){var _Ob=E(_NO);}else{var _Ob=B(_Ng(_Oa,_NO));}if(!E(_O9)){var _Oc=E(_NP);}else{var _Oc=B(_Ng(_Oa,_NP));}var _Od=_NK,_Oe=_NL,_Of=_NM,_Og=_NN,_Oh=_NQ,_Oi=_NR,_Oj=_NS,_Ok=_NT,_Ol=_NU,_Om=_NV,_On=_NW,_Oo=_NX,_Op=_NY,_Oq=_NZ,_Or=_O0,_Os=_O1,_Ot=_O2,_Ou=_O3,_Ov=_O4,_Ow=_O5;_Nl=_O6.b;_Nm=_Od;_Nn=_Oe;_No=_Of;_Np=_Og;_Nq=_Ob;_Nr=_Oc;_Ns=_Oh;_Nt=_Oi;_Nu=_Oj;_Nv=_Ok;_Nw=_Ol;_Nx=_Om;_Ny=_On;_Nz=_Oo;_NA=_Op;_NB=_Oq;_NC=_Or;_ND=_Os;_NE=_Ot;_NF=_Ou;_NG=_Ov;_NH=_Ow;return __continue;}})(_Nl,_Nm,_Nn,_No,_Np,_Nq,_Nr,_Ns,_Nt,_Nu,_Nv,_Nw,_Nx,_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH));if(_NI!=__continue){return _NI;}}},_Ox=function(_Oy){var _Oz=E(_Oy);if(!_Oz._){return new T2(0,_S,_S);}else{var _OA=E(_Oz.a),_OB=new T(function(){var _OC=B(_Ox(_Oz.b));return new T2(0,_OC.a,_OC.b);});return new T2(0,new T2(1,_OA.a,new T(function(){return E(E(_OB).a);})),new T2(1,_OA.b,new T(function(){return E(E(_OB).b);})));}},_OD=function(_OE,_OF){while(1){var _OG=E(_OE);if(!_OG._){return E(_OF);}else{var _OH=_OF+E(_OG.a)|0;_OE=_OG.b;_OF=_OH;continue;}}},_OI=function(_OJ,_OK){while(1){var _OL=E(_OK);if(!_OL._){return __Z;}else{var _OM=_OL.b,_ON=E(_OJ);if(_ON==1){return E(_OM);}else{_OJ=_ON-1|0;_OK=_OM;continue;}}}},_OO=function(_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY,_OZ,_P0,_P1,_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb){while(1){var _Pc=B((function(_Pd,_Pe,_Pf,_Pg,_Ph,_Pi,_Pj,_Pk,_Pl,_Pm,_Pn,_Po,_Pp,_Pq,_Pr,_Ps,_Pt,_Pu,_Pv,_Pw,_Px,_Py,_Pz){var _PA=E(_Pd);if(!_PA._){return {_:0,a:_Pe,b:_Pf,c:_Pg,d:_Ph,e:_Pi,f:_Pj,g:_Pk,h:_Pl,i:_Pm,j:_Pn,k:_Po,l:_Pp,m:_Pq,n:_Pr,o:_Ps,p:_Pt,q:_Pu,r:_Pv,s:_Pw,t:_Px,u:_Py,v:_Pz};}else{var _PB=new T(function(){var _PC=B(_Gl(B(_sI(_Gj,_PA.a))));if(!_PC._){return E(_FH);}else{if(!E(_PC.b)._){return B(_q(B(_A(0,B(_6X(_Pv,E(_PC.a))),_S)),new T(function(){if(_Pm>0){return B(_OI(_Pm,_Pg));}else{return E(_Pg);}},1)));}else{return E(_FI);}}});if(0>=_Pm){var _PD=E(_PB);}else{var _PE=function(_PF,_PG){var _PH=E(_PF);if(!_PH._){return E(_PB);}else{var _PI=_PH.a,_PJ=E(_PG);return (_PJ==1)?new T2(1,_PI,_PB):new T2(1,_PI,new T(function(){return B(_PE(_PH.b,_PJ-1|0));}));}},_PD=B(_PE(_Pg,_Pm));}var _PK=_Pe,_PL=_Pf,_PM=_Ph,_PN=_Pi,_PO=_Pj,_PP=_Pk,_PQ=_Pl,_PR=_Pm,_PS=_Pn,_PT=_Po,_PU=_Pp,_PV=_Pq,_PW=_Pr,_PX=_Ps,_PY=_Pt,_PZ=_Pu,_Q0=_Pv,_Q1=_Pw,_Q2=_Px,_Q3=_Py,_Q4=_Pz;_OP=_PA.b;_OQ=_PK;_OR=_PL;_OS=_PD;_OT=_PM;_OU=_PN;_OV=_PO;_OW=_PP;_OX=_PQ;_OY=_PR;_OZ=_PS;_P0=_PT;_P1=_PU;_P2=_PV;_P3=_PW;_P4=_PX;_P5=_PY;_P6=_PZ;_P7=_Q0;_P8=_Q1;_P9=_Q2;_Pa=_Q3;_Pb=_Q4;return __continue;}})(_OP,_OQ,_OR,_OS,_OT,_OU,_OV,_OW,_OX,_OY,_OZ,_P0,_P1,_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb));if(_Pc!=__continue){return _Pc;}}},_Q5=function(_Q6){return new F(function(){return _Lv("Event.hs:119:28-52|(c : d : _)");});},_Q7=new T(function(){return B(_Q5(_));}),_Q8=function(_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC){while(1){var _QD=B((function(_QE,_QF,_QG,_QH,_QI,_QJ,_QK,_QL,_QM,_QN,_QO,_QP,_QQ,_QR,_QS,_QT,_QU,_QV,_QW,_QX,_QY,_QZ,_R0,_R1,_R2,_R3,_R4,_R5,_R6,_R7){var _R8=E(_QE);if(!_R8._){return {_:0,a:E(_QF),b:E(_QG),c:E(_QH),d:E(_QI),e:E(_QJ),f:E(_QK),g:E(_QL),h:E(_QM),i:_QN,j:_QO,k:_QP,l:_QQ,m:E(_QR),n:_QS,o:E(_QT),p:E(_QU),q:_QV,r:E(_QW),s:E(_QX),t:_QY,u:E({_:0,a:E(_QZ),b:E(_R0),c:E(_R1),d:E(_wE),e:E(_R3),f:E(_R4),g:E(_wE),h:E(_R6)}),v:E(_R7)};}else{var _R9=new T(function(){var _Ra=E(_R8.a);if(!_Ra._){return E(_Q7);}else{var _Rb=E(_Ra.b);if(!_Rb._){return E(_Q7);}else{var _Rc=_Rb.a,_Rd=_Rb.b,_Re=E(_Ra.a);if(E(_Re)==44){return new T2(0,_S,new T(function(){return E(B(_Hd(44,_Rc,_Rd)).a);}));}else{var _Rf=B(_Hd(44,_Rc,_Rd)),_Rg=E(_Rf.b);if(!_Rg._){return E(_Q7);}else{return new T2(0,new T2(1,_Re,_Rf.a),_Rg.a);}}}}}),_Rh=_QF,_Ri=_QG,_Rj=_QH,_Rk=_QI,_Rl=_QJ,_Rm=_QK,_Rn=_QL,_Ro=_QM,_Rp=_QN,_Rq=_QO,_Rr=_QP,_Rs=_QQ,_Rt=B(_q(_QR,new T2(1,new T2(0,new T(function(){return E(E(_R9).a);}),new T(function(){return E(E(_R9).b);})),_S))),_Ru=_QS,_Rv=_QT,_Rw=_QU,_Rx=_QV,_Ry=_QW,_Rz=_QX,_RA=_QY,_RB=_QZ,_RC=_R0,_RD=_R1,_RE=_R2,_RF=_R3,_RG=_R4,_RH=_R5,_RI=_R6,_RJ=_R7;_Q9=_R8.b;_Qa=_Rh;_Qb=_Ri;_Qc=_Rj;_Qd=_Rk;_Qe=_Rl;_Qf=_Rm;_Qg=_Rn;_Qh=_Ro;_Qi=_Rp;_Qj=_Rq;_Qk=_Rr;_Ql=_Rs;_Qm=_Rt;_Qn=_Ru;_Qo=_Rv;_Qp=_Rw;_Qq=_Rx;_Qr=_Ry;_Qs=_Rz;_Qt=_RA;_Qu=_RB;_Qv=_RC;_Qw=_RD;_Qx=_RE;_Qy=_RF;_Qz=_RG;_QA=_RH;_QB=_RI;_QC=_RJ;return __continue;}})(_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm,_Qn,_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC));if(_QD!=__continue){return _QD;}}},_RK=function(_RL){return new F(function(){return _Lv("Event.hs:65:27-53|(x\' : y\' : _)");});},_RM=new T(function(){return B(_RK(_));}),_RN=function(_RO){return new F(function(){return _Lv("Event.hs:66:27-55|(chs : tps : _)");});},_RP=new T(function(){return B(_RN(_));}),_RQ=new T(function(){return B(_ed("Event.hs:(63,1)-(69,83)|function putCell"));}),_RR=function(_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se){while(1){var _Sf=B((function(_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA,_SB,_SC){var _SD=E(_Sg);if(!_SD._){return {_:0,a:_Sh,b:_Si,c:_Sj,d:_Sk,e:_Sl,f:_Sm,g:_Sn,h:_So,i:_Sp,j:_Sq,k:_Sr,l:_Ss,m:_St,n:_Su,o:_Sv,p:_Sw,q:_Sx,r:_Sy,s:_Sz,t:_SA,u:_SB,v:_SC};}else{var _SE=E(_SD.b);if(!_SE._){return E(_RQ);}else{var _SF=E(_Sh),_SG=new T(function(){var _SH=E(_SD.a);if(!_SH._){return E(_RM);}else{var _SI=E(_SH.b);if(!_SI._){return E(_RM);}else{var _SJ=_SI.a,_SK=_SI.b,_SL=E(_SH.a);if(E(_SL)==44){return new T2(0,_S,new T(function(){return E(B(_Hd(44,_SJ,_SK)).a);}));}else{var _SM=B(_Hd(44,_SJ,_SK)),_SN=E(_SM.b);if(!_SN._){return E(_RM);}else{return new T2(0,new T2(1,_SL,_SM.a),_SN.a);}}}}}),_SO=B(_Gl(B(_sI(_Gj,new T(function(){return E(E(_SG).b);})))));if(!_SO._){return E(_FH);}else{if(!E(_SO.b)._){var _SP=new T(function(){var _SQ=E(_SE.a);if(!_SQ._){return E(_RP);}else{var _SR=E(_SQ.b);if(!_SR._){return E(_RP);}else{var _SS=_SR.a,_ST=_SR.b,_SU=E(_SQ.a);if(E(_SU)==44){return new T2(0,_S,new T(function(){return E(B(_Hd(44,_SS,_ST)).a);}));}else{var _SV=B(_Hd(44,_SS,_ST)),_SW=E(_SV.b);if(!_SW._){return E(_RP);}else{return new T2(0,new T2(1,_SU,_SV.a),_SW.a);}}}}}),_SX=new T(function(){var _SY=B(_Gl(B(_sI(_Gj,new T(function(){return E(E(_SG).a);})))));if(!_SY._){return E(_FH);}else{if(!E(_SY.b)._){return E(_SY.a);}else{return E(_FI);}}},1),_SZ=_Si,_T0=_Sj,_T1=_Sk,_T2=_Sl,_T3=_Sm,_T4=_Sn,_T5=_So,_T6=_Sp,_T7=_Sq,_T8=_Sr,_T9=_Ss,_Ta=_St,_Tb=_Su,_Tc=_Sv,_Td=_Sw,_Te=_Sx,_Tf=_Sy,_Tg=_Sz,_Th=_SA,_Ti=_SB,_Tj=_SC;_RS=_SE.b;_RT={_:0,a:E(_SF.a),b:E(B(_L4(_SX,E(_SO.a),new T(function(){return B(_Js(E(_SP).a));}),new T(function(){return B(_JG(E(_SP).b));}),_SF.b))),c:E(_SF.c),d:_SF.d,e:_SF.e,f:_SF.f,g:E(_SF.g),h:_SF.h,i:E(_SF.i),j:E(_SF.j),k:E(_SF.k)};_RU=_SZ;_RV=_T0;_RW=_T1;_RX=_T2;_RY=_T3;_RZ=_T4;_S0=_T5;_S1=_T6;_S2=_T7;_S3=_T8;_S4=_T9;_S5=_Ta;_S6=_Tb;_S7=_Tc;_S8=_Td;_S9=_Te;_Sa=_Tf;_Sb=_Tg;_Sc=_Th;_Sd=_Ti;_Se=_Tj;return __continue;}else{return E(_FI);}}}}})(_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7,_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se));if(_Sf!=__continue){return _Sf;}}},_Tk=function(_Tl,_Tm){while(1){var _Tn=E(_Tm);if(!_Tn._){return __Z;}else{var _To=_Tn.b,_Tp=E(_Tl);if(_Tp==1){return E(_To);}else{_Tl=_Tp-1|0;_Tm=_To;continue;}}}},_Tq=function(_Tr){var _Ts=E(_Tr);if(!_Ts._){return new T2(0,_S,_S);}else{var _Tt=E(_Ts.a),_Tu=new T(function(){var _Tv=B(_Tq(_Ts.b));return new T2(0,_Tv.a,_Tv.b);});return new T2(0,new T2(1,_Tt.a,new T(function(){return E(E(_Tu).a);})),new T2(1,_Tt.b,new T(function(){return E(E(_Tu).b);})));}},_Tw=32,_Tx=function(_Ty,_Tz,_TA,_TB){var _TC=E(_TB);if(!_TC._){return __Z;}else{var _TD=_TC.b;if(!B(_4A(_3L,_Ty,_TA))){var _TE=new T(function(){return B(_Tx(new T(function(){return E(_Ty)+1|0;}),_Tz,_TA,_TD));});return new T2(1,_TC.a,_TE);}else{var _TF=new T(function(){return B(_Tx(new T(function(){return E(_Ty)+1|0;}),_Tz,_TA,_TD));});return new T2(1,_Tz,_TF);}}},_TG=function(_TH,_TI){var _TJ=E(_TI);if(!_TJ._){return __Z;}else{var _TK=new T(function(){var _TL=B(_Tq(_TJ.a)),_TM=_TL.a,_TN=new T(function(){return B(_J5(0,_TH,_TM));});return B(_Gx(B(_Tx(_ru,_Tw,_TN,_TM)),new T(function(){return B(_Jc(0,_Ej,_TN,_TL.b));},1)));});return new T2(1,_TK,new T(function(){return B(_TG(_TH,_TJ.b));}));}},_TO=function(_TP,_TQ){var _TR=E(_TQ);return (_TR._==0)?__Z:new T2(1,_TP,new T(function(){return B(_TO(_TR.a,_TR.b));}));},_TS=new T(function(){return B(unCStr("init"));}),_TT=new T(function(){return B(_nk(_TS));}),_TU=function(_TV,_TW){var _TX=function(_TY){var _TZ=E(_TY);if(!_TZ._){return __Z;}else{var _U0=new T(function(){return B(_q(new T2(1,_TV,_S),new T(function(){return B(_TX(_TZ.b));},1)));},1);return new F(function(){return _q(_TZ.a,_U0);});}},_U1=B(_TX(_TW));if(!_U1._){return E(_TT);}else{return new F(function(){return _TO(_U1.a,_U1.b);});}},_U2=61,_U3=46,_U4=new T(function(){return B(_ed("Event.hs:(109,1)-(115,61)|function makeDecision"));}),_U5=new T(function(){return B(unCStr("sm"));}),_U6=new T(function(){return B(unCStr("rt"));}),_U7=new T(function(){return B(unCStr("rs"));}),_U8=new T(function(){return B(unCStr("rk"));}),_U9=new T(function(){return B(unCStr("if"));}),_Ua=new T(function(){return B(unCStr("hm"));}),_Ub=new T(function(){return B(unCStr("cleq"));}),_Uc=new T(function(){return B(unCStr("da"));}),_Ud=new T(function(){return B(unCStr("ct"));}),_Ue=function(_Uf,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB){var _UC=function(_UD,_UE){var _UF=function(_UG){if(!B(_qW(_UD,_Ud))){if(!B(_qW(_UD,_Uc))){var _UH=function(_UI){if(!B(_qW(_UD,_Ub))){var _UJ=function(_UK){if(!B(_qW(_UD,_rX))){if(!B(_qW(_UD,_Ua))){if(!B(_qW(_UD,_U9))){if(!B(_qW(_UD,_U8))){if(!B(_qW(_UD,_U7))){if(!B(_qW(_UD,_U6))){if(!B(_qW(_UD,_U5))){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{var _UL=E(_UA);return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E({_:0,a:E(_UL.a),b:E(_UL.b),c:E(_UL.c),d:E(_UL.d),e:E(_UL.e),f:E(_UL.f),g:E(_UL.g),h:E(_wE)}),v:E(_UB)};}}else{var _UM=B(_OO(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_UM.a),b:E(_UM.b),c:E(_UM.c),d:E(_UM.d),e:E(_UM.e),f:E(_UM.f),g:E(_UM.g),h:E(_UM.h),i:_UM.i,j:_UM.j,k:_UM.k,l:_UM.l,m:E(_UM.m),n:_UM.n,o:E(_UM.o),p:E(_UM.p),q:_UM.q,r:E(_UM.r),s:E(_UM.s),t:_UM.t,u:E(_UM.u),v:E(_UM.v)};}}else{var _UN=new T(function(){return B(_q(B(_A(0,600-B(_OD(_Ux,0))|0,_S)),new T(function(){if(_Uo>0){return B(_Tk(_Uo,_Ui));}else{return E(_Ui);}},1)));});if(0>=_Uo){var _UO=E(_UN);}else{var _UP=function(_UQ,_UR){var _US=E(_UQ);if(!_US._){return E(_UN);}else{var _UT=_US.a,_UU=E(_UR);return (_UU==1)?new T2(1,_UT,_UN):new T2(1,_UT,new T(function(){return B(_UP(_US.b,_UU-1|0));}));}},_UO=B(_UP(_Ui,_Uo));}return {_:0,a:E(_Ug),b:E(_Uh),c:E(_UO),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}}else{return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_UE),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}}else{var _UV=E(_UE);if(!_UV._){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{var _UW=_UV.a,_UX=E(_UV.b);if(!_UX._){return E(_U4);}else{var _UY=_UX.a,_UZ=B(_Ox(_Um)),_V0=_UZ.a,_V1=_UZ.b,_V2=function(_V3){if(!B(_4A(_qk,_UW,_V0))){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{if(!B(_qW(_UY,B(_6X(_V1,B(_MU(_qk,_UW,_V0))))))){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{return new F(function(){return _Ue(_V3,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}}},_V4=B(_TU(_U3,_UX.b));if(!_V4._){return new F(function(){return _V2(_S);});}else{var _V5=_V4.a,_V6=E(_V4.b);if(!_V6._){return new F(function(){return _V2(new T2(1,_V5,_S));});}else{var _V7=_V6.a,_V8=_V6.b,_V9=E(_V5);if(E(_V9)==47){if(!B(_4A(_qk,_UW,_V0))){return new F(function(){return _Ue(B(_Hd(47,_V7,_V8)).a,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}else{if(!B(_qW(_UY,B(_6X(_V1,B(_MU(_qk,_UW,_V0))))))){return new F(function(){return _Ue(B(_Hd(47,_V7,_V8)).a,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}else{return new F(function(){return _Ue(_S,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}}}else{if(!B(_4A(_qk,_UW,_V0))){var _Va=E(B(_Hd(47,_V7,_V8)).b);if(!_Va._){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{return new F(function(){return _Ue(_Va.a,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}}else{if(!B(_qW(_UY,B(_6X(_V1,B(_MU(_qk,_UW,_V0))))))){var _Vb=E(B(_Hd(47,_V7,_V8)).b);if(!_Vb._){return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}else{return new F(function(){return _Ue(_Vb.a,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}}else{return new F(function(){return _Ue(new T2(1,_V9,new T(function(){return E(B(_Hd(47,_V7,_V8)).a);})),_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB);});}}}}}}}}}else{var _Vc=E(_UA);return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E({_:0,a:E(_Vc.a),b:E(_Vc.b),c:E(_Vc.c),d:E(_Vc.d),e:E(_Vc.e),f:E(_Vc.f),g:E(_Vc.g),h:E(_wD)}),v:E(_UB)};}}else{var _Vd=E(_UA);return new F(function(){return _Q8(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_S,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_Vd.a,_Vd.b,_Vd.c,_Vd.d,_Vd.e,_Vd.f,_Vd.g,_Vd.h,_UB);});}},_Ve=E(_UD);if(!_Ve._){return new F(function(){return _UJ(_);});}else{if(E(_Ve.a)==109){if(!E(_Ve.b)._){var _Vf=B(_Hq(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vf.a),b:E(_Vf.b),c:E(_Vf.c),d:E(_Vf.d),e:E(_Vf.e),f:E(_Vf.f),g:E(_Vf.g),h:E(_Vf.h),i:_Vf.i,j:_Vf.j,k:_Vf.k,l:_Vf.l,m:E(_Vf.m),n:_Vf.n,o:E(_Vf.o),p:E(_Vf.p),q:_Vf.q,r:E(_Vf.r),s:E(_Vf.s),t:_Vf.t,u:E(_Vf.u),v:E(_Vf.v)};}else{return new F(function(){return _UJ(_);});}}else{return new F(function(){return _UJ(_);});}}}else{var _Vg=E(_Ug);return {_:0,a:E({_:0,a:E(_Vg.a),b:E(B(_TG(_U2,_Vg.b))),c:E(_Vg.c),d:_Vg.d,e:_Vg.e,f:_Vg.f,g:E(_Vg.g),h:_Vg.h,i:E(_Vg.i),j:E(_Vg.j),k:E(_Vg.k)}),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_Uk),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}},_Vh=E(_UD);if(!_Vh._){return new F(function(){return _UH(_);});}else{var _Vi=_Vh.b;switch(E(_Vh.a)){case 99:if(!E(_Vi)._){var _Vj=B(_LA(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vj.a),b:E(_Vj.b),c:E(_Vj.c),d:E(_Vj.d),e:E(_Vj.e),f:E(_Vj.f),g:E(_Vj.g),h:E(_Vj.h),i:_Vj.i,j:_Vj.j,k:_Vj.k,l:_Vj.l,m:E(_Vj.m),n:_Vj.n,o:E(_Vj.o),p:E(_Vj.p),q:_Vj.q,r:E(_Vj.r),s:E(_Vj.s),t:_Vj.t,u:E(_Vj.u),v:E(_Vj.v)};}else{return new F(function(){return _UH(_);});}break;case 112:if(!E(_Vi)._){var _Vk=B(_RR(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vk.a),b:E(_Vk.b),c:E(_Vk.c),d:E(_Vk.d),e:E(_Vk.e),f:E(_Vk.f),g:E(_Vk.g),h:E(_Vk.h),i:_Vk.i,j:_Vk.j,k:_Vk.k,l:_Vk.l,m:E(_Vk.m),n:_Vk.n,o:E(_Vk.o),p:E(_Vk.p),q:_Vk.q,r:E(_Vk.r),s:E(_Vk.s),t:_Vk.t,u:E(_Vk.u),v:E(_Vk.v)};}else{return new F(function(){return _UH(_);});}break;default:return new F(function(){return _UH(_);});}}}else{return {_:0,a:E(_Ug),b:E(_Uh),c:E(_Ui),d:E(_Uj),e:E(_S),f:E(_Ul),g:E(_Um),h:E(_Un),i:_Uo,j:_Up,k:_Uq,l:_Ur,m:E(_Us),n:_Ut,o:E(_Uu),p:E(_Uv),q:_Uw,r:E(_Ux),s:E(_Uy),t:_Uz,u:E(_UA),v:E(_UB)};}}else{var _Vl=B(_JI(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vl.a),b:E(_Vl.b),c:E(_Vl.c),d:E(_Vl.d),e:E(_Vl.e),f:E(_Vl.f),g:E(_Vl.g),h:E(_Vl.h),i:_Vl.i,j:_Vl.j,k:_Vl.k,l:_Vl.l,m:E(_Vl.m),n:_Vl.n,o:E(_Vl.o),p:E(_Vl.p),q:_Vl.q,r:E(_Vl.r),s:E(_Vl.s),t:_Vl.t,u:E(_Vl.u),v:E(_Vl.v)};}},_Vm=E(_UD);if(!_Vm._){return new F(function(){return _UF(_);});}else{var _Vn=_Vm.b;switch(E(_Vm.a)){case 100:if(!E(_Vn)._){var _Vo=B(_Nk(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vo.a),b:E(_Vo.b),c:E(_Vo.c),d:E(_Vo.d),e:E(_Vo.e),f:E(_Vo.f),g:E(_Vo.g),h:E(_Vo.h),i:_Vo.i,j:_Vo.j,k:_Vo.k,l:_Vo.l,m:E(_Vo.m),n:_Vo.n,o:E(_Vo.o),p:E(_Vo.p),q:_Vo.q,r:E(_Vo.r),s:E(_Vo.s),t:_Vo.t,u:E(_Vo.u),v:E(_Vo.v)};}else{return new F(function(){return _UF(_);});}break;case 101:if(!E(_Vn)._){var _Vp=B(_qn(_UE,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));return {_:0,a:E(_Vp.a),b:E(_Vp.b),c:E(_Vp.c),d:E(_Vp.d),e:E(_Vp.e),f:E(_Vp.f),g:E(_Vp.g),h:E(_Vp.h),i:_Vp.i,j:_Vp.j,k:_Vp.k,l:_Vp.l,m:E(_Vp.m),n:_Vp.n,o:E(_Vp.o),p:E(_Vp.p),q:_Vp.q,r:E(_Vp.r),s:E(_Vp.s),t:_Vp.t,u:E(_Vp.u),v:E(_Vp.v)};}else{return new F(function(){return _UF(_);});}break;default:return new F(function(){return _UF(_);});}}},_Vq=E(_Uf);if(!_Vq._){return new F(function(){return _UC(_S,_S);});}else{var _Vr=_Vq.a,_Vs=E(_Vq.b);if(!_Vs._){return new F(function(){return _UC(new T2(1,_Vr,_S),_S);});}else{var _Vt=E(_Vr),_Vu=new T(function(){var _Vv=B(_Hd(46,_Vs.a,_Vs.b));return new T2(0,_Vv.a,_Vv.b);});if(E(_Vt)==46){return new F(function(){return _UC(_S,new T2(1,new T(function(){return E(E(_Vu).a);}),new T(function(){return E(E(_Vu).b);})));});}else{return new F(function(){return _UC(new T2(1,_Vt,new T(function(){return E(E(_Vu).a);})),new T(function(){return E(E(_Vu).b);}));});}}}},_Vw=new T(function(){return B(unCStr("last"));}),_Vx=new T(function(){return B(_nk(_Vw));}),_Vy=32,_Vz=0,_VA=65306,_VB=125,_VC=new T1(0,1),_VD=function(_VE,_VF,_VG,_VH,_VI){var _VJ=new T(function(){return E(_VI).i;}),_VK=new T(function(){var _VL=E(_VF)/28,_VM=_VL&4294967295;if(_VL>=_VM){return _VM-1|0;}else{return (_VM-1|0)-1|0;}}),_VN=new T(function(){if(!E(E(_VH).h)){return E(_je);}else{return 2+(E(E(E(_VI).b).b)+3|0)|0;}}),_VO=new T(function(){if(!E(_VJ)){return new T2(0,_VK,_VN);}else{return E(E(_VI).h);}}),_VP=new T(function(){return E(E(_VI).c);}),_VQ=new T(function(){var _VR=E(_VJ)+1|0;if(0>=_VR){return E(_Vy);}else{var _VS=B(_pU(_VR,_VP));if(!_VS._){return E(_Vy);}else{return B(_og(_VS.a,_VS.b,_Vx));}}}),_VT=new T(function(){var _VU=E(_VQ);switch(E(_VU)){case 125:return E(_Vy);break;case 12289:return E(_Vy);break;case 12290:return E(_Vy);break;default:return E(_VU);}}),_VV=new T(function(){if(E(_VT)==10){return true;}else{return false;}}),_VW=new T(function(){return E(E(_VO).b);}),_VX=new T(function(){if(!E(_VV)){if(E(_VT)==12300){return E(_jd);}else{return E(_VI).j;}}else{return E(_Vz);}}),_VY=new T(function(){return E(E(_VO).a);}),_VZ=new T(function(){if(E(_VT)==65306){return true;}else{return false;}}),_W0=new T(function(){if(!E(_VZ)){if(!E(_VV)){var _W1=E(_VW);if((_W1+1)*20<=E(_VG)-10){return new T2(0,_VY,_W1+1|0);}else{return new T2(0,new T(function(){return E(_VY)-1|0;}),_VN);}}else{return new T2(0,new T(function(){return E(_VY)-1|0;}),_VN);}}else{return new T2(0,_VY,_VW);}}),_W2=new T(function(){if(E(E(_W0).a)==1){if(E(_VY)==1){return false;}else{return true;}}else{return false;}}),_W3=new T(function(){return B(_mz(_VP,0))-1|0;}),_W4=new T(function(){if(!E(_VZ)){return __Z;}else{return B(_qc(_VA,E(_VJ),_VP));}}),_W5=new T(function(){if(E(_VT)==123){return true;}else{return false;}}),_W6=new T(function(){if(!E(_W5)){return __Z;}else{return B(_qc(_VB,E(_VJ),_VP));}}),_W7=new T(function(){if(!E(_VZ)){if(!E(_W5)){return E(_jd);}else{return B(_mz(_W6,0))+2|0;}}else{return B(_mz(_W4,0))+2|0;}}),_W8=new T(function(){var _W9=E(_VI),_Wa=_W9.a,_Wb=_W9.b,_Wc=_W9.c,_Wd=_W9.d,_We=_W9.e,_Wf=_W9.f,_Wg=_W9.g,_Wh=_W9.h,_Wi=_W9.j,_Wj=_W9.k,_Wk=_W9.l,_Wl=_W9.m,_Wm=_W9.n,_Wn=_W9.o,_Wo=_W9.p,_Wp=_W9.q,_Wq=_W9.r,_Wr=_W9.s,_Ws=_W9.t,_Wt=_W9.v,_Wu=E(_VJ),_Wv=E(_W7);if((_Wu+_Wv|0)<=E(_W3)){var _Ww=E(_VH),_Wx=_Ww.a,_Wy=_Ww.b,_Wz=_Ww.c,_WA=_Ww.e,_WB=_Ww.f,_WC=_Ww.g,_WD=_Ww.h;if(E(_VQ)==12290){var _WE=true;}else{var _WE=false;}if(!E(_W5)){return {_:0,a:E(_Wa),b:E(_Wb),c:E(_Wc),d:E(_Wd),e:E(_We),f:E(_Wf),g:E(_Wg),h:E(_Wh),i:_Wu+_Wv|0,j:_Wi,k:_Wj,l:_Wk,m:E(_Wl),n:_Wm,o:E(_Wn),p:E(_Wo),q:_Wp,r:E(_Wq),s:E(_Wr),t:_Ws,u:E({_:0,a:E(_Wx),b:E(_Wy),c:E(_Wz),d:E(_WE),e:E(_WA),f:E(_WB),g:E(_WC),h:E(_WD)}),v:E(_Wt)};}else{return B(_Ue(_W6,_Wa,_Wb,_Wc,_Wd,_We,_Wf,_Wg,_Wh,_Wu+_Wv|0,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,{_:0,a:E(_Wx),b:E(_Wy),c:E(_Wz),d:E(_WE),e:E(_WA),f:E(_WB),g:E(_WC),h:E(_WD)},_Wt));}}else{var _WF=E(_VH),_WG=_WF.a,_WH=_WF.b,_WI=_WF.c,_WJ=_WF.e,_WK=_WF.f,_WL=_WF.g,_WM=_WF.h;if(E(_VQ)==12290){var _WN=true;}else{var _WN=false;}if(!E(_W5)){return {_:0,a:E(_Wa),b:E(_Wb),c:E(_Wc),d:E(_Wd),e:E(_We),f:E(_Wf),g:E(_Wg),h:E(_Wh),i:0,j:_Wi,k:_Wj,l:_Wk,m:E(_Wl),n:_Wm,o:E(_Wn),p:E(_Wo),q:_Wp,r:E(_Wq),s:E(_Wr),t:_Ws,u:E({_:0,a:E(_WG),b:E(_WH),c:E(_WI),d:E(_WN),e:E(_WJ),f:E(_WK),g:E(_WL),h:E(_WM)}),v:E(_Wt)};}else{return B(_Ue(_W6,_Wa,_Wb,_Wc,_Wd,_We,_Wf,_Wg,_Wh,0,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,{_:0,a:E(_WG),b:E(_WH),c:E(_WI),d:E(_WN),e:E(_WJ),f:E(_WK),g:E(_WL),h:E(_WM)},_Wt));}}}),_WO=new T(function(){return E(E(_W8).u);}),_WP=new T(function(){if(!E(_VJ)){return E(_Vz);}else{return E(_W8).k;}}),_WQ=new T(function(){var _WR=B(_oa(B(_o8(_VE)))),_WS=new T(function(){var _WT=B(_pB(_VE,E(_VF)/16)),_WU=_WT.a;if(E(_WT.b)>=0){return E(_WU);}else{return B(A3(_oN,_WR,_WU,new T(function(){return B(A2(_hk,_WR,_VC));})));}});return B(A3(_oN,_WR,_WS,new T(function(){return B(A2(_hk,_WR,_ht));})));});return {_:0,a:_VT,b:_VY,c:_VW,d:new T(function(){if(E(_VN)!=E(_VW)){return E(_VY);}else{return E(_VY)+1|0;}}),e:new T(function(){var _WV=E(_VW);if(E(_VN)!=_WV){return _WV-1|0;}else{var _WW=(E(_VG)-10)/20,_WX=_WW&4294967295;if(_WW>=_WX){return _WX;}else{return _WX-1|0;}}}),f:_VN,g:_VJ,h:_VP,i:new T(function(){return B(_6X(_ja,E(_VX)));}),j:_W4,k:_VK,l:_WQ,m:_WP,n:_jf,o:_VZ,p:_W5,q:_W2,r:_WO,s:_W8,t:new T(function(){var _WY=E(_W8),_WZ=_WY.a,_X0=_WY.b,_X1=_WY.c,_X2=_WY.d,_X3=_WY.e,_X4=_WY.f,_X5=_WY.g,_X6=_WY.i,_X7=_WY.l,_X8=_WY.m,_X9=_WY.n,_Xa=_WY.o,_Xb=_WY.p,_Xc=_WY.q,_Xd=_WY.r,_Xe=_WY.s,_Xf=_WY.t,_Xg=_WY.v;if(!E(_W2)){var _Xh=E(_W0);}else{var _Xh=new T2(0,_VY,_VN);}var _Xi=E(_VX);if(!E(_W2)){var _Xj=E(_WO);return {_:0,a:E(_WZ),b:E(_X0),c:E(_X1),d:E(_X2),e:E(_X3),f:E(_X4),g:E(_X5),h:E(_Xh),i:_X6,j:_Xi,k:E(_WP),l:_X7,m:E(_X8),n:_X9,o:E(_Xa),p:E(_Xb),q:_Xc,r:E(_Xd),s:E(_Xe),t:_Xf,u:E({_:0,a:E(_Xj.a),b:E(_Xj.b),c:(E(_VJ)+E(_W7)|0)<=E(_W3),d:E(_Xj.d),e:E(_Xj.e),f:E(_Xj.f),g:E(_Xj.g),h:E(_Xj.h)}),v:E(_Xg)};}else{var _Xk=E(_WO);return {_:0,a:E(_WZ),b:E(_X0),c:E(_X1),d:E(_X2),e:E(_X3),f:E(_X4),g:E(_X5),h:E(_Xh),i:_X6,j:_Xi,k:E(_WP)+1|0,l:_X7,m:E(_X8),n:_X9,o:E(_Xa),p:E(_Xb),q:_Xc,r:E(_Xd),s:E(_Xe),t:_Xf,u:E({_:0,a:E(_Xk.a),b:E(_Xk.b),c:(E(_VJ)+E(_W7)|0)<=E(_W3),d:E(_Xk.d),e:E(_Xk.e),f:E(_Xk.f),g:E(_Xk.g),h:E(_Xk.h)}),v:E(_Xg)};}})};},_Xl=function(_Xm){var _Xn=E(_Xm);if(!_Xn._){return new T2(0,_S,_S);}else{var _Xo=E(_Xn.a),_Xp=new T(function(){var _Xq=B(_Xl(_Xn.b));return new T2(0,_Xq.a,_Xq.b);});return new T2(0,new T2(1,_Xo.a,new T(function(){return E(E(_Xp).a);})),new T2(1,_Xo.b,new T(function(){return E(E(_Xp).b);})));}},_Xr=42,_Xs=32,_Xt=function(_Xu,_Xv,_Xw){var _Xx=E(_Xu);if(!_Xx._){return __Z;}else{var _Xy=_Xx.a,_Xz=_Xx.b;if(_Xv!=_Xw){var _XA=E(_Xy);return (_XA._==0)?E(_nn):(E(_XA.a)==42)?new T2(1,new T2(1,_Xs,_XA.b),new T(function(){return B(_Xt(_Xz,_Xv,_Xw+1|0));})):new T2(1,new T2(1,_Xs,_XA),new T(function(){return B(_Xt(_Xz,_Xv,_Xw+1|0));}));}else{var _XB=E(_Xy);return (_XB._==0)?E(_nn):(E(_XB.a)==42)?new T2(1,new T2(1,_Xs,_XB),new T(function(){return B(_Xt(_Xz,_Xv,_Xw+1|0));})):new T2(1,new T2(1,_Xr,_XB),new T(function(){return B(_Xt(_Xz,_Xv,_Xw+1|0));}));}}},_XC=new T(function(){return B(unCStr("\n\n"));}),_XD=function(_XE){var _XF=E(_XE);if(!_XF._){return __Z;}else{var _XG=new T(function(){return B(_q(_XC,new T(function(){return B(_XD(_XF.b));},1)));},1);return new F(function(){return _q(_XF.a,_XG);});}},_XH=function(_XI,_XJ,_XK){var _XL=new T(function(){var _XM=new T(function(){var _XN=E(_XJ);if(!_XN._){return B(_XD(_S));}else{var _XO=_XN.a,_XP=_XN.b,_XQ=E(_XK);if(!_XQ){var _XR=E(_XO);if(!_XR._){return E(_nn);}else{if(E(_XR.a)==42){return B(_XD(new T2(1,new T2(1,_Xs,_XR),new T(function(){return B(_Xt(_XP,0,1));}))));}else{return B(_XD(new T2(1,new T2(1,_Xr,_XR),new T(function(){return B(_Xt(_XP,0,1));}))));}}}else{var _XS=E(_XO);if(!_XS._){return E(_nn);}else{if(E(_XS.a)==42){return B(_XD(new T2(1,new T2(1,_Xs,_XS.b),new T(function(){return B(_Xt(_XP,_XQ,1));}))));}else{return B(_XD(new T2(1,new T2(1,_Xs,_XS),new T(function(){return B(_Xt(_XP,_XQ,1));}))));}}}}});return B(unAppCStr("\n\n",_XM));},1);return new F(function(){return _q(_XI,_XL);});},_XT=function(_XU){return E(E(_XU).c);},_XV=function(_XW,_XX,_XY,_XZ,_Y0,_Y1,_Y2,_Y3,_Y4){var _Y5=new T(function(){if(!E(_XX)){return E(_XY);}else{return false;}}),_Y6=new T(function(){if(!E(_XX)){return false;}else{return E(E(_Y3).g);}}),_Y7=new T(function(){if(!E(_Y6)){if(!E(_Y5)){return B(A2(_hk,_XW,_hs));}else{return B(A3(_mE,_XW,new T(function(){return B(A3(_mE,_XW,_Y1,_Y2));}),new T(function(){return B(A2(_hk,_XW,_VC));})));}}else{return B(A3(_mE,_XW,_Y1,_Y2));}}),_Y8=new T(function(){if(!E(_Y6)){if(!E(_Y5)){return __Z;}else{var _Y9=E(_XZ)+1|0;if(0>=_Y9){return __Z;}else{return B(_pU(_Y9,_Y0));}}}else{return B(_XH(B(_XT(_Y4)),new T(function(){return E(B(_Xl(E(_Y4).m)).a);},1),new T(function(){return E(_Y4).n;},1)));}});return new T4(0,_Y6,_Y5,_Y8,_Y7);},_Ya=function(_Yb,_Yc,_Yd){var _Ye=E(_Yc),_Yf=E(_Yd),_Yg=new T(function(){var _Yh=B(_hg(_Yb)),_Yi=B(_Ya(_Yb,_Yf,B(A3(_oN,_Yh,new T(function(){return B(A3(_mE,_Yh,_Yf,_Yf));}),_Ye))));return new T2(1,_Yi.a,_Yi.b);});return new T2(0,_Ye,_Yg);},_Yj=1,_Yk=new T(function(){var _Yl=B(_Ya(_gh,_hS,_Yj));return new T2(1,_Yl.a,_Yl.b);}),_Ym=function(_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_){var _YV={_:0,a:E(_YM),b:E(_YN),c:E(_YO),d:E(_YP),e:E(_YQ),f:E(_YR),g:E(_YS),h:E(_YT)};if(!E(_YO)){return {_:0,a:E(_Yq),b:E(new T2(0,_Yr,_Ys)),c:E(_Yt),d:E(_Yu),e:E(_Yv),f:E(_Yw),g:E(_Yx),h:E(new T2(0,_Yy,_Yz)),i:_YA,j:_YB,k:_YC,l:_YD,m:E(_YE),n:_YF,o:E(_YG),p:E(_YH),q:_YI,r:E(_YJ),s:E(_YK),t:_YL,u:E(_YV),v:E(_YU)};}else{if(!E(_YP)){var _YW=B(_VD(_bY,_Yo,_Yp,_YV,{_:0,a:E(_Yq),b:E(new T2(0,_Yr,_Ys)),c:E(_Yt),d:E(_Yu),e:E(_Yv),f:E(_Yw),g:E(_Yx),h:E(new T2(0,_Yy,_Yz)),i:_YA,j:_YB,k:_YC,l:_YD,m:E(_YE),n:_YF,o:E(_YG),p:E(_YH),q:_YI,r:E(_YJ),s:E(_YK),t:_YL,u:E(_YV),v:E(_YU)})),_YX=_YW.d,_YY=_YW.e,_YZ=_YW.f,_Z0=_YW.i,_Z1=_YW.n,_Z2=_YW.p,_Z3=_YW.q,_Z4=_YW.s,_Z5=_YW.t;if(!E(_YW.o)){var _Z6=B(_XV(_bt,_Z2,_Z3,_YW.g,_YW.h,_YW.k,_YW.m,_YW.r,_Z4)),_Z7=_Z6.c,_Z8=_Z6.d,_Z9=function(_){var _Za=function(_){if(!E(_Z2)){if(!E(_Z3)){var _Zb=B(_iH(E(_Yn).a,_Z0,_jb,_hS,_YW.b,_YW.c,_YW.a,_));return _Z5;}else{return _Z5;}}else{return _Z5;}};if(!E(_Z6.b)){return new F(function(){return _Za(_);});}else{var _Zc=E(_Yn),_Zd=_Zc.a,_Ze=_Zc.b,_Zf=B(_nW(_Zd,_Ze,_YW.l,_Z4,_)),_Zg=B(_lu(_Zd,_Ze,_Yp,0,_YZ,_Z8,_YZ,_Z7,_));return new F(function(){return _Za(_);});}};if(!E(_Z6.a)){return new F(function(){return _Z9(_);});}else{var _Zh=B(_jg(_Yn,_Yp,0,_YZ,_Z8,_YZ,_Z7,_));return new F(function(){return _Z9(_);});}}else{var _Zi=E(_YW.j);if(!_Zi._){return _Z5;}else{var _Zj=E(_Yk);if(!_Zj._){return _Z5;}else{var _Zk=E(_Yn).a,_Zl=B(_iH(_Zk,_Z0,_Z1,_Zj.a,_YX,_YY,_Zi.a,_)),_Zm=function(_Zn,_Zo,_){while(1){var _Zp=E(_Zn);if(!_Zp._){return _gK;}else{var _Zq=E(_Zo);if(!_Zq._){return _gK;}else{var _Zr=B(_iH(_Zk,_Z0,_Z1,_Zq.a,_YX,_YY,_Zp.a,_));_Zn=_Zp.b;_Zo=_Zq.b;continue;}}}},_Zs=B(_Zm(_Zi.b,_Zj.b,_));return _Z5;}}}}else{return {_:0,a:E(_Yq),b:E(new T2(0,_Yr,_Ys)),c:E(_Yt),d:E(_Yu),e:E(_Yv),f:E(_Yw),g:E(_Yx),h:E(new T2(0,_Yy,_Yz)),i:_YA,j:_YB,k:_YC,l:_YD,m:E(_YE),n:_YF,o:E(_YG),p:E(_YH),q:_YI,r:E(_YJ),s:E(_YK),t:_YL,u:E(_YV),v:E(_YU)};}}},_Zt=function(_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZA,_ZB,_ZC,_ZD,_ZE,_ZF,_ZG,_ZH,_ZI,_ZJ,_ZK,_ZL,_ZM,_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT,_ZU,_ZV,_ZW,_ZX,_ZY,_ZZ,_100,_101,_){while(1){var _102=B(_Ym(_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZA,_ZB,_ZC,_ZD,_ZE,_ZF,_ZG,_ZH,_ZI,_ZJ,_ZK,_ZL,_ZM,_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT,_ZU,_ZV,_ZW,_ZX,_ZY,_ZZ,_100,_101,_)),_103=E(_102),_104=_103.a,_105=_103.c,_106=_103.d,_107=_103.e,_108=_103.f,_109=_103.g,_10a=_103.i,_10b=_103.j,_10c=_103.k,_10d=_103.l,_10e=_103.m,_10f=_103.n,_10g=_103.o,_10h=_103.p,_10i=_103.q,_10j=_103.r,_10k=_103.s,_10l=_103.t,_10m=_103.v,_10n=E(_103.u),_10o=_10n.a,_10p=_10n.b,_10q=_10n.c,_10r=_10n.e,_10s=_10n.g,_10t=_10n.h,_10u=E(_103.b),_10v=E(_103.h);if(!E(_10n.d)){if(!E(_ZV)){return {_:0,a:E(_104),b:E(_10u),c:E(_105),d:E(_106),e:E(_107),f:E(_108),g:E(_109),h:E(_10v),i:_10a,j:_10b,k:_10c,l:_10d,m:E(_10e),n:_10f,o:E(_10g),p:E(_10h),q:_10i,r:E(_10j),s:E(_10k),t:_10l,u:E({_:0,a:E(_10o),b:E(_10p),c:E(_10q),d:E(_wD),e:E(_10r),f:E(_wD),g:E(_10s),h:E(_10t)}),v:E(_10m)};}else{_Zx=_104;_Zy=_10u.a;_Zz=_10u.b;_ZA=_105;_ZB=_106;_ZC=_107;_ZD=_108;_ZE=_109;_ZF=_10v.a;_ZG=_10v.b;_ZH=_10a;_ZI=_10b;_ZJ=_10c;_ZK=_10d;_ZL=_10e;_ZM=_10f;_ZN=_10g;_ZO=_10h;_ZP=_10i;_ZQ=_10j;_ZR=_10k;_ZS=_10l;_ZT=_10o;_ZU=_10p;_ZV=_10q;_ZW=_wD;_ZX=_10r;_ZY=_10n.f;_ZZ=_10s;_100=_10t;_101=_10m;continue;}}else{return {_:0,a:E(_104),b:E(_10u),c:E(_105),d:E(_106),e:E(_107),f:E(_108),g:E(_109),h:E(_10v),i:_10a,j:_10b,k:_10c,l:_10d,m:E(_10e),n:_10f,o:E(_10g),p:E(_10h),q:_10i,r:E(_10j),s:E(_10k),t:_10l,u:E({_:0,a:E(_10o),b:E(_10p),c:E(_10q),d:E(_wE),e:E(_10r),f:E(_wD),g:E(_10s),h:E(_10t)}),v:E(_10m)};}}},_10w=function(_10x,_10y,_10z,_10A,_10B,_10C,_10D,_10E,_10F,_10G,_10H,_10I,_10J,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,_10S,_10T,_10U,_10V,_10W,_10X,_10Y,_10Z,_110,_111,_112,_113,_){var _114=B(_Ym(_10x,_10y,_10z,_10A,_10B,_10C,_10D,_10E,_10F,_10G,_10H,_10I,_10J,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,_10S,_10T,_10U,_10V,_10W,_10X,_wE,_10Y,_10Z,_110,_111,_112,_113,_)),_115=E(_114),_116=_115.a,_117=_115.c,_118=_115.d,_119=_115.e,_11a=_115.f,_11b=_115.g,_11c=_115.i,_11d=_115.j,_11e=_115.k,_11f=_115.l,_11g=_115.m,_11h=_115.n,_11i=_115.o,_11j=_115.p,_11k=_115.q,_11l=_115.r,_11m=_115.s,_11n=_115.t,_11o=_115.v,_11p=E(_115.u),_11q=_11p.a,_11r=_11p.b,_11s=_11p.c,_11t=_11p.e,_11u=_11p.g,_11v=_11p.h,_11w=E(_115.b),_11x=E(_115.h);if(!E(_11p.d)){return new F(function(){return _Zt(_10x,_10y,_10z,_116,_11w.a,_11w.b,_117,_118,_119,_11a,_11b,_11x.a,_11x.b,_11c,_11d,_11e,_11f,_11g,_11h,_11i,_11j,_11k,_11l,_11m,_11n,_11q,_11r,_11s,_wD,_11t,_11p.f,_11u,_11v,_11o,_);});}else{return {_:0,a:E(_116),b:E(_11w),c:E(_117),d:E(_118),e:E(_119),f:E(_11a),g:E(_11b),h:E(_11x),i:_11c,j:_11d,k:_11e,l:_11f,m:E(_11g),n:_11h,o:E(_11i),p:E(_11j),q:_11k,r:E(_11l),s:E(_11m),t:_11n,u:E({_:0,a:E(_11q),b:E(_11r),c:E(_11s),d:E(_wE),e:E(_11t),f:E(_wD),g:E(_11u),h:E(_11v)}),v:E(_11o)};}},_11y=function(_11z,_11A){while(1){var _11B=E(_11z);if(!_11B._){return (E(_11A)._==0)?1:0;}else{var _11C=E(_11A);if(!_11C._){return 2;}else{var _11D=E(_11B.a),_11E=E(_11C.a);if(_11D!=_11E){return (_11D>_11E)?2:0;}else{_11z=_11B.b;_11A=_11C.b;continue;}}}}},_11F=new T0(1),_11G=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_11H=function(_11I){return new F(function(){return err(_11G);});},_11J=new T(function(){return B(_11H(_));}),_11K=function(_11L,_11M,_11N,_11O){var _11P=E(_11N);if(!_11P._){var _11Q=_11P.a,_11R=E(_11O);if(!_11R._){var _11S=_11R.a,_11T=_11R.b,_11U=_11R.c;if(_11S<=(imul(3,_11Q)|0)){return new T5(0,(1+_11Q|0)+_11S|0,E(_11L),_11M,E(_11P),E(_11R));}else{var _11V=E(_11R.d);if(!_11V._){var _11W=_11V.a,_11X=_11V.b,_11Y=_11V.c,_11Z=_11V.d,_120=E(_11R.e);if(!_120._){var _121=_120.a;if(_11W>=(imul(2,_121)|0)){var _122=function(_123){var _124=E(_11L),_125=E(_11V.e);return (_125._==0)?new T5(0,(1+_11Q|0)+_11S|0,E(_11X),_11Y,E(new T5(0,(1+_11Q|0)+_123|0,E(_124),_11M,E(_11P),E(_11Z))),E(new T5(0,(1+_121|0)+_125.a|0,E(_11T),_11U,E(_125),E(_120)))):new T5(0,(1+_11Q|0)+_11S|0,E(_11X),_11Y,E(new T5(0,(1+_11Q|0)+_123|0,E(_124),_11M,E(_11P),E(_11Z))),E(new T5(0,1+_121|0,E(_11T),_11U,E(_11F),E(_120))));},_126=E(_11Z);if(!_126._){return new F(function(){return _122(_126.a);});}else{return new F(function(){return _122(0);});}}else{return new T5(0,(1+_11Q|0)+_11S|0,E(_11T),_11U,E(new T5(0,(1+_11Q|0)+_11W|0,E(_11L),_11M,E(_11P),E(_11V))),E(_120));}}else{return E(_11J);}}else{return E(_11J);}}}else{return new T5(0,1+_11Q|0,E(_11L),_11M,E(_11P),E(_11F));}}else{var _127=E(_11O);if(!_127._){var _128=_127.a,_129=_127.b,_12a=_127.c,_12b=_127.e,_12c=E(_127.d);if(!_12c._){var _12d=_12c.a,_12e=_12c.b,_12f=_12c.c,_12g=_12c.d,_12h=E(_12b);if(!_12h._){var _12i=_12h.a;if(_12d>=(imul(2,_12i)|0)){var _12j=function(_12k){var _12l=E(_11L),_12m=E(_12c.e);return (_12m._==0)?new T5(0,1+_128|0,E(_12e),_12f,E(new T5(0,1+_12k|0,E(_12l),_11M,E(_11F),E(_12g))),E(new T5(0,(1+_12i|0)+_12m.a|0,E(_129),_12a,E(_12m),E(_12h)))):new T5(0,1+_128|0,E(_12e),_12f,E(new T5(0,1+_12k|0,E(_12l),_11M,E(_11F),E(_12g))),E(new T5(0,1+_12i|0,E(_129),_12a,E(_11F),E(_12h))));},_12n=E(_12g);if(!_12n._){return new F(function(){return _12j(_12n.a);});}else{return new F(function(){return _12j(0);});}}else{return new T5(0,1+_128|0,E(_129),_12a,E(new T5(0,1+_12d|0,E(_11L),_11M,E(_11F),E(_12c))),E(_12h));}}else{return new T5(0,3,E(_12e),_12f,E(new T5(0,1,E(_11L),_11M,E(_11F),E(_11F))),E(new T5(0,1,E(_129),_12a,E(_11F),E(_11F))));}}else{var _12o=E(_12b);return (_12o._==0)?new T5(0,3,E(_129),_12a,E(new T5(0,1,E(_11L),_11M,E(_11F),E(_11F))),E(_12o)):new T5(0,2,E(_11L),_11M,E(_11F),E(_127));}}else{return new T5(0,1,E(_11L),_11M,E(_11F),E(_11F));}}},_12p=function(_12q,_12r){return new T5(0,1,E(_12q),_12r,E(_11F),E(_11F));},_12s=function(_12t,_12u,_12v){var _12w=E(_12v);if(!_12w._){return new F(function(){return _11K(_12w.b,_12w.c,_12w.d,B(_12s(_12t,_12u,_12w.e)));});}else{return new F(function(){return _12p(_12t,_12u);});}},_12x=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_12y=function(_12z){return new F(function(){return err(_12x);});},_12A=new T(function(){return B(_12y(_));}),_12B=function(_12C,_12D,_12E,_12F){var _12G=E(_12F);if(!_12G._){var _12H=_12G.a,_12I=E(_12E);if(!_12I._){var _12J=_12I.a,_12K=_12I.b,_12L=_12I.c;if(_12J<=(imul(3,_12H)|0)){return new T5(0,(1+_12J|0)+_12H|0,E(_12C),_12D,E(_12I),E(_12G));}else{var _12M=E(_12I.d);if(!_12M._){var _12N=_12M.a,_12O=E(_12I.e);if(!_12O._){var _12P=_12O.a,_12Q=_12O.b,_12R=_12O.c,_12S=_12O.d;if(_12P>=(imul(2,_12N)|0)){var _12T=function(_12U){var _12V=E(_12O.e);return (_12V._==0)?new T5(0,(1+_12J|0)+_12H|0,E(_12Q),_12R,E(new T5(0,(1+_12N|0)+_12U|0,E(_12K),_12L,E(_12M),E(_12S))),E(new T5(0,(1+_12H|0)+_12V.a|0,E(_12C),_12D,E(_12V),E(_12G)))):new T5(0,(1+_12J|0)+_12H|0,E(_12Q),_12R,E(new T5(0,(1+_12N|0)+_12U|0,E(_12K),_12L,E(_12M),E(_12S))),E(new T5(0,1+_12H|0,E(_12C),_12D,E(_11F),E(_12G))));},_12W=E(_12S);if(!_12W._){return new F(function(){return _12T(_12W.a);});}else{return new F(function(){return _12T(0);});}}else{return new T5(0,(1+_12J|0)+_12H|0,E(_12K),_12L,E(_12M),E(new T5(0,(1+_12H|0)+_12P|0,E(_12C),_12D,E(_12O),E(_12G))));}}else{return E(_12A);}}else{return E(_12A);}}}else{return new T5(0,1+_12H|0,E(_12C),_12D,E(_11F),E(_12G));}}else{var _12X=E(_12E);if(!_12X._){var _12Y=_12X.a,_12Z=_12X.b,_130=_12X.c,_131=_12X.e,_132=E(_12X.d);if(!_132._){var _133=_132.a,_134=E(_131);if(!_134._){var _135=_134.a,_136=_134.b,_137=_134.c,_138=_134.d;if(_135>=(imul(2,_133)|0)){var _139=function(_13a){var _13b=E(_134.e);return (_13b._==0)?new T5(0,1+_12Y|0,E(_136),_137,E(new T5(0,(1+_133|0)+_13a|0,E(_12Z),_130,E(_132),E(_138))),E(new T5(0,1+_13b.a|0,E(_12C),_12D,E(_13b),E(_11F)))):new T5(0,1+_12Y|0,E(_136),_137,E(new T5(0,(1+_133|0)+_13a|0,E(_12Z),_130,E(_132),E(_138))),E(new T5(0,1,E(_12C),_12D,E(_11F),E(_11F))));},_13c=E(_138);if(!_13c._){return new F(function(){return _139(_13c.a);});}else{return new F(function(){return _139(0);});}}else{return new T5(0,1+_12Y|0,E(_12Z),_130,E(_132),E(new T5(0,1+_135|0,E(_12C),_12D,E(_134),E(_11F))));}}else{return new T5(0,3,E(_12Z),_130,E(_132),E(new T5(0,1,E(_12C),_12D,E(_11F),E(_11F))));}}else{var _13d=E(_131);return (_13d._==0)?new T5(0,3,E(_13d.b),_13d.c,E(new T5(0,1,E(_12Z),_130,E(_11F),E(_11F))),E(new T5(0,1,E(_12C),_12D,E(_11F),E(_11F)))):new T5(0,2,E(_12C),_12D,E(_12X),E(_11F));}}else{return new T5(0,1,E(_12C),_12D,E(_11F),E(_11F));}}},_13e=function(_13f,_13g,_13h){var _13i=E(_13h);if(!_13i._){return new F(function(){return _12B(_13i.b,_13i.c,B(_13e(_13f,_13g,_13i.d)),_13i.e);});}else{return new F(function(){return _12p(_13f,_13g);});}},_13j=function(_13k,_13l,_13m,_13n,_13o,_13p,_13q){return new F(function(){return _12B(_13n,_13o,B(_13e(_13k,_13l,_13p)),_13q);});},_13r=function(_13s,_13t,_13u,_13v,_13w,_13x,_13y,_13z){var _13A=E(_13u);if(!_13A._){var _13B=_13A.a,_13C=_13A.b,_13D=_13A.c,_13E=_13A.d,_13F=_13A.e;if((imul(3,_13B)|0)>=_13v){if((imul(3,_13v)|0)>=_13B){return new T5(0,(_13B+_13v|0)+1|0,E(_13s),_13t,E(_13A),E(new T5(0,_13v,E(_13w),_13x,E(_13y),E(_13z))));}else{return new F(function(){return _11K(_13C,_13D,_13E,B(_13r(_13s,_13t,_13F,_13v,_13w,_13x,_13y,_13z)));});}}else{return new F(function(){return _12B(_13w,_13x,B(_13G(_13s,_13t,_13B,_13C,_13D,_13E,_13F,_13y)),_13z);});}}else{return new F(function(){return _13j(_13s,_13t,_13v,_13w,_13x,_13y,_13z);});}},_13G=function(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O){var _13P=E(_13O);if(!_13P._){var _13Q=_13P.a,_13R=_13P.b,_13S=_13P.c,_13T=_13P.d,_13U=_13P.e;if((imul(3,_13J)|0)>=_13Q){if((imul(3,_13Q)|0)>=_13J){return new T5(0,(_13J+_13Q|0)+1|0,E(_13H),_13I,E(new T5(0,_13J,E(_13K),_13L,E(_13M),E(_13N))),E(_13P));}else{return new F(function(){return _11K(_13K,_13L,_13M,B(_13r(_13H,_13I,_13N,_13Q,_13R,_13S,_13T,_13U)));});}}else{return new F(function(){return _12B(_13R,_13S,B(_13G(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13T)),_13U);});}}else{return new F(function(){return _12s(_13H,_13I,new T5(0,_13J,E(_13K),_13L,E(_13M),E(_13N)));});}},_13V=function(_13W,_13X,_13Y,_13Z){var _140=E(_13Y);if(!_140._){var _141=_140.a,_142=_140.b,_143=_140.c,_144=_140.d,_145=_140.e,_146=E(_13Z);if(!_146._){var _147=_146.a,_148=_146.b,_149=_146.c,_14a=_146.d,_14b=_146.e;if((imul(3,_141)|0)>=_147){if((imul(3,_147)|0)>=_141){return new T5(0,(_141+_147|0)+1|0,E(_13W),_13X,E(_140),E(_146));}else{return new F(function(){return _11K(_142,_143,_144,B(_13r(_13W,_13X,_145,_147,_148,_149,_14a,_14b)));});}}else{return new F(function(){return _12B(_148,_149,B(_13G(_13W,_13X,_141,_142,_143,_144,_145,_14a)),_14b);});}}else{return new F(function(){return _12s(_13W,_13X,_140);});}}else{return new F(function(){return _13e(_13W,_13X,_13Z);});}},_14c=function(_14d,_14e,_14f,_14g){var _14h=E(_14d);if(_14h==1){var _14i=E(_14g);return (_14i._==0)?new T3(0,new T(function(){return new T5(0,1,E(_14e),_14f,E(_11F),E(_11F));}),_S,_S):(B(_11y(_14e,E(_14i.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_14e),_14f,E(_11F),E(_11F));}),_14i,_S):new T3(0,new T(function(){return new T5(0,1,E(_14e),_14f,E(_11F),E(_11F));}),_S,_14i);}else{var _14j=B(_14c(_14h>>1,_14e,_14f,_14g)),_14k=_14j.a,_14l=_14j.c,_14m=E(_14j.b);if(!_14m._){return new T3(0,_14k,_S,_14l);}else{var _14n=E(_14m.a),_14o=_14n.a,_14p=_14n.b,_14q=E(_14m.b);if(!_14q._){return new T3(0,new T(function(){return B(_12s(_14o,_14p,_14k));}),_S,_14l);}else{var _14r=E(_14q.a),_14s=_14r.a;if(!B(_11y(_14o,_14s))){var _14t=B(_14c(_14h>>1,_14s,_14r.b,_14q.b));return new T3(0,new T(function(){return B(_13V(_14o,_14p,_14k,_14t.a));}),_14t.b,_14t.c);}else{return new T3(0,_14k,_S,_14m);}}}}},_14u=function(_14v,_14w,_14x){var _14y=E(_14v),_14z=E(_14x);if(!_14z._){var _14A=_14z.b,_14B=_14z.c,_14C=_14z.d,_14D=_14z.e;switch(B(_11y(_14y,_14A))){case 0:return new F(function(){return _12B(_14A,_14B,B(_14u(_14y,_14w,_14C)),_14D);});break;case 1:return new T5(0,_14z.a,E(_14y),_14w,E(_14C),E(_14D));default:return new F(function(){return _11K(_14A,_14B,_14C,B(_14u(_14y,_14w,_14D)));});}}else{return new T5(0,1,E(_14y),_14w,E(_11F),E(_11F));}},_14E=function(_14F,_14G){while(1){var _14H=E(_14G);if(!_14H._){return E(_14F);}else{var _14I=E(_14H.a),_14J=B(_14u(_14I.a,_14I.b,_14F));_14F=_14J;_14G=_14H.b;continue;}}},_14K=function(_14L,_14M,_14N,_14O){return new F(function(){return _14E(B(_14u(_14M,_14N,_14L)),_14O);});},_14P=function(_14Q,_14R,_14S){var _14T=E(_14R);return new F(function(){return _14E(B(_14u(_14T.a,_14T.b,_14Q)),_14S);});},_14U=function(_14V,_14W,_14X){while(1){var _14Y=E(_14X);if(!_14Y._){return E(_14W);}else{var _14Z=E(_14Y.a),_150=_14Z.a,_151=_14Z.b,_152=E(_14Y.b);if(!_152._){return new F(function(){return _12s(_150,_151,_14W);});}else{var _153=E(_152.a),_154=_153.a;if(!B(_11y(_150,_154))){var _155=B(_14c(_14V,_154,_153.b,_152.b)),_156=_155.a,_157=E(_155.c);if(!_157._){var _158=_14V<<1,_159=B(_13V(_150,_151,_14W,_156));_14V=_158;_14W=_159;_14X=_155.b;continue;}else{return new F(function(){return _14P(B(_13V(_150,_151,_14W,_156)),_157.a,_157.b);});}}else{return new F(function(){return _14K(_14W,_150,_151,_152);});}}}}},_15a=function(_15b,_15c,_15d,_15e,_15f){var _15g=E(_15f);if(!_15g._){return new F(function(){return _12s(_15d,_15e,_15c);});}else{var _15h=E(_15g.a),_15i=_15h.a;if(!B(_11y(_15d,_15i))){var _15j=B(_14c(_15b,_15i,_15h.b,_15g.b)),_15k=_15j.a,_15l=E(_15j.c);if(!_15l._){return new F(function(){return _14U(_15b<<1,B(_13V(_15d,_15e,_15c,_15k)),_15j.b);});}else{return new F(function(){return _14P(B(_13V(_15d,_15e,_15c,_15k)),_15l.a,_15l.b);});}}else{return new F(function(){return _14K(_15c,_15d,_15e,_15g);});}}},_15m=function(_15n){var _15o=E(_15n);if(!_15o._){return new T0(1);}else{var _15p=E(_15o.a),_15q=_15p.a,_15r=_15p.b,_15s=E(_15o.b);if(!_15s._){return new T5(0,1,E(_15q),_15r,E(_11F),E(_11F));}else{var _15t=_15s.b,_15u=E(_15s.a),_15v=_15u.a,_15w=_15u.b;if(!B(_11y(_15q,_15v))){return new F(function(){return _15a(1,new T5(0,1,E(_15q),_15r,E(_11F),E(_11F)),_15v,_15w,_15t);});}else{return new F(function(){return _14K(new T5(0,1,E(_15q),_15r,E(_11F),E(_11F)),_15v,_15w,_15t);});}}}},_15x=function(_15y){var _15z=E(_15y);if(!_15z._){return __Z;}else{var _15A=E(_15z.b);return (_15A._==0)?__Z:new T2(1,new T2(0,_15z.a,_15A.a),new T(function(){return B(_15x(_15A.b));}));}},_15B=function(_15C,_15D,_15E){return new T2(1,new T2(0,_15C,_15D),new T(function(){return B(_15x(_15E));}));},_15F=function(_15G,_15H){var _15I=E(_15H);return (_15I._==0)?__Z:new T2(1,new T2(0,_15G,_15I.a),new T(function(){return B(_15x(_15I.b));}));},_15J="Invalid JSON!",_15K=new T1(0,_15J),_15L="No such value",_15M=new T1(0,_15L),_15N=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_15O=function(_15P){return E(E(_15P).c);},_15Q=function(_15R,_15S,_){var _15T=__app1(E(_15N),_15S),_15U=__eq(_15T,E(_3a));if(!E(_15U)){var _15V=__isUndef(_15T);return (E(_15V)==0)?new T(function(){var _15W=String(_15T),_15X=jsParseJSON(_15W);if(!_15X._){return E(_15K);}else{return B(A2(_15O,_15R,_15X.a));}}):_15M;}else{return _15M;}},_15Y=new T1(0,0),_15Z=function(_160,_161){while(1){var _162=E(_160);if(!_162._){var _163=_162.a,_164=E(_161);if(!_164._){return new T1(0,(_163>>>0|_164.a>>>0)>>>0&4294967295);}else{_160=new T1(1,I_fromInt(_163));_161=_164;continue;}}else{var _165=E(_161);if(!_165._){_160=_162;_161=new T1(1,I_fromInt(_165.a));continue;}else{return new T1(1,I_or(_162.a,_165.a));}}}},_166=function(_167){var _168=E(_167);if(!_168._){return E(_15Y);}else{return new F(function(){return _15Z(new T1(0,E(_168.a)),B(_cU(B(_166(_168.b)),31)));});}},_169=function(_16a,_16b){if(!E(_16a)){return new F(function(){return _fz(B(_166(_16b)));});}else{return new F(function(){return _166(_16b);});}},_16c=1420103680,_16d=465,_16e=new T2(1,_16d,_S),_16f=new T2(1,_16c,_16e),_16g=new T(function(){return B(_169(_wE,_16f));}),_16h=function(_16i){return E(_16g);},_16j=new T(function(){return B(unCStr("s"));}),_16k=function(_16l,_16m){while(1){var _16n=E(_16l);if(!_16n._){return E(_16m);}else{_16l=_16n.b;_16m=_16n.a;continue;}}},_16o=function(_16p,_16q,_16r){return new F(function(){return _16k(_16q,_16p);});},_16s=new T1(0,1),_16t=function(_16u,_16v){var _16w=E(_16u);return new T2(0,_16w,new T(function(){var _16x=B(_16t(B(_cB(_16w,_16v)),_16v));return new T2(1,_16x.a,_16x.b);}));},_16y=function(_16z){var _16A=B(_16t(_16z,_16s));return new T2(1,_16A.a,_16A.b);},_16B=function(_16C,_16D){var _16E=B(_16t(_16C,new T(function(){return B(_eU(_16D,_16C));})));return new T2(1,_16E.a,_16E.b);},_16F=new T1(0,0),_16G=function(_16H,_16I){var _16J=E(_16H);if(!_16J._){var _16K=_16J.a,_16L=E(_16I);return (_16L._==0)?_16K>=_16L.a:I_compareInt(_16L.a,_16K)<=0;}else{var _16M=_16J.a,_16N=E(_16I);return (_16N._==0)?I_compareInt(_16M,_16N.a)>=0:I_compare(_16M,_16N.a)>=0;}},_16O=function(_16P,_16Q,_16R){if(!B(_16G(_16Q,_16F))){var _16S=function(_16T){return (!B(_dd(_16T,_16R)))?new T2(1,_16T,new T(function(){return B(_16S(B(_cB(_16T,_16Q))));})):__Z;};return new F(function(){return _16S(_16P);});}else{var _16U=function(_16V){return (!B(_d4(_16V,_16R)))?new T2(1,_16V,new T(function(){return B(_16U(B(_cB(_16V,_16Q))));})):__Z;};return new F(function(){return _16U(_16P);});}},_16W=function(_16X,_16Y,_16Z){return new F(function(){return _16O(_16X,B(_eU(_16Y,_16X)),_16Z);});},_170=function(_171,_172){return new F(function(){return _16O(_171,_16s,_172);});},_173=function(_174){return new F(function(){return _bg(_174);});},_175=function(_176){return new F(function(){return _eU(_176,_16s);});},_177=function(_178){return new F(function(){return _cB(_178,_16s);});},_179=function(_17a){return new F(function(){return _aX(E(_17a));});},_17b={_:0,a:_177,b:_175,c:_179,d:_173,e:_16y,f:_16B,g:_170,h:_16W},_17c=function(_17d,_17e){while(1){var _17f=E(_17d);if(!_17f._){var _17g=E(_17f.a);if(_17g==( -2147483648)){_17d=new T1(1,I_fromInt( -2147483648));continue;}else{var _17h=E(_17e);if(!_17h._){return new T1(0,B(_9p(_17g,_17h.a)));}else{_17d=new T1(1,I_fromInt(_17g));_17e=_17h;continue;}}}else{var _17i=_17f.a,_17j=E(_17e);return (_17j._==0)?new T1(1,I_div(_17i,I_fromInt(_17j.a))):new T1(1,I_div(_17i,_17j.a));}}},_17k=function(_17l,_17m){if(!B(_ct(_17m,_oR))){return new F(function(){return _17c(_17l,_17m);});}else{return E(_a0);}},_17n=function(_17o,_17p){while(1){var _17q=E(_17o);if(!_17q._){var _17r=E(_17q.a);if(_17r==( -2147483648)){_17o=new T1(1,I_fromInt( -2147483648));continue;}else{var _17s=E(_17p);if(!_17s._){var _17t=_17s.a;return new T2(0,new T1(0,B(_9p(_17r,_17t))),new T1(0,B(_au(_17r,_17t))));}else{_17o=new T1(1,I_fromInt(_17r));_17p=_17s;continue;}}}else{var _17u=E(_17p);if(!_17u._){_17o=_17q;_17p=new T1(1,I_fromInt(_17u.a));continue;}else{var _17v=I_divMod(_17q.a,_17u.a);return new T2(0,new T1(1,_17v.a),new T1(1,_17v.b));}}}},_17w=function(_17x,_17y){if(!B(_ct(_17y,_oR))){var _17z=B(_17n(_17x,_17y));return new T2(0,_17z.a,_17z.b);}else{return E(_a0);}},_17A=function(_17B,_17C){while(1){var _17D=E(_17B);if(!_17D._){var _17E=E(_17D.a);if(_17E==( -2147483648)){_17B=new T1(1,I_fromInt( -2147483648));continue;}else{var _17F=E(_17C);if(!_17F._){return new T1(0,B(_au(_17E,_17F.a)));}else{_17B=new T1(1,I_fromInt(_17E));_17C=_17F;continue;}}}else{var _17G=_17D.a,_17H=E(_17C);return (_17H._==0)?new T1(1,I_mod(_17G,I_fromInt(_17H.a))):new T1(1,I_mod(_17G,_17H.a));}}},_17I=function(_17J,_17K){if(!B(_ct(_17K,_oR))){return new F(function(){return _17A(_17J,_17K);});}else{return E(_a0);}},_17L=function(_17M,_17N){while(1){var _17O=E(_17M);if(!_17O._){var _17P=E(_17O.a);if(_17P==( -2147483648)){_17M=new T1(1,I_fromInt( -2147483648));continue;}else{var _17Q=E(_17N);if(!_17Q._){return new T1(0,quot(_17P,_17Q.a));}else{_17M=new T1(1,I_fromInt(_17P));_17N=_17Q;continue;}}}else{var _17R=_17O.a,_17S=E(_17N);return (_17S._==0)?new T1(0,I_toInt(I_quot(_17R,I_fromInt(_17S.a)))):new T1(1,I_quot(_17R,_17S.a));}}},_17T=function(_17U,_17V){if(!B(_ct(_17V,_oR))){return new F(function(){return _17L(_17U,_17V);});}else{return E(_a0);}},_17W=function(_17X,_17Y){if(!B(_ct(_17Y,_oR))){var _17Z=B(_cK(_17X,_17Y));return new T2(0,_17Z.a,_17Z.b);}else{return E(_a0);}},_180=function(_181,_182){while(1){var _183=E(_181);if(!_183._){var _184=E(_183.a);if(_184==( -2147483648)){_181=new T1(1,I_fromInt( -2147483648));continue;}else{var _185=E(_182);if(!_185._){return new T1(0,_184%_185.a);}else{_181=new T1(1,I_fromInt(_184));_182=_185;continue;}}}else{var _186=_183.a,_187=E(_182);return (_187._==0)?new T1(1,I_rem(_186,I_fromInt(_187.a))):new T1(1,I_rem(_186,_187.a));}}},_188=function(_189,_18a){if(!B(_ct(_18a,_oR))){return new F(function(){return _180(_189,_18a);});}else{return E(_a0);}},_18b=function(_18c){return E(_18c);},_18d=function(_18e){return E(_18e);},_18f=function(_18g){var _18h=E(_18g);if(!_18h._){var _18i=E(_18h.a);return (_18i==( -2147483648))?E(_fy):(_18i<0)?new T1(0, -_18i):E(_18h);}else{var _18j=_18h.a;return (I_compareInt(_18j,0)>=0)?E(_18h):new T1(1,I_negate(_18j));}},_18k=new T1(0, -1),_18l=function(_18m){var _18n=E(_18m);if(!_18n._){var _18o=_18n.a;return (_18o>=0)?(E(_18o)==0)?E(_15Y):E(_dc):E(_18k);}else{var _18p=I_compareInt(_18n.a,0);return (_18p<=0)?(E(_18p)==0)?E(_15Y):E(_18k):E(_dc);}},_18q={_:0,a:_cB,b:_eU,c:_ol,d:_fz,e:_18f,f:_18l,g:_18d},_18r=function(_18s,_18t){var _18u=E(_18s);if(!_18u._){var _18v=_18u.a,_18w=E(_18t);return (_18w._==0)?_18v!=_18w.a:(I_compareInt(_18w.a,_18v)==0)?false:true;}else{var _18x=_18u.a,_18y=E(_18t);return (_18y._==0)?(I_compareInt(_18x,_18y.a)==0)?false:true:(I_compare(_18x,_18y.a)==0)?false:true;}},_18z=new T2(0,_ct,_18r),_18A=function(_18B,_18C){return (!B(_eF(_18B,_18C)))?E(_18B):E(_18C);},_18D=function(_18E,_18F){return (!B(_eF(_18E,_18F)))?E(_18F):E(_18E);},_18G={_:0,a:_18z,b:_cd,c:_dd,d:_eF,e:_d4,f:_16G,g:_18A,h:_18D},_18H=function(_18I){return new T2(0,E(_18I),E(_b1));},_18J=new T3(0,_18q,_18G,_18H),_18K={_:0,a:_18J,b:_17b,c:_17T,d:_188,e:_17k,f:_17I,g:_17W,h:_17w,i:_18b},_18L=new T1(0,0),_18M=function(_18N,_18O,_18P){var _18Q=B(A1(_18N,_18O));if(!B(_ct(_18Q,_18L))){return new F(function(){return _17c(B(_ol(_18O,_18P)),_18Q);});}else{return E(_a0);}},_18R=function(_18S,_18T){while(1){if(!B(_ct(_18T,_oR))){var _18U=_18T,_18V=B(_188(_18S,_18T));_18S=_18U;_18T=_18V;continue;}else{return E(_18S);}}},_18W=5,_18X=new T(function(){return B(_9W(_18W));}),_18Y=new T(function(){return die(_18X);}),_18Z=function(_190,_191){if(!B(_ct(_191,_oR))){var _192=B(_18R(B(_18f(_190)),B(_18f(_191))));return (!B(_ct(_192,_oR)))?new T2(0,B(_17L(_190,_192)),B(_17L(_191,_192))):E(_a0);}else{return E(_18Y);}},_193=function(_194,_195,_196,_197){var _198=B(_ol(_195,_196));return new F(function(){return _18Z(B(_ol(B(_ol(_194,_197)),B(_18l(_198)))),B(_18f(_198)));});},_199=function(_19a,_19b,_19c){var _19d=new T(function(){if(!B(_ct(_19c,_oR))){var _19e=B(_cK(_19b,_19c));return new T2(0,_19e.a,_19e.b);}else{return E(_a0);}}),_19f=new T(function(){return B(A2(_hk,B(_oa(B(_o8(_19a)))),new T(function(){return E(E(_19d).a);})));});return new T2(0,_19f,new T(function(){return new T2(0,E(E(_19d).b),E(_19c));}));},_19g=function(_19h,_19i,_19j){var _19k=B(_199(_19h,_19i,_19j)),_19l=_19k.a,_19m=E(_19k.b);if(!B(_dd(B(_ol(_19m.a,_b1)),B(_ol(_oR,_19m.b))))){return E(_19l);}else{var _19n=B(_oa(B(_o8(_19h))));return new F(function(){return A3(_oN,_19n,_19l,new T(function(){return B(A2(_hk,_19n,_b1));}));});}},_19o=479723520,_19p=40233135,_19q=new T2(1,_19p,_S),_19r=new T2(1,_19o,_19q),_19s=new T(function(){return B(_169(_wE,_19r));}),_19t=new T1(0,40587),_19u=function(_19v){var _19w=new T(function(){var _19x=B(_193(_19v,_b1,_16g,_b1)),_19y=B(_193(_19s,_b1,_16g,_b1)),_19z=B(_193(_19x.a,_19x.b,_19y.a,_19y.b));return B(_19g(_18K,_19z.a,_19z.b));});return new T2(0,new T(function(){return B(_cB(_19t,_19w));}),new T(function(){return B(_eU(_19v,B(_18M(_16h,B(_ol(_19w,_16g)),_19s))));}));},_19A=function(_19B,_){var _19C=__get(_19B,0),_19D=__get(_19B,1),_19E=Number(_19C),_19F=jsTrunc(_19E),_19G=Number(_19D),_19H=jsTrunc(_19G);return new T2(0,_19F,_19H);},_19I=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_19J=660865024,_19K=465661287,_19L=new T2(1,_19K,_S),_19M=new T2(1,_19J,_19L),_19N=new T(function(){return B(_169(_wE,_19M));}),_19O=function(_){var _19P=__app0(E(_19I)),_19Q=B(_19A(_19P,_));return new T(function(){var _19R=E(_19Q);if(!B(_ct(_19N,_18L))){return B(_cB(B(_ol(B(_aX(E(_19R.a))),_16g)),B(_17c(B(_ol(B(_ol(B(_aX(E(_19R.b))),_16g)),_16g)),_19N))));}else{return E(_a0);}});},_19S=new T(function(){return B(err(_sD));}),_19T=new T(function(){return B(err(_sz));}),_19U=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_19V=new T1(0,1),_19W=new T1(0,10),_19X=function(_19Y){while(1){var _19Z=E(_19Y);if(!_19Z._){_19Y=new T1(1,I_fromInt(_19Z.a));continue;}else{return new F(function(){return I_toString(_19Z.a);});}}},_1a0=function(_1a1,_1a2){return new F(function(){return _q(fromJSStr(B(_19X(_1a1))),_1a2);});},_1a3=new T1(0,0),_1a4=function(_1a5,_1a6,_1a7){if(_1a5<=6){return new F(function(){return _1a0(_1a6,_1a7);});}else{if(!B(_dd(_1a6,_1a3))){return new F(function(){return _1a0(_1a6,_1a7);});}else{return new T2(1,_z,new T(function(){return B(_q(fromJSStr(B(_19X(_1a6))),new T2(1,_y,_1a7)));}));}}},_1a8=function(_1a9){return new F(function(){return _1a4(0,_1a9,_S);});},_1aa=new T(function(){return B(_ct(_19W,_18L));}),_1ab=function(_1ac){while(1){if(!B(_ct(_1ac,_18L))){if(!E(_1aa)){if(!B(_ct(B(_17A(_1ac,_19W)),_18L))){return new F(function(){return _1a8(_1ac);});}else{var _1ad=B(_17c(_1ac,_19W));_1ac=_1ad;continue;}}else{return E(_a0);}}else{return __Z;}}},_1ae=46,_1af=48,_1ag=function(_1ah,_1ai,_1aj){if(!B(_dd(_1aj,_18L))){var _1ak=B(A1(_1ah,_1aj));if(!B(_ct(_1ak,_18L))){var _1al=B(_17n(_1aj,_1ak)),_1am=_1al.b,_1an=new T(function(){var _1ao=Math.log(B(_fS(_1ak)))/Math.log(10),_1ap=_1ao&4294967295,_1aq=function(_1ar){if(_1ar>=0){var _1as=E(_1ar);if(!_1as){var _1at=B(_17c(B(_eU(B(_cB(B(_ol(_1am,_b1)),_1ak)),_19V)),_1ak));}else{var _1at=B(_17c(B(_eU(B(_cB(B(_ol(_1am,B(_oB(_19W,_1as)))),_1ak)),_19V)),_1ak));}var _1au=function(_1av){var _1aw=B(_1a4(0,_1at,_S)),_1ax=_1ar-B(_mz(_1aw,0))|0;if(0>=_1ax){if(!E(_1ai)){return E(_1aw);}else{return new F(function(){return _1ab(_1at);});}}else{var _1ay=new T(function(){if(!E(_1ai)){return E(_1aw);}else{return B(_1ab(_1at));}}),_1az=function(_1aA){var _1aB=E(_1aA);return (_1aB==1)?E(new T2(1,_1af,_1ay)):new T2(1,_1af,new T(function(){return B(_1az(_1aB-1|0));}));};return new F(function(){return _1az(_1ax);});}};if(!E(_1ai)){var _1aC=B(_1au(_));return (_1aC._==0)?__Z:new T2(1,_1ae,_1aC);}else{if(!B(_ct(_1at,_18L))){var _1aD=B(_1au(_));return (_1aD._==0)?__Z:new T2(1,_1ae,_1aD);}else{return __Z;}}}else{return E(_px);}};if(_1ap>=_1ao){return B(_1aq(_1ap));}else{return B(_1aq(_1ap+1|0));}},1);return new F(function(){return _q(B(_1a4(0,_1al.a,_S)),_1an);});}else{return E(_a0);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_1ag(_1ah,_1ai,B(_fz(_1aj))));}));});}},_1aE=function(_1aF,_1aG,_){var _1aH=B(_19O(_)),_1aI=new T(function(){var _1aJ=new T(function(){var _1aK=new T(function(){var _1aL=B(_q(B(_1ag(_16h,_wE,B(_19u(_1aH)).b)),_16j));if(!_1aL._){return E(_TT);}else{var _1aM=B(_TO(_1aL.a,_1aL.b));if(!_1aM._){return B(_16o(_S,_S,_Vx));}else{var _1aN=_1aM.a,_1aO=E(_1aM.b);if(!_1aO._){return B(_16o(new T2(1,_1aN,_S),_S,_Vx));}else{var _1aP=E(_1aN),_1aQ=new T(function(){var _1aR=B(_Hd(46,_1aO.a,_1aO.b));return new T2(0,_1aR.a,_1aR.b);});if(E(_1aP)==46){return B(_16o(_S,new T2(1,new T(function(){return E(E(_1aQ).a);}),new T(function(){return E(E(_1aQ).b);})),_Vx));}else{return B(_16o(new T2(1,_1aP,new T(function(){return E(E(_1aQ).a);})),new T(function(){return E(E(_1aQ).b);}),_Vx));}}}}}),_1aS=B(_Gl(B(_sI(_19U,_1aK))));if(!_1aS._){return E(_19T);}else{if(!E(_1aS.b)._){return B(_pU(3,B(_A(0,E(_1aS.a)+(imul(E(_1aG),E(_1aF)-1|0)|0)|0,_S))));}else{return E(_19S);}}}),_1aT=B(_Gl(B(_sI(_19U,_1aJ))));if(!_1aT._){return E(_19T);}else{if(!E(_1aT.b)._){return E(_1aT.a);}else{return E(_19S);}}});return new T2(0,new T(function(){return B(_aB(_1aI,_1aF));}),_1aI);},_1aU=function(_1aV,_1aW){while(1){var _1aX=E(_1aW);if(!_1aX._){return __Z;}else{var _1aY=_1aX.b,_1aZ=E(_1aV);if(_1aZ==1){return E(_1aY);}else{_1aV=_1aZ-1|0;_1aW=_1aY;continue;}}}},_1b0=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1b1=new T(function(){return B(err(_1b0));}),_1b2=0,_1b3=function(_1b4,_1b5,_1b6){return new F(function(){return _A(E(_1b4),E(_1b5),_1b6);});},_1b7=function(_1b8,_1b9){return new F(function(){return _A(0,E(_1b8),_1b9);});},_1ba=function(_1bb,_1bc){return new F(function(){return _2v(_1b7,_1bb,_1bc);});},_1bd=new T3(0,_1b3,_6H,_1ba),_1be=0,_1bf=new T(function(){return B(unCStr(" out of range "));}),_1bg=new T(function(){return B(unCStr("}.index: Index "));}),_1bh=new T(function(){return B(unCStr("Ix{"));}),_1bi=new T2(1,_y,_S),_1bj=new T2(1,_y,_1bi),_1bk=0,_1bl=function(_1bm){return E(E(_1bm).a);},_1bn=function(_1bo,_1bp,_1bq,_1br,_1bs){var _1bt=new T(function(){var _1bu=new T(function(){var _1bv=new T(function(){var _1bw=new T(function(){var _1bx=new T(function(){return B(A3(_sl,_6D,new T2(1,new T(function(){return B(A3(_1bl,_1bq,_1bk,_1br));}),new T2(1,new T(function(){return B(A3(_1bl,_1bq,_1bk,_1bs));}),_S)),_1bj));});return B(_q(_1bf,new T2(1,_z,new T2(1,_z,_1bx))));});return B(A(_1bl,[_1bq,_1be,_1bp,new T2(1,_y,_1bw)]));});return B(_q(_1bg,new T2(1,_z,_1bv)));},1);return B(_q(_1bo,_1bu));},1);return new F(function(){return err(B(_q(_1bh,_1bt)));});},_1by=function(_1bz,_1bA,_1bB,_1bC,_1bD){return new F(function(){return _1bn(_1bz,_1bA,_1bD,_1bB,_1bC);});},_1bE=function(_1bF,_1bG,_1bH,_1bI){var _1bJ=E(_1bH);return new F(function(){return _1by(_1bF,_1bG,_1bJ.a,_1bJ.b,_1bI);});},_1bK=function(_1bL,_1bM,_1bN,_1bO){return new F(function(){return _1bE(_1bO,_1bN,_1bM,_1bL);});},_1bP=new T(function(){return B(unCStr("Int"));}),_1bQ=function(_1bR,_1bS,_1bT){return new F(function(){return _1bK(_1bd,new T2(0,_1bS,_1bT),_1bR,_1bP);});},_1bU=new T(function(){return B(unCStr("Negative range size"));}),_1bV=new T(function(){return B(err(_1bU));}),_1bW=function(_1bX){var _1bY=B(A1(_1bX,_));return E(_1bY);},_1bZ=function(_1c0,_1c1,_1c2,_){var _1c3=E(_1c0);if(!_1c3){return new T2(0,_S,_1c1);}else{var _1c4=new T(function(){return B(_mz(_1c2,0))-1|0;}),_1c5=B(_1aE(new T(function(){return E(_1c4)+1|0;}),_1c1,_)),_1c6=E(_1c5),_1c7=_1c6.a,_1c8=_1c6.b,_1c9=new T(function(){var _1ca=E(_1c7);if(B(_mz(_1c2,0))>=(_1ca+1|0)){var _1cb=new T(function(){var _1cc=_1ca+1|0;if(_1cc>0){return B(_1aU(_1cc,_1c2));}else{return E(_1c2);}});if(0>=_1ca){return E(_1cb);}else{var _1cd=function(_1ce,_1cf){var _1cg=E(_1ce);if(!_1cg._){return E(_1cb);}else{var _1ch=_1cg.a,_1ci=E(_1cf);return (_1ci==1)?new T2(1,_1ch,_1cb):new T2(1,_1ch,new T(function(){return B(_1cd(_1cg.b,_1ci-1|0));}));}};return B(_1cd(_1c2,_1ca));}}else{return E(_1c2);}}),_1cj=B(_1bZ(_1c3-1|0,_1c8,_1c9,_)),_1ck=new T(function(){var _1cl=function(_){var _1cm=E(_1c4),_1cn=function(_1co){if(_1co>=0){var _1cp=newArr(_1co,_1b1),_1cq=_1cp,_1cr=E(_1co);if(!_1cr){return new T4(0,E(_1b2),E(_1cm),0,_1cq);}else{var _1cs=function(_1ct,_1cu,_){while(1){var _1cv=E(_1ct);if(!_1cv._){return E(_);}else{var _=_1cq[_1cu]=_1cv.a;if(_1cu!=(_1cr-1|0)){var _1cw=_1cu+1|0;_1ct=_1cv.b;_1cu=_1cw;continue;}else{return E(_);}}}},_=B(_1cs(_1c2,0,_));return new T4(0,E(_1b2),E(_1cm),_1cr,_1cq);}}else{return E(_1bV);}};if(0>_1cm){return new F(function(){return _1cn(0);});}else{return new F(function(){return _1cn(_1cm+1|0);});}},_1cx=B(_1bW(_1cl)),_1cy=E(_1cx.a),_1cz=E(_1cx.b),_1cA=E(_1c7);if(_1cy>_1cA){return B(_1bQ(_1cA,_1cy,_1cz));}else{if(_1cA>_1cz){return B(_1bQ(_1cA,_1cy,_1cz));}else{return E(_1cx.d[_1cA-_1cy|0]);}}});return new T2(0,new T2(1,_1ck,new T(function(){return B(_sr(_1cj));})),_1c8);}},_1cB=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1cC=function(_1cD,_1cE,_1cF,_1cG,_){var _1cH=__app1(E(_gN),_1cG),_1cI=__app3(E(_1cB),_1cG,E(_1cD),E(_1cE)),_1cJ=B(A2(_1cF,_1cG,_)),_1cK=__app1(E(_gM),_1cG);return new F(function(){return _gL(_);});},_1cL=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_1cM=function(_1cN,_1cO,_1cP,_1cQ,_){var _1cR=__app4(E(_1cL),_1cQ,_1cN,_1cO,_1cP);return new F(function(){return _gL(_);});},_1cS=2,_1cT=function(_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_){var _1d0=function(_1d1,_){return new F(function(){return _1cC(_1cS,_1cS,function(_1d2,_){return new F(function(){return _1cM(B(_6X(_1cV,E(_1cZ))),0,0,E(_1d2),_);});},E(_1d1),_);});};return new F(function(){return _gY(new T(function(){return E(_1cW)-E(_1cX)*16;},1),new T(function(){return E(_1cY)*20;},1),_1d0,_1cU,_);});},_1d3=1,_1d4=new T(function(){return B(_6X(_ja,1));}),_1d5=function(_1d6){return E(_1d6).d;},_1d7=function(_1d8,_1d9,_1da,_1db,_1dc,_1dd,_){var _1de=new T(function(){return E(E(_1dd).s);}),_1df=new T(function(){return E(E(_1de).a);}),_1dg=new T(function(){if(!B(_au(E(_1dd).t,10))){var _1dh=E(E(_1de).b);if(!(_1dh%2)){return _1dh+1|0;}else{return _1dh-1|0;}}else{return E(E(_1de).b);}}),_1di=new T(function(){var _1dj=E(_1dd);return {_:0,a:E(_1dj.a),b:E(_1dj.b),c:E(_1dj.c),d:E(_1dj.d),e:E(_1dj.e),f:E(_1dj.f),g:E(_1dj.g),h:E(_1dj.h),i:_1dj.i,j:_1dj.j,k:_1dj.k,l:_1dj.l,m:E(_1dj.m),n:_1dj.n,o:E(_1dj.o),p:E(_1dj.p),q:_1dj.q,r:E(_1dj.r),s:E(new T2(0,_1df,_1dg)),t:_1dj.t,u:E(_1dj.u),v:E(_1dj.v)};}),_1dk=new T(function(){return E(E(_1di).a);}),_1dl=new T(function(){return E(E(_1di).b);}),_1dm=new T(function(){return E(E(_1dl).a);}),_1dn=new T(function(){var _1do=E(_1da)/16,_1dp=_1do&4294967295;if(_1do>=_1dp){return _1dp-2|0;}else{return (_1dp-1|0)-2|0;}}),_1dq=B(_nw(_1d8,_1d9,new T(function(){return B(_ba(_1dn,_1dm));}),_nV,new T(function(){return E(E(_1dk).b);}),_)),_1dr=new T(function(){return E(E(E(_1di).a).a);}),_1ds=B(A(_mU,[_1d8,new T(function(){if(E(E(_1dk).e)==32){return E(_nT);}else{return E(_nU);}}),new T(function(){return ((E(E(_1dr).a)+E(_1dn)|0)-E(_1dm)|0)+1|0;},1),new T(function(){return (E(E(_1dr).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1d5(_1dk));}),_S),_])),_1dt=E(_1di),_1du=_1dt.c,_1dv=_1dt.k,_1dw=E(_1dt.u),_1dx=new T(function(){var _1dy=E(_1da)/28,_1dz=_1dy&4294967295;if(_1dy>=_1dz){return (_1dz-1|0)+_1dv|0;}else{return ((_1dz-1|0)-1|0)+_1dv|0;}}),_1dA=new T(function(){return (2+E(E(_1dl).b)|0)+3|0;}),_1dB=new T2(0,_1d8,_1d9),_1dC=function(_){var _1dD=function(_){var _1dE=function(_){var _1dF=B(_1cT(_1d8,new T(function(){return E(E(_1dc).b);},1),_1da,new T(function(){return E(_1dm)+10|0;},1),_nV,new T(function(){return (imul(E(_1df),8)|0)+E(_1dg)|0;},1),_));return _1dt;};if(!E(_1dt.p)._){return new F(function(){return _1dE(_);});}else{var _1dG=B(A(_mU,[_1d8,_1d4,_1d3,_1d3,B(_A(0,_1dt.q,_S)),_]));return new F(function(){return _1dE(_);});}};if(!E(_1dw.g)){return new F(function(){return _1dD(_);});}else{var _1dH=B(_jg(_1dB,_1db,0,_1dA,_1dx,_1dA,B(_XH(_1du,new T(function(){return B(_6k(_sr,_1dt.m));},1),_1dt.n)),_));return new F(function(){return _1dD(_);});}};if(!E(_1dw.c)){var _1dI=B(_jg(_1dB,_1db,0,_1dA,_1dx,_1dA,_1du,_));return new F(function(){return _1dC(_);});}else{return new F(function(){return _1dC(_);});}},_1dJ=function(_1dK,_1dL){while(1){var _1dM=E(_1dK);if(!_1dM._){return E(_1dL);}else{_1dK=_1dM.b;_1dL=_1dM.a;continue;}}},_1dN=function(_1dO,_1dP,_1dQ){return new F(function(){return _1dJ(_1dP,_1dO);});},_1dR=function(_1dS,_1dT){while(1){var _1dU=E(_1dS);if(!_1dU._){return E(_1dT);}else{_1dS=_1dU.b;_1dT=_1dU.a;continue;}}},_1dV=function(_1dW,_1dX,_1dY){return new F(function(){return _1dR(_1dX,_1dW);});},_1dZ=function(_1e0,_1e1){while(1){var _1e2=E(_1e1);if(!_1e2._){return __Z;}else{var _1e3=_1e2.b,_1e4=E(_1e0);if(_1e4==1){return E(_1e3);}else{_1e0=_1e4-1|0;_1e1=_1e3;continue;}}}},_1e5=function(_1e6,_1e7){var _1e8=new T(function(){var _1e9=_1e6+1|0;if(_1e9>0){return B(_1dZ(_1e9,_1e7));}else{return E(_1e7);}});if(0>=_1e6){return E(_1e8);}else{var _1ea=function(_1eb,_1ec){var _1ed=E(_1eb);if(!_1ed._){return E(_1e8);}else{var _1ee=_1ed.a,_1ef=E(_1ec);return (_1ef==1)?new T2(1,_1ee,_1e8):new T2(1,_1ee,new T(function(){return B(_1ea(_1ed.b,_1ef-1|0));}));}};return new F(function(){return _1ea(_1e7,_1e6);});}},_1eg=new T(function(){return B(unCStr(":"));}),_1eh=function(_1ei){var _1ej=E(_1ei);if(!_1ej._){return __Z;}else{var _1ek=new T(function(){return B(_q(_1eg,new T(function(){return B(_1eh(_1ej.b));},1)));},1);return new F(function(){return _q(_1ej.a,_1ek);});}},_1el=function(_1em,_1en){var _1eo=new T(function(){return B(_q(_1eg,new T(function(){return B(_1eh(_1en));},1)));},1);return new F(function(){return _q(_1em,_1eo);});},_1ep=function(_1eq){return new F(function(){return _Lv("Check.hs:173:7-35|(co : na : xs)");});},_1er=new T(function(){return B(_1ep(_));}),_1es=new T(function(){return B(err(_sz));}),_1et=new T(function(){return B(err(_sD));}),_1eu=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_1ev=0,_1ew=new T(function(){return B(unCStr("!"));}),_1ex=function(_1ey,_1ez){var _1eA=E(_1ez);if(!_1eA._){return E(_1er);}else{var _1eB=E(_1eA.b);if(!_1eB._){return E(_1er);}else{var _1eC=E(_1eA.a),_1eD=new T(function(){var _1eE=B(_Hd(58,_1eB.a,_1eB.b));return new T2(0,_1eE.a,_1eE.b);}),_1eF=function(_1eG,_1eH,_1eI){var _1eJ=function(_1eK){if((_1ey+1|0)!=_1eK){return new T3(0,_1ey+1|0,_1eH,_1eA);}else{var _1eL=E(_1eI);return (_1eL._==0)?new T3(0,_1ev,_1eH,_S):new T3(0,_1ev,_1eH,new T(function(){var _1eM=B(_1el(_1eL.a,_1eL.b));if(!_1eM._){return E(_TT);}else{return B(_TO(_1eM.a,_1eM.b));}}));}};if(!B(_qW(_1eG,_1ew))){var _1eN=B(_Gl(B(_sI(_1eu,_1eG))));if(!_1eN._){return E(_1es);}else{if(!E(_1eN.b)._){return new F(function(){return _1eJ(E(_1eN.a));});}else{return E(_1et);}}}else{return new F(function(){return _1eJ( -1);});}};if(E(_1eC)==58){return new F(function(){return _1eF(_S,new T(function(){return E(E(_1eD).a);}),new T(function(){return E(E(_1eD).b);}));});}else{var _1eO=E(_1eD),_1eP=E(_1eO.b);if(!_1eP._){return E(_1er);}else{return new F(function(){return _1eF(new T2(1,_1eC,_1eO.a),_1eP.a,_1eP.b);});}}}}},_1eQ=function(_1eR,_1eS){while(1){var _1eT=E(_1eS);if(!_1eT._){return __Z;}else{var _1eU=_1eT.b,_1eV=E(_1eR);if(_1eV==1){return E(_1eU);}else{_1eR=_1eV-1|0;_1eS=_1eU;continue;}}}},_1eW=function(_1eX,_1eY,_1eZ){var _1f0=new T2(1,_1eY,new T(function(){var _1f1=_1eX+1|0;if(_1f1>0){return B(_1eQ(_1f1,_1eZ));}else{return E(_1eZ);}}));if(0>=_1eX){return E(_1f0);}else{var _1f2=function(_1f3,_1f4){var _1f5=E(_1f3);if(!_1f5._){return E(_1f0);}else{var _1f6=_1f5.a,_1f7=E(_1f4);return (_1f7==1)?new T2(1,_1f6,_1f0):new T2(1,_1f6,new T(function(){return B(_1f2(_1f5.b,_1f7-1|0));}));}};return new F(function(){return _1f2(_1eZ,_1eX);});}},_1f8=new T2(0,_Tw,_Ej),_1f9=function(_1fa,_1fb,_1fc){while(1){var _1fd=E(_1fc);if(!_1fd._){return E(_1f8);}else{var _1fe=_1fd.b,_1ff=E(_1fd.a),_1fg=E(_1ff.a);if(_1fa!=E(_1fg.a)){_1fc=_1fe;continue;}else{if(_1fb!=E(_1fg.b)){_1fc=_1fe;continue;}else{return E(_1ff.b);}}}}},_1fh=function(_1fi,_1fj){while(1){var _1fk=E(_1fj);if(!_1fk._){return __Z;}else{var _1fl=_1fk.b,_1fm=E(_1fi);if(_1fm==1){return E(_1fl);}else{_1fi=_1fm-1|0;_1fj=_1fl;continue;}}}},_1fn=function(_1fo,_1fp,_1fq){var _1fr=E(_1fo);if(_1fr==1){return E(_1fq);}else{return new F(function(){return _1fh(_1fr-1|0,_1fq);});}},_1fs=function(_1ft,_1fu,_1fv){return new T2(1,new T(function(){if(0>=_1ft){return __Z;}else{return B(_pU(_1ft,new T2(1,_1fu,_1fv)));}}),new T(function(){if(_1ft>0){return B(_1fw(_1ft,B(_1fn(_1ft,_1fu,_1fv))));}else{return B(_1fs(_1ft,_1fu,_1fv));}}));},_1fw=function(_1fx,_1fy){var _1fz=E(_1fy);if(!_1fz._){return __Z;}else{var _1fA=_1fz.a,_1fB=_1fz.b;return new T2(1,new T(function(){if(0>=_1fx){return __Z;}else{return B(_pU(_1fx,_1fz));}}),new T(function(){if(_1fx>0){return B(_1fw(_1fx,B(_1fn(_1fx,_1fA,_1fB))));}else{return B(_1fs(_1fx,_1fA,_1fB));}}));}},_1fC=function(_1fD,_1fE,_1fF){var _1fG=_1fE-1|0;if(0<=_1fG){var _1fH=E(_1fD),_1fI=function(_1fJ){var _1fK=new T(function(){if(_1fJ!=_1fG){return B(_1fI(_1fJ+1|0));}else{return __Z;}}),_1fL=function(_1fM){var _1fN=E(_1fM);return (_1fN._==0)?E(_1fK):new T2(1,new T(function(){var _1fO=E(_1fF);if(!_1fO._){return E(_1f8);}else{var _1fP=_1fO.b,_1fQ=E(_1fO.a),_1fR=E(_1fQ.a),_1fS=E(_1fN.a);if(_1fS!=E(_1fR.a)){return B(_1f9(_1fS,_1fJ,_1fP));}else{if(_1fJ!=E(_1fR.b)){return B(_1f9(_1fS,_1fJ,_1fP));}else{return E(_1fQ.b);}}}}),new T(function(){return B(_1fL(_1fN.b));}));};return new F(function(){return _1fL(B(_8y(0,_1fH-1|0)));});};return new F(function(){return _1fw(_1fH,B(_1fI(0)));});}else{return __Z;}},_1fT=function(_1fU){return new F(function(){return _Lv("Check.hs:72:21-47|(l : r : _)");});},_1fV=new T(function(){return B(_1fT(_));}),_1fW=61,_1fX=function(_1fY,_1fZ){while(1){var _1g0=E(_1fY);if(!_1g0._){return E(_1fZ);}else{_1fY=_1g0.b;_1fZ=_1g0.a;continue;}}},_1g1=function(_1g2,_1g3,_1g4){return new F(function(){return _1fX(_1g3,_1g2);});},_1g5=function(_1g6,_1g7){var _1g8=E(_1g7);if(!_1g8._){return new T2(0,_S,_S);}else{var _1g9=_1g8.a;if(!B(A1(_1g6,_1g9))){var _1ga=new T(function(){var _1gb=B(_1g5(_1g6,_1g8.b));return new T2(0,_1gb.a,_1gb.b);});return new T2(0,new T2(1,_1g9,new T(function(){return E(E(_1ga).a);})),new T(function(){return E(E(_1ga).b);}));}else{return new T2(0,_S,_1g8);}}},_1gc=function(_1gd,_1ge){while(1){var _1gf=E(_1ge);if(!_1gf._){return __Z;}else{if(!B(A1(_1gd,_1gf.a))){return E(_1gf);}else{_1ge=_1gf.b;continue;}}}},_1gg=function(_1gh){var _1gi=_1gh>>>0;if(_1gi>887){var _1gj=u_iswspace(_1gh);return (E(_1gj)==0)?false:true;}else{var _1gk=E(_1gi);return (_1gk==32)?true:(_1gk-9>>>0>4)?(E(_1gk)==160)?true:false:true;}},_1gl=function(_1gm){return new F(function(){return _1gg(E(_1gm));});},_1gn=function(_1go){var _1gp=B(_1gc(_1gl,_1go));if(!_1gp._){return __Z;}else{var _1gq=new T(function(){var _1gr=B(_1g5(_1gl,_1gp));return new T2(0,_1gr.a,_1gr.b);});return new T2(1,new T(function(){return E(E(_1gq).a);}),new T(function(){return B(_1gn(E(_1gq).b));}));}},_1gs=function(_1gt){if(!B(_4A(_hd,_1fW,_1gt))){return new T2(0,_1gt,_S);}else{var _1gu=new T(function(){var _1gv=E(_1gt);if(!_1gv._){return E(_1fV);}else{var _1gw=E(_1gv.b);if(!_1gw._){return E(_1fV);}else{var _1gx=_1gw.a,_1gy=_1gw.b,_1gz=E(_1gv.a);if(E(_1gz)==61){return new T2(0,_S,new T(function(){return E(B(_Hd(61,_1gx,_1gy)).a);}));}else{var _1gA=B(_Hd(61,_1gx,_1gy)),_1gB=E(_1gA.b);if(!_1gB._){return E(_1fV);}else{return new T2(0,new T2(1,_1gz,_1gA.a),_1gB.a);}}}}});return new T2(0,new T(function(){var _1gC=B(_1gn(E(_1gu).a));if(!_1gC._){return __Z;}else{return B(_1g1(_1gC.a,_1gC.b,_Vx));}}),new T(function(){var _1gD=B(_1gn(E(_1gu).b));if(!_1gD._){return __Z;}else{return E(_1gD.a);}}));}},_1gE=function(_1gF,_1gG){return new F(function(){return _1e5(E(_1gF),_1gG);});},_1gH=function(_1gI){var _1gJ=E(_1gI);if(!_1gJ._){return new T2(0,_S,_S);}else{var _1gK=E(_1gJ.a),_1gL=new T(function(){var _1gM=B(_1gH(_1gJ.b));return new T2(0,_1gM.a,_1gM.b);});return new T2(0,new T2(1,_1gK.a,new T(function(){return E(E(_1gL).a);})),new T2(1,_1gK.b,new T(function(){return E(E(_1gL).b);})));}},_1gN=new T(function(){return B(unCStr("\u570b\u53f2\u4e26\u3079\u66ff\u3078\u554f\u984c\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_1gO=new T(function(){return B(unCStr("t0"));}),_1gP=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u30de\u30c3\u30d7\u4e0a\u306e\uff20\u3092\u52d5\u304b\u3057\u307e\u3059\u3002\n\u753b\u9762\u306e\u4e0a\u7aef\u30fb\u4e0b\u7aef\u30fb\u5de6\u7aef\u30fb\u53f3\u7aef\u306a\u3069\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3068\uff20\u306f\u305d\u306e\u65b9\u5411\u3078\u52d5\u304d\u307e\u3059\u3002\n{e.ea.m1:t1}{e.eb.m1:t1}{e.ec.m1:t1}"));}),_1gQ=new T2(0,_1gO,_1gP),_1gR=new T(function(){return B(unCStr("t1"));}),_1gS=new T(function(){return B(unCStr("\n\u3053\u308c\u3089\u306e\u6587\u5b57\u306e\u65b9\u5411\u3078\u884c\u304f\u3068 \u3042\u306a\u305f\u306f \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 <\u6301\u3063\u305f> \u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u3053\u306e\u3068\u304d\uff20\u306e\u8272\u304c\u6fc3\u304f\u306a\u3063\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f \uff20\u3092\u3069\u3053\u304b \u5225\u306e\u3068\u3053\u308d\u3078\u6301\u3063\u3066\u3044\u304d \u753b\u9762\u306e\u4e2d\u5fc3\u90e8\u3092\u30bf\u30c3\u30d7\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n{da}{e.oa.m1:t2}{e.ob.m1:t2}{e.oc.m1:t2}"));}),_1gT=new T2(0,_1gR,_1gS),_1gU=new T(function(){return B(unCStr("t2"));}),_1gV=new T(function(){return B(unCStr("\n{da}\n\u3053\u306e\u3068\u304d \u6301\u3063\u3066\u3090\u305f\u6587\u5b57\u304c\u958b\u653e\u3055\u308c \u30de\u30c3\u30d7\u4e0a\u306b \u7f6e\u304b\u308c\u305f\u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u554f\u984c\u3092\u89e3\u304f\u3068\u304d \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 \u30a4\u30b3\u30fc\u30eb <\uff1d>\u306e\u53f3\u306b \u5de6\u304b\u3089\u9806\u756a\u306b\u4e26\u3079\u308b\u5fc5\u8981\u304c\u3042\u308a\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f\u554f\u984c\u3092\u59cb\u3081\u307e\u3059\u3002\n\u3088\u308d\u3057\u3044\u3067\u3059\u304b\uff1f{ch.\u306f\u3044,t3.\u6700\u521d\u304b\u3089,t0}"));}),_1gW=new T2(0,_1gU,_1gV),_1gX=new T(function(){return B(unCStr("t3"));}),_1gY=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f\u59cb\u3081\u307e\u3059\u3002{e.X.jl0}\n{e.X.m1:s0}"));}),_1gZ=new T2(0,_1gX,_1gY),_1h0=new T(function(){return B(unCStr("s0"));}),_1h1=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abc.s0c}{e.b=0.m0:s0eq}"));}),_1h2=new T2(0,_1h0,_1h1),_1h3=new T(function(){return B(unCStr("s0eq"));}),_1h4=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1h5=new T2(0,_1h3,_1h4),_1h6=new T(function(){return B(unCStr("s0c"));}),_1h7=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.0}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306e\u554f\u984c\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s1}"));}),_1h8=new T2(0,_1h6,_1h7),_1h9=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1ha=new T(function(){return B(unCStr("msgR"));}),_1hb=new T2(0,_1ha,_1h9),_1hc=new T(function(){return B(unCStr("s1eq"));}),_1hd=new T2(0,_1hc,_1h4),_1he=new T(function(){return B(unCStr("s1c"));}),_1hf=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s2}"));}),_1hg=new T2(0,_1he,_1hf),_1hh=new T(function(){return B(unCStr("s2"));}),_1hi=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n}"));}),_1hj=new T2(0,_1hh,_1hi),_1hk=new T(function(){return B(unCStr("s2A0"));}),_1hl=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\u5206\u306e\u570b\u306e\u6b74\u53f2\u3092\u77e5\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1hm=new T2(0,_1hk,_1hl),_1hn=new T(function(){return B(unCStr("s2A1_0"));}),_1ho=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1hp=new T2(0,_1hn,_1ho),_1hq=new T(function(){return B(unCStr("s2A1_1"));}),_1hr=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\u7406\u306b\u77e5\u308b\u5fc5\u8981\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1hs=new T2(0,_1hq,_1hr),_1ht=new T(function(){return B(unCStr("s2A1_2"));}),_1hu=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1hv=new T2(0,_1ht,_1hu),_1hw=new T(function(){return B(unCStr("s2B0"));}),_1hx=new T(function(){return B(unCStr("\n\u79c1\u306e\u6301\u3063\u3066\u3090\u308b\u60c5\u5831\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\u308b\u306e\u306b\u4f7f\u306f\u308c\u305f\u77f3\u306f \u7a7a\u4e2d\u306b\u6301\u3061\u4e0a\u3052\u3089\u308c\u3066 \u7d44\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1hy=new T2(0,_1hw,_1hx),_1hz=new T(function(){return B(unCStr("s2C0"));}),_1hA=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\u672c\u3092\u8a2a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\u6240\u306b\u306f \u305d\u306e\u5f62\u8de1\u304c \u3044\u304f\u3064\u3082\u6b8b\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\u6280\u3092\u6388\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\u9332\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1hB=new T2(0,_1hz,_1hA),_1hC=new T(function(){return B(unCStr("s2D0"));}),_1hD=new T(function(){return B(unCStr("\n\u6b74\u53f2\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\u3078\u308b\u76ee\u7684\u3084 \u50b3\u3078\u308b\u4eba\u3005\u306e\u4e16\u754c\u89c0 \u50b3\u3078\u305f\u7576\u6642\u306b\u6b8b\u3063\u3066\u3090\u305f\u8cc7\u6599\u306e\u7a2e\u985e\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\u3058\u6642\u4ee3\u306b\u95dc\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\u7576\u7570\u306a\u3063\u305f\u50b3\u3078\u65b9\u304c\u70ba\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\u5be6\u306a\u6b74\u53f2\u306f\u5b58\u5728\u305b\u305a \u6b74\u53f2\u3092\u5b78\u3076\u610f\u7fa9\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\u5f97\u3057 \u4ed6\u306e\u4eba\u9054\u3068\u5171\u6709\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\u8eab\u304c\u898b\u51fa\u3057 \u7d21\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\u7d44\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\u5024\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\u304d\u308b\u610f\u5473\u306b\u3082 \u7e4b\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1hE=new T2(0,_1hC,_1hD),_1hF=new T(function(){return B(unCStr("s2n"));}),_1hG=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n1.\u9032\u307e\u306a\u3044,s2n0}"));}),_1hH=new T2(0,_1hF,_1hG),_1hI=new T(function(){return B(unCStr("s8I2"));}),_1hJ=new T(function(){return B(unCStr("\n\u3067\u306f \u3088\u3044\u4e00\u65e5\u3092\u30fb\u30fb\u30fb\u3002{e.X.l}"));}),_1hK=new T2(0,_1hI,_1hJ),_1hL=new T2(1,_1hK,_S),_1hM=new T(function(){return B(unCStr("s8I1"));}),_1hN=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u59cb\u3081\u307e\u305b\u3046\u3002{da}{e.c8.m1:s0}{e.X.jl0}"));}),_1hO=new T2(0,_1hM,_1hN),_1hP=new T2(1,_1hO,_1hL),_1hQ=new T(function(){return B(unCStr("s8I0"));}),_1hR=new T(function(){return B(unCStr("\n\u304a\u3064\u304b\u308c\u3055\u307e\u3067\u3059\u3002\n\u3042\u306a\u305f\u306e\u9ede\u6578\u306f{rs}\n\u9ede\u3067\u3059\u3002\n\u307e\u3046\u3044\u3061\u3069 \u3084\u308a\u307e\u3059\u304b\uff1f{ch.\u3084\u308b,s8I1.\u3084\u3081\u308b,s8I2}"));}),_1hS=new T2(0,_1hQ,_1hR),_1hT=new T2(1,_1hS,_1hP),_1hU=new T(function(){return B(unCStr("s8"));}),_1hV=new T(function(){return B(unCStr("\n\u3060\u308c\u304b\u3090\u307e\u3059\u3002{da}{e.bI.m0:s8I0}"));}),_1hW=new T2(0,_1hU,_1hV),_1hX=new T2(1,_1hW,_1hT),_1hY=new T(function(){return B(unCStr("s7c"));}),_1hZ=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s8}"));}),_1i0=new T2(0,_1hY,_1hZ),_1i1=new T2(1,_1i0,_1hX),_1i2=new T(function(){return B(unCStr("s7eq"));}),_1i3=new T2(0,_1i2,_1h4),_1i4=new T2(1,_1i3,_1i1),_1i5=new T(function(){return B(unCStr("s7"));}),_1i6=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcde.s7c}{e.b=0.m0:s7eq}"));}),_1i7=new T2(0,_1i5,_1i6),_1i8=new T2(1,_1i7,_1i4),_1i9=new T(function(){return B(unCStr("s6c"));}),_1ia=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s7}"));}),_1ib=new T2(0,_1i9,_1ia),_1ic=new T2(1,_1ib,_1i8),_1id=new T(function(){return B(unCStr("s6eq"));}),_1ie=new T2(0,_1id,_1h4),_1if=new T2(1,_1ie,_1ic),_1ig=new T(function(){return B(unCStr("s6"));}),_1ih=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abcde.s6c}{e.b=0.m0:s6eq}"));}),_1ii=new T2(0,_1ig,_1ih),_1ij=new T2(1,_1ii,_1if),_1ik=new T(function(){return B(unCStr("s5n1"));}),_1il=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s6}"));}),_1im=new T2(0,_1ik,_1il),_1in=new T2(1,_1im,_1ij),_1io=new T(function(){return B(unCStr("s5n0"));}),_1ip=new T(function(){return B(unCStr("\n\u884c\u304f\u306e\u3092\u3084\u3081\u307e\u3057\u305f\u3002"));}),_1iq=new T2(0,_1io,_1ip),_1ir=new T2(1,_1iq,_1in),_1is=new T(function(){return B(unCStr("s5n"));}),_1it=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n1.\u9032\u307e\u306a\u3044,s5n0}"));}),_1iu=new T2(0,_1is,_1it),_1iv=new T2(1,_1iu,_1ir),_1iw=new T(function(){return B(unCStr("s5H0"));}),_1ix=new T(function(){return B(unCStr("\n\u6211\u304c\u570b\u306e\u6557\u6230\u5f8c \u7279\u306b\u5f37\u307e\u3063\u305f \u65e5\u672c\u8a9e\u306e\u7834\u58ca\u5de5\u4f5c\u306f \u305d\u308c\u3092\u4ed5\u639b\u3051\u305f\u4eba\u306e\u610f\u5716\u3068\u9006\u306b \u65e5\u672c\u8a9e\u3092\u5f37\u5316\u3057 \u305d\u306e\u67d4\u8edf\u3055\u3092 \u3088\u308a\u4e16\u754c\u306b\u767c\u4fe1\u3059\u308b\u571f\u58cc\u3092\u4f5c\u3063\u305f\u306e\u3067\u306f\u306a\u3044\u304b\u3068 \u79c1\u306f\u8003\u3078\u3066\u3090\u307e\u3059\u3002\n\u3067\u3059\u304b\u3089 \u304b\u306a\u9063\u3072\u3092\u6df7\u4e82\u3055\u305b\u305f\u308a \u6f22\u5b57\u3092\u3068\u3063\u305f\u308a\u3064\u3051\u305f\u308a\u3057\u305f\u3053\u3068\u304c \u9006\u306b\u65e5\u672c\u8a9e\u306e\u5f37\u3055 \u67d4\u8edf\u3055\u306e\u8a3c\u660e\u3092\u3082\u305f\u3089\u3057\u305f\u3068\u3082\u3044\u3078\u308b\u306e\u3067 \u65e5\u672c\u8a9e\u3092\u6df7\u4e82\u3055\u305b\u305f\u4eba\u3005\u306b \u79c1\u306f\u611f\u8b1d\u3057\u3066\u3090\u308b\u306e\u3067\u3059\u3002"));}),_1iy=new T2(0,_1iw,_1ix),_1iz=new T2(1,_1iy,_1iv),_1iA=new T(function(){return B(unCStr("s5G0"));}),_1iB=new T(function(){return B(unCStr("\n\u540c\u3058\u6642\u4ee3\u306e \u540c\u3058\u5834\u6240\u306b\u95dc\u3059\u308b\u898b\u65b9\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u9055\u3075\u306e\u306f\n\u4eca \u79c1\u3068 \u3042\u306a\u305f\u304c\u540c\u3058\u5834\u6240\u306b\u3090\u3066 \u305d\u3053\u306b\u5c45\u308b\u5225\u8ab0\u304b\u306b\u5c0d\u3059\u308b\u5370\u8c61\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u7570\u306a\u3063\u3066\u3090\u308b\u3053\u3068\u3068 \u4f3c\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u306f \u81ea\u7136\u306a\u3053\u3068\u3067 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306e\u898b\u65b9\u304c\u9055\u3075\u306e\u306f \u5168\u304f\u554f\u984c\u3042\u308a\u307e\u305b\u3093\u3002\n\u898b\u65b9\u304c\u5168\u7136\u7570\u306a\u3063\u3066\u3090\u3066\u3082 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306f \u5171\u611f\u3059\u308b\u559c\u3073\u3092\u5473\u308f\u3046\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1iC=new T2(0,_1iA,_1iB),_1iD=new T2(1,_1iC,_1iz),_1iE=new T(function(){return B(unCStr("s5F0"));}),_1iF=new T(function(){return B(unCStr("\n\u672a\u4f86\u306f\u7576\u7136\u3055\u3046\u3067\u3059\u304c \u904e\u53bb\u3092\u6c7a\u3081\u308b\u306e\u3082 \u4eca\u306e\u3042\u306a\u305f\u6b21\u7b2c\u3067\u3059\u3002"));}),_1iG=new T2(0,_1iE,_1iF),_1iH=new T2(1,_1iG,_1iD),_1iI=new T(function(){return B(unCStr("s5E0"));}),_1iJ=new T(function(){return B(unCStr("\n\u904e\u53bb\u3082\u672a\u4f86\u3082 \u305d\u3057\u3066\u5225\u306e\u4e26\u884c\u4e16\u754c\u3082 \u3059\u3079\u3066\u306f \u4eca \u3053\u3053\u306b\u3042\u308a\u307e\u3059\u3002"));}),_1iK=new T2(0,_1iI,_1iJ),_1iL=new T2(1,_1iK,_1iH),_1iM=new T(function(){return B(unCStr("s5"));}),_1iN=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n}"));}),_1iO=new T2(0,_1iM,_1iN),_1iP=new T2(1,_1iO,_1iL),_1iQ=new T(function(){return B(unCStr("s4c"));}),_1iR=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s5}"));}),_1iS=new T2(0,_1iQ,_1iR),_1iT=new T2(1,_1iS,_1iP),_1iU=new T(function(){return B(unCStr("s4eq"));}),_1iV=new T2(0,_1iU,_1h4),_1iW=new T2(1,_1iV,_1iT),_1iX=new T(function(){return B(unCStr("s4"));}),_1iY=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s4c}{e.b=0.m0:s4eq}"));}),_1iZ=new T2(0,_1iX,_1iY),_1j0=new T2(1,_1iZ,_1iW),_1j1=new T(function(){return B(unCStr("s3c"));}),_1j2=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s4}"));}),_1j3=new T2(0,_1j1,_1j2),_1j4=new T2(1,_1j3,_1j0),_1j5=new T(function(){return B(unCStr("s3eq"));}),_1j6=new T2(0,_1j5,_1h4),_1j7=new T2(1,_1j6,_1j4),_1j8=new T(function(){return B(unCStr("s3"));}),_1j9=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s3c}{e.b=0.m0:s3eq}"));}),_1ja=new T2(0,_1j8,_1j9),_1jb=new T2(1,_1ja,_1j7),_1jc=new T(function(){return B(unCStr("s2n1"));}),_1jd=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s3}"));}),_1je=new T2(0,_1jc,_1jd),_1jf=new T2(1,_1je,_1jb),_1jg=new T(function(){return B(unCStr("s2n0"));}),_1jh=new T2(0,_1jg,_1ip),_1ji=new T2(1,_1jh,_1jf),_1jj=new T2(1,_1hH,_1ji),_1jk=new T2(1,_1hE,_1jj),_1jl=new T2(1,_1hB,_1jk),_1jm=new T2(1,_1hy,_1jl),_1jn=new T2(1,_1hv,_1jm),_1jo=new T2(1,_1hs,_1jn),_1jp=new T2(1,_1hp,_1jo),_1jq=new T2(1,_1hm,_1jp),_1jr=new T2(1,_1hj,_1jq),_1js=new T2(1,_1hg,_1jr),_1jt=new T2(1,_1hd,_1js),_1ju=new T(function(){return B(unCStr("s1"));}),_1jv=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.1.z.abc.s1c}{e.b=0.m0:s1eq}"));}),_1jw=new T2(0,_1ju,_1jv),_1jx=new T2(1,_1jw,_1jt),_1jy=new T(function(){return B(unCStr("nubatama"));}),_1jz=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1jA=new T2(0,_1jy,_1jz),_1jB=new T2(1,_1jA,_1jx),_1jC=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1jD=new T(function(){return B(unCStr("msgW"));}),_1jE=new T2(0,_1jD,_1jC),_1jF=new T2(1,_1jE,_1jB),_1jG=new T2(1,_1hb,_1jF),_1jH=new T2(1,_1h8,_1jG),_1jI=new T2(1,_1h5,_1jH),_1jJ=new T2(1,_1h2,_1jI),_1jK=new T2(1,_1gZ,_1jJ),_1jL=new T2(1,_1gW,_1jK),_1jM=new T2(1,_1gT,_1jL),_1jN=new T2(1,_1gQ,_1jM),_1jO=new T(function(){return B(unCStr("initMsg"));}),_1jP=function(_1jQ,_1jR){var _1jS=new T(function(){var _1jT=B(_1gH(_1jQ));return new T2(0,_1jT.a,_1jT.b);}),_1jU=function(_1jV){var _1jW=E(_1jV);if(!_1jW._){return E(_1jS);}else{var _1jX=E(_1jW.a),_1jY=new T(function(){return B(_1jU(_1jW.b));});return new T2(0,new T2(1,_1jX.a,new T(function(){return E(E(_1jY).a);})),new T2(1,_1jX.b,new T(function(){return E(E(_1jY).b);})));}},_1jZ=function(_1k0,_1k1,_1k2){var _1k3=new T(function(){return B(_1jU(_1k2));});return new T2(0,new T2(1,_1k0,new T(function(){return E(E(_1k3).a);})),new T2(1,_1k1,new T(function(){return E(E(_1k3).b);})));},_1k4=B(_1jZ(_1jO,_1gN,_1jN)),_1k5=_1k4.a;if(!B(_4A(_qk,_1jR,_1k5))){return __Z;}else{return new F(function(){return _6X(_1k4.b,B(_MU(_qk,_1jR,_1k5)));});}},_1k6=5,_1k7=new T2(0,_1k6,_1k6),_1k8=7,_1k9=new T2(0,_1k8,_1k6),_1ka=6,_1kb=new T2(0,_1k6,_1ka),_1kc=new T2(1,_1kb,_S),_1kd=new T2(1,_1k9,_1kc),_1ke=new T2(1,_1k9,_1kd),_1kf=new T2(1,_1kb,_1ke),_1kg=new T2(1,_1k9,_1kf),_1kh=new T2(1,_1k9,_1kg),_1ki=new T2(1,_1kb,_1kh),_1kj=new T2(1,_1k7,_1ki),_1kk=new T2(1,_1k7,_1kj),_1kl=2,_1km=new T2(0,_1kl,_1kl),_1kn=new T2(1,_1km,_S),_1ko=new T2(1,_1km,_1kn),_1kp=new T2(1,_1km,_1ko),_1kq=new T2(1,_1km,_1kp),_1kr=new T2(1,_1km,_1kq),_1ks=new T2(1,_1km,_1kr),_1kt=new T2(1,_1km,_1ks),_1ku=new T2(1,_1km,_1kt),_1kv=new T2(1,_1km,_1ku),_1kw=new T(function(){return B(unCStr("Int"));}),_1kx=function(_1ky,_1kz,_1kA){return new F(function(){return _1bK(_1bd,new T2(0,_1kz,_1kA),_1ky,_1kw);});},_1kB=new T(function(){return B(unCStr("msgR"));}),_1kC=new T(function(){return B(_1jP(_S,_1kB));}),_1kD=new T(function(){return B(unCStr("msgW"));}),_1kE=new T(function(){return B(_1jP(_S,_1kD));}),_1kF=function(_1kG){var _1kH=E(_1kG);return 0;},_1kI=new T(function(){return B(unCStr("@@@@@@@@@"));}),_1kJ=new T(function(){var _1kK=E(_1kI);if(!_1kK._){return E(_nn);}else{return E(_1kK.a);}}),_1kL=122,_1kM=new T2(0,_1kL,_Ep),_1kN=0,_1kO=new T2(0,_1kN,_1kN),_1kP=new T2(0,_1kO,_1kM),_1kQ=61,_1kR=new T2(0,_1kQ,_Ep),_1kS=1,_1kT=new T2(0,_1kS,_1kN),_1kU=new T2(0,_1kT,_1kR),_1kV=97,_1kW=new T2(0,_1kV,_Ej),_1kX=4,_1kY=new T2(0,_1kN,_1kX),_1kZ=new T2(0,_1kY,_1kW),_1l0=98,_1l1=new T2(0,_1l0,_Ej),_1l2=new T2(0,_1kl,_1kX),_1l3=new T2(0,_1l2,_1l1),_1l4=99,_1l5=new T2(0,_1l4,_Ej),_1l6=new T2(0,_1kX,_1kX),_1l7=new T2(0,_1l6,_1l5),_1l8=new T2(1,_1l7,_S),_1l9=new T2(1,_1l3,_1l8),_1la=new T2(1,_1kZ,_1l9),_1lb=new T2(1,_1kU,_1la),_1lc=new T2(1,_1kP,_1lb),_1ld=new T(function(){return B(_1fC(_1k6,5,_1lc));}),_1le=new T(function(){return B(_Lv("Check.hs:142:22-33|(ch : po)"));}),_1lf=new T(function(){return B(_ed("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1lg=110,_1lh=new T2(0,_1lg,_Ev),_1li=new T2(0,_1kX,_1k6),_1lj=new T2(0,_1li,_1lh),_1lk=new T2(1,_1lj,_S),_1ll=new T2(0,_1kl,_1k6),_1lm=66,_1ln=new T2(0,_1lm,_Ep),_1lo=new T2(0,_1ll,_1ln),_1lp=new T2(1,_1lo,_1lk),_1lq=3,_1lr=new T2(0,_1kN,_1lq),_1ls=67,_1lt=new T2(0,_1ls,_Ep),_1lu=new T2(0,_1lr,_1lt),_1lv=new T2(1,_1lu,_1lp),_1lw=new T2(0,_1kX,_1kS),_1lx=65,_1ly=new T2(0,_1lx,_Ep),_1lz=new T2(0,_1lw,_1ly),_1lA=new T2(1,_1lz,_1lv),_1lB=68,_1lC=new T2(0,_1lB,_Ep),_1lD=new T2(0,_1kT,_1lC),_1lE=new T2(1,_1lD,_1lA),_1lF=100,_1lG=new T2(0,_1lF,_Ej),_1lH=new T2(0,_1ka,_1kX),_1lI=new T2(0,_1lH,_1lG),_1lJ=new T2(1,_1lI,_S),_1lK=new T2(1,_1l7,_1lJ),_1lL=new T2(1,_1l3,_1lK),_1lM=new T2(1,_1kZ,_1lL),_1lN=new T2(1,_1kU,_1lM),_1lO=new T2(1,_1kP,_1lN),_1lP=70,_1lQ=new T2(0,_1lP,_Ep),_1lR=new T2(0,_1ll,_1lQ),_1lS=new T2(1,_1lR,_1lk),_1lT=72,_1lU=new T2(0,_1lT,_Ep),_1lV=new T2(0,_1lr,_1lU),_1lW=new T2(1,_1lV,_1lS),_1lX=69,_1lY=new T2(0,_1lX,_Ep),_1lZ=new T2(0,_1lw,_1lY),_1m0=new T2(1,_1lZ,_1lW),_1m1=71,_1m2=new T2(0,_1m1,_Ep),_1m3=new T2(0,_1kT,_1m2),_1m4=new T2(1,_1m3,_1m0),_1m5=101,_1m6=new T2(0,_1m5,_Ej),_1m7=new T2(0,_1kX,_1kl),_1m8=new T2(0,_1m7,_1m6),_1m9=new T2(1,_1m8,_1lM),_1ma=new T2(1,_1kU,_1m9),_1mb=new T2(1,_1kP,_1ma),_1mc=73,_1md=new T2(0,_1mc,_Ep),_1me=new T2(0,_1kl,_1kN),_1mf=new T2(0,_1me,_1md),_1mg=new T2(1,_1mf,_S),_1mh=new T2(1,_1mg,_S),_1mi=new T2(1,_1mb,_1mh),_1mj=new T2(1,_1mb,_1mi),_1mk=new T2(1,_1m4,_1mj),_1ml=new T2(1,_1lO,_1mk),_1mm=new T2(1,_1lO,_1ml),_1mn=new T2(1,_1lE,_1mm),_1mo=new T2(1,_1lc,_1mn),_1mp=new T2(1,_1lc,_1mo),_1mq=function(_1mr){var _1ms=E(_1mr);if(!_1ms._){return __Z;}else{var _1mt=_1ms.b,_1mu=E(_1ms.a),_1mv=_1mu.b,_1mw=E(_1mu.a),_1mx=function(_1my){if(E(_1mw)==32){return new T2(1,_1mu,new T(function(){return B(_1mq(_1mt));}));}else{switch(E(_1mv)){case 0:return new T2(1,new T2(0,_1mw,_Ej),new T(function(){return B(_1mq(_1mt));}));case 1:return new T2(1,new T2(0,_1mw,_EU),new T(function(){return B(_1mq(_1mt));}));case 2:return new T2(1,new T2(0,_1mw,_Ev),new T(function(){return B(_1mq(_1mt));}));case 3:return new T2(1,new T2(0,_1mw,_EB),new T(function(){return B(_1mq(_1mt));}));case 4:return new T2(1,new T2(0,_1mw,_EH),new T(function(){return B(_1mq(_1mt));}));case 5:return new T2(1,new T2(0,_1mw,_F8),new T(function(){return B(_1mq(_1mt));}));case 6:return new T2(1,new T2(0,_1mw,_F1),new T(function(){return B(_1mq(_1mt));}));case 7:return new T2(1,new T2(0,_1mw,_EU),new T(function(){return B(_1mq(_1mt));}));default:return new T2(1,new T2(0,_1mw,_EN),new T(function(){return B(_1mq(_1mt));}));}}};if(E(_1mw)==32){return new F(function(){return _1mx(_);});}else{switch(E(_1mv)){case 0:return new T2(1,new T2(0,_1mw,_EN),new T(function(){return B(_1mq(_1mt));}));case 1:return new F(function(){return _1mx(_);});break;case 2:return new F(function(){return _1mx(_);});break;case 3:return new F(function(){return _1mx(_);});break;case 4:return new F(function(){return _1mx(_);});break;case 5:return new F(function(){return _1mx(_);});break;case 6:return new F(function(){return _1mx(_);});break;case 7:return new F(function(){return _1mx(_);});break;default:return new F(function(){return _1mx(_);});}}}},_1mz=function(_1mA){var _1mB=E(_1mA);return (_1mB._==0)?__Z:new T2(1,new T(function(){return B(_1mq(_1mB.a));}),new T(function(){return B(_1mz(_1mB.b));}));},_1mC=function(_1mD){var _1mE=E(_1mD);if(!_1mE._){return __Z;}else{var _1mF=_1mE.b,_1mG=E(_1mE.a),_1mH=_1mG.b,_1mI=E(_1mG.a),_1mJ=function(_1mK){if(E(_1mI)==32){return new T2(1,_1mG,new T(function(){return B(_1mC(_1mF));}));}else{switch(E(_1mH)){case 0:return new T2(1,new T2(0,_1mI,_Ej),new T(function(){return B(_1mC(_1mF));}));case 1:return new T2(1,new T2(0,_1mI,_Ep),new T(function(){return B(_1mC(_1mF));}));case 2:return new T2(1,new T2(0,_1mI,_Ev),new T(function(){return B(_1mC(_1mF));}));case 3:return new T2(1,new T2(0,_1mI,_EB),new T(function(){return B(_1mC(_1mF));}));case 4:return new T2(1,new T2(0,_1mI,_EH),new T(function(){return B(_1mC(_1mF));}));case 5:return new T2(1,new T2(0,_1mI,_F8),new T(function(){return B(_1mC(_1mF));}));case 6:return new T2(1,new T2(0,_1mI,_F1),new T(function(){return B(_1mC(_1mF));}));case 7:return new T2(1,new T2(0,_1mI,_Ep),new T(function(){return B(_1mC(_1mF));}));default:return new T2(1,new T2(0,_1mI,_EN),new T(function(){return B(_1mC(_1mF));}));}}};if(E(_1mI)==32){return new F(function(){return _1mJ(_);});}else{if(E(_1mH)==8){return new T2(1,new T2(0,_1mI,_Ej),new T(function(){return B(_1mC(_1mF));}));}else{return new F(function(){return _1mJ(_);});}}}},_1mL=function(_1mM){var _1mN=E(_1mM);return (_1mN._==0)?__Z:new T2(1,new T(function(){return B(_1mC(_1mN.a));}),new T(function(){return B(_1mL(_1mN.b));}));},_1mO=function(_1mP,_1mQ,_1mR,_1mS,_1mT,_1mU,_1mV,_1mW,_1mX,_1mY,_1mZ,_1n0,_1n1,_1n2,_1n3,_1n4,_1n5,_1n6,_1n7,_1n8,_1n9,_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt){var _1nu=E(_1mQ);if(!_1nu._){return E(_1lf);}else{var _1nv=_1nu.b,_1nw=E(_1nu.a),_1nx=new T(function(){var _1ny=function(_){var _1nz=B(_mz(_1n6,0))-1|0,_1nA=function(_1nB){if(_1nB>=0){var _1nC=newArr(_1nB,_1b1),_1nD=_1nC,_1nE=E(_1nB);if(!_1nE){return new T4(0,E(_1ev),E(_1nz),0,_1nD);}else{var _1nF=function(_1nG,_1nH,_){while(1){var _1nI=E(_1nG);if(!_1nI._){return E(_);}else{var _=_1nD[_1nH]=_1nI.a;if(_1nH!=(_1nE-1|0)){var _1nJ=_1nH+1|0;_1nG=_1nI.b;_1nH=_1nJ;continue;}else{return E(_);}}}},_=B(_1nF(_1n6,0,_));return new T4(0,E(_1ev),E(_1nz),_1nE,_1nD);}}else{return E(_1bV);}};if(0>_1nz){return new F(function(){return _1nA(0);});}else{return new F(function(){return _1nA(_1nz+1|0);});}},_1nK=B(_1bW(_1ny)),_1nL=E(_1nK.a),_1nM=E(_1nK.b),_1nN=E(_1mP);if(_1nL>_1nN){return B(_1kx(_1nN,_1nL,_1nM));}else{if(_1nN>_1nM){return B(_1kx(_1nN,_1nL,_1nM));}else{return E(_1nK.d[_1nN-_1nL|0]);}}});switch(E(_1nw)){case 97:var _1nO=new T(function(){var _1nP=E(_1nv);if(!_1nP._){return E(_1le);}else{return new T2(0,_1nP.a,_1nP.b);}}),_1nQ=new T(function(){var _1nR=B(_1gs(E(_1nO).b));return new T2(0,_1nR.a,_1nR.b);}),_1nS=B(_Gl(B(_sI(_1eu,new T(function(){return E(E(_1nQ).b);})))));if(!_1nS._){return E(_1es);}else{if(!E(_1nS.b)._){var _1nT=new T(function(){var _1nU=B(_Gl(B(_sI(_1eu,new T(function(){return E(E(_1nQ).a);})))));if(!_1nU._){return E(_1es);}else{if(!E(_1nU.b)._){return E(_1nU.a);}else{return E(_1et);}}},1);return {_:0,a:E({_:0,a:E(_1mR),b:E(B(_L4(_1nT,E(_1nS.a),new T(function(){return E(E(_1nO).a);}),_Ej,_1mS))),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};}else{return E(_1et);}}break;case 104:return {_:0,a:E({_:0,a:E(_1mR),b:E(B(_1mz(_1mS))),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};case 106:var _1nV=E(_1nv);if(!_1nV._){return {_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l: -1,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};}else{if(E(_1nV.a)==108){var _1nW=E(_1mP),_1nX=B(_Gl(B(_sI(_1eu,_1nV.b))));return (_1nX._==0)?E(_1es):(E(_1nX.b)._==0)?{_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(B(_1e5(_1nW,_1n5))),f:E(B(_1e5(_1nW,_1n6))),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:E(_1nX.a),m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_wE),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)}:E(_1et);}else{var _1nY=B(_Gl(B(_sI(_1eu,_1nV))));return (_1nY._==0)?E(_1es):(E(_1nY.b)._==0)?{_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:E(_1nY.a),m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)}:E(_1et);}}break;case 108:var _1nZ=E(_1mP);return {_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(B(_1e5(_1nZ,_1n5))),f:E(B(_1e5(_1nZ,_1n6))),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_wE),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};case 109:var _1o0=B(_1ex(E(_1nx),_1nv)),_1o1=_1o0.c,_1o2=B(_qW(_1o1,_S));if(!E(_1o2)){var _1o3=E(_1mP),_1o4=new T(function(){var _1o5=function(_){var _1o6=B(_mz(_1n5,0))-1|0,_1o7=function(_1o8){if(_1o8>=0){var _1o9=newArr(_1o8,_1b1),_1oa=_1o9,_1ob=E(_1o8);if(!_1ob){return new T4(0,E(_1ev),E(_1o6),0,_1oa);}else{var _1oc=function(_1od,_1oe,_){while(1){var _1of=E(_1od);if(!_1of._){return E(_);}else{var _=_1oa[_1oe]=_1of.a;if(_1oe!=(_1ob-1|0)){var _1og=_1oe+1|0;_1od=_1of.b;_1oe=_1og;continue;}else{return E(_);}}}},_=B(_1oc(_1n5,0,_));return new T4(0,E(_1ev),E(_1o6),_1ob,_1oa);}}else{return E(_1bV);}};if(0>_1o6){return new F(function(){return _1o7(0);});}else{return new F(function(){return _1o7(_1o6+1|0);});}},_1oh=B(_1bW(_1o5)),_1oi=E(_1oh.a),_1oj=E(_1oh.b);if(_1oi>_1o3){return B(_1kx(_1o3,_1oi,_1oj));}else{if(_1o3>_1oj){return B(_1kx(_1o3,_1oi,_1oj));}else{return E(E(_1oh.d[_1o3-_1oi|0]).a);}}}),_1ok=B(_1eW(_1o3,new T2(0,_1o4,new T2(1,_1nw,_1o1)),_1n5));}else{var _1ok=B(_1gE(_1mP,_1n5));}if(!E(_1o2)){var _1ol=B(_1eW(E(_1mP),_1o0.a,_1n6));}else{var _1ol=B(_1gE(_1mP,_1n6));}return {_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(B(_1jP(_1n4,_1o0.b))),d:E(_1n4),e:E(_1ok),f:E(_1ol),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_wE),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};case 114:var _1om=B(_6X(_1kk,_1mW));return {_:0,a:E({_:0,a:E(B(_6X(_1kv,_1mW))),b:E(B(_1fC(_1om.a,E(_1om.b),new T(function(){return B(_6X(_1mp,_1mW));})))),c:E(_1mT),d:B(_6X(_1kI,_1mW)),e:32,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1om),c:E(_1kC),d:E(_1n4),e:E(_1n5),f:E(B(_6k(_1kF,_1n6))),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_wE),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};case 115:return {_:0,a:E({_:0,a:E(_1mR),b:E(B(_1mL(_1mS))),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};case 116:var _1on=E(_1nx),_1oo=B(_1ex(_1on,_1nv)),_1op=E(_1oo.a);if(!E(_1op)){var _1oq=true;}else{var _1oq=false;}if(!E(_1oq)){var _1or=B(_1eW(E(_1mP),_1op,_1n6));}else{var _1or=B(_1eW(E(_1mP),_1on+1|0,_1n6));}if(!E(_1oq)){var _1os=__Z;}else{var _1os=E(_1oo.b);}if(!B(_qW(_1os,_S))){var _1ot=B(_1mO(_1mP,_1os,_1mR,_1mS,_1mT,_1mU,_1mV,_1mW,_1mX,_1mY,_1mZ,_1n0,_1n1,_1n2,_1n3,_1n4,_1n5,_1or,_1n7,_1n8,_1n9,_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt)),_1ou=E(_1ot.a);return {_:0,a:E({_:0,a:E(_1ou.a),b:E(_1ou.b),c:E(_1ou.c),d:_1ou.d,e:_1ou.e,f:_1ou.f,g:E(_1ou.g),h:_1ou.h,i:E(B(_q(_1mZ,_1nu))),j:E(_1ou.j),k:E(_1ou.k)}),b:E(_1ot.b),c:E(_1ot.c),d:E(_1ot.d),e:E(_1ot.e),f:E(_1ot.f),g:E(_1ot.g),h:E(_1ot.h),i:_1ot.i,j:_1ot.j,k:_1ot.k,l:_1ot.l,m:E(_1ot.m),n:_1ot.n,o:E(_1ot.o),p:E(_1ot.p),q:_1ot.q,r:E(_1ot.r),s:E(_1ot.s),t:_1ot.t,u:E(_1ot.u),v:E(_1ot.v)};}else{return {_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1or),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};}break;case 119:return {_:0,a:E({_:0,a:E(_1km),b:E(_1ld),c:E(_1mT),d:E(_1kJ),e:32,f:0,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1k7),c:E(_1kE),d:E(_1n4),e:E(_1n5),f:E(B(_6k(_1kF,_1n6))),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_wE),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};default:return {_:0,a:E({_:0,a:E(_1mR),b:E(_1mS),c:E(_1mT),d:_1mU,e:_1mV,f:_1mW,g:E(_1mX),h:_1mY,i:E(B(_q(_1mZ,_1nu))),j:E(_1n0),k:E(_1n1)}),b:E(_1n2),c:E(_1n3),d:E(_1n4),e:E(_1n5),f:E(_1n6),g:E(_1n7),h:E(_1n8),i:_1n9,j:_1na,k:_1nb,l:_1nc,m:E(_1nd),n:_1ne,o:E(_1nf),p:E(_1ng),q:_1nh,r:E(_1ni),s:E(_1nj),t:_1nk,u:E({_:0,a:E(_1nl),b:E(_1nm),c:E(_1nn),d:E(_1no),e:E(_1np),f:E(_1nq),g:E(_1nr),h:E(_1ns)}),v:E(_1nt)};}}},_1ov=function(_1ow,_1ox){while(1){var _1oy=E(_1ox);if(!_1oy._){return __Z;}else{var _1oz=_1oy.b,_1oA=E(_1ow);if(_1oA==1){return E(_1oz);}else{_1ow=_1oA-1|0;_1ox=_1oz;continue;}}}},_1oB=new T(function(){return B(unCStr("X"));}),_1oC=new T(function(){return B(_ed("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1oD=38,_1oE=function(_1oF,_1oG,_1oH,_1oI,_1oJ,_1oK,_1oL,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3){var _1p4=E(_1oH);if(!_1p4._){return {_:0,a:_1oI,b:_1oJ,c:_1oK,d:_1oL,e:_1oM,f:_1oN,g:_1oO,h:_1oP,i:_1oQ,j:_1oR,k:_1oS,l:_1oT,m:_1oU,n:_1oV,o:_1oW,p:_1oX,q:_1oY,r:_1oZ,s:_1p0,t:_1p1,u:_1p2,v:_1p3};}else{var _1p5=_1p4.b,_1p6=E(_1p4.a),_1p7=_1p6.a,_1p8=_1p6.b,_1p9=function(_1pa,_1pb,_1pc){var _1pd=function(_1pe,_1pf){if(!B(_qW(_1pe,_S))){var _1pg=E(_1oI),_1ph=E(_1p2),_1pi=B(_1mO(_1pf,_1pe,_1pg.a,_1pg.b,_1pg.c,_1pg.d,_1pg.e,_1pg.f,_1pg.g,_1pg.h,_1pg.i,_1pg.j,_1pg.k,_1oJ,_1oK,_1oL,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1ph.a,_1ph.b,_1ph.c,_1ph.d,_1ph.e,_1ph.f,_1ph.g,_1ph.h,_1p3)),_1pj=_1pi.a,_1pk=_1pi.b,_1pl=_1pi.c,_1pm=_1pi.d,_1pn=_1pi.e,_1po=_1pi.f,_1pp=_1pi.g,_1pq=_1pi.h,_1pr=_1pi.i,_1ps=_1pi.j,_1pt=_1pi.k,_1pu=_1pi.l,_1pv=_1pi.m,_1pw=_1pi.n,_1px=_1pi.o,_1py=_1pi.p,_1pz=_1pi.q,_1pA=_1pi.r,_1pB=_1pi.s,_1pC=_1pi.t,_1pD=_1pi.u,_1pE=_1pi.v;if(B(_mz(_1po,0))!=B(_mz(_1oN,0))){return {_:0,a:_1pj,b:_1pk,c:_1pl,d:_1pm,e:_1pn,f:_1po,g:_1pp,h:_1pq,i:_1pr,j:_1ps,k:_1pt,l:_1pu,m:_1pv,n:_1pw,o:_1px,p:_1py,q:_1pz,r:_1pA,s:_1pB,t:_1pC,u:_1pD,v:_1pE};}else{return new F(function(){return _1oE(new T(function(){return E(_1oF)+1|0;}),_1oG,_1p5,_1pj,_1pk,_1pl,_1pm,_1pn,_1po,_1pp,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv,_1pw,_1px,_1py,_1pz,_1pA,_1pB,_1pC,_1pD,_1pE);});}}else{return new F(function(){return _1oE(new T(function(){return E(_1oF)+1|0;}),_1oG,_1p5,_1oI,_1oJ,_1oK,_1oL,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3);});}},_1pF=B(_mz(_1oG,0))-B(_mz(new T2(1,_1pa,_1pb),0))|0;if(_1pF>0){var _1pG=B(_1ov(_1pF,_1oG));}else{var _1pG=E(_1oG);}if(E(B(_1dN(_1pa,_1pb,_Vx)))==63){var _1pH=B(_TO(_1pa,_1pb));}else{var _1pH=new T2(1,_1pa,_1pb);}var _1pI=function(_1pJ){if(!B(_4A(_hd,_1oD,_1p7))){return new T2(0,_1p8,_1oF);}else{var _1pK=function(_1pL){while(1){var _1pM=B((function(_1pN){var _1pO=E(_1pN);if(!_1pO._){return true;}else{var _1pP=_1pO.b,_1pQ=E(_1pO.a);if(!_1pQ._){return E(_1oC);}else{switch(E(_1pQ.a)){case 99:var _1pR=E(_1oI);if(!E(_1pR.k)){return false;}else{var _1pS=function(_1pT){while(1){var _1pU=E(_1pT);if(!_1pU._){return true;}else{var _1pV=_1pU.b,_1pW=E(_1pU.a);if(!_1pW._){return E(_1oC);}else{if(E(_1pW.a)==115){var _1pX=B(_Gl(B(_sI(_1eu,_1pW.b))));if(!_1pX._){return E(_1es);}else{if(!E(_1pX.b)._){if(_1pR.f!=E(_1pX.a)){return false;}else{_1pT=_1pV;continue;}}else{return E(_1et);}}}else{_1pT=_1pV;continue;}}}}};return new F(function(){return _1pS(_1pP);});}break;case 115:var _1pY=E(_1oI),_1pZ=_1pY.f,_1q0=B(_Gl(B(_sI(_1eu,_1pQ.b))));if(!_1q0._){return E(_1es);}else{if(!E(_1q0.b)._){if(_1pZ!=E(_1q0.a)){return false;}else{var _1q1=function(_1q2){while(1){var _1q3=E(_1q2);if(!_1q3._){return true;}else{var _1q4=_1q3.b,_1q5=E(_1q3.a);if(!_1q5._){return E(_1oC);}else{switch(E(_1q5.a)){case 99:if(!E(_1pY.k)){return false;}else{_1q2=_1q4;continue;}break;case 115:var _1q6=B(_Gl(B(_sI(_1eu,_1q5.b))));if(!_1q6._){return E(_1es);}else{if(!E(_1q6.b)._){if(_1pZ!=E(_1q6.a)){return false;}else{_1q2=_1q4;continue;}}else{return E(_1et);}}break;default:_1q2=_1q4;continue;}}}}};return new F(function(){return _1q1(_1pP);});}}else{return E(_1et);}}break;default:_1pL=_1pP;return __continue;}}}})(_1pL));if(_1pM!=__continue){return _1pM;}}};return (!B(_1pK(_1pc)))?(!B(_qW(_1pH,_1oB)))?new T2(0,_S,_1oF):new T2(0,_1p8,_1oF):new T2(0,_1p8,_1oF);}};if(E(B(_1dV(_1pa,_1pb,_Vx)))==63){if(!B(_6f(_1pG,_S))){var _1q7=E(_1pG);if(!_1q7._){return E(_TT);}else{if(!B(_qW(_1pH,B(_TO(_1q7.a,_1q7.b))))){if(!B(_qW(_1pH,_1oB))){return new F(function(){return _1pd(_S,_1oF);});}else{return new F(function(){return _1pd(_1p8,_1oF);});}}else{var _1q8=B(_1pI(_));return new F(function(){return _1pd(_1q8.a,_1q8.b);});}}}else{if(!B(_qW(_1pH,_1pG))){if(!B(_qW(_1pH,_1oB))){return new F(function(){return _1pd(_S,_1oF);});}else{return new F(function(){return _1pd(_1p8,_1oF);});}}else{var _1q9=B(_1pI(_));return new F(function(){return _1pd(_1q9.a,_1q9.b);});}}}else{if(!B(_qW(_1pH,_1pG))){if(!B(_qW(_1pH,_1oB))){return new F(function(){return _1pd(_S,_1oF);});}else{return new F(function(){return _1pd(_1p8,_1oF);});}}else{var _1qa=B(_1pI(_));return new F(function(){return _1pd(_1qa.a,_1qa.b);});}}},_1qb=E(_1p7);if(!_1qb._){return E(_Vx);}else{var _1qc=_1qb.a,_1qd=E(_1qb.b);if(!_1qd._){return new F(function(){return _1p9(_1qc,_S,_S);});}else{var _1qe=E(_1qc),_1qf=new T(function(){var _1qg=B(_Hd(38,_1qd.a,_1qd.b));return new T2(0,_1qg.a,_1qg.b);});if(E(_1qe)==38){return E(_Vx);}else{return new F(function(){return _1p9(_1qe,new T(function(){return E(E(_1qf).a);}),new T(function(){return E(E(_1qf).b);}));});}}}}},_1qh="]",_1qi="}",_1qj=":",_1qk=",",_1ql=new T(function(){return eval("JSON.stringify");}),_1qm="false",_1qn="null",_1qo="[",_1qp="{",_1qq="\"",_1qr="true",_1qs=function(_1qt,_1qu){var _1qv=E(_1qu);switch(_1qv._){case 0:return new T2(0,new T(function(){return jsShow(_1qv.a);}),_1qt);case 1:return new T2(0,new T(function(){var _1qw=__app1(E(_1ql),_1qv.a);return String(_1qw);}),_1qt);case 2:return (!E(_1qv.a))?new T2(0,_1qm,_1qt):new T2(0,_1qr,_1qt);case 3:var _1qx=E(_1qv.a);if(!_1qx._){return new T2(0,_1qo,new T2(1,_1qh,_1qt));}else{var _1qy=new T(function(){var _1qz=new T(function(){var _1qA=function(_1qB){var _1qC=E(_1qB);if(!_1qC._){return E(new T2(1,_1qh,_1qt));}else{var _1qD=new T(function(){var _1qE=B(_1qs(new T(function(){return B(_1qA(_1qC.b));}),_1qC.a));return new T2(1,_1qE.a,_1qE.b);});return new T2(1,_1qk,_1qD);}};return B(_1qA(_1qx.b));}),_1qF=B(_1qs(_1qz,_1qx.a));return new T2(1,_1qF.a,_1qF.b);});return new T2(0,_1qo,_1qy);}break;case 4:var _1qG=E(_1qv.a);if(!_1qG._){return new T2(0,_1qp,new T2(1,_1qi,_1qt));}else{var _1qH=E(_1qG.a),_1qI=new T(function(){var _1qJ=new T(function(){var _1qK=function(_1qL){var _1qM=E(_1qL);if(!_1qM._){return E(new T2(1,_1qi,_1qt));}else{var _1qN=E(_1qM.a),_1qO=new T(function(){var _1qP=B(_1qs(new T(function(){return B(_1qK(_1qM.b));}),_1qN.b));return new T2(1,_1qP.a,_1qP.b);});return new T2(1,_1qk,new T2(1,_1qq,new T2(1,_1qN.a,new T2(1,_1qq,new T2(1,_1qj,_1qO)))));}};return B(_1qK(_1qG.b));}),_1qQ=B(_1qs(_1qJ,_1qH.b));return new T2(1,_1qQ.a,_1qQ.b);});return new T2(0,_1qp,new T2(1,new T(function(){var _1qR=__app1(E(_1ql),E(_1qH.a));return String(_1qR);}),new T2(1,_1qj,_1qI)));}break;default:return new T2(0,_1qn,_1qt);}},_1qS=new T(function(){return toJSStr(_S);}),_1qT=function(_1qU){var _1qV=B(_1qs(_S,_1qU)),_1qW=jsCat(new T2(1,_1qV.a,_1qV.b),E(_1qS));return E(_1qW);},_1qX=function(_1qY){var _1qZ=E(_1qY);if(!_1qZ._){return new T2(0,_S,_S);}else{var _1r0=E(_1qZ.a),_1r1=new T(function(){var _1r2=B(_1qX(_1qZ.b));return new T2(0,_1r2.a,_1r2.b);});return new T2(0,new T2(1,_1r0.a,new T(function(){return E(E(_1r1).a);})),new T2(1,_1r0.b,new T(function(){return E(E(_1r1).b);})));}},_1r3=new T(function(){return B(unCStr("Rk"));}),_1r4=function(_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri,_1rj,_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr){while(1){var _1rs=B((function(_1rt,_1ru,_1rv,_1rw,_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP){var _1rQ=E(_1rt);if(!_1rQ._){return {_:0,a:_1ru,b:_1rv,c:_1rw,d:_1rx,e:_1ry,f:_1rz,g:_1rA,h:_1rB,i:_1rC,j:_1rD,k:_1rE,l:_1rF,m:_1rG,n:_1rH,o:_1rI,p:_1rJ,q:_1rK,r:_1rL,s:_1rM,t:_1rN,u:_1rO,v:_1rP};}else{var _1rR=_1rQ.a,_1rS=B(_Ue(B(unAppCStr("e.e",new T2(1,_1rR,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1rR,_1r3)));})))),_1ru,_1rv,_1rw,_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP));_1r5=_1rQ.b;_1r6=_1rS.a;_1r7=_1rS.b;_1r8=_1rS.c;_1r9=_1rS.d;_1ra=_1rS.e;_1rb=_1rS.f;_1rc=_1rS.g;_1rd=_1rS.h;_1re=_1rS.i;_1rf=_1rS.j;_1rg=_1rS.k;_1rh=_1rS.l;_1ri=_1rS.m;_1rj=_1rS.n;_1rk=_1rS.o;_1rl=_1rS.p;_1rm=_1rS.q;_1rn=_1rS.r;_1ro=_1rS.s;_1rp=_1rS.t;_1rq=_1rS.u;_1rr=_1rS.v;return __continue;}})(_1r5,_1r6,_1r7,_1r8,_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri,_1rj,_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr));if(_1rs!=__continue){return _1rs;}}},_1rT=function(_1rU){var _1rV=E(_1rU);switch(_1rV){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1rV>>>0>1114111){return new F(function(){return _wO(_1rV);});}else{return _1rV;}}},_1rW=function(_1rX,_1rY,_1rZ){while(1){var _1s0=E(_1rY);if(!_1s0._){return (E(_1rZ)._==0)?true:false;}else{var _1s1=E(_1rZ);if(!_1s1._){return false;}else{if(!B(A3(_4y,_1rX,_1s0.a,_1s1.a))){return false;}else{_1rY=_1s0.b;_1rZ=_1s1.b;continue;}}}}},_1s2=function(_1s3,_1s4){return (!B(_1rW(_rt,_1s3,_1s4)))?true:false;},_1s5=function(_1s6,_1s7){return new F(function(){return _1rW(_rt,_1s6,_1s7);});},_1s8=new T2(0,_1s5,_1s2),_1s9=function(_1sa){var _1sb=E(_1sa);if(!_1sb._){return new T2(0,_S,_S);}else{var _1sc=E(_1sb.a),_1sd=new T(function(){var _1se=B(_1s9(_1sb.b));return new T2(0,_1se.a,_1se.b);});return new T2(0,new T2(1,_1sc.a,new T(function(){return E(E(_1sd).a);})),new T2(1,_1sc.b,new T(function(){return E(E(_1sd).b);})));}},_1sf=function(_1sg,_1sh){while(1){var _1si=E(_1sh);if(!_1si._){return __Z;}else{var _1sj=_1si.b,_1sk=E(_1sg);if(_1sk==1){return E(_1sj);}else{_1sg=_1sk-1|0;_1sh=_1sj;continue;}}}},_1sl=function(_1sm,_1sn){while(1){var _1so=E(_1sn);if(!_1so._){return __Z;}else{var _1sp=_1so.b,_1sq=E(_1sm);if(_1sq==1){return E(_1sp);}else{_1sm=_1sq-1|0;_1sn=_1sp;continue;}}}},_1sr=function(_1ss){return new F(function(){return _Gs(_1ss,_S);});},_1st=function(_1su,_1sv,_1sw,_1sx){var _1sy=new T(function(){return B(_MU(_hd,_1sv,_1sw));}),_1sz=new T(function(){var _1sA=E(_1sy),_1sB=new T(function(){var _1sC=_1sA+1|0;if(_1sC>0){return B(_1sl(_1sC,_1sw));}else{return E(_1sw);}});if(0>=_1sA){return E(_1sB);}else{var _1sD=function(_1sE,_1sF){var _1sG=E(_1sE);if(!_1sG._){return E(_1sB);}else{var _1sH=_1sG.a,_1sI=E(_1sF);return (_1sI==1)?new T2(1,_1sH,_1sB):new T2(1,_1sH,new T(function(){return B(_1sD(_1sG.b,_1sI-1|0));}));}};return B(_1sD(_1sw,_1sA));}}),_1sJ=new T(function(){var _1sK=E(_1sy),_1sL=new T(function(){if(E(_1sv)==94){return B(A2(_1su,new T(function(){return B(_6X(_1sx,_1sK+1|0));}),new T(function(){return B(_6X(_1sx,_1sK));})));}else{return B(A2(_1su,new T(function(){return B(_6X(_1sx,_1sK));}),new T(function(){return B(_6X(_1sx,_1sK+1|0));})));}}),_1sM=new T2(1,_1sL,new T(function(){var _1sN=_1sK+2|0;if(_1sN>0){return B(_1sf(_1sN,_1sx));}else{return E(_1sx);}}));if(0>=_1sK){return E(_1sM);}else{var _1sO=function(_1sP,_1sQ){var _1sR=E(_1sP);if(!_1sR._){return E(_1sM);}else{var _1sS=_1sR.a,_1sT=E(_1sQ);return (_1sT==1)?new T2(1,_1sS,_1sM):new T2(1,_1sS,new T(function(){return B(_1sO(_1sR.b,_1sT-1|0));}));}};return B(_1sO(_1sx,_1sK));}});return (E(_1sv)==94)?new T2(0,new T(function(){return B(_1sr(_1sz));}),new T(function(){return B(_1sr(_1sJ));})):new T2(0,_1sz,_1sJ);},_1sU=new T(function(){return B(_ct(_oS,_oR));}),_1sV=function(_1sW,_1sX,_1sY){while(1){if(!E(_1sU)){if(!B(_ct(B(_180(_1sX,_oS)),_oR))){if(!B(_ct(_1sX,_b1))){var _1sZ=B(_ol(_1sW,_1sW)),_1t0=B(_17L(B(_eU(_1sX,_b1)),_oS)),_1t1=B(_ol(_1sW,_1sY));_1sW=_1sZ;_1sX=_1t0;_1sY=_1t1;continue;}else{return new F(function(){return _ol(_1sW,_1sY);});}}else{var _1sZ=B(_ol(_1sW,_1sW)),_1t0=B(_17L(_1sX,_oS));_1sW=_1sZ;_1sX=_1t0;continue;}}else{return E(_a0);}}},_1t2=function(_1t3,_1t4){while(1){if(!E(_1sU)){if(!B(_ct(B(_180(_1t4,_oS)),_oR))){if(!B(_ct(_1t4,_b1))){return new F(function(){return _1sV(B(_ol(_1t3,_1t3)),B(_17L(B(_eU(_1t4,_b1)),_oS)),_1t3);});}else{return E(_1t3);}}else{var _1t5=B(_ol(_1t3,_1t3)),_1t6=B(_17L(_1t4,_oS));_1t3=_1t5;_1t4=_1t6;continue;}}else{return E(_a0);}}},_1t7=function(_1t8,_1t9){if(!B(_dd(_1t9,_oR))){if(!B(_ct(_1t9,_oR))){return new F(function(){return _1t2(_1t8,_1t9);});}else{return E(_b1);}}else{return E(_px);}},_1ta=94,_1tb=45,_1tc=43,_1td=42,_1te=function(_1tf,_1tg){while(1){var _1th=B((function(_1ti,_1tj){var _1tk=E(_1tj);if(!_1tk._){return __Z;}else{if((B(_mz(_1ti,0))+1|0)==B(_mz(_1tk,0))){if(!B(_4A(_hd,_1ta,_1ti))){if(!B(_4A(_hd,_1td,_1ti))){if(!B(_4A(_hd,_1tc,_1ti))){if(!B(_4A(_hd,_1tb,_1ti))){return E(_1tk);}else{var _1tl=B(_1st(_eU,45,_1ti,_1tk));_1tf=_1tl.a;_1tg=_1tl.b;return __continue;}}else{var _1tm=B(_1st(_cB,43,_1ti,_1tk));_1tf=_1tm.a;_1tg=_1tm.b;return __continue;}}else{var _1tn=B(_1st(_ol,42,_1ti,_1tk));_1tf=_1tn.a;_1tg=_1tn.b;return __continue;}}else{var _1to=B(_1st(_1t7,94,new T(function(){return B(_1sr(_1ti));}),new T(function(){return B(_Gs(_1tk,_S));})));_1tf=_1to.a;_1tg=_1to.b;return __continue;}}else{return __Z;}}})(_1tf,_1tg));if(_1th!=__continue){return _1th;}}},_1tp=function(_1tq){var _1tr=E(_1tq);if(!_1tr._){return new T2(0,_S,_S);}else{var _1ts=E(_1tr.a),_1tt=new T(function(){var _1tu=B(_1tp(_1tr.b));return new T2(0,_1tu.a,_1tu.b);});return new T2(0,new T2(1,_1ts.a,new T(function(){return E(E(_1tt).a);})),new T2(1,_1ts.b,new T(function(){return E(E(_1tt).b);})));}},_1tv=new T(function(){return B(unCStr("0123456789+-"));}),_1tw=function(_1tx){while(1){var _1ty=E(_1tx);if(!_1ty._){return true;}else{if(!B(_4A(_hd,_1ty.a,_1tv))){return false;}else{_1tx=_1ty.b;continue;}}}},_1tz=new T(function(){return B(err(_sz));}),_1tA=new T(function(){return B(err(_sD));}),_1tB=function(_1tC,_1tD){var _1tE=function(_1tF,_1tG){var _1tH=function(_1tI){return new F(function(){return A1(_1tG,new T(function(){return B(_fz(_1tI));}));});},_1tJ=new T(function(){return B(_Dh(function(_1tK){return new F(function(){return A3(_1tC,_1tK,_1tF,_1tH);});}));}),_1tL=function(_1tM){return E(_1tJ);},_1tN=function(_1tO){return new F(function(){return A2(_BY,_1tO,_1tL);});},_1tP=new T(function(){return B(_Dh(function(_1tQ){var _1tR=E(_1tQ);if(_1tR._==4){var _1tS=E(_1tR.a);if(!_1tS._){return new F(function(){return A3(_1tC,_1tR,_1tF,_1tG);});}else{if(E(_1tS.a)==45){if(!E(_1tS.b)._){return E(new T1(1,_1tN));}else{return new F(function(){return A3(_1tC,_1tR,_1tF,_1tG);});}}else{return new F(function(){return A3(_1tC,_1tR,_1tF,_1tG);});}}}else{return new F(function(){return A3(_1tC,_1tR,_1tF,_1tG);});}}));}),_1tT=function(_1tU){return E(_1tP);};return new T1(1,function(_1tV){return new F(function(){return A2(_BY,_1tV,_1tT);});});};return new F(function(){return _E8(_1tE,_1tD);});},_1tW=function(_1tX){var _1tY=E(_1tX);if(_1tY._==5){var _1tZ=B(_G4(_1tY.a));return (_1tZ._==0)?E(_G9):function(_1u0,_1u1){return new F(function(){return A1(_1u1,_1tZ.a);});};}else{return E(_G9);}},_1u2=new T(function(){return B(A3(_1tB,_1tW,_DO,_FB));}),_1u3=function(_1u4,_1u5){var _1u6=E(_1u5);if(!_1u6._){return __Z;}else{var _1u7=_1u6.a,_1u8=_1u6.b,_1u9=function(_1ua){var _1ub=B(_1tp(_1u4)),_1uc=_1ub.a;return (!B(_4A(_qk,_1u7,_1uc)))?__Z:new T2(1,new T(function(){return B(_6X(_1ub.b,B(_MU(_qk,_1u7,_1uc))));}),new T(function(){return B(_1u3(_1u4,_1u8));}));};if(!B(_6f(_1u7,_S))){if(!B(_1tw(_1u7))){return new F(function(){return _1u9(_);});}else{return new T2(1,new T(function(){var _1ud=B(_Gl(B(_sI(_1u2,_1u7))));if(!_1ud._){return E(_1tz);}else{if(!E(_1ud.b)._){return E(_1ud.a);}else{return E(_1tA);}}}),new T(function(){return B(_1u3(_1u4,_1u8));}));}}else{return new F(function(){return _1u9(_);});}}},_1ue=new T(function(){return B(unCStr("+-*^"));}),_1uf=new T(function(){return B(unCStr("0123456789"));}),_1ug=new T(function(){return B(_Lv("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1uh=new T2(1,_S,_S),_1ui=function(_1uj){var _1uk=E(_1uj);if(!_1uk._){return new T2(0,_1uh,_S);}else{var _1ul=_1uk.a,_1um=new T(function(){var _1un=B(_1ui(_1uk.b)),_1uo=E(_1un.a);if(!_1uo._){return E(_1ug);}else{return new T3(0,_1uo.a,_1uo.b,_1un.b);}});return (!B(_4A(_hd,_1ul,_1uf)))?(!B(_4A(_hd,_1ul,_1ue)))?new T2(0,new T2(1,new T2(1,_1ul,new T(function(){return E(E(_1um).a);})),new T(function(){return E(E(_1um).b);})),new T(function(){return E(E(_1um).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1um).a);}),new T(function(){return E(E(_1um).b);}))),new T2(1,_1ul,new T(function(){return E(E(_1um).c);}))):new T2(0,new T2(1,new T2(1,_1ul,new T(function(){return E(E(_1um).a);})),new T(function(){return E(E(_1um).b);})),new T(function(){return E(E(_1um).c);}));}},_1up=function(_1uq,_1ur){var _1us=new T(function(){var _1ut=B(_1ui(_1ur)),_1uu=E(_1ut.a);if(!_1uu._){return E(_1ug);}else{return new T3(0,_1uu.a,_1uu.b,_1ut.b);}});return (!B(_4A(_hd,_1uq,_1uf)))?(!B(_4A(_hd,_1uq,_1ue)))?new T2(0,new T2(1,new T2(1,_1uq,new T(function(){return E(E(_1us).a);})),new T(function(){return E(E(_1us).b);})),new T(function(){return E(E(_1us).c);})):new T2(0,new T2(1,_S,new T2(1,new T(function(){return E(E(_1us).a);}),new T(function(){return E(E(_1us).b);}))),new T2(1,_1uq,new T(function(){return E(E(_1us).c);}))):new T2(0,new T2(1,new T2(1,_1uq,new T(function(){return E(E(_1us).a);})),new T(function(){return E(E(_1us).b);})),new T(function(){return E(E(_1us).c);}));},_1uv=function(_1uw,_1ux){while(1){var _1uy=E(_1uw);if(!_1uy._){return E(_1ux);}else{_1uw=_1uy.b;_1ux=_1uy.a;continue;}}},_1uz=function(_1uA,_1uB,_1uC){return new F(function(){return _1uv(_1uB,_1uA);});},_1uD=function(_1uE,_1uF){var _1uG=E(_1uF);if(!_1uG._){return __Z;}else{var _1uH=B(_1up(_1uG.a,_1uG.b)),_1uI=B(_1te(_1uH.b,B(_1u3(_1uE,_1uH.a))));if(!_1uI._){return E(_1uG);}else{return new F(function(){return _1a4(0,B(_1uz(_1uI.a,_1uI.b,_Vx)),_S);});}}},_1uJ=function(_1uK,_1uL){var _1uM=function(_1uN,_1uO){while(1){var _1uP=B((function(_1uQ,_1uR){var _1uS=E(_1uR);if(!_1uS._){return (!B(_qW(_1uQ,_S)))?new T2(0,_wE,_1uQ):new T2(0,_wD,_S);}else{var _1uT=_1uS.b,_1uU=B(_1s9(_1uS.a)).a;if(!B(_4A(_hd,_1fW,_1uU))){var _1uV=_1uQ;_1uN=_1uV;_1uO=_1uT;return __continue;}else{var _1uW=B(_1gs(_1uU)),_1uX=_1uW.a,_1uY=_1uW.b;if(!B(_6f(_1uY,_S))){if(!B(_qW(B(_1uD(_1uK,_1uX)),B(_1uD(_1uK,_1uY))))){return new T2(0,_wD,_S);}else{var _1uZ=new T(function(){if(!B(_qW(_1uQ,_S))){return B(_q(_1uQ,new T(function(){return B(unAppCStr(" ",_1uX));},1)));}else{return E(_1uX);}});_1uN=_1uZ;_1uO=_1uT;return __continue;}}else{return new T2(0,_wD,_S);}}}})(_1uN,_1uO));if(_1uP!=__continue){return _1uP;}}};return new F(function(){return _1uM(_S,_1uL);});},_1v0=function(_1v1,_1v2){var _1v3=new T(function(){var _1v4=B(_Gl(B(_sI(_19U,new T(function(){return B(_pU(3,B(_A(0,imul(E(_1v2),E(_1v1)-1|0)|0,_S))));})))));if(!_1v4._){return E(_19T);}else{if(!E(_1v4.b)._){return E(_1v4.a);}else{return E(_19S);}}});return new T2(0,new T(function(){return B(_aB(_1v3,_1v1));}),_1v3);},_1v5=function(_1v6,_1v7){while(1){var _1v8=E(_1v7);if(!_1v8._){return __Z;}else{var _1v9=_1v8.b,_1va=E(_1v6);if(_1va==1){return E(_1v9);}else{_1v6=_1va-1|0;_1v7=_1v9;continue;}}}},_1vb=function(_1vc,_1vd){while(1){var _1ve=E(_1vd);if(!_1ve._){return __Z;}else{var _1vf=_1ve.b,_1vg=E(_1vc);if(_1vg==1){return E(_1vf);}else{_1vc=_1vg-1|0;_1vd=_1vf;continue;}}}},_1vh=64,_1vi=new T2(1,_1vh,_S),_1vj=function(_1vk,_1vl,_1vm,_1vn){return (!B(_qW(_1vk,_1vm)))?true:(!B(_ct(_1vl,_1vn)))?true:false;},_1vo=function(_1vp,_1vq){var _1vr=E(_1vp),_1vs=E(_1vq);return new F(function(){return _1vj(_1vr.a,_1vr.b,_1vs.a,_1vs.b);});},_1vt=function(_1vu,_1vv,_1vw,_1vx){if(!B(_qW(_1vu,_1vw))){return false;}else{return new F(function(){return _ct(_1vv,_1vx);});}},_1vy=function(_1vz,_1vA){var _1vB=E(_1vz),_1vC=E(_1vA);return new F(function(){return _1vt(_1vB.a,_1vB.b,_1vC.a,_1vC.b);});},_1vD=new T2(0,_1vy,_1vo),_1vE=function(_1vF){var _1vG=E(_1vF);if(!_1vG._){return new T2(0,_S,_S);}else{var _1vH=E(_1vG.a),_1vI=new T(function(){var _1vJ=B(_1vE(_1vG.b));return new T2(0,_1vJ.a,_1vJ.b);});return new T2(0,new T2(1,_1vH.a,new T(function(){return E(E(_1vI).a);})),new T2(1,_1vH.b,new T(function(){return E(E(_1vI).b);})));}},_1vK=function(_1vL){var _1vM=E(_1vL);if(!_1vM._){return new T2(0,_S,_S);}else{var _1vN=E(_1vM.a),_1vO=new T(function(){var _1vP=B(_1vK(_1vM.b));return new T2(0,_1vP.a,_1vP.b);});return new T2(0,new T2(1,_1vN.a,new T(function(){return E(E(_1vO).a);})),new T2(1,_1vN.b,new T(function(){return E(E(_1vO).b);})));}},_1vQ=function(_1vR){var _1vS=E(_1vR);if(!_1vS._){return new T2(0,_S,_S);}else{var _1vT=E(_1vS.a),_1vU=new T(function(){var _1vV=B(_1vQ(_1vS.b));return new T2(0,_1vV.a,_1vV.b);});return new T2(0,new T2(1,_1vT.a,new T(function(){return E(E(_1vU).a);})),new T2(1,_1vT.b,new T(function(){return E(E(_1vU).b);})));}},_1vW=function(_1vX,_1vY){return (_1vX<=_1vY)?new T2(1,_1vX,new T(function(){return B(_1vW(_1vX+1|0,_1vY));})):__Z;},_1vZ=new T(function(){return B(_1vW(65,90));}),_1w0=function(_1w1){return (_1w1<=122)?new T2(1,_1w1,new T(function(){return B(_1w0(_1w1+1|0));})):E(_1vZ);},_1w2=new T(function(){return B(_1w0(97));}),_1w3=function(_1w4){while(1){var _1w5=E(_1w4);if(!_1w5._){return true;}else{if(!B(_4A(_hd,_1w5.a,_1w2))){return false;}else{_1w4=_1w5.b;continue;}}}},_1w6=new T2(0,_S,_S),_1w7=new T(function(){return B(err(_sz));}),_1w8=new T(function(){return B(err(_sD));}),_1w9=new T(function(){return B(A3(_1tB,_1tW,_DO,_FB));}),_1wa=function(_1wb,_1wc,_1wd){while(1){var _1we=B((function(_1wf,_1wg,_1wh){var _1wi=E(_1wh);if(!_1wi._){return __Z;}else{var _1wj=_1wi.b,_1wk=B(_1vK(_1wg)),_1wl=_1wk.a,_1wm=B(_1vE(_1wl)),_1wn=_1wm.a,_1wo=new T(function(){return E(B(_1vQ(_1wi.a)).a);}),_1wp=new T(function(){return B(_4A(_hd,_1fW,_1wo));}),_1wq=new T(function(){if(!E(_1wp)){return E(_1w6);}else{var _1wr=B(_1gs(_1wo));return new T2(0,_1wr.a,_1wr.b);}}),_1ws=new T(function(){return E(E(_1wq).a);}),_1wt=new T(function(){return B(_MU(_qk,_1ws,_1wn));}),_1wu=new T(function(){var _1wv=function(_){var _1ww=B(_mz(_1wg,0))-1|0,_1wx=function(_1wy){if(_1wy>=0){var _1wz=newArr(_1wy,_1b1),_1wA=_1wz,_1wB=E(_1wy);if(!_1wB){return new T4(0,E(_1ev),E(_1ww),0,_1wA);}else{var _1wC=function(_1wD,_1wE,_){while(1){var _1wF=E(_1wD);if(!_1wF._){return E(_);}else{var _=_1wA[_1wE]=_1wF.a;if(_1wE!=(_1wB-1|0)){var _1wG=_1wE+1|0;_1wD=_1wF.b;_1wE=_1wG;continue;}else{return E(_);}}}},_=B(_1wC(_1wk.b,0,_));return new T4(0,E(_1ev),E(_1ww),_1wB,_1wA);}}else{return E(_1bV);}};if(0>_1ww){return new F(function(){return _1wx(0);});}else{return new F(function(){return _1wx(_1ww+1|0);});}};return B(_1bW(_1wv));});if(!B(_4A(_qk,_1ws,_1wn))){var _1wH=false;}else{var _1wI=E(_1wu),_1wJ=E(_1wI.a),_1wK=E(_1wI.b),_1wL=E(_1wt);if(_1wJ>_1wL){var _1wM=B(_1kx(_1wL,_1wJ,_1wK));}else{if(_1wL>_1wK){var _1wN=B(_1kx(_1wL,_1wJ,_1wK));}else{var _1wN=E(_1wI.d[_1wL-_1wJ|0])==E(_1wf);}var _1wM=_1wN;}var _1wH=_1wM;}var _1wO=new T(function(){return E(E(_1wq).b);}),_1wP=new T(function(){return B(_MU(_qk,_1wO,_1wn));}),_1wQ=new T(function(){if(!B(_4A(_qk,_1wO,_1wn))){return false;}else{var _1wR=E(_1wu),_1wS=E(_1wR.a),_1wT=E(_1wR.b),_1wU=E(_1wP);if(_1wS>_1wU){return B(_1kx(_1wU,_1wS,_1wT));}else{if(_1wU>_1wT){return B(_1kx(_1wU,_1wS,_1wT));}else{return E(_1wR.d[_1wU-_1wS|0])==E(_1wf);}}}}),_1wV=new T(function(){var _1wW=function(_){var _1wX=B(_mz(_1wl,0))-1|0,_1wY=function(_1wZ){if(_1wZ>=0){var _1x0=newArr(_1wZ,_1b1),_1x1=_1x0,_1x2=E(_1wZ);if(!_1x2){return new T4(0,E(_1ev),E(_1wX),0,_1x1);}else{var _1x3=function(_1x4,_1x5,_){while(1){var _1x6=E(_1x4);if(!_1x6._){return E(_);}else{var _=_1x1[_1x5]=_1x6.a;if(_1x5!=(_1x2-1|0)){var _1x7=_1x5+1|0;_1x4=_1x6.b;_1x5=_1x7;continue;}else{return E(_);}}}},_=B(_1x3(_1wm.b,0,_));return new T4(0,E(_1ev),E(_1wX),_1x2,_1x1);}}else{return E(_1bV);}};if(0>_1wX){return new F(function(){return _1wY(0);});}else{return new F(function(){return _1wY(_1wX+1|0);});}};return B(_1bW(_1wW));}),_1x8=function(_1x9){var _1xa=function(_1xb){return (!E(_1wH))?__Z:(!E(_1wQ))?__Z:new T2(1,new T2(0,_1ws,new T(function(){var _1xc=E(_1wV),_1xd=E(_1xc.a),_1xe=E(_1xc.b),_1xf=E(_1wt);if(_1xd>_1xf){return B(_1kx(_1xf,_1xd,_1xe));}else{if(_1xf>_1xe){return B(_1kx(_1xf,_1xd,_1xe));}else{return E(_1xc.d[_1xf-_1xd|0]);}}})),new T2(1,new T2(0,_1wO,new T(function(){var _1xg=E(_1wV),_1xh=E(_1xg.a),_1xi=E(_1xg.b),_1xj=E(_1wP);if(_1xh>_1xj){return B(_1kx(_1xj,_1xh,_1xi));}else{if(_1xj>_1xi){return B(_1kx(_1xj,_1xh,_1xi));}else{return E(_1xg.d[_1xj-_1xh|0]);}}})),_S));};if(!E(_1wH)){if(!E(_1wQ)){return new F(function(){return _1xa(_);});}else{return new T2(1,new T2(0,_1wO,new T(function(){var _1xk=E(_1wV),_1xl=E(_1xk.a),_1xm=E(_1xk.b),_1xn=E(_1wP);if(_1xl>_1xn){return B(_1kx(_1xn,_1xl,_1xm));}else{if(_1xn>_1xm){return B(_1kx(_1xn,_1xl,_1xm));}else{return E(_1xk.d[_1xn-_1xl|0]);}}})),_S);}}else{return new F(function(){return _1xa(_);});}};if(!E(_1wH)){var _1xo=B(_1x8(_));}else{if(!E(_1wQ)){var _1xp=new T2(1,new T2(0,_1ws,new T(function(){var _1xq=E(_1wV),_1xr=E(_1xq.a),_1xs=E(_1xq.b),_1xt=E(_1wt);if(_1xr>_1xt){return B(_1kx(_1xt,_1xr,_1xs));}else{if(_1xt>_1xs){return B(_1kx(_1xt,_1xr,_1xs));}else{return E(_1xq.d[_1xt-_1xr|0]);}}})),_S);}else{var _1xp=B(_1x8(_));}var _1xo=_1xp;}if(!B(_1rW(_1vD,_1xo,_S))){return new F(function(){return _q(_1xo,new T(function(){return B(_1wa(_1wf,_1wg,_1wj));},1));});}else{if(!E(_1wp)){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{if(!B(_1w3(_1ws))){if(!B(_1w3(_1wO))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{if(!E(_1wH)){if(!E(_1wQ)){if(!B(_6f(_1ws,_S))){if(!B(_1tw(_1ws))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{return new T2(1,new T2(0,_1wO,new T(function(){var _1xw=B(_Gl(B(_sI(_1w9,_1ws))));if(!_1xw._){return E(_1w7);}else{if(!E(_1xw.b)._){return E(_1xw.a);}else{return E(_1w8);}}})),new T(function(){return B(_1wa(_1wf,_1wg,_1wj));}));}}else{var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}else{var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}else{var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}}else{if(!E(_1wH)){if(!E(_1wQ)){if(!B(_6f(_1wO,_S))){if(!B(_1tw(_1wO))){if(!B(_1w3(_1wO))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{if(!B(_6f(_1ws,_S))){if(!B(_1tw(_1ws))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{return new T2(1,new T2(0,_1wO,new T(function(){var _1xx=B(_Gl(B(_sI(_1w9,_1ws))));if(!_1xx._){return E(_1w7);}else{if(!E(_1xx.b)._){return E(_1xx.a);}else{return E(_1w8);}}})),new T(function(){return B(_1wa(_1wf,_1wg,_1wj));}));}}else{var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}}else{return new T2(1,new T2(0,_1ws,new T(function(){var _1xy=B(_Gl(B(_sI(_1w9,_1wO))));if(!_1xy._){return E(_1w7);}else{if(!E(_1xy.b)._){return E(_1xy.a);}else{return E(_1w8);}}})),new T(function(){return B(_1wa(_1wf,_1wg,_1wj));}));}}else{if(!B(_1w3(_1wO))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{if(!B(_6f(_1ws,_S))){if(!B(_1tw(_1ws))){var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}else{return new T2(1,new T2(0,_1wO,new T(function(){var _1xz=B(_Gl(B(_sI(_1w9,_1ws))));if(!_1xz._){return E(_1w7);}else{if(!E(_1xz.b)._){return E(_1xz.a);}else{return E(_1w8);}}})),new T(function(){return B(_1wa(_1wf,_1wg,_1wj));}));}}else{var _1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}}}else{var _1xA=B(_1w3(_1wO)),_1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}else{var _1xB=B(_1w3(_1wO)),_1xu=_1wf,_1xv=_1wg;_1wb=_1xu;_1wc=_1xv;_1wd=_1wj;return __continue;}}}}}})(_1wb,_1wc,_1wd));if(_1we!=__continue){return _1we;}}},_1xC=102,_1xD=101,_1xE=new T(function(){return B(unCStr("=="));}),_1xF=new T(function(){return B(_ed("Action.hs:(103,17)-(107,70)|case"));}),_1xG=new T(function(){return B(_ed("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1xH=5,_1xI=117,_1xJ=98,_1xK=110,_1xL=118,_1xM=function(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,_1xT,_1xU,_1xV,_1xW,_1xX,_1xY,_1xZ,_1y0){var _1y1=B(_6X(B(_6X(_1xR,_1xO)),_1xN)),_1y2=_1y1.a,_1y3=_1y1.b;if(E(_1xU)==32){if(!B(_4A(_hd,_1y2,_1vi))){var _1y4=false;}else{switch(E(_1y3)){case 0:var _1y5=true;break;case 1:var _1y5=false;break;case 2:var _1y5=false;break;case 3:var _1y5=false;break;case 4:var _1y5=false;break;case 5:var _1y5=false;break;case 6:var _1y5=false;break;case 7:var _1y5=false;break;default:var _1y5=false;}var _1y4=_1y5;}var _1y6=_1y4;}else{var _1y6=false;}if(E(_1xU)==32){if(E(_1y2)==32){var _1y7=false;}else{switch(E(_1y3)){case 0:if(!E(_1y6)){var _1y8=true;}else{var _1y8=false;}var _1y9=_1y8;break;case 1:var _1y9=false;break;case 2:var _1y9=false;break;case 3:var _1y9=false;break;case 4:var _1y9=false;break;case 5:var _1y9=false;break;case 6:var _1y9=false;break;case 7:var _1y9=false;break;default:if(!E(_1y6)){var _1ya=true;}else{var _1ya=false;}var _1y9=_1ya;}var _1y7=_1y9;}var _1yb=_1y7;}else{var _1yb=false;}var _1yc=new T(function(){return B(_L4(_1xN,_1xO,new T(function(){if(!E(_1yb)){if(!E(_1y6)){return E(_1y2);}else{return _1xT;}}else{return E(_Xs);}}),_1y3,_1xR));});switch(E(_1y3)){case 3:var _1yd=true;break;case 4:if(E(_1xU)==32){var _1ye=true;}else{var _1ye=false;}var _1yd=_1ye;break;default:var _1yd=false;}if(!E(_1yd)){var _1yf=E(_1yc);}else{var _1yg=E(_1xP),_1yh=new T(function(){return B(_6X(_1yc,_1xO));}),_1yi=function(_1yj,_1yk){var _1yl=E(_1yj);if(_1yl==( -1)){return E(_1yc);}else{var _1ym=new T(function(){return B(_L4(_1xN,_1xO,_Xs,_Ej,_1yc));}),_1yn=E(_1yk);if(_1yn==( -1)){var _1yo=__Z;}else{var _1yo=B(_6X(_1ym,_1yn));}if(E(B(_6X(_1yo,_1yl)).a)==32){var _1yp=new T(function(){var _1yq=new T(function(){return B(_6X(_1yh,_1xN));}),_1yr=new T2(1,new T2(0,new T(function(){return E(E(_1yq).a);}),new T(function(){return E(E(_1yq).b);})),new T(function(){var _1ys=_1yl+1|0;if(_1ys>0){return B(_1vb(_1ys,_1yo));}else{return E(_1yo);}}));if(0>=_1yl){return E(_1yr);}else{var _1yt=function(_1yu,_1yv){var _1yw=E(_1yu);if(!_1yw._){return E(_1yr);}else{var _1yx=_1yw.a,_1yy=E(_1yv);return (_1yy==1)?new T2(1,_1yx,_1yr):new T2(1,_1yx,new T(function(){return B(_1yt(_1yw.b,_1yy-1|0));}));}};return B(_1yt(_1yo,_1yl));}}),_1yz=new T2(1,_1yp,new T(function(){var _1yA=_1yk+1|0;if(_1yA>0){return B(_1v5(_1yA,_1ym));}else{return E(_1ym);}}));if(0>=_1yk){return E(_1yz);}else{var _1yB=function(_1yC,_1yD){var _1yE=E(_1yC);if(!_1yE._){return E(_1yz);}else{var _1yF=_1yE.a,_1yG=E(_1yD);return (_1yG==1)?new T2(1,_1yF,_1yz):new T2(1,_1yF,new T(function(){return B(_1yB(_1yE.b,_1yG-1|0));}));}};return new F(function(){return _1yB(_1ym,_1yk);});}}else{return E(_1yc);}}};if(_1xN<=_1yg){if(_1yg<=_1xN){var _1yH=E(_1xQ);if(_1xO<=_1yH){if(_1yH<=_1xO){var _1yI=E(_1xF);}else{var _1yJ=E(_1xO);if(!_1yJ){var _1yK=B(_1yi( -1, -1));}else{var _1yK=B(_1yi(_1xN,_1yJ-1|0));}var _1yI=_1yK;}var _1yL=_1yI;}else{if(_1xO!=(B(_mz(_1yc,0))-1|0)){var _1yM=B(_1yi(_1xN,_1xO+1|0));}else{var _1yM=B(_1yi( -1, -1));}var _1yL=_1yM;}var _1yN=_1yL;}else{var _1yO=E(_1xN);if(!_1yO){var _1yP=B(_1yi( -1, -1));}else{var _1yP=B(_1yi(_1yO-1|0,_1xO));}var _1yN=_1yP;}var _1yQ=_1yN;}else{if(_1xN!=(B(_mz(_1yh,0))-1|0)){var _1yR=B(_1yi(_1xN+1|0,_1xO));}else{var _1yR=B(_1yi( -1, -1));}var _1yQ=_1yR;}var _1yf=_1yQ;}if(!E(_1xZ)){var _1yS=E(_1yf);}else{var _1yT=new T(function(){var _1yU=E(_1yf);if(!_1yU._){return E(_nn);}else{return B(_mz(_1yU.a,0));}}),_1yV=new T(function(){return B(_mz(_1yf,0));}),_1yW=function(_1yX,_1yY,_1yZ,_1z0,_1z1,_1z2,_1z3){while(1){var _1z4=B((function(_1z5,_1z6,_1z7,_1z8,_1z9,_1za,_1zb){var _1zc=E(_1zb);if(!_1zc._){return E(_1z8);}else{var _1zd=_1zc.b,_1ze=E(_1zc.a);if(!_1ze._){return E(_1xG);}else{var _1zf=_1ze.b,_1zg=E(_1ze.a);if(E(_1zg.b)==5){var _1zh=new T(function(){var _1zi=B(_1v0(_1xH,_1z5));return new T2(0,_1zi.a,_1zi.b);}),_1zj=new T(function(){var _1zk=function(_1zl,_1zm){var _1zn=function(_1zo){return new F(function(){return _L4(_1z6,_1z7,_Xs,_Ej,new T(function(){return B(_L4(_1zl,_1zm,_1zg.a,_F8,_1z8));}));});};if(_1zl!=_1z6){return new F(function(){return _1zn(_);});}else{if(_1zm!=_1z7){return new F(function(){return _1zn(_);});}else{return E(_1z8);}}};switch(E(E(_1zh).a)){case 1:var _1zp=_1z6-1|0;if(_1zp<0){return B(_1zk(_1z6,_1z7));}else{if(_1zp>=E(_1yT)){return B(_1zk(_1z6,_1z7));}else{if(_1z7<0){return B(_1zk(_1z6,_1z7));}else{if(_1z7>=E(_1yV)){return B(_1zk(_1z6,_1z7));}else{if(_1zp!=_1z9){if(E(B(_6X(B(_6X(_1z8,_1z7)),_1zp)).a)==32){return B(_1zk(_1zp,_1z7));}else{return B(_1zk(_1z6,_1z7));}}else{if(_1z7!=_1za){if(E(B(_6X(B(_6X(_1z8,_1z7)),_1zp)).a)==32){return B(_1zk(_1zp,_1z7));}else{return B(_1zk(_1z6,_1z7));}}else{return B(_1zk(_1z6,_1z7));}}}}}}break;case 2:if(_1z6<0){return B(_1zk(_1z6,_1z7));}else{if(_1z6>=E(_1yT)){return B(_1zk(_1z6,_1z7));}else{var _1zq=_1z7-1|0;if(_1zq<0){return B(_1zk(_1z6,_1z7));}else{if(_1zq>=E(_1yV)){return B(_1zk(_1z6,_1z7));}else{if(_1z6!=_1z9){if(E(B(_6X(B(_6X(_1z8,_1zq)),_1z6)).a)==32){return B(_1zk(_1z6,_1zq));}else{return B(_1zk(_1z6,_1z7));}}else{if(_1zq!=_1za){if(E(B(_6X(B(_6X(_1z8,_1zq)),_1z6)).a)==32){return B(_1zk(_1z6,_1zq));}else{return B(_1zk(_1z6,_1z7));}}else{return B(_1zk(_1z6,_1z7));}}}}}}break;case 3:var _1zr=_1z6+1|0;if(_1zr<0){return B(_1zk(_1z6,_1z7));}else{if(_1zr>=E(_1yT)){return B(_1zk(_1z6,_1z7));}else{if(_1z7<0){return B(_1zk(_1z6,_1z7));}else{if(_1z7>=E(_1yV)){return B(_1zk(_1z6,_1z7));}else{if(_1zr!=_1z9){if(E(B(_6X(B(_6X(_1z8,_1z7)),_1zr)).a)==32){return B(_1zk(_1zr,_1z7));}else{return B(_1zk(_1z6,_1z7));}}else{if(_1z7!=_1za){if(E(B(_6X(B(_6X(_1z8,_1z7)),_1zr)).a)==32){return B(_1zk(_1zr,_1z7));}else{return B(_1zk(_1z6,_1z7));}}else{return B(_1zk(_1z6,_1z7));}}}}}}break;case 4:if(_1z6<0){return B(_1zk(_1z6,_1z7));}else{if(_1z6>=E(_1yT)){return B(_1zk(_1z6,_1z7));}else{var _1zs=_1z7+1|0;if(_1zs<0){return B(_1zk(_1z6,_1z7));}else{if(_1zs>=E(_1yV)){return B(_1zk(_1z6,_1z7));}else{if(_1z6!=_1z9){if(E(B(_6X(B(_6X(_1z8,_1zs)),_1z6)).a)==32){return B(_1zk(_1z6,_1zs));}else{return B(_1zk(_1z6,_1z7));}}else{if(_1zs!=_1za){if(E(B(_6X(B(_6X(_1z8,_1zs)),_1z6)).a)==32){return B(_1zk(_1z6,_1zs));}else{return B(_1zk(_1z6,_1z7));}}else{return B(_1zk(_1z6,_1z7));}}}}}}break;default:if(_1z6<0){return B(_1zk(_1z6,_1z7));}else{if(_1z6>=E(_1yT)){return B(_1zk(_1z6,_1z7));}else{if(_1z7<0){return B(_1zk(_1z6,_1z7));}else{if(_1z7>=E(_1yV)){return B(_1zk(_1z6,_1z7));}else{if(_1z6!=_1z9){var _1zt=E(B(_6X(B(_6X(_1z8,_1z7)),_1z6)).a);return B(_1zk(_1z6,_1z7));}else{if(_1z7!=_1za){var _1zu=E(B(_6X(B(_6X(_1z8,_1z7)),_1z6)).a);return B(_1zk(_1z6,_1z7));}else{return B(_1zk(_1z6,_1z7));}}}}}}}}),_1zv=E(_1zf);if(!_1zv._){var _1zw=_1z7+1|0,_1zx=_1z9,_1zy=_1za;_1yX=new T(function(){return E(E(_1zh).b);},1);_1yY=0;_1yZ=_1zw;_1z0=_1zj;_1z1=_1zx;_1z2=_1zy;_1z3=_1zd;return __continue;}else{return new F(function(){return _1zz(new T(function(){return E(E(_1zh).b);},1),_1z6+1|0,_1z7,_1zj,_1z9,_1za,_1zv.a,_1zv.b,_1zd);});}}else{var _1zA=E(_1zf);if(!_1zA._){var _1zB=_1z5,_1zw=_1z7+1|0,_1zC=_1z8,_1zx=_1z9,_1zy=_1za;_1yX=_1zB;_1yY=0;_1yZ=_1zw;_1z0=_1zC;_1z1=_1zx;_1z2=_1zy;_1z3=_1zd;return __continue;}else{return new F(function(){return _1zz(_1z5,_1z6+1|0,_1z7,_1z8,_1z9,_1za,_1zA.a,_1zA.b,_1zd);});}}}}})(_1yX,_1yY,_1yZ,_1z0,_1z1,_1z2,_1z3));if(_1z4!=__continue){return _1z4;}}},_1zz=function(_1zD,_1zE,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL){while(1){var _1zM=B((function(_1zN,_1zO,_1zP,_1zQ,_1zR,_1zS,_1zT,_1zU,_1zV){var _1zW=E(_1zT);if(E(_1zW.b)==5){var _1zX=new T(function(){var _1zY=B(_1v0(_1xH,_1zN));return new T2(0,_1zY.a,_1zY.b);}),_1zZ=new T(function(){var _1A0=function(_1A1,_1A2){var _1A3=function(_1A4){return new F(function(){return _L4(_1zO,_1zP,_Xs,_Ej,new T(function(){return B(_L4(_1A1,_1A2,_1zW.a,_F8,_1zQ));}));});};if(_1A1!=_1zO){return new F(function(){return _1A3(_);});}else{if(_1A2!=_1zP){return new F(function(){return _1A3(_);});}else{return E(_1zQ);}}};switch(E(E(_1zX).a)){case 1:var _1A5=_1zO-1|0;if(_1A5<0){return B(_1A0(_1zO,_1zP));}else{if(_1A5>=E(_1yT)){return B(_1A0(_1zO,_1zP));}else{if(_1zP<0){return B(_1A0(_1zO,_1zP));}else{if(_1zP>=E(_1yV)){return B(_1A0(_1zO,_1zP));}else{if(_1A5!=_1zR){if(E(B(_6X(B(_6X(_1zQ,_1zP)),_1A5)).a)==32){return B(_1A0(_1A5,_1zP));}else{return B(_1A0(_1zO,_1zP));}}else{if(_1zP!=_1zS){if(E(B(_6X(B(_6X(_1zQ,_1zP)),_1A5)).a)==32){return B(_1A0(_1A5,_1zP));}else{return B(_1A0(_1zO,_1zP));}}else{return B(_1A0(_1zO,_1zP));}}}}}}break;case 2:if(_1zO<0){return B(_1A0(_1zO,_1zP));}else{if(_1zO>=E(_1yT)){return B(_1A0(_1zO,_1zP));}else{var _1A6=_1zP-1|0;if(_1A6<0){return B(_1A0(_1zO,_1zP));}else{if(_1A6>=E(_1yV)){return B(_1A0(_1zO,_1zP));}else{if(_1zO!=_1zR){if(E(B(_6X(B(_6X(_1zQ,_1A6)),_1zO)).a)==32){return B(_1A0(_1zO,_1A6));}else{return B(_1A0(_1zO,_1zP));}}else{if(_1A6!=_1zS){if(E(B(_6X(B(_6X(_1zQ,_1A6)),_1zO)).a)==32){return B(_1A0(_1zO,_1A6));}else{return B(_1A0(_1zO,_1zP));}}else{return B(_1A0(_1zO,_1zP));}}}}}}break;case 3:var _1A7=_1zO+1|0;if(_1A7<0){return B(_1A0(_1zO,_1zP));}else{if(_1A7>=E(_1yT)){return B(_1A0(_1zO,_1zP));}else{if(_1zP<0){return B(_1A0(_1zO,_1zP));}else{if(_1zP>=E(_1yV)){return B(_1A0(_1zO,_1zP));}else{if(_1A7!=_1zR){if(E(B(_6X(B(_6X(_1zQ,_1zP)),_1A7)).a)==32){return B(_1A0(_1A7,_1zP));}else{return B(_1A0(_1zO,_1zP));}}else{if(_1zP!=_1zS){if(E(B(_6X(B(_6X(_1zQ,_1zP)),_1A7)).a)==32){return B(_1A0(_1A7,_1zP));}else{return B(_1A0(_1zO,_1zP));}}else{return B(_1A0(_1zO,_1zP));}}}}}}break;case 4:if(_1zO<0){return B(_1A0(_1zO,_1zP));}else{if(_1zO>=E(_1yT)){return B(_1A0(_1zO,_1zP));}else{var _1A8=_1zP+1|0;if(_1A8<0){return B(_1A0(_1zO,_1zP));}else{if(_1A8>=E(_1yV)){return B(_1A0(_1zO,_1zP));}else{if(_1zO!=_1zR){if(E(B(_6X(B(_6X(_1zQ,_1A8)),_1zO)).a)==32){return B(_1A0(_1zO,_1A8));}else{return B(_1A0(_1zO,_1zP));}}else{if(_1A8!=_1zS){if(E(B(_6X(B(_6X(_1zQ,_1A8)),_1zO)).a)==32){return B(_1A0(_1zO,_1A8));}else{return B(_1A0(_1zO,_1zP));}}else{return B(_1A0(_1zO,_1zP));}}}}}}break;default:if(_1zO<0){return B(_1A0(_1zO,_1zP));}else{if(_1zO>=E(_1yT)){return B(_1A0(_1zO,_1zP));}else{if(_1zP<0){return B(_1A0(_1zO,_1zP));}else{if(_1zP>=E(_1yV)){return B(_1A0(_1zO,_1zP));}else{if(_1zO!=_1zR){var _1A9=E(B(_6X(B(_6X(_1zQ,_1zP)),_1zO)).a);return B(_1A0(_1zO,_1zP));}else{if(_1zP!=_1zS){var _1Aa=E(B(_6X(B(_6X(_1zQ,_1zP)),_1zO)).a);return B(_1A0(_1zO,_1zP));}else{return B(_1A0(_1zO,_1zP));}}}}}}}}),_1Ab=E(_1zU);if(!_1Ab._){return new F(function(){return _1yW(new T(function(){return E(E(_1zX).b);},1),0,_1zP+1|0,_1zZ,_1zR,_1zS,_1zV);});}else{var _1Ac=_1zO+1|0,_1Ad=_1zP,_1Ae=_1zR,_1Af=_1zS,_1Ag=_1zV;_1zD=new T(function(){return E(E(_1zX).b);},1);_1zE=_1Ac;_1zF=_1Ad;_1zG=_1zZ;_1zH=_1Ae;_1zI=_1Af;_1zJ=_1Ab.a;_1zK=_1Ab.b;_1zL=_1Ag;return __continue;}}else{var _1Ah=E(_1zU);if(!_1Ah._){return new F(function(){return _1yW(_1zN,0,_1zP+1|0,_1zQ,_1zR,_1zS,_1zV);});}else{var _1Ai=_1zN,_1Ac=_1zO+1|0,_1Ad=_1zP,_1Aj=_1zQ,_1Ae=_1zR,_1Af=_1zS,_1Ag=_1zV;_1zD=_1Ai;_1zE=_1Ac;_1zF=_1Ad;_1zG=_1Aj;_1zH=_1Ae;_1zI=_1Af;_1zJ=_1Ah.a;_1zK=_1Ah.b;_1zL=_1Ag;return __continue;}}})(_1zD,_1zE,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL));if(_1zM!=__continue){return _1zM;}}},_1yS=B(_1yW(_1xX,0,0,_1yf,_1xN,_1xO,_1yf));}var _1Ak=function(_1Al){var _1Am=function(_1An){var _1Ao=new T(function(){switch(E(_1y3)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1Ap=new T(function(){if(!E(_1yd)){if(!E(_1Ao)){return new T2(0,_1xN,_1xO);}else{return new T2(0,_1xP,_1xQ);}}else{if(!B(_1rW(_1s8,_1yS,_1yc))){if(!E(_1Ao)){return new T2(0,_1xN,_1xO);}else{return new T2(0,_1xP,_1xQ);}}else{return new T2(0,_1xP,_1xQ);}}}),_1Aq=new T(function(){return E(E(_1Ap).b);}),_1Ar=new T(function(){return E(E(_1Ap).a);});if(!E(_1yd)){var _1As=E(_1y0);}else{var _1As=E(B(_1uJ(new T(function(){return B(_1wa(_1xV,_1xW,_1yS));}),_1yS)).a);}var _1At=new T(function(){if(!E(_1yb)){if(!E(_1y6)){var _1Au=function(_1Av){var _1Aw=function(_1Ax){var _1Ay=E(_1y3);if(_1Ay==4){return new T2(1,_1xK,new T2(1,_1y2,_S));}else{if(!E(_1Ao)){return (E(_1Ay)==2)?new T2(1,_1xI,new T2(1,_1y2,_S)):__Z;}else{var _1Az=E(_1y2);return (E(_1Az)==61)?new T2(1,_1xJ,new T2(1,_1Az,new T(function(){return B(_A(0,_1xO,_S));}))):new T2(1,_1xJ,new T2(1,_1Az,_S));}}};if(!E(_1yd)){return new F(function(){return _1Aw(_);});}else{if(E(_1xP)!=E(_1Ar)){return new T2(1,_1xL,new T2(1,_1y2,_S));}else{if(E(_1xQ)!=E(_1Aq)){return new T2(1,_1xL,new T2(1,_1y2,_S));}else{return new F(function(){return _1Aw(_);});}}}};if(!E(_1yd)){return B(_1Au(_));}else{if(!E(_1As)){return B(_1Au(_));}else{return E(_1xE);}}}else{return new T2(1,_1xC,new T2(1,_1y2,_S));}}else{return new T2(1,_1xD,new T2(1,_1y2,_S));}},1);return {_:0,a:E(new T2(0,_1Ar,_1Aq)),b:E(_1yS),c:E(_1xS),d:_1Al,e:_1An,f:_1xV,g:E(_1xW),h:_1xX,i:E(B(_q(_1xY,_1At))),j:E(_1xZ),k:E(_1As)};};if(!E(_1yb)){return new F(function(){return _1Am(_1xU);});}else{return new F(function(){return _1Am(E(_1y2));});}};if(!E(_1y6)){return new F(function(){return _1Ak(_1xT);});}else{return new F(function(){return _1Ak(E(_1y2));});}},_1AA=new T2(1,_5U,_S),_1AB=5,_1AC=new T2(1,_1AB,_S),_1AD=function(_1AE,_1AF){while(1){var _1AG=E(_1AE);if(!_1AG._){return E(_1AF);}else{_1AE=_1AG.b;_1AF=_1AG.a;continue;}}},_1AH=57,_1AI=48,_1AJ=new T2(1,_1vh,_S),_1AK=new T(function(){return B(err(_sD));}),_1AL=new T(function(){return B(err(_sz));}),_1AM=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_1AN=function(_1AO,_1AP){if((_1AP-48|0)>>>0>9){var _1AQ=_1AP+_1AO|0,_1AR=function(_1AS){if(!B(_4A(_hd,_1AS,_1AJ))){return E(_1AS);}else{return new F(function(){return _1AN(_1AO,_1AS);});}};if(_1AQ<=122){if(_1AQ>=97){if(_1AQ>>>0>1114111){return new F(function(){return _wO(_1AQ);});}else{return new F(function(){return _1AR(_1AQ);});}}else{if(_1AQ<=90){if(_1AQ>>>0>1114111){return new F(function(){return _wO(_1AQ);});}else{return new F(function(){return _1AR(_1AQ);});}}else{var _1AT=65+(_1AQ-90|0)|0;if(_1AT>>>0>1114111){return new F(function(){return _wO(_1AT);});}else{return new F(function(){return _1AR(_1AT);});}}}}else{var _1AU=97+(_1AQ-122|0)|0;if(_1AU>>>0>1114111){return new F(function(){return _wO(_1AU);});}else{return new F(function(){return _1AR(_1AU);});}}}else{var _1AV=B(_Gl(B(_sI(_1AM,new T2(1,_1AP,_S)))));if(!_1AV._){return E(_1AL);}else{if(!E(_1AV.b)._){var _1AW=E(_1AV.a)+_1AO|0;switch(_1AW){case  -1:return E(_1AI);case 10:return E(_1AH);default:return new F(function(){return _1AD(B(_A(0,_1AW,_S)),_Vx);});}}else{return E(_1AK);}}}},_1AX=function(_1AY,_1AZ){if((_1AY-48|0)>>>0>9){return _1AZ;}else{var _1B0=B(_Gl(B(_sI(_1AM,new T2(1,_1AY,_S)))));if(!_1B0._){return E(_1AL);}else{if(!E(_1B0.b)._){return new F(function(){return _1AN(E(_1B0.a),_1AZ);});}else{return E(_1AK);}}}},_1B1=function(_1B2,_1B3){return new F(function(){return _1AX(E(_1B2),E(_1B3));});},_1B4=new T2(1,_1B1,_S),_1B5=112,_1B6=111,_1B7=function(_1B8,_1B9,_1Ba,_1Bb,_1Bc,_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi,_1Bj){var _1Bk=new T(function(){return B(_6X(B(_6X(_1Ba,_1B9)),E(_1B8)));}),_1Bl=new T(function(){return E(E(_1Bk).b);}),_1Bm=new T(function(){if(E(_1Bl)==4){return true;}else{return false;}}),_1Bn=new T(function(){return E(E(_1Bk).a);});if(E(_1Bd)==32){var _1Bo=false;}else{if(E(_1Bn)==32){var _1Bp=true;}else{var _1Bp=false;}var _1Bo=_1Bp;}var _1Bq=new T(function(){var _1Br=new T(function(){return B(A3(_6X,_1AA,B(_MU(_hd,_1Bc,_1vi)),_1Bd));});if(!E(_1Bo)){if(!E(_1Bm)){return E(_1Bn);}else{if(!B(_4A(_3L,_1Be,_1AC))){return E(_1Bn);}else{return B(A(_6X,[_1B4,B(_MU(_3L,_1Be,_1AC)),_1Br,_1Bn]));}}}else{return E(_1Br);}}),_1Bs=B(_L4(_1B8,_1B9,_1Bq,_1Bl,_1Ba)),_1Bt=function(_1Bu){var _1Bv=B(_1uJ(new T(function(){return B(_1wa(_1Be,_1Bf,_1Bs));}),_1Bs)).a;return {_:0,a:E(new T2(0,_1B8,_1B9)),b:E(_1Bs),c:E(_1Bb),d:_1Bc,e:_1Bu,f:_1Be,g:E(_1Bf),h:_1Bg,i:E(B(_q(_1Bh,new T(function(){if(!E(_1Bv)){if(!E(_1Bo)){if(!E(_1Bm)){return __Z;}else{return new T2(1,_1B5,new T2(1,_1Bq,_S));}}else{return new T2(1,_1B6,new T2(1,_1Bq,_S));}}else{return E(_1xE);}},1)))),j:E(_1Bi),k:E(_1Bv)};};if(!E(_1Bo)){return new F(function(){return _1Bt(_1Bd);});}else{return new F(function(){return _1Bt(32);});}},_1Bw=function(_1Bx,_1By){while(1){var _1Bz=E(_1By);if(!_1Bz._){return __Z;}else{var _1BA=_1Bz.b,_1BB=E(_1Bx);if(_1BB==1){return E(_1BA);}else{_1Bx=_1BB-1|0;_1By=_1BA;continue;}}}},_1BC=4,_1BD=new T(function(){return B(unCStr("\u5e74 "));}),_1BE=function(_1BF,_1BG,_1BH,_1BI,_1BJ){var _1BK=new T(function(){var _1BL=new T(function(){var _1BM=new T(function(){return B(_q(_1BG,new T(function(){return B(unAppCStr(" >>",_1BI));},1)));},1);return B(_q(_1BD,_1BM));},1);return B(_q(B(_A(0,_1BF,_S)),_1BL));});return new T2(0,new T2(1,_1BJ,_1r3),_1BK);},_1BN=function(_1BO){var _1BP=E(_1BO),_1BQ=E(_1BP.a),_1BR=B(_1BE(_1BQ.a,_1BQ.b,_1BQ.c,_1BQ.d,_1BP.b));return new T2(0,_1BR.a,_1BR.b);},_1BS=function(_1BT){var _1BU=E(_1BT);return new T2(0,new T2(1,_1BU.b,_1r3),E(_1BU.a).b);},_1BV=new T(function(){return B(_ed("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1BW=function(_1BX,_1BY){while(1){var _1BZ=E(_1BY);if(!_1BZ._){return false;}else{var _1C0=_1BZ.b,_1C1=E(_1BX),_1C2=_1C1.a,_1C3=_1C1.b,_1C4=E(_1BZ.a);if(!_1C4._){return E(_1BV);}else{var _1C5=E(_1C4.a),_1C6=_1C5.a,_1C7=_1C5.b,_1C8=E(_1C4.b);if(!_1C8._){var _1C9=E(_1C2),_1Ca=E(_1C9);if(_1Ca==32){switch(E(_1C3)){case 0:if(!E(_1C7)){return true;}else{_1BX=new T2(0,_1C9,_Ej);_1BY=_1C0;continue;}break;case 1:if(E(_1C7)==1){return true;}else{_1BX=new T2(0,_1C9,_Ep);_1BY=_1C0;continue;}break;case 2:if(E(_1C7)==2){return true;}else{_1BX=new T2(0,_1C9,_Ev);_1BY=_1C0;continue;}break;case 3:if(E(_1C7)==3){return true;}else{_1BX=new T2(0,_1C9,_EB);_1BY=_1C0;continue;}break;case 4:if(E(_1C7)==4){return true;}else{_1BX=new T2(0,_1C9,_EH);_1BY=_1C0;continue;}break;case 5:if(E(_1C7)==5){return true;}else{_1BX=new T2(0,_1C9,_F8);_1BY=_1C0;continue;}break;case 6:if(E(_1C7)==6){return true;}else{_1BX=new T2(0,_1C9,_F1);_1BY=_1C0;continue;}break;case 7:if(E(_1C7)==7){return true;}else{_1BX=new T2(0,_1C9,_EU);_1BY=_1C0;continue;}break;default:if(E(_1C7)==8){return true;}else{_1BX=new T2(0,_1C9,_EN);_1BY=_1C0;continue;}}}else{if(_1Ca!=E(_1C6)){_1BX=_1C1;_1BY=_1C0;continue;}else{switch(E(_1C3)){case 0:if(!E(_1C7)){return true;}else{_1BX=new T2(0,_1C9,_Ej);_1BY=_1C0;continue;}break;case 1:if(E(_1C7)==1){return true;}else{_1BX=new T2(0,_1C9,_Ep);_1BY=_1C0;continue;}break;case 2:if(E(_1C7)==2){return true;}else{_1BX=new T2(0,_1C9,_Ev);_1BY=_1C0;continue;}break;case 3:if(E(_1C7)==3){return true;}else{_1BX=new T2(0,_1C9,_EB);_1BY=_1C0;continue;}break;case 4:if(E(_1C7)==4){return true;}else{_1BX=new T2(0,_1C9,_EH);_1BY=_1C0;continue;}break;case 5:if(E(_1C7)==5){return true;}else{_1BX=new T2(0,_1C9,_F8);_1BY=_1C0;continue;}break;case 6:if(E(_1C7)==6){return true;}else{_1BX=new T2(0,_1C9,_F1);_1BY=_1C0;continue;}break;case 7:if(E(_1C7)==7){return true;}else{_1BX=new T2(0,_1C9,_EU);_1BY=_1C0;continue;}break;default:if(E(_1C7)==8){return true;}else{_1BX=new T2(0,_1C9,_EN);_1BY=_1C0;continue;}}}}}else{var _1Cb=E(_1C2),_1Cc=E(_1Cb);if(_1Cc==32){switch(E(_1C3)){case 0:if(!E(_1C7)){return true;}else{_1BX=new T2(0,_1Cb,_Ej);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 1:if(E(_1C7)==1){return true;}else{_1BX=new T2(0,_1Cb,_Ep);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 2:if(E(_1C7)==2){return true;}else{_1BX=new T2(0,_1Cb,_Ev);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 3:if(E(_1C7)==3){return true;}else{_1BX=new T2(0,_1Cb,_EB);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 4:if(E(_1C7)==4){return true;}else{_1BX=new T2(0,_1Cb,_EH);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 5:if(E(_1C7)==5){return true;}else{_1BX=new T2(0,_1Cb,_F8);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 6:if(E(_1C7)==6){return true;}else{_1BX=new T2(0,_1Cb,_F1);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 7:if(E(_1C7)==7){return true;}else{_1BX=new T2(0,_1Cb,_EU);_1BY=new T2(1,_1C8,_1C0);continue;}break;default:if(E(_1C7)==8){return true;}else{_1BX=new T2(0,_1Cb,_EN);_1BY=new T2(1,_1C8,_1C0);continue;}}}else{if(_1Cc!=E(_1C6)){_1BX=_1C1;_1BY=new T2(1,_1C8,_1C0);continue;}else{switch(E(_1C3)){case 0:if(!E(_1C7)){return true;}else{_1BX=new T2(0,_1Cb,_Ej);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 1:if(E(_1C7)==1){return true;}else{_1BX=new T2(0,_1Cb,_Ep);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 2:if(E(_1C7)==2){return true;}else{_1BX=new T2(0,_1Cb,_Ev);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 3:if(E(_1C7)==3){return true;}else{_1BX=new T2(0,_1Cb,_EB);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 4:if(E(_1C7)==4){return true;}else{_1BX=new T2(0,_1Cb,_EH);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 5:if(E(_1C7)==5){return true;}else{_1BX=new T2(0,_1Cb,_F8);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 6:if(E(_1C7)==6){return true;}else{_1BX=new T2(0,_1Cb,_F1);_1BY=new T2(1,_1C8,_1C0);continue;}break;case 7:if(E(_1C7)==7){return true;}else{_1BX=new T2(0,_1Cb,_EU);_1BY=new T2(1,_1C8,_1C0);continue;}break;default:if(E(_1C7)==8){return true;}else{_1BX=new T2(0,_1Cb,_EN);_1BY=new T2(1,_1C8,_1C0);continue;}}}}}}}}},_1Cd=function(_1Ce,_1Cf,_1Cg,_1Ch,_1Ci){var _1Cj=E(_1Ci);if(!_1Cj._){var _1Ck=new T(function(){var _1Cl=B(_1Cd(_1Cj.a,_1Cj.b,_1Cj.c,_1Cj.d,_1Cj.e));return new T2(0,_1Cl.a,_1Cl.b);});return new T2(0,new T(function(){return E(E(_1Ck).a);}),new T(function(){return B(_12B(_1Cf,_1Cg,_1Ch,E(_1Ck).b));}));}else{return new T2(0,new T2(0,_1Cf,_1Cg),_1Ch);}},_1Cm=function(_1Cn,_1Co,_1Cp,_1Cq,_1Cr){var _1Cs=E(_1Cq);if(!_1Cs._){var _1Ct=new T(function(){var _1Cu=B(_1Cm(_1Cs.a,_1Cs.b,_1Cs.c,_1Cs.d,_1Cs.e));return new T2(0,_1Cu.a,_1Cu.b);});return new T2(0,new T(function(){return E(E(_1Ct).a);}),new T(function(){return B(_11K(_1Co,_1Cp,E(_1Ct).b,_1Cr));}));}else{return new T2(0,new T2(0,_1Co,_1Cp),_1Cr);}},_1Cv=function(_1Cw,_1Cx){var _1Cy=E(_1Cw);if(!_1Cy._){var _1Cz=_1Cy.a,_1CA=E(_1Cx);if(!_1CA._){var _1CB=_1CA.a;if(_1Cz<=_1CB){var _1CC=B(_1Cm(_1CB,_1CA.b,_1CA.c,_1CA.d,_1CA.e)),_1CD=E(_1CC.a);return new F(function(){return _12B(_1CD.a,_1CD.b,_1Cy,_1CC.b);});}else{var _1CE=B(_1Cd(_1Cz,_1Cy.b,_1Cy.c,_1Cy.d,_1Cy.e)),_1CF=E(_1CE.a);return new F(function(){return _11K(_1CF.a,_1CF.b,_1CE.b,_1CA);});}}else{return E(_1Cy);}}else{return E(_1Cx);}},_1CG=function(_1CH,_1CI){var _1CJ=E(_1CH),_1CK=E(_1CI);if(!_1CK._){var _1CL=_1CK.b,_1CM=_1CK.c,_1CN=_1CK.d,_1CO=_1CK.e;switch(B(_11y(_1CJ,_1CL))){case 0:return new F(function(){return _11K(_1CL,_1CM,B(_1CG(_1CJ,_1CN)),_1CO);});break;case 1:return new F(function(){return _1Cv(_1CN,_1CO);});break;default:return new F(function(){return _12B(_1CL,_1CM,_1CN,B(_1CG(_1CJ,_1CO)));});}}else{return new T0(1);}},_1CP=function(_1CQ,_1CR){while(1){var _1CS=E(_1CQ);if(!_1CS._){return E(_1CR);}else{var _1CT=B(_1CG(new T2(1,_1CS.a,_1r3),_1CR));_1CQ=_1CS.b;_1CR=_1CT;continue;}}},_1CU=new T(function(){return B(unCStr("\n"));}),_1CV=function(_1CW,_1CX,_){var _1CY=jsWriteHandle(E(_1CW),toJSStr(E(_1CX)));return _gK;},_1CZ=function(_1D0,_1D1,_){var _1D2=E(_1D0),_1D3=jsWriteHandle(_1D2,toJSStr(E(_1D1)));return new F(function(){return _1CV(_1D2,_1CU,_);});},_1D4=function(_1D5){var _1D6=E(_1D5);if(!_1D6._){return __Z;}else{return new F(function(){return _q(_1D6.a,new T(function(){return B(_1D4(_1D6.b));},1));});}},_1D7=new T(function(){return B(unCStr("removed"));}),_1D8=new T(function(){return B(unCStr("loadError"));}),_1D9=new T(function(){return B(unCStr("saved"));}),_1Da=new T(function(){return B(err(_sz));}),_1Db=new T(function(){return B(err(_sD));}),_1Dc=8,_1Dd=3,_1De=new T(function(){return B(unCStr("Congratulations!"));}),_1Df=5,_1Dg=32,_1Dh=new T2(0,_1Dg,_F8),_1Di=99,_1Dj=64,_1Dk=new T(function(){return B(_mz(_1mp,0));}),_1Dl=new T(function(){return B(unCStr("loadError"));}),_1Dm=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_1Dn=new T(function(){return B(unCStr(","));}),_1Do=new T(function(){return B(unCStr("~"));}),_1Dp=new T(function(){return B(unCStr("savedata"));}),_1Dq=new T(function(){return B(unCStr("---"));}),_1Dr=new T(function(){return B(unCStr("=="));}),_1Ds=0,_1Dt=4,_1Du=6,_1Dv=new T1(0,333),_1Dw=new T(function(){return B(_8y(1,2147483647));}),_1Dx=function(_1Dy){var _1Dz=B(_Gl(B(_sI(_1Dm,_1Dy))));return (_1Dz._==0)?E(_1Da):(E(_1Dz.b)._==0)?E(_1Dz.a):E(_1Db);},_1DA=new T(function(){var _1DB=E(_1kI);if(!_1DB._){return E(_nn);}else{return E(_1DB.a);}}),_1DC=new T(function(){return B(unAppCStr("[]",_S));}),_1DD=new T(function(){return B(unCStr("\""));}),_1DE=new T2(1,_S,_S),_1DF=new T(function(){return B(_6k(_1Dx,_1DE));}),_1DG=function(_1DH,_1DI){return new T2(1,_6J,new T(function(){return B(_8q(_1DH,new T2(1,_6J,_1DI)));}));},_1DJ=function(_1DK,_1DL){var _1DM=E(_1DK),_1DN=new T(function(){var _1DO=function(_1DP){var _1DQ=E(_1DM.a),_1DR=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1DS){return new F(function(){return _1DG(_1DQ.a,_1DS);});},new T2(1,function(_1DT){return new F(function(){return _1a4(0,_1DQ.b,_1DT);});},_S)),new T2(1,_y,_1DP)));});return new T2(1,_z,_1DR);};return B(A3(_sl,_6D,new T2(1,_1DO,new T2(1,function(_1DU){return new F(function(){return _A(0,E(_1DM.b),_1DU);});},_S)),new T2(1,_y,_1DL)));});return new T2(1,_z,_1DN);},_1DV=new T(function(){return B(_1fC(_1k6,5,_1lc));}),_1DW=new T2(1,_6J,_S),_1DX=new T(function(){return B(unCStr("Thank you for playing!"));}),_1DY=17,_1DZ=2,_1E0=new T(function(){return B(unCStr("Coding : yokoP"));}),_1E1=function(_1E2,_1E3){var _1E4=E(_1E3);return (_1E4._==0)?__Z:new T2(1,_1E2,new T2(1,_1E4.a,new T(function(){return B(_1E1(_1E2,_1E4.b));})));},_1E5=new T(function(){return B(unCStr("noContent"));}),_1E6=new T(function(){return B(unCStr("noHint"));}),_1E7=new T(function(){return B(err(_sD));}),_1E8=new T(function(){return B(err(_sz));}),_1E9=new T(function(){return B(A3(_FJ,_Gc,_DO,_FB));}),_1Ea=function(_1Eb,_1Ec){var _1Ed=E(_1Ec);if(!_1Ed._){var _1Ee=B(_Gl(B(_sI(_1E9,_1Eb))));return (_1Ee._==0)?E(_1E8):(E(_1Ee.b)._==0)?new T4(0,E(_1Ee.a),_S,_S,_S):E(_1E7);}else{var _1Ef=_1Ed.a,_1Eg=E(_1Ed.b);if(!_1Eg._){var _1Eh=B(_Gl(B(_sI(_1E9,_1Eb))));return (_1Eh._==0)?E(_1E8):(E(_1Eh.b)._==0)?new T4(0,E(_1Eh.a),E(_1Ef),E(_1E6),E(_1E5)):E(_1E7);}else{var _1Ei=_1Eg.a,_1Ej=E(_1Eg.b);if(!_1Ej._){var _1Ek=B(_Gl(B(_sI(_1E9,_1Eb))));return (_1Ek._==0)?E(_1E8):(E(_1Ek.b)._==0)?new T4(0,E(_1Ek.a),E(_1Ef),E(_1Ei),E(_1E5)):E(_1E7);}else{if(!E(_1Ej.b)._){var _1El=B(_Gl(B(_sI(_1E9,_1Eb))));return (_1El._==0)?E(_1E8):(E(_1El.b)._==0)?new T4(0,E(_1El.a),E(_1Ef),E(_1Ei),E(_1Ej.a)):E(_1E7);}else{return new T4(0,0,_S,_S,_S);}}}}},_1Em=function(_1En){var _1Eo=E(_1En);if(!_1Eo._){return new F(function(){return _1Ea(_S,_S);});}else{var _1Ep=_1Eo.a,_1Eq=E(_1Eo.b);if(!_1Eq._){return new F(function(){return _1Ea(new T2(1,_1Ep,_S),_S);});}else{var _1Er=E(_1Ep),_1Es=new T(function(){var _1Et=B(_Hd(44,_1Eq.a,_1Eq.b));return new T2(0,_1Et.a,_1Et.b);});if(E(_1Er)==44){return new F(function(){return _1Ea(_S,new T2(1,new T(function(){return E(E(_1Es).a);}),new T(function(){return E(E(_1Es).b);})));});}else{var _1Eu=E(_1Es);return new F(function(){return _1Ea(new T2(1,_1Er,_1Eu.a),_1Eu.b);});}}}},_1Ev=function(_1Ew){var _1Ex=B(_1Em(_1Ew));return new T4(0,_1Ex.a,E(_1Ex.b),E(_1Ex.c),E(_1Ex.d));},_1Ey=function(_1Ez){return (E(_1Ez)==10)?true:false;},_1EA=function(_1EB){var _1EC=E(_1EB);if(!_1EC._){return __Z;}else{var _1ED=new T(function(){var _1EE=B(_1g5(_1Ey,_1EC));return new T2(0,_1EE.a,new T(function(){var _1EF=E(_1EE.b);if(!_1EF._){return __Z;}else{return B(_1EA(_1EF.b));}}));});return new T2(1,new T(function(){return E(E(_1ED).a);}),new T(function(){return E(E(_1ED).b);}));}},_1EG=new T(function(){return B(unCStr("57,\u5974\uff1a\u306a\uff1a\u56fd\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304c\u5f8c\uff1a\u3053\u3046\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u304b\u3089\u91d1\uff1a\u304d\u3093\uff1a\u5370\uff1a\u3044\u3093\uff1a,<\u5f8c\uff1a\u3054\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\uff1a\u3057\uff1a\u8cc0\uff1a\u304b\u306e\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u3066<\u6f22\uff1a\u304b\u3093\u306e\uff1a\u59d4\uff1a\u308f\u306e\uff1a\u5974\uff1a\u306a\u306e\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a>\u3068\u523b\uff1a\u304d\u3056\uff1a\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\uff1a\u306f\u3063\uff1a\u898b\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b >>\u5927\uff1a\u3084\uff1a\u548c\uff1a\u307e\u3068\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u3068\u306e\u95dc\uff1a\u304b\u3093\uff1a\u4fc2\uff1a\u3051\u3044\uff1a\u306f\u4e0d\u660e\n239,<\u5351\uff1a\u3072\uff1a\u5f25\uff1a\u307f\uff1a\u547c\uff1a\u3053\uff1a>\u304c\u9b4f\uff1a\u304e\uff1a\u306b\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u306e\u6b74\u53f2\u66f8<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u3055\u308c\u3066\u3090\u308b\u5deb\uff1a\u307f\uff1a\u5973\uff1a\u3053\uff1a,<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u502d\uff1a\u308f\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u4f1d\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u3057\u308b\uff1a\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\uff1a\u306e\u3053\uff1a\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687 \u7a0e\u3092\u514d\uff1a\u3081\u3093\uff1a\u9664\uff1a\u3058\u3087\uff1a,<\u53e4\uff1a\u3053\uff1a\u4e8b\uff1a\u3058\uff1a\u8a18\uff1a\u304d\uff1a><\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a\u7d00\uff1a\u304d\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c<\u6c11\uff1a\u305f\u307f\uff1a\u306e\u304b\u307e\u3069\u3088\u308a\u7159\uff1a\u3051\u3080\u308a\uff1a\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\uff1a\u307e\u3065\uff1a\u3057\u304f\u3066\u708a\uff1a\u305f\uff1a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\uff1a\u304d\u3085\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306e\u4fee\uff1a\u3057\u3085\u3046\uff1a\u7e55\uff1a\u305c\u3093\uff1a\u3092\u5f8c\uff1a\u3042\u3068\uff1a\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\uff1a\u3086\u305f\uff1a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d\uff1a\u308f\uff1a>\u306e\u6b66\uff1a\u3076\uff1a\u738b\uff1a\u304a\u3046\uff1a \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5b8b\uff1a\u305d\u3046\uff1a\u3078\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u96c4\uff1a\u3086\u3046\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\uff1a\u3066\u3044\uff1a\u8aac\uff1a\u305b\u3064\uff1a,<\u5b8b\uff1a\u305d\u3046\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u502d\uff1a\u308f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u50b3\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b >> \u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\uff1a\u3076\u3063\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f1d\uff1a\u3067\u3093\uff1a,\u6b3d\uff1a\u304d\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u5fa1\uff1a\u307f\uff1a\u4ee3\uff1a\u3088\uff1a\u306b\u767e\uff1a\u304f\uff1a\u6e08\uff1a\u3060\u3089\uff1a\u306e\u8056\uff1a\u305b\u3044\uff1a\u660e\uff1a\u3081\u3044\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304b\u3089\u50b3\uff1a\u3067\u3093\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3057\u305f\u3068\u306e\u6587\uff1a\u3076\u3093\uff1a\u732e\uff1a\u3051\u3093\uff1a\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\n604,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e03\uff1a\u3057\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u61b2\uff1a\u3051\u3093\uff1a\u6cd5\uff1a\u307d\u3046\uff1a\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u304c\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\uff1a\u308f\uff1a\u3092\u4ee5\uff1a\u3082\u3063\uff1a\u3066\u8cb4\uff1a\u305f\u3075\u3068\uff1a\u3057\u3068\u70ba\uff1a\u306a\uff1a\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\uff1a\u306a\uff1a\u304d\u3092\u5b97\uff1a\u3080\u306d\uff1a\u3068\u305b\u3088>\n607,\u6cd5\uff1a\u307b\u3046\uff1a\u9686\uff1a\u308a\u3085\u3046\uff1a\u5bfa\uff1a\u3058\uff1a\u304c\u5275\uff1a\u305d\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u3086\u304b\u308a\u306e\u5bfa\uff1a\u3058\uff1a\u9662\uff1a\u3044\u3093\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u9662\uff1a\u3044\u3093\uff1a\u4f3d\uff1a\u304c\uff1a\u85cd\uff1a\u3089\u3093\uff1a\u306f\u73fe\uff1a\u3052\u3093\uff1a\u5b58\uff1a\u305e\u3093\uff1a\u3059\u308b\u4e16\u754c\u6700\uff1a\u3055\u3044\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u6728\uff1a\u3082\u304f\uff1a\u9020\uff1a\u305e\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u7bc9\uff1a\u3061\u304f\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\uff1a\u3044\u3063\uff1a\u5df3\uff1a\u3057\uff1a\u306e\u5909\uff1a\u3078\u3093\uff1a,\u3053\u306e\u5f8c\u3059\u3050\u5927\uff1a\u305f\u3044\uff1a\u5316\uff1a\u304b\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306a\u308b,\u4e2d\uff1a\u306a\u304b\u306e\uff1a\u5927\uff1a\u304a\u304a\uff1a\u5144\uff1a\u3048\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a(\u5f8c\u306e38\u4ee3\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687)\u304c\u8607\uff1a\u305d\uff1a\u6211\uff1a\u304c\uff1a\u6c0f\uff1a\u3057\uff1a\u3092\u4ea1\uff1a\u307b\u308d\uff1a\u307c\u3059\n663,\u767d\uff1a\u306f\u304f\uff1a\u6751\uff1a\u3059\u304d\u306e\uff1a\u6c5f\uff1a\u3048\uff1a\u306e\u6226\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u3068\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u306b\u6ec5\uff1a\u307b\u308d\uff1a\u307c\u3055\u308c\u305f\u767e\uff1a\u304f\u3060\uff1a\u6e08\uff1a\u3089\uff1a\u3092\u518d\uff1a\u3055\u3044\uff1a\u8208\uff1a\u3053\u3046\uff1a\u3059\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u30fb\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u3054\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u308b\n672,\u58ec\uff1a\u3058\u3093\uff1a\u7533\uff1a\u3057\u3093\uff1a\u306e\u4e71\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u4e89\uff1a\u3042\u3089\u305d\uff1a\u3072,\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u3067\u3042\u3063\u305f\u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u306b\u53d4\uff1a\u304a\uff1a\u7236\uff1a\u3058\uff1a\u306e\u5927\uff1a\u304a\u304a\uff1a\u6d77\uff1a\u3042\uff1a\u4eba\uff1a\u307e\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u304c\u53cd\uff1a\u306f\u3093\uff1a\u65d7\uff1a\u304d\uff1a\u3092\u7ffb\uff1a\u3072\u308b\u304c\u3078\uff1a\u3057 \u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u3066\u5929\uff1a\u3066\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b<\u82b1\u306e\u5fa1\u6240>\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075<\u4e0b\u524b\u4e0a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d <\u5929\u4e0b\u5e03\u6b66>\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b<\u9396\u56fd>\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c<\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4>\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b >>\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71) >>\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04 >>\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1EH=new T(function(){return B(_1EA(_1EG));}),_1EI=new T(function(){return B(_6k(_1Ev,_1EH));}),_1EJ=new T(function(){return B(_8V(1,2));}),_1EK=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b<\u4e0d\u5e73\u7b49>\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1882,\u58ec\u5348\u306e\u5909,\u4ff8\u7d66\u306e\u9045\u914d\u3092\u304d\u3063\u304b\u3051\u3068\u3057\u305f\u65e7\u5175\u306e\u66b4\u52d5\u3092\u5927\u9662\u541b\u304c\u717d\u52d5(\u5927\u9662\u541b\u306f\u65e7\u5b88\u6d3e \u9594\u5983\u4e00\u65cf\u306f\u958b\u5316\u6d3e),\u65e5\u97d3\u4fee\u4ea4\u4ee5\u964d \u9594\u5983\u4e00\u65cf\u306e\u958b\u5316\u6d3e\u304c\u529b\u3092\u306e\u3070\u3057 \u65e5\u672c\u306e\u8fd1\u4ee3\u5316\u306b\u5023\u306f\u3093\u3068 \u5927\u898f\u6a21\u306a\u8996\u5bdf\u56e3\u3092\u6d3e\u9063\u3057\u305f\u308a \u65e5\u672c\u304b\u3089\u5800\u672c\u793c\u9020\u3092\u62db\u3044\u3066\u65b0\u5f0f\u8ecd\u968a\u3092\u7de8\u6210\u3059\u308b\u306a\u3069\u8ecd\u653f\u6539\u9769\u3092\u65ad\u884c\u3057\u3066\u3090\u305f\u304c \u65e7\u5175\u3068\u5927\u9662\u541b\u306e\u53cd\u4e71\u306b\u3088\u308a \u591a\u6570\u306e\u65e5\u672c\u4eba\u304c\u8650\u6bba\u3055\u308c\u65e5\u672c\u516c\u4f7f\u9928\u304c\u8972\u6483\u3055\u308c\u305f(\u5800\u672c\u793c\u9020\u3082\u6bba\u3055\u308c\u308b) \u6e05\u570b\u306f\u7d04\u4e94\u5343\u306e\u5175\u3092\u304a\u304f\u308a\u4e71\u306e\u93ae\u5727\u306b\u5f53\u308b\u3068\u3068\u3082\u306b \u9996\u9b41\u3067\u3042\u308b\u5927\u9662\u541b\u3092\u6e05\u570b\u306b\u62c9\u81f4\u3057\u6291\u7559**\u3053\u306e\u4e8b\u5909\u306e\u5584\u5f8c\u7d04\u5b9a\u3068\u3057\u3066 \u65e5\u672c\u30fb\u671d\u9bae\u9593\u306b\u6e08\u7269\u6d66\u6761\u7d04\u304c\u7d50\u3070\u308c \u671d\u9bae\u5074\u306f\u72af\u4eba\u306e\u53b3\u7f70 \u8ce0\u511f\u91d1 \u516c\u4f7f\u9928\u8b66\u5099\u306e\u305f\u3081\u4eac\u57ce\u306b\u65e5\u672c\u8ecd\u82e5\u5e72\u3092\u7f6e\u304f \u65e5\u672c\u306b\u8b1d\u7f6a\u4f7f\u3092\u6d3e\u9063\u3059\u308b\u3053\u3068\u3092\u7d04\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,<\u6276\u6e05\u6ec5\u6d0b>\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***<\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287>\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b<\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42>,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059>\u30fc\u30fc\u5f8c\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059>"));}),_1EL=new T(function(){return B(_1EA(_1EK));}),_1EM=new T(function(){return B(_6k(_1Ev,_1EL));}),_1EN=function(_1EO,_1EP){var _1EQ=E(_1EO);if(!_1EQ._){return __Z;}else{var _1ER=E(_1EP);return (_1ER._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1EQ.a).a;}),_1ER.a),new T(function(){return B(_1EN(_1EQ.b,_1ER.b));}));}},_1ES=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1ET=new T(function(){return B(unCStr("tail"));}),_1EU=new T(function(){return B(_nk(_1ET));}),_1EV=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1EW=new T2(1,_2t,_S),_1EX=function(_1EY){var _1EZ=E(_1EY);if(!_1EZ._){return E(_1EW);}else{var _1F0=new T(function(){return B(_A(0,E(_1EZ.a),new T(function(){return B(_1EX(_1EZ.b));})));});return new T2(1,_2s,_1F0);}},_1F1=function(_1F2){var _1F3=E(_1F2);if(!_1F3._){return E(_1EW);}else{var _1F4=new T(function(){var _1F5=E(_1F3.a),_1F6=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1F7){return new F(function(){return _1DG(_1F5.a,_1F7);});},new T2(1,function(_1F8){return new F(function(){return _1DG(_1F5.b,_1F8);});},_S)),new T2(1,_y,new T(function(){return B(_1F1(_1F3.b));}))));});return new T2(1,_z,_1F6);});return new T2(1,_2s,_1F4);}},_1F9=function(_1Fa){var _1Fb=E(_1Fa);if(!_1Fb._){return E(_1EW);}else{var _1Fc=new T(function(){return B(_A(0,E(_1Fb.a),new T(function(){return B(_1F9(_1Fb.b));})));});return new T2(1,_2s,_1Fc);}},_1Fd=function(_1Fe){var _1Ff=E(_1Fe);if(!_1Ff._){return E(_1EW);}else{var _1Fg=new T(function(){var _1Fh=E(_1Ff.a),_1Fi=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1Fj){return new F(function(){return _1DG(_1Fh.a,_1Fj);});},new T2(1,function(_1Fk){return new F(function(){return _1DG(_1Fh.b,_1Fk);});},_S)),new T2(1,_y,new T(function(){return B(_1Fd(_1Ff.b));}))));});return new T2(1,_z,_1Fi);});return new T2(1,_2s,_1Fg);}},_1Fl=new T(function(){return B(unCStr("True"));}),_1Fm=new T(function(){return B(unCStr("False"));}),_1Fn=function(_1Fo){return E(E(_1Fo).b);},_1Fp=function(_1Fq,_1Fr,_1Fs){var _1Ft=new T(function(){var _1Fu=E(_1Fs);if(!_1Fu._){return __Z;}else{var _1Fv=_1Fu.b,_1Fw=E(_1Fu.a),_1Fx=E(_1Fw.a);if(_1Fx<_1Fq){var _1Fy=function(_1Fz){while(1){var _1FA=B((function(_1FB){var _1FC=E(_1FB);if(!_1FC._){return __Z;}else{var _1FD=_1FC.b,_1FE=E(_1FC.a);if(E(_1FE.a)<_1Fq){_1Fz=_1FD;return __continue;}else{return new T2(1,_1FE,new T(function(){return B(_1Fy(_1FD));}));}}})(_1Fz));if(_1FA!=__continue){return _1FA;}}};return B(_1FF(B(_1Fy(_1Fv))));}else{var _1FG=new T(function(){var _1FH=function(_1FI){while(1){var _1FJ=B((function(_1FK){var _1FL=E(_1FK);if(!_1FL._){return __Z;}else{var _1FM=_1FL.b,_1FN=E(_1FL.a);if(E(_1FN.a)<_1Fq){_1FI=_1FM;return __continue;}else{return new T2(1,_1FN,new T(function(){return B(_1FH(_1FM));}));}}})(_1FI));if(_1FJ!=__continue){return _1FJ;}}};return B(_1FH(_1Fv));});return B(_1Fp(_1Fx,_1Fw.b,_1FG));}}}),_1FO=E(_1Fs);if(!_1FO._){return new F(function(){return _q(_S,new T2(1,new T2(0,_1Fq,_1Fr),_1Ft));});}else{var _1FP=_1FO.b,_1FQ=E(_1FO.a),_1FR=E(_1FQ.a);if(_1FR>=_1Fq){var _1FS=function(_1FT){while(1){var _1FU=B((function(_1FV){var _1FW=E(_1FV);if(!_1FW._){return __Z;}else{var _1FX=_1FW.b,_1FY=E(_1FW.a);if(E(_1FY.a)>=_1Fq){_1FT=_1FX;return __continue;}else{return new T2(1,_1FY,new T(function(){return B(_1FS(_1FX));}));}}})(_1FT));if(_1FU!=__continue){return _1FU;}}};return new F(function(){return _q(B(_1FF(B(_1FS(_1FP)))),new T2(1,new T2(0,_1Fq,_1Fr),_1Ft));});}else{var _1FZ=new T(function(){var _1G0=function(_1G1){while(1){var _1G2=B((function(_1G3){var _1G4=E(_1G3);if(!_1G4._){return __Z;}else{var _1G5=_1G4.b,_1G6=E(_1G4.a);if(E(_1G6.a)>=_1Fq){_1G1=_1G5;return __continue;}else{return new T2(1,_1G6,new T(function(){return B(_1G0(_1G5));}));}}})(_1G1));if(_1G2!=__continue){return _1G2;}}};return B(_1G0(_1FP));});return new F(function(){return _q(B(_1Fp(_1FR,_1FQ.b,_1FZ)),new T2(1,new T2(0,_1Fq,_1Fr),_1Ft));});}}},_1FF=function(_1G7){var _1G8=E(_1G7);if(!_1G8._){return __Z;}else{var _1G9=_1G8.b,_1Ga=E(_1G8.a),_1Gb=_1Ga.a,_1Gc=new T(function(){var _1Gd=E(_1G9);if(!_1Gd._){return __Z;}else{var _1Ge=_1Gd.b,_1Gf=E(_1Gd.a),_1Gg=E(_1Gf.a),_1Gh=E(_1Gb);if(_1Gg<_1Gh){var _1Gi=function(_1Gj){while(1){var _1Gk=B((function(_1Gl){var _1Gm=E(_1Gl);if(!_1Gm._){return __Z;}else{var _1Gn=_1Gm.b,_1Go=E(_1Gm.a);if(E(_1Go.a)<_1Gh){_1Gj=_1Gn;return __continue;}else{return new T2(1,_1Go,new T(function(){return B(_1Gi(_1Gn));}));}}})(_1Gj));if(_1Gk!=__continue){return _1Gk;}}};return B(_1FF(B(_1Gi(_1Ge))));}else{var _1Gp=new T(function(){var _1Gq=function(_1Gr){while(1){var _1Gs=B((function(_1Gt){var _1Gu=E(_1Gt);if(!_1Gu._){return __Z;}else{var _1Gv=_1Gu.b,_1Gw=E(_1Gu.a);if(E(_1Gw.a)<_1Gh){_1Gr=_1Gv;return __continue;}else{return new T2(1,_1Gw,new T(function(){return B(_1Gq(_1Gv));}));}}})(_1Gr));if(_1Gs!=__continue){return _1Gs;}}};return B(_1Gq(_1Ge));});return B(_1Fp(_1Gg,_1Gf.b,_1Gp));}}}),_1Gx=E(_1G9);if(!_1Gx._){return new F(function(){return _q(_S,new T2(1,_1Ga,_1Gc));});}else{var _1Gy=_1Gx.b,_1Gz=E(_1Gx.a),_1GA=E(_1Gz.a),_1GB=E(_1Gb);if(_1GA>=_1GB){var _1GC=function(_1GD){while(1){var _1GE=B((function(_1GF){var _1GG=E(_1GF);if(!_1GG._){return __Z;}else{var _1GH=_1GG.b,_1GI=E(_1GG.a);if(E(_1GI.a)>=_1GB){_1GD=_1GH;return __continue;}else{return new T2(1,_1GI,new T(function(){return B(_1GC(_1GH));}));}}})(_1GD));if(_1GE!=__continue){return _1GE;}}};return new F(function(){return _q(B(_1FF(B(_1GC(_1Gy)))),new T2(1,_1Ga,_1Gc));});}else{var _1GJ=new T(function(){var _1GK=function(_1GL){while(1){var _1GM=B((function(_1GN){var _1GO=E(_1GN);if(!_1GO._){return __Z;}else{var _1GP=_1GO.b,_1GQ=E(_1GO.a);if(E(_1GQ.a)>=_1GB){_1GL=_1GP;return __continue;}else{return new T2(1,_1GQ,new T(function(){return B(_1GK(_1GP));}));}}})(_1GL));if(_1GM!=__continue){return _1GM;}}};return B(_1GK(_1Gy));});return new F(function(){return _q(B(_1Fp(_1GA,_1Gz.b,_1GJ)),new T2(1,_1Ga,_1Gc));});}}}},_1GR=function(_){return new F(function(){return jsMkStdout();});},_1GS=new T(function(){return B(_36(_1GR));}),_1GT=new T(function(){return B(_Lv("Browser.hs:82:24-56|(Right j)"));}),_1GU=function(_1GV){var _1GW=jsParseJSON(toJSStr(E(_1GV)));return (_1GW._==0)?E(_1GT):E(_1GW.a);},_1GX=function(_1GY,_1GZ,_1H0,_1H1,_1H2,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI,_){var _1HJ={_:0,a:E(_1HA),b:E(_1HB),c:E(_1HC),d:E(_1HD),e:E(_1HE),f:E(_1HF),g:E(_1HG),h:E(_1HH)},_1HK=new T2(0,_1Hx,_1Hy),_1HL=new T2(0,_1Hl,_1Hm),_1HM=new T2(0,_1He,_1Hf),_1HN={_:0,a:E(_1H3),b:E(_1H4),c:E(_1H5),d:_1H6,e:_1H7,f:_1H8,g:E(_1H9),h:_1Ha,i:E(_1Hb),j:E(_1Hc),k:E(_1Hd)},_1HO={_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:_1Hs,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};if(!E(_1HF)){var _1HP=function(_1HQ){if(!E(_1HD)){if(!E(_1HH)){return _1HO;}else{var _1HR=function(_,_1HS,_1HT,_1HU,_1HV,_1HW,_1HX,_1HY,_1HZ,_1I0,_1I1,_1I2,_1I3,_1I4,_1I5,_1I6,_1I7,_1I8,_1I9,_1Ia,_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In,_1Io){var _1Ip=function(_){var _1Iq=function(_){var _1Ir=function(_){var _1Is=B(_1CZ(_1GS,new T2(1,_6J,new T(function(){return B(_8q(_1I0,_1DW));})),_)),_1It=function(_){var _1Iu=B(_1CZ(_1GS,B(_A(0,_1Hq,_S)),_)),_1Iv=B(_1CZ(_1GS,B(_2v(_1DJ,_1HY,_S)),_)),_1Iw=function(_){var _1Ix=B(_1aE(_1Df,_1HZ,_)),_1Iy=_1Ix,_1Iz=E(_1GY),_1IA=_1Iz.a,_1IB=_1Iz.b,_1IC=new T(function(){return B(_1rT(E(_1H2)));}),_1ID=new T(function(){var _1IE=E(_1IC),_1IF=E(_1HS),_1IG=_1IF.a,_1IH=_1IF.b,_1II=function(_1IJ,_1IK){var _1IL=E(_1IJ),_1IM=E(_1IK),_1IN=E(_1IG);if(_1IL<=_1IN){if(_1IN<=_1IL){var _1IO=E(_1IH);if(_1IM<=_1IO){if(_1IO<=_1IM){var _1IP=4;}else{var _1IP=0;}var _1IQ=_1IP;}else{var _1IQ=1;}var _1IR=_1IQ;}else{var _1IR=2;}var _1IS=_1IR;}else{var _1IS=3;}var _1IT=function(_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3){switch(E(_1IS)){case 0:if(!E(_1HU)){var _1J4=new T2(0,_1Ik,_1Il);}else{var _1J4=new T2(0,_1Ik,_1DZ);}var _1J5=_1J4;break;case 1:if(E(_1HU)==1){var _1J6=new T2(0,_1Ik,_1Il);}else{var _1J6=new T2(0,_1Ik,_1Ds);}var _1J5=_1J6;break;case 2:if(E(_1HU)==2){var _1J7=new T2(0,_1Ik,_1Il);}else{var _1J7=new T2(0,_1Ik,_1Du);}var _1J5=_1J7;break;case 3:if(E(_1HU)==3){var _1J8=new T2(0,_1Ik,_1Il);}else{var _1J8=new T2(0,_1Ik,_1Dt);}var _1J5=_1J8;break;default:if(E(_1HU)==4){var _1J9=new T2(0,_1Ik,_1Il);}else{var _1J9=new T2(0,_1Ik,_1Ds);}var _1J5=_1J9;}var _1Ja=B(_1oE(_1Ds,_1J1,_1I6,{_:0,a:E(_1IU),b:E(_1IV),c:E(_1IW),d:_1IX,e:_1IY,f:_1IZ,g:E(_1J0),h:E(E(_1Iy).b),i:E(_1J1),j:E(_1J2),k:E(_1J3)},_1I3,_1I4,_1I5,_1I6,_1I7,_1I8,_1I9,_1Ia,_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1J5,_1Im,_1In,_1Io)),_1Jb=_1Ja.a,_1Jc=_1Ja.b,_1Jd=_1Ja.c,_1Je=_1Ja.d,_1Jf=_1Ja.e,_1Jg=_1Ja.f,_1Jh=_1Ja.g,_1Ji=_1Ja.h,_1Jj=_1Ja.i,_1Jk=_1Ja.j,_1Jl=_1Ja.k,_1Jm=_1Ja.l,_1Jn=_1Ja.m,_1Jo=_1Ja.n,_1Jp=_1Ja.o,_1Jq=_1Ja.q,_1Jr=_1Ja.r,_1Js=_1Ja.s,_1Jt=_1Ja.t,_1Ju=_1Ja.u,_1Jv=_1Ja.v,_1Jw=E(_1Ja.p);if(!_1Jw._){return {_:0,a:E(_1Jb),b:E(_1Jc),c:E(_1Jd),d:E(_1Je),e:E(_1Jf),f:E(_1Jg),g:E(_1Jh),h:E(_1Ji),i:_1Jj,j:_1Jk,k:_1Jl,l:_1Jm,m:E(_1Jn),n:_1Jo,o:E(_1Jp),p:E(_S),q:_1Jq,r:E(_1Jr),s:E(_1Js),t:_1Jt,u:E(_1Ju),v:E(_1Jv)};}else{var _1Jx=B(_mz(_1J1,0))-2|0,_1Jy=function(_1Jz){var _1JA=E(_1Jb);return {_:0,a:E({_:0,a:E(_1JA.a),b:E(_1JA.b),c:E(_1JA.c),d:_1JA.d,e:_1JA.e,f:_1JA.f,g:E(_S),h:_1JA.h,i:E(_1JA.i),j:E(_1JA.j),k:E(_1JA.k)}),b:E(_1Jc),c:E(_1Jd),d:E(B(_q(B(_68(_S,B(_1CP(B(_6k(_1Fn,_1Jw)),B(_15m(_1Je)))))),new T(function(){return B(_6k(_1BN,_1Jw));},1)))),e:E(_1Jf),f:E(_1Jg),g:E(_1Jh),h:E(_1Ji),i:_1Jj,j:_1Jk,k:_1Jl,l:_1Jm,m:E(_1Jn),n:_1Jo,o:E(_1Jp),p:E(_S),q:_1Jq,r:E(B(_q(_1Jr,new T2(1,_1Jq,_S)))),s:E(_1Js),t:_1Jt,u:E(_1Ju),v:E(_1Jv)};};if(_1Jx>0){if(!B(_qW(B(_1Bw(_1Jx,_1J1)),_1Dr))){return {_:0,a:E(_1Jb),b:E(_1Jc),c:E(_1Jd),d:E(_1Je),e:E(_1Jf),f:E(_1Jg),g:E(_1Jh),h:E(_1Ji),i:_1Jj,j:_1Jk,k:_1Jl,l:_1Jm,m:E(_1Jn),n:_1Jo,o:E(_1Jp),p:E(_1Jw),q:_1Jq,r:E(_1Jr),s:E(_1Js),t:_1Jt,u:E(_1Ju),v:E(_1Jv)};}else{return new F(function(){return _1Jy(_);});}}else{if(!B(_qW(_1J1,_1Dr))){return {_:0,a:E(_1Jb),b:E(_1Jc),c:E(_1Jd),d:E(_1Je),e:E(_1Jf),f:E(_1Jg),g:E(_1Jh),h:E(_1Ji),i:_1Jj,j:_1Jk,k:_1Jl,l:_1Jm,m:E(_1Jn),n:_1Jo,o:E(_1Jp),p:E(_1Jw),q:_1Jq,r:E(_1Jr),s:E(_1Js),t:_1Jt,u:E(_1Ju),v:E(_1Jv)};}else{return new F(function(){return _1Jy(_);});}}}};if(E(_1IE)==32){var _1JB=B(_1xM(_1IL,_1IM,_1IN,_1IH,_1HT,_1IS,_1HV,_1HW,_1HX,_1HY,_1HZ,_1I0,_1I1,_1I2)),_1JC=E(_1JB.a),_1JD=B(_1B7(_1JC.a,E(_1JC.b),_1JB.b,_1JB.c,_1JB.d,_1JB.e,_1JB.f,_1JB.g,_1JB.h,_1JB.i,_1JB.j,_1JB.k));return new F(function(){return _1IT(_1JD.a,_1JD.b,_1JD.c,_1JD.d,_1JD.e,_1JD.f,_1JD.g,_1JD.i,_1JD.j,_1JD.k);});}else{var _1JE=B(_1xM(_1IL,_1IM,_1IN,_1IH,_1HT,_1IS,_1HV,_1HW,_1HX,_1HY,_1HZ,_1I0,_1I1,_1I2));return new F(function(){return _1IT(_1JE.a,_1JE.b,_1JE.c,_1JE.d,_1JE.e,_1JE.f,_1JE.g,_1JE.i,_1JE.j,_1JE.k);});}};switch(E(_1IE)){case 72:var _1JF=E(_1IH);if(0<=(_1JF-1|0)){return B(_1II(_1IG,_1JF-1|0));}else{return B(_1II(_1IG,_1JF));}break;case 75:var _1JG=E(_1IG);if(0<=(_1JG-1|0)){return B(_1II(_1JG-1|0,_1IH));}else{return B(_1II(_1JG,_1IH));}break;case 77:var _1JH=E(_1IG);if(E(_1He)!=(_1JH+1|0)){return B(_1II(_1JH+1|0,_1IH));}else{return B(_1II(_1JH,_1IH));}break;case 80:var _1JI=E(_1IH);if(E(_1Hf)!=(_1JI+1|0)){return B(_1II(_1IG,_1JI+1|0));}else{return B(_1II(_1IG,_1JI));}break;case 104:var _1JJ=E(_1IG);if(0<=(_1JJ-1|0)){return B(_1II(_1JJ-1|0,_1IH));}else{return B(_1II(_1JJ,_1IH));}break;case 106:var _1JK=E(_1IH);if(E(_1Hf)!=(_1JK+1|0)){return B(_1II(_1IG,_1JK+1|0));}else{return B(_1II(_1IG,_1JK));}break;case 107:var _1JL=E(_1IH);if(0<=(_1JL-1|0)){return B(_1II(_1IG,_1JL-1|0));}else{return B(_1II(_1IG,_1JL));}break;case 108:var _1JM=E(_1IG);if(E(_1He)!=(_1JM+1|0)){return B(_1II(_1JM+1|0,_1IH));}else{return B(_1II(_1JM,_1IH));}break;default:return B(_1II(_1IG,_1IH));}}),_1JN=B(_1d7(_1IA,_1IB,_1GZ,_1H0,_1H1,_1ID,_)),_1JO=_1JN,_1JP=E(_1IC),_1JQ=function(_,_1JR){var _1JS=function(_1JT){var _1JU=B(_1CZ(_1GS,B(_8w(_1JR)),_)),_1JV=E(_1JO),_1JW=_1JV.d,_1JX=_1JV.e,_1JY=_1JV.f,_1JZ=_1JV.g,_1K0=_1JV.i,_1K1=_1JV.j,_1K2=_1JV.k,_1K3=_1JV.l,_1K4=_1JV.m,_1K5=_1JV.n,_1K6=_1JV.o,_1K7=_1JV.p,_1K8=_1JV.q,_1K9=_1JV.r,_1Ka=_1JV.t,_1Kb=_1JV.v,_1Kc=E(_1JV.u),_1Kd=_1Kc.a,_1Ke=_1Kc.d,_1Kf=_1Kc.e,_1Kg=_1Kc.f,_1Kh=_1Kc.g,_1Ki=_1Kc.h,_1Kj=E(_1JV.a),_1Kk=_1Kj.c,_1Kl=_1Kj.f,_1Km=_1Kj.g,_1Kn=_1Kj.h,_1Ko=E(_1JV.h),_1Kp=E(_1JV.s),_1Kq=function(_1Kr){var _1Ks=function(_1Kt){if(_1Kt!=E(_1Dk)){var _1Ku=B(_6X(_1kk,_1Kt)),_1Kv=_1Ku.a,_1Kw=E(_1Ku.b),_1Kx=B(_1fC(_1Kv,_1Kw,new T(function(){return B(_6X(_1mp,_1Kt));})));return new F(function(){return _1GX(_1Iz,_1GZ,_1H0,_1H1,_1Dj,B(_6X(_1kv,_1Kt)),_1Kx,_1Kk,B(_6X(_1kI,_1Kt)),32,_1Kt,_1Km,_1Kn,B(_q(_1Kj.i,new T2(1,_1Di,new T(function(){return B(_A(0,_1Kl,_S));})))),B(_1BW(_1Dh,_1Kx)),_wD,_1Kv,_1Kw,_S,_1JW,_1JX,_1JY,_1JZ,_1Ko.a,_1Ko.b,_1K0,_1K1,_1K2, -1,_1K4,_1K5,_1K6,_1K7,_1K8,_1K9,_1Kp.a,_1Kp.b,_1Ka,_wD,_wD,_wD,_1Ke,_1Kf,_1Kg,_1Kh,_1Ki,_1Kb,_);});}else{var _1Ky=__app1(E(_no),_1IB),_1Kz=B(A2(_np,_1IA,_)),_1KA=B(A(_mU,[_1IA,_j9,_1DZ,_1Df,_1De,_])),_1KB=B(A(_mU,[_1IA,_j9,_1Dd,_1Dc,_1E0,_])),_1KC=B(A(_mU,[_1IA,_j9,_1DZ,_1DY,_1DX,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1km),b:E(_1DV),c:E(_1Kk),d:E(_1DA),e:32,f:0,g:E(_1Km),h:_1Kn,i:E(_S),j:E(_1Kj.j),k:E(_wD)}),b:E(_1k7),c:E(_1JV.c),d:E(_1JW),e:E(_1JX),f:E(_1JY),g:E(_1JZ),h:E(_1Ko),i:_1K0,j:_1K1,k:_1K2,l:_1K3,m:E(_1K4),n:_1K5,o:E(_1K6),p:E(_1K7),q:_1K8,r:E(_1K9),s:E(_1Kp),t:_1Ka,u:E({_:0,a:E(_1Kd),b:E(_wD),c:E(_wD),d:E(_1Ke),e:E(_1Kf),f:E(_1Kg),g:E(_1Kh),h:E(_1Ki)}),v:E(_1Kb)};});}};if(_1K3>=0){return new F(function(){return _1Ks(_1K3);});}else{return new F(function(){return _1Ks(_1Kl+1|0);});}};if(!E(_1Kd)){if(E(_1JP)==110){return new F(function(){return _1Kq(_);});}else{return _1JV;}}else{return new F(function(){return _1Kq(_);});}};if(E(_1JP)==114){if(!B(_6f(_1JR,_1Dl))){var _1KD=E(_1JR);if(!_1KD._){return _1JO;}else{var _1KE=_1KD.b;return new T(function(){var _1KF=E(_1JO),_1KG=E(_1KF.a),_1KH=E(_1KD.a),_1KI=E(_1KH);if(_1KI==34){var _1KJ=B(_TO(_1KH,_1KE));if(!_1KJ._){var _1KK=E(_1EU);}else{var _1KL=E(_1KJ.b);if(!_1KL._){var _1KM=E(_1DE);}else{var _1KN=_1KL.a,_1KO=E(_1KL.b);if(!_1KO._){var _1KP=new T2(1,new T2(1,_1KN,_S),_S);}else{var _1KQ=E(_1KN),_1KR=new T(function(){var _1KS=B(_Hd(126,_1KO.a,_1KO.b));return new T2(0,_1KS.a,_1KS.b);});if(E(_1KQ)==126){var _1KT=new T2(1,_S,new T2(1,new T(function(){return E(E(_1KR).a);}),new T(function(){return E(E(_1KR).b);})));}else{var _1KT=new T2(1,new T2(1,_1KQ,new T(function(){return E(E(_1KR).a);})),new T(function(){return E(E(_1KR).b);}));}var _1KP=_1KT;}var _1KM=_1KP;}var _1KK=_1KM;}var _1KU=_1KK;}else{var _1KV=E(_1KE);if(!_1KV._){var _1KW=new T2(1,new T2(1,_1KH,_S),_S);}else{var _1KX=new T(function(){var _1KY=B(_Hd(126,_1KV.a,_1KV.b));return new T2(0,_1KY.a,_1KY.b);});if(E(_1KI)==126){var _1KZ=new T2(1,_S,new T2(1,new T(function(){return E(E(_1KX).a);}),new T(function(){return E(E(_1KX).b);})));}else{var _1KZ=new T2(1,new T2(1,_1KH,new T(function(){return E(E(_1KX).a);})),new T(function(){return E(E(_1KX).b);}));}var _1KW=_1KZ;}var _1KU=_1KW;}var _1L0=B(_Gl(B(_sI(_1Dm,new T(function(){return B(_Js(_1KU));})))));if(!_1L0._){return E(_1Da);}else{if(!E(_1L0.b)._){var _1L1=E(_1L0.a),_1L2=B(_6X(_1kk,_1L1)),_1L3=B(_6X(_1KU,1));if(!_1L3._){var _1L4=__Z;}else{var _1L5=E(_1L3.b);if(!_1L5._){var _1L6=__Z;}else{var _1L7=E(_1L3.a),_1L8=new T(function(){var _1L9=B(_Hd(44,_1L5.a,_1L5.b));return new T2(0,_1L9.a,_1L9.b);});if(E(_1L7)==44){var _1La=B(_15B(_S,new T(function(){return E(E(_1L8).a);}),new T(function(){return E(E(_1L8).b);})));}else{var _1La=B(_15F(new T2(1,_1L7,new T(function(){return E(E(_1L8).a);})),new T(function(){return E(E(_1L8).b);})));}var _1L6=_1La;}var _1L4=_1L6;}var _1Lb=B(_6X(_1KU,2));if(!_1Lb._){var _1Lc=E(_1DF);}else{var _1Ld=_1Lb.a,_1Le=E(_1Lb.b);if(!_1Le._){var _1Lf=B(_6k(_1Dx,new T2(1,new T2(1,_1Ld,_S),_S)));}else{var _1Lg=E(_1Ld),_1Lh=new T(function(){var _1Li=B(_Hd(44,_1Le.a,_1Le.b));return new T2(0,_1Li.a,_1Li.b);});if(E(_1Lg)==44){var _1Lj=B(_6k(_1Dx,new T2(1,_S,new T2(1,new T(function(){return E(E(_1Lh).a);}),new T(function(){return E(E(_1Lh).b);})))));}else{var _1Lj=B(_6k(_1Dx,new T2(1,new T2(1,_1Lg,new T(function(){return E(E(_1Lh).a);})),new T(function(){return E(E(_1Lh).b);}))));}var _1Lf=_1Lj;}var _1Lc=_1Lf;}return {_:0,a:E({_:0,a:E(B(_6X(_1kv,_1L1))),b:E(B(_1fC(_1L2.a,E(_1L2.b),new T(function(){return B(_6X(_1mp,_1L1));})))),c:E(_1KG.c),d:B(_6X(_1kI,_1L1)),e:32,f:_1L1,g:E(_1KG.g),h:_1KG.h,i:E(_1KG.i),j:E(_1KG.j),k:E(_1KG.k)}),b:E(_1L2),c:E(_1KF.c),d:E(_1KF.d),e:E(_1L4),f:E(_1Lc),g:E(_1KF.g),h:E(_1KF.h),i:_1KF.i,j:_1KF.j,k:_1KF.k,l:_1KF.l,m:E(_1KF.m),n:_1KF.n,o:E(_1KF.o),p:E(_1KF.p),q:_1KF.q,r:E(_1KF.r),s:E(_1KF.s),t:_1KF.t,u:E(_1KF.u),v:E(_1KF.v)};}else{return E(_1Db);}}});}}else{return new F(function(){return _1JS(_);});}}else{return new F(function(){return _1JS(_);});}};switch(E(_1JP)){case 100:var _1Lk=__app1(E(_1ES),toJSStr(E(_1Dp)));return new F(function(){return _1JQ(_,_1D7);});break;case 114:var _1Ll=B(_15Q(_6C,toJSStr(E(_1Dp)),_));return new F(function(){return _1JQ(_,new T(function(){var _1Lm=E(_1Ll);if(!_1Lm._){return E(_1D8);}else{return fromJSStr(B(_1qT(_1Lm.a)));}}));});break;case 115:var _1Ln=new T(function(){var _1Lo=new T(function(){var _1Lp=new T(function(){var _1Lq=B(_6k(_6H,_1Hj));if(!_1Lq._){return __Z;}else{return B(_1D4(new T2(1,_1Lq.a,new T(function(){return B(_1E1(_1Dn,_1Lq.b));}))));}}),_1Lr=new T(function(){var _1Ls=function(_1Lt){var _1Lu=E(_1Lt);if(!_1Lu._){return __Z;}else{var _1Lv=E(_1Lu.a);return new T2(1,_1Lv.a,new T2(1,_1Lv.b,new T(function(){return B(_1Ls(_1Lu.b));})));}},_1Lw=B(_1Ls(_1Hi));if(!_1Lw._){return __Z;}else{return B(_1D4(new T2(1,_1Lw.a,new T(function(){return B(_1E1(_1Dn,_1Lw.b));}))));}});return B(_1E1(_1Do,new T2(1,_1Lr,new T2(1,_1Lp,_S))));});return B(_q(B(_1D4(new T2(1,new T(function(){return B(_A(0,_1H8,_S));}),_1Lo))),_1DD));}),_1Lx=__app2(E(_1EV),toJSStr(E(_1Dp)),B(_1qT(B(_1GU(B(unAppCStr("\"",_1Ln)))))));return new F(function(){return _1JQ(_,_1D9);});break;default:return new F(function(){return _1JQ(_,_1Dq);});}},_1Ly=E(_1Hw);if(!_1Ly._){var _1Lz=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Iw(_);});}else{var _1LA=new T(function(){return B(_A(0,E(_1Ly.a),new T(function(){return B(_1EX(_1Ly.b));})));}),_1LB=B(_1CZ(_1GS,new T2(1,_2u,_1LA),_));return new F(function(){return _1Iw(_);});}};if(!E(_1I2)){var _1LC=B(_1CZ(_1GS,_1Fm,_));return new F(function(){return _1It(_);});}else{var _1LD=B(_1CZ(_1GS,_1Fl,_));return new F(function(){return _1It(_);});}},_1LE=E(_1Hk);if(!_1LE._){var _1LF=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Ir(_);});}else{var _1LG=new T(function(){var _1LH=E(_1LE.a),_1LI=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1LJ){return new F(function(){return _1DG(_1LH.a,_1LJ);});},new T2(1,function(_1LK){return new F(function(){return _1DG(_1LH.b,_1LK);});},_S)),new T2(1,_y,new T(function(){return B(_1F1(_1LE.b));}))));});return new T2(1,_z,_1LI);}),_1LL=B(_1CZ(_1GS,new T2(1,_2u,_1LG),_));return new F(function(){return _1Ir(_);});}},_1LM=E(_1Hj);if(!_1LM._){var _1LN=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Iq(_);});}else{var _1LO=new T(function(){return B(_A(0,E(_1LM.a),new T(function(){return B(_1F9(_1LM.b));})));}),_1LP=B(_1CZ(_1GS,new T2(1,_2u,_1LO),_));return new F(function(){return _1Iq(_);});}},_1LQ=E(_1Hi);if(!_1LQ._){var _1LR=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Ip(_);});}else{var _1LS=new T(function(){var _1LT=E(_1LQ.a),_1LU=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1LV){return new F(function(){return _1DG(_1LT.a,_1LV);});},new T2(1,function(_1LW){return new F(function(){return _1DG(_1LT.b,_1LW);});},_S)),new T2(1,_y,new T(function(){return B(_1Fd(_1LQ.b));}))));});return new T2(1,_z,_1LU);}),_1LX=B(_1CZ(_1GS,new T2(1,_2u,_1LS),_));return new F(function(){return _1Ip(_);});}},_1LY=E(_1Ht);if(!_1LY._){return new F(function(){return _1HR(_,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1HM,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HJ,_1HI);});}else{var _1LZ=E(_1LY.b);if(!_1LZ._){return new F(function(){return _1HR(_,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1HM,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HJ,_1HI);});}else{var _1M0=E(_1LZ.b);if(!_1M0._){return new F(function(){return _1HR(_,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1HM,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HJ,_1HI);});}else{var _1M1=_1M0.a,_1M2=E(_1M0.b);if(!_1M2._){return new F(function(){return _1HR(_,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1HM,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HJ,_1HI);});}else{if(!E(_1M2.b)._){var _1M3=B(_1bZ(B(_mz(_1M1,0)),_1Ha,new T(function(){var _1M4=B(_Gl(B(_sI(_1Dm,_1LY.a))));if(!_1M4._){return E(_1EI);}else{if(!E(_1M4.b)._){if(E(_1M4.a)==2){return E(_1EM);}else{return E(_1EI);}}else{return E(_1EI);}}}),_)),_1M5=E(_1M3),_1M6=_1M5.a,_1M7=new T(function(){var _1M8=new T(function(){return B(_6k(function(_1M9){var _1Ma=B(_st(_3L,_1M9,B(_Gx(_1Dw,_1M1))));return (_1Ma._==0)?E(_1Dg):E(_1Ma.a);},B(_6k(_1Fn,B(_1FF(B(_1EN(_1M6,_1EJ))))))));}),_1Mb=B(_Gx(_1M6,_1M1)),_1Mc=B(_Ue(B(unAppCStr("e.==.m1:",_1M2.a)),{_:0,a:E(_1H3),b:E(_1H4),c:E(_1H5),d:_1H6,e:_1H7,f:_1H8,g:E(B(_q(_1H9,new T2(1,new T2(0,new T2(0,_1LZ.a,_1Dv),_1H8),new T2(1,new T2(0,new T2(0,_1M8,_1Dv),_1H8),_S))))),h:E(_1M5.b),i:E(_1Hb),j:E(_1Hc),k:E(_1Hd)},_1HM,_1Hg,B(_q(B(_68(_S,B(_1CP(_1M1,B(_15m(_1Hh)))))),new T(function(){return B(_6k(_1BS,_1Mb));},1))),_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,E(_1Mb),0,_1Hw,_1HK,_1Hz,_1HJ,_1HI)),_1Md=B(_1r4(_1M1,_1Mc.a,_1Mc.b,_1Mc.c,_1Mc.d,_1Mc.e,_1Mc.f,_1Mc.g,_1Mc.h,_1Mc.i,_1Mc.j,_1Mc.k,_1Mc.l,_1Mc.m,_1Mc.n,_1Mc.o,_1Mc.p,_1Mc.q,_1Mc.r,_1Mc.s,_1Mc.t,_1Mc.u,_1Mc.v));return {_:0,a:E(_1Md.a),b:E(_1Md.b),c:E(_1Md.c),d:E(_1Md.d),e:E(_1Md.e),f:E(_1Md.f),g:E(_1Md.g),h:E(_1Md.h),i:_1Md.i,j:_1Md.j,k:_1Md.k,l:_1Md.l,m:E(_1Md.m),n:_1Md.n,o:E(_1Md.o),p:E(_1Md.p),q:_1Md.q,r:E(_1Md.r),s:E(_1Md.s),t:_1Md.t,u:E(_1Md.u),v:E(_1Md.v)};}),_1Me=function(_){var _1Mf=function(_){var _1Mg=function(_){var _1Mh=new T(function(){var _1Mi=E(E(_1M7).a);return new T6(0,_1Mi,_1Mi.a,_1Mi.g,_1Mi.h,_1Mi.i,_1Mi.k);}),_1Mj=B(_1CZ(_1GS,new T2(1,_6J,new T(function(){return B(_8q(E(_1Mh).e,_1DW));})),_)),_1Mk=E(_1Mh),_1Ml=_1Mk.a,_1Mm=function(_){var _1Mn=B(_1CZ(_1GS,B(_A(0,_1Hq,_S)),_)),_1Mo=B(_1CZ(_1GS,B(_2v(_1DJ,_1Mk.c,_S)),_)),_1Mp=function(_){var _1Mq=B(_1aE(_1Df,_1Mk.d,_)),_1Mr=E(_1Mq).b,_1Ms=E(_1GY),_1Mt=_1Ms.a,_1Mu=_1Ms.b,_1Mv=new T(function(){return B(_1rT(E(_1H2)));}),_1Mw=new T(function(){var _1Mx=E(_1M7),_1My=_1Mx.b,_1Mz=_1Mx.c,_1MA=_1Mx.d,_1MB=_1Mx.e,_1MC=_1Mx.f,_1MD=_1Mx.g,_1ME=_1Mx.h,_1MF=_1Mx.i,_1MG=_1Mx.j,_1MH=_1Mx.k,_1MI=_1Mx.l,_1MJ=_1Mx.m,_1MK=_1Mx.n,_1ML=_1Mx.o,_1MM=_1Mx.p,_1MN=_1Mx.q,_1MO=_1Mx.r,_1MP=_1Mx.t,_1MQ=_1Mx.u,_1MR=_1Mx.v,_1MS=E(_1Mx.s),_1MT=_1MS.a,_1MU=_1MS.b,_1MV=E(_1Mv),_1MW=E(_1Mk.b),_1MX=_1MW.a,_1MY=_1MW.b,_1MZ=function(_1N0,_1N1){var _1N2=E(_1N0),_1N3=E(_1MX);if(_1N2<=_1N3){if(_1N3<=_1N2){var _1N4=E(_1MY);if(_1N1<=_1N4){if(_1N4<=_1N1){var _1N5=4;}else{var _1N5=0;}var _1N6=_1N5;}else{var _1N6=1;}var _1N7=_1N6;}else{var _1N7=2;}var _1N8=_1N7;}else{var _1N8=3;}var _1N9=function(_1Na,_1Nb,_1Nc,_1Nd,_1Ne,_1Nf,_1Ng,_1Nh,_1Ni,_1Nj){switch(E(_1N8)){case 0:if(!E(E(_1Ml).c)){var _1Nk=new T2(0,_1MT,_1MU);}else{var _1Nk=new T2(0,_1MT,_1DZ);}var _1Nl=_1Nk;break;case 1:if(E(E(_1Ml).c)==1){var _1Nm=new T2(0,_1MT,_1MU);}else{var _1Nm=new T2(0,_1MT,_1Ds);}var _1Nl=_1Nm;break;case 2:if(E(E(_1Ml).c)==2){var _1Nn=new T2(0,_1MT,_1MU);}else{var _1Nn=new T2(0,_1MT,_1Du);}var _1Nl=_1Nn;break;case 3:if(E(E(_1Ml).c)==3){var _1No=new T2(0,_1MT,_1MU);}else{var _1No=new T2(0,_1MT,_1Dt);}var _1Nl=_1No;break;default:if(E(E(_1Ml).c)==4){var _1Np=new T2(0,_1MT,_1MU);}else{var _1Np=new T2(0,_1MT,_1Ds);}var _1Nl=_1Np;}var _1Nq=B(_1oE(_1Ds,_1Nh,_1MB,{_:0,a:E(_1Na),b:E(_1Nb),c:E(_1Nc),d:_1Nd,e:_1Ne,f:_1Nf,g:E(_1Ng),h:E(_1Mr),i:E(_1Nh),j:E(_1Ni),k:E(_1Nj)},_1My,_1Mz,_1MA,_1MB,_1MC,_1MD,_1ME,_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1Nl,_1MP,_1MQ,_1MR)),_1Nr=_1Nq.a,_1Ns=_1Nq.b,_1Nt=_1Nq.c,_1Nu=_1Nq.d,_1Nv=_1Nq.e,_1Nw=_1Nq.f,_1Nx=_1Nq.g,_1Ny=_1Nq.h,_1Nz=_1Nq.i,_1NA=_1Nq.j,_1NB=_1Nq.k,_1NC=_1Nq.l,_1ND=_1Nq.m,_1NE=_1Nq.n,_1NF=_1Nq.o,_1NG=_1Nq.q,_1NH=_1Nq.r,_1NI=_1Nq.s,_1NJ=_1Nq.t,_1NK=_1Nq.u,_1NL=_1Nq.v,_1NM=E(_1Nq.p);if(!_1NM._){return {_:0,a:E(_1Nr),b:E(_1Ns),c:E(_1Nt),d:E(_1Nu),e:E(_1Nv),f:E(_1Nw),g:E(_1Nx),h:E(_1Ny),i:_1Nz,j:_1NA,k:_1NB,l:_1NC,m:E(_1ND),n:_1NE,o:E(_1NF),p:E(_S),q:_1NG,r:E(_1NH),s:E(_1NI),t:_1NJ,u:E(_1NK),v:E(_1NL)};}else{var _1NN=B(_mz(_1Nh,0))-2|0,_1NO=function(_1NP){var _1NQ=E(_1Nr);return {_:0,a:E({_:0,a:E(_1NQ.a),b:E(_1NQ.b),c:E(_1NQ.c),d:_1NQ.d,e:_1NQ.e,f:_1NQ.f,g:E(_S),h:_1NQ.h,i:E(_1NQ.i),j:E(_1NQ.j),k:E(_1NQ.k)}),b:E(_1Ns),c:E(_1Nt),d:E(B(_q(B(_68(_S,B(_1CP(B(_6k(_1Fn,_1NM)),B(_15m(_1Nu)))))),new T(function(){return B(_6k(_1BN,_1NM));},1)))),e:E(_1Nv),f:E(_1Nw),g:E(_1Nx),h:E(_1Ny),i:_1Nz,j:_1NA,k:_1NB,l:_1NC,m:E(_1ND),n:_1NE,o:E(_1NF),p:E(_S),q:_1NG,r:E(B(_q(_1NH,new T2(1,_1NG,_S)))),s:E(_1NI),t:_1NJ,u:E(_1NK),v:E(_1NL)};};if(_1NN>0){if(!B(_qW(B(_1Bw(_1NN,_1Nh)),_1Dr))){return {_:0,a:E(_1Nr),b:E(_1Ns),c:E(_1Nt),d:E(_1Nu),e:E(_1Nv),f:E(_1Nw),g:E(_1Nx),h:E(_1Ny),i:_1Nz,j:_1NA,k:_1NB,l:_1NC,m:E(_1ND),n:_1NE,o:E(_1NF),p:E(_1NM),q:_1NG,r:E(_1NH),s:E(_1NI),t:_1NJ,u:E(_1NK),v:E(_1NL)};}else{return new F(function(){return _1NO(_);});}}else{if(!B(_qW(_1Nh,_1Dr))){return {_:0,a:E(_1Nr),b:E(_1Ns),c:E(_1Nt),d:E(_1Nu),e:E(_1Nv),f:E(_1Nw),g:E(_1Nx),h:E(_1Ny),i:_1Nz,j:_1NA,k:_1NB,l:_1NC,m:E(_1ND),n:_1NE,o:E(_1NF),p:E(_1NM),q:_1NG,r:E(_1NH),s:E(_1NI),t:_1NJ,u:E(_1NK),v:E(_1NL)};}else{return new F(function(){return _1NO(_);});}}}};if(E(_1MV)==32){var _1NR=E(_1Ml),_1NS=E(_1NR.a),_1NT=B(_1xM(_1N2,_1N1,_1NS.a,_1NS.b,_1NR.b,_1N8,_1NR.d,_1NR.e,_1NR.f,_1NR.g,_1NR.h,_1NR.i,_1NR.j,_1NR.k)),_1NU=E(_1NT.a),_1NV=B(_1B7(_1NU.a,E(_1NU.b),_1NT.b,_1NT.c,_1NT.d,_1NT.e,_1NT.f,_1NT.g,_1NT.h,_1NT.i,_1NT.j,_1NT.k));return new F(function(){return _1N9(_1NV.a,_1NV.b,_1NV.c,_1NV.d,_1NV.e,_1NV.f,_1NV.g,_1NV.i,_1NV.j,_1NV.k);});}else{var _1NW=E(_1Ml),_1NX=E(_1NW.a),_1NY=B(_1xM(_1N2,_1N1,_1NX.a,_1NX.b,_1NW.b,_1N8,_1NW.d,_1NW.e,_1NW.f,_1NW.g,_1NW.h,_1NW.i,_1NW.j,_1NW.k));return new F(function(){return _1N9(_1NY.a,_1NY.b,_1NY.c,_1NY.d,_1NY.e,_1NY.f,_1NY.g,_1NY.i,_1NY.j,_1NY.k);});}},_1NZ=function(_1O0,_1O1){var _1O2=E(_1O1),_1O3=E(_1MX);if(_1O0<=_1O3){if(_1O3<=_1O0){var _1O4=E(_1MY);if(_1O2<=_1O4){if(_1O4<=_1O2){var _1O5=4;}else{var _1O5=0;}var _1O6=_1O5;}else{var _1O6=1;}var _1O7=_1O6;}else{var _1O7=2;}var _1O8=_1O7;}else{var _1O8=3;}var _1O9=function(_1Oa,_1Ob,_1Oc,_1Od,_1Oe,_1Of,_1Og,_1Oh,_1Oi,_1Oj){switch(E(_1O8)){case 0:if(!E(E(_1Ml).c)){var _1Ok=new T2(0,_1MT,_1MU);}else{var _1Ok=new T2(0,_1MT,_1DZ);}var _1Ol=_1Ok;break;case 1:if(E(E(_1Ml).c)==1){var _1Om=new T2(0,_1MT,_1MU);}else{var _1Om=new T2(0,_1MT,_1Ds);}var _1Ol=_1Om;break;case 2:if(E(E(_1Ml).c)==2){var _1On=new T2(0,_1MT,_1MU);}else{var _1On=new T2(0,_1MT,_1Du);}var _1Ol=_1On;break;case 3:if(E(E(_1Ml).c)==3){var _1Oo=new T2(0,_1MT,_1MU);}else{var _1Oo=new T2(0,_1MT,_1Dt);}var _1Ol=_1Oo;break;default:if(E(E(_1Ml).c)==4){var _1Op=new T2(0,_1MT,_1MU);}else{var _1Op=new T2(0,_1MT,_1Ds);}var _1Ol=_1Op;}var _1Oq=B(_1oE(_1Ds,_1Oh,_1MB,{_:0,a:E(_1Oa),b:E(_1Ob),c:E(_1Oc),d:_1Od,e:_1Oe,f:_1Of,g:E(_1Og),h:E(_1Mr),i:E(_1Oh),j:E(_1Oi),k:E(_1Oj)},_1My,_1Mz,_1MA,_1MB,_1MC,_1MD,_1ME,_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1Ol,_1MP,_1MQ,_1MR)),_1Or=_1Oq.a,_1Os=_1Oq.b,_1Ot=_1Oq.c,_1Ou=_1Oq.d,_1Ov=_1Oq.e,_1Ow=_1Oq.f,_1Ox=_1Oq.g,_1Oy=_1Oq.h,_1Oz=_1Oq.i,_1OA=_1Oq.j,_1OB=_1Oq.k,_1OC=_1Oq.l,_1OD=_1Oq.m,_1OE=_1Oq.n,_1OF=_1Oq.o,_1OG=_1Oq.q,_1OH=_1Oq.r,_1OI=_1Oq.s,_1OJ=_1Oq.t,_1OK=_1Oq.u,_1OL=_1Oq.v,_1OM=E(_1Oq.p);if(!_1OM._){return {_:0,a:E(_1Or),b:E(_1Os),c:E(_1Ot),d:E(_1Ou),e:E(_1Ov),f:E(_1Ow),g:E(_1Ox),h:E(_1Oy),i:_1Oz,j:_1OA,k:_1OB,l:_1OC,m:E(_1OD),n:_1OE,o:E(_1OF),p:E(_S),q:_1OG,r:E(_1OH),s:E(_1OI),t:_1OJ,u:E(_1OK),v:E(_1OL)};}else{var _1ON=B(_mz(_1Oh,0))-2|0,_1OO=function(_1OP){var _1OQ=E(_1Or);return {_:0,a:E({_:0,a:E(_1OQ.a),b:E(_1OQ.b),c:E(_1OQ.c),d:_1OQ.d,e:_1OQ.e,f:_1OQ.f,g:E(_S),h:_1OQ.h,i:E(_1OQ.i),j:E(_1OQ.j),k:E(_1OQ.k)}),b:E(_1Os),c:E(_1Ot),d:E(B(_q(B(_68(_S,B(_1CP(B(_6k(_1Fn,_1OM)),B(_15m(_1Ou)))))),new T(function(){return B(_6k(_1BN,_1OM));},1)))),e:E(_1Ov),f:E(_1Ow),g:E(_1Ox),h:E(_1Oy),i:_1Oz,j:_1OA,k:_1OB,l:_1OC,m:E(_1OD),n:_1OE,o:E(_1OF),p:E(_S),q:_1OG,r:E(B(_q(_1OH,new T2(1,_1OG,_S)))),s:E(_1OI),t:_1OJ,u:E(_1OK),v:E(_1OL)};};if(_1ON>0){if(!B(_qW(B(_1Bw(_1ON,_1Oh)),_1Dr))){return {_:0,a:E(_1Or),b:E(_1Os),c:E(_1Ot),d:E(_1Ou),e:E(_1Ov),f:E(_1Ow),g:E(_1Ox),h:E(_1Oy),i:_1Oz,j:_1OA,k:_1OB,l:_1OC,m:E(_1OD),n:_1OE,o:E(_1OF),p:E(_1OM),q:_1OG,r:E(_1OH),s:E(_1OI),t:_1OJ,u:E(_1OK),v:E(_1OL)};}else{return new F(function(){return _1OO(_);});}}else{if(!B(_qW(_1Oh,_1Dr))){return {_:0,a:E(_1Or),b:E(_1Os),c:E(_1Ot),d:E(_1Ou),e:E(_1Ov),f:E(_1Ow),g:E(_1Ox),h:E(_1Oy),i:_1Oz,j:_1OA,k:_1OB,l:_1OC,m:E(_1OD),n:_1OE,o:E(_1OF),p:E(_1OM),q:_1OG,r:E(_1OH),s:E(_1OI),t:_1OJ,u:E(_1OK),v:E(_1OL)};}else{return new F(function(){return _1OO(_);});}}}};if(E(_1MV)==32){var _1OR=E(_1Ml),_1OS=E(_1OR.a),_1OT=B(_1xM(_1O0,_1O2,_1OS.a,_1OS.b,_1OR.b,_1O8,_1OR.d,_1OR.e,_1OR.f,_1OR.g,_1OR.h,_1OR.i,_1OR.j,_1OR.k)),_1OU=E(_1OT.a),_1OV=B(_1B7(_1OU.a,E(_1OU.b),_1OT.b,_1OT.c,_1OT.d,_1OT.e,_1OT.f,_1OT.g,_1OT.h,_1OT.i,_1OT.j,_1OT.k));return new F(function(){return _1O9(_1OV.a,_1OV.b,_1OV.c,_1OV.d,_1OV.e,_1OV.f,_1OV.g,_1OV.i,_1OV.j,_1OV.k);});}else{var _1OW=E(_1Ml),_1OX=E(_1OW.a),_1OY=B(_1xM(_1O0,_1O2,_1OX.a,_1OX.b,_1OW.b,_1O8,_1OW.d,_1OW.e,_1OW.f,_1OW.g,_1OW.h,_1OW.i,_1OW.j,_1OW.k));return new F(function(){return _1O9(_1OY.a,_1OY.b,_1OY.c,_1OY.d,_1OY.e,_1OY.f,_1OY.g,_1OY.i,_1OY.j,_1OY.k);});}},_1OZ=E(_1MV);switch(_1OZ){case 72:var _1P0=E(_1MY);if(0<=(_1P0-1|0)){return B(_1MZ(_1MX,_1P0-1|0));}else{return B(_1MZ(_1MX,_1P0));}break;case 75:var _1P1=E(_1MX);if(0<=(_1P1-1|0)){return B(_1NZ(_1P1-1|0,_1MY));}else{return B(_1NZ(_1P1,_1MY));}break;case 77:var _1P2=E(_1MX);if(E(_1He)!=(_1P2+1|0)){return B(_1NZ(_1P2+1|0,_1MY));}else{return B(_1NZ(_1P2,_1MY));}break;case 80:var _1P3=E(_1MY);if(E(_1Hf)!=(_1P3+1|0)){return B(_1MZ(_1MX,_1P3+1|0));}else{return B(_1MZ(_1MX,_1P3));}break;case 104:var _1P4=E(_1MX);if(0<=(_1P4-1|0)){return B(_1NZ(_1P4-1|0,_1MY));}else{return B(_1NZ(_1P4,_1MY));}break;case 106:var _1P5=E(_1MY);if(E(_1Hf)!=(_1P5+1|0)){return B(_1MZ(_1MX,_1P5+1|0));}else{return B(_1MZ(_1MX,_1P5));}break;case 107:var _1P6=E(_1MY);if(0<=(_1P6-1|0)){return B(_1MZ(_1MX,_1P6-1|0));}else{return B(_1MZ(_1MX,_1P6));}break;case 108:var _1P7=E(_1MX);if(E(_1He)!=(_1P7+1|0)){return B(_1NZ(_1P7+1|0,_1MY));}else{return B(_1NZ(_1P7,_1MY));}break;default:var _1P8=E(_1MX),_1P9=E(_1MY),_1Pa=function(_1Pb,_1Pc,_1Pd,_1Pe,_1Pf,_1Pg,_1Ph,_1Pi,_1Pj,_1Pk){if(E(E(_1Ml).c)==4){var _1Pl=new T2(0,_1MT,_1MU);}else{var _1Pl=new T2(0,_1MT,_1Ds);}var _1Pm=B(_1oE(_1Ds,_1Pi,_1MB,{_:0,a:E(_1Pb),b:E(_1Pc),c:E(_1Pd),d:_1Pe,e:_1Pf,f:_1Pg,g:E(_1Ph),h:E(_1Mr),i:E(_1Pi),j:E(_1Pj),k:E(_1Pk)},_1My,_1Mz,_1MA,_1MB,_1MC,_1MD,_1ME,_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1Pl,_1MP,_1MQ,_1MR)),_1Pn=_1Pm.a,_1Po=_1Pm.b,_1Pp=_1Pm.c,_1Pq=_1Pm.d,_1Pr=_1Pm.e,_1Ps=_1Pm.f,_1Pt=_1Pm.g,_1Pu=_1Pm.h,_1Pv=_1Pm.i,_1Pw=_1Pm.j,_1Px=_1Pm.k,_1Py=_1Pm.l,_1Pz=_1Pm.m,_1PA=_1Pm.n,_1PB=_1Pm.o,_1PC=_1Pm.q,_1PD=_1Pm.r,_1PE=_1Pm.s,_1PF=_1Pm.t,_1PG=_1Pm.u,_1PH=_1Pm.v,_1PI=E(_1Pm.p);if(!_1PI._){return {_:0,a:E(_1Pn),b:E(_1Po),c:E(_1Pp),d:E(_1Pq),e:E(_1Pr),f:E(_1Ps),g:E(_1Pt),h:E(_1Pu),i:_1Pv,j:_1Pw,k:_1Px,l:_1Py,m:E(_1Pz),n:_1PA,o:E(_1PB),p:E(_S),q:_1PC,r:E(_1PD),s:E(_1PE),t:_1PF,u:E(_1PG),v:E(_1PH)};}else{var _1PJ=B(_mz(_1Pi,0))-2|0,_1PK=function(_1PL){var _1PM=E(_1Pn);return {_:0,a:E({_:0,a:E(_1PM.a),b:E(_1PM.b),c:E(_1PM.c),d:_1PM.d,e:_1PM.e,f:_1PM.f,g:E(_S),h:_1PM.h,i:E(_1PM.i),j:E(_1PM.j),k:E(_1PM.k)}),b:E(_1Po),c:E(_1Pp),d:E(B(_q(B(_68(_S,B(_1CP(B(_6k(_1Fn,_1PI)),B(_15m(_1Pq)))))),new T(function(){return B(_6k(_1BN,_1PI));},1)))),e:E(_1Pr),f:E(_1Ps),g:E(_1Pt),h:E(_1Pu),i:_1Pv,j:_1Pw,k:_1Px,l:_1Py,m:E(_1Pz),n:_1PA,o:E(_1PB),p:E(_S),q:_1PC,r:E(B(_q(_1PD,new T2(1,_1PC,_S)))),s:E(_1PE),t:_1PF,u:E(_1PG),v:E(_1PH)};};if(_1PJ>0){if(!B(_qW(B(_1Bw(_1PJ,_1Pi)),_1Dr))){return {_:0,a:E(_1Pn),b:E(_1Po),c:E(_1Pp),d:E(_1Pq),e:E(_1Pr),f:E(_1Ps),g:E(_1Pt),h:E(_1Pu),i:_1Pv,j:_1Pw,k:_1Px,l:_1Py,m:E(_1Pz),n:_1PA,o:E(_1PB),p:E(_1PI),q:_1PC,r:E(_1PD),s:E(_1PE),t:_1PF,u:E(_1PG),v:E(_1PH)};}else{return new F(function(){return _1PK(_);});}}else{if(!B(_qW(_1Pi,_1Dr))){return {_:0,a:E(_1Pn),b:E(_1Po),c:E(_1Pp),d:E(_1Pq),e:E(_1Pr),f:E(_1Ps),g:E(_1Pt),h:E(_1Pu),i:_1Pv,j:_1Pw,k:_1Px,l:_1Py,m:E(_1Pz),n:_1PA,o:E(_1PB),p:E(_1PI),q:_1PC,r:E(_1PD),s:E(_1PE),t:_1PF,u:E(_1PG),v:E(_1PH)};}else{return new F(function(){return _1PK(_);});}}}};if(E(_1OZ)==32){var _1PN=E(_1Ml),_1PO=E(_1PN.a),_1PP=B(_1xM(_1P8,_1P9,_1PO.a,_1PO.b,_1PN.b,_1BC,_1PN.d,_1PN.e,_1PN.f,_1PN.g,_1PN.h,_1PN.i,_1PN.j,_1PN.k)),_1PQ=E(_1PP.a),_1PR=B(_1B7(_1PQ.a,E(_1PQ.b),_1PP.b,_1PP.c,_1PP.d,_1PP.e,_1PP.f,_1PP.g,_1PP.h,_1PP.i,_1PP.j,_1PP.k));return B(_1Pa(_1PR.a,_1PR.b,_1PR.c,_1PR.d,_1PR.e,_1PR.f,_1PR.g,_1PR.i,_1PR.j,_1PR.k));}else{var _1PS=E(_1Ml),_1PT=E(_1PS.a),_1PU=B(_1xM(_1P8,_1P9,_1PT.a,_1PT.b,_1PS.b,_1BC,_1PS.d,_1PS.e,_1PS.f,_1PS.g,_1PS.h,_1PS.i,_1PS.j,_1PS.k));return B(_1Pa(_1PU.a,_1PU.b,_1PU.c,_1PU.d,_1PU.e,_1PU.f,_1PU.g,_1PU.i,_1PU.j,_1PU.k));}}}),_1PV=B(_1d7(_1Mt,_1Mu,_1GZ,_1H0,_1H1,_1Mw,_)),_1PW=_1PV,_1PX=E(_1Mv),_1PY=function(_,_1PZ){var _1Q0=function(_1Q1){var _1Q2=B(_1CZ(_1GS,B(_8w(_1PZ)),_)),_1Q3=E(_1PW),_1Q4=_1Q3.d,_1Q5=_1Q3.e,_1Q6=_1Q3.f,_1Q7=_1Q3.g,_1Q8=_1Q3.i,_1Q9=_1Q3.j,_1Qa=_1Q3.k,_1Qb=_1Q3.l,_1Qc=_1Q3.m,_1Qd=_1Q3.n,_1Qe=_1Q3.o,_1Qf=_1Q3.p,_1Qg=_1Q3.q,_1Qh=_1Q3.r,_1Qi=_1Q3.t,_1Qj=_1Q3.v,_1Qk=E(_1Q3.u),_1Ql=_1Qk.a,_1Qm=_1Qk.d,_1Qn=_1Qk.e,_1Qo=_1Qk.f,_1Qp=_1Qk.g,_1Qq=_1Qk.h,_1Qr=E(_1Q3.a),_1Qs=_1Qr.c,_1Qt=_1Qr.f,_1Qu=_1Qr.g,_1Qv=_1Qr.h,_1Qw=E(_1Q3.h),_1Qx=E(_1Q3.s),_1Qy=function(_1Qz){var _1QA=function(_1QB){if(_1QB!=E(_1Dk)){var _1QC=B(_6X(_1kk,_1QB)),_1QD=_1QC.a,_1QE=E(_1QC.b),_1QF=B(_1fC(_1QD,_1QE,new T(function(){return B(_6X(_1mp,_1QB));})));return new F(function(){return _1GX(_1Ms,_1GZ,_1H0,_1H1,_1Dj,B(_6X(_1kv,_1QB)),_1QF,_1Qs,B(_6X(_1kI,_1QB)),32,_1QB,_1Qu,_1Qv,B(_q(_1Qr.i,new T2(1,_1Di,new T(function(){return B(_A(0,_1Qt,_S));})))),B(_1BW(_1Dh,_1QF)),_wD,_1QD,_1QE,_S,_1Q4,_1Q5,_1Q6,_1Q7,_1Qw.a,_1Qw.b,_1Q8,_1Q9,_1Qa, -1,_1Qc,_1Qd,_1Qe,_1Qf,_1Qg,_1Qh,_1Qx.a,_1Qx.b,_1Qi,_wD,_wD,_wD,_1Qm,_1Qn,_1Qo,_1Qp,_1Qq,_1Qj,_);});}else{var _1QG=__app1(E(_no),_1Mu),_1QH=B(A2(_np,_1Mt,_)),_1QI=B(A(_mU,[_1Mt,_j9,_1DZ,_1Df,_1De,_])),_1QJ=B(A(_mU,[_1Mt,_j9,_1Dd,_1Dc,_1E0,_])),_1QK=B(A(_mU,[_1Mt,_j9,_1DZ,_1DY,_1DX,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1km),b:E(_1DV),c:E(_1Qs),d:E(_1DA),e:32,f:0,g:E(_1Qu),h:_1Qv,i:E(_S),j:E(_1Qr.j),k:E(_wD)}),b:E(_1k7),c:E(_1Q3.c),d:E(_1Q4),e:E(_1Q5),f:E(_1Q6),g:E(_1Q7),h:E(_1Qw),i:_1Q8,j:_1Q9,k:_1Qa,l:_1Qb,m:E(_1Qc),n:_1Qd,o:E(_1Qe),p:E(_1Qf),q:_1Qg,r:E(_1Qh),s:E(_1Qx),t:_1Qi,u:E({_:0,a:E(_1Ql),b:E(_wD),c:E(_wD),d:E(_1Qm),e:E(_1Qn),f:E(_1Qo),g:E(_1Qp),h:E(_1Qq)}),v:E(_1Qj)};});}};if(_1Qb>=0){return new F(function(){return _1QA(_1Qb);});}else{return new F(function(){return _1QA(_1Qt+1|0);});}};if(!E(_1Ql)){if(E(_1PX)==110){return new F(function(){return _1Qy(_);});}else{return _1Q3;}}else{return new F(function(){return _1Qy(_);});}};if(E(_1PX)==114){if(!B(_6f(_1PZ,_1Dl))){var _1QL=E(_1PZ);if(!_1QL._){return _1PW;}else{var _1QM=_1QL.b;return new T(function(){var _1QN=E(_1PW),_1QO=E(_1QN.a),_1QP=E(_1QL.a),_1QQ=E(_1QP);if(_1QQ==34){var _1QR=B(_TO(_1QP,_1QM));if(!_1QR._){var _1QS=E(_1EU);}else{var _1QT=E(_1QR.b);if(!_1QT._){var _1QU=E(_1DE);}else{var _1QV=_1QT.a,_1QW=E(_1QT.b);if(!_1QW._){var _1QX=new T2(1,new T2(1,_1QV,_S),_S);}else{var _1QY=E(_1QV),_1QZ=new T(function(){var _1R0=B(_Hd(126,_1QW.a,_1QW.b));return new T2(0,_1R0.a,_1R0.b);});if(E(_1QY)==126){var _1R1=new T2(1,_S,new T2(1,new T(function(){return E(E(_1QZ).a);}),new T(function(){return E(E(_1QZ).b);})));}else{var _1R1=new T2(1,new T2(1,_1QY,new T(function(){return E(E(_1QZ).a);})),new T(function(){return E(E(_1QZ).b);}));}var _1QX=_1R1;}var _1QU=_1QX;}var _1QS=_1QU;}var _1R2=_1QS;}else{var _1R3=E(_1QM);if(!_1R3._){var _1R4=new T2(1,new T2(1,_1QP,_S),_S);}else{var _1R5=new T(function(){var _1R6=B(_Hd(126,_1R3.a,_1R3.b));return new T2(0,_1R6.a,_1R6.b);});if(E(_1QQ)==126){var _1R7=new T2(1,_S,new T2(1,new T(function(){return E(E(_1R5).a);}),new T(function(){return E(E(_1R5).b);})));}else{var _1R7=new T2(1,new T2(1,_1QP,new T(function(){return E(E(_1R5).a);})),new T(function(){return E(E(_1R5).b);}));}var _1R4=_1R7;}var _1R2=_1R4;}var _1R8=B(_Gl(B(_sI(_1Dm,new T(function(){return B(_Js(_1R2));})))));if(!_1R8._){return E(_1Da);}else{if(!E(_1R8.b)._){var _1R9=E(_1R8.a),_1Ra=B(_6X(_1kk,_1R9)),_1Rb=B(_6X(_1R2,1));if(!_1Rb._){var _1Rc=__Z;}else{var _1Rd=E(_1Rb.b);if(!_1Rd._){var _1Re=__Z;}else{var _1Rf=E(_1Rb.a),_1Rg=new T(function(){var _1Rh=B(_Hd(44,_1Rd.a,_1Rd.b));return new T2(0,_1Rh.a,_1Rh.b);});if(E(_1Rf)==44){var _1Ri=B(_15B(_S,new T(function(){return E(E(_1Rg).a);}),new T(function(){return E(E(_1Rg).b);})));}else{var _1Ri=B(_15F(new T2(1,_1Rf,new T(function(){return E(E(_1Rg).a);})),new T(function(){return E(E(_1Rg).b);})));}var _1Re=_1Ri;}var _1Rc=_1Re;}var _1Rj=B(_6X(_1R2,2));if(!_1Rj._){var _1Rk=E(_1DF);}else{var _1Rl=_1Rj.a,_1Rm=E(_1Rj.b);if(!_1Rm._){var _1Rn=B(_6k(_1Dx,new T2(1,new T2(1,_1Rl,_S),_S)));}else{var _1Ro=E(_1Rl),_1Rp=new T(function(){var _1Rq=B(_Hd(44,_1Rm.a,_1Rm.b));return new T2(0,_1Rq.a,_1Rq.b);});if(E(_1Ro)==44){var _1Rr=B(_6k(_1Dx,new T2(1,_S,new T2(1,new T(function(){return E(E(_1Rp).a);}),new T(function(){return E(E(_1Rp).b);})))));}else{var _1Rr=B(_6k(_1Dx,new T2(1,new T2(1,_1Ro,new T(function(){return E(E(_1Rp).a);})),new T(function(){return E(E(_1Rp).b);}))));}var _1Rn=_1Rr;}var _1Rk=_1Rn;}return {_:0,a:E({_:0,a:E(B(_6X(_1kv,_1R9))),b:E(B(_1fC(_1Ra.a,E(_1Ra.b),new T(function(){return B(_6X(_1mp,_1R9));})))),c:E(_1QO.c),d:B(_6X(_1kI,_1R9)),e:32,f:_1R9,g:E(_1QO.g),h:_1QO.h,i:E(_1QO.i),j:E(_1QO.j),k:E(_1QO.k)}),b:E(_1Ra),c:E(_1QN.c),d:E(_1QN.d),e:E(_1Rc),f:E(_1Rk),g:E(_1QN.g),h:E(_1QN.h),i:_1QN.i,j:_1QN.j,k:_1QN.k,l:_1QN.l,m:E(_1QN.m),n:_1QN.n,o:E(_1QN.o),p:E(_1QN.p),q:_1QN.q,r:E(_1QN.r),s:E(_1QN.s),t:_1QN.t,u:E(_1QN.u),v:E(_1QN.v)};}else{return E(_1Db);}}});}}else{return new F(function(){return _1Q0(_);});}}else{return new F(function(){return _1Q0(_);});}};switch(E(_1PX)){case 100:var _1Rs=__app1(E(_1ES),toJSStr(E(_1Dp)));return new F(function(){return _1PY(_,_1D7);});break;case 114:var _1Rt=B(_15Q(_6C,toJSStr(E(_1Dp)),_));return new F(function(){return _1PY(_,new T(function(){var _1Ru=E(_1Rt);if(!_1Ru._){return E(_1D8);}else{return fromJSStr(B(_1qT(_1Ru.a)));}}));});break;case 115:var _1Rv=new T(function(){var _1Rw=new T(function(){var _1Rx=new T(function(){var _1Ry=B(_6k(_6H,_1Hj));if(!_1Ry._){return __Z;}else{return B(_1D4(new T2(1,_1Ry.a,new T(function(){return B(_1E1(_1Dn,_1Ry.b));}))));}}),_1Rz=new T(function(){var _1RA=function(_1RB){var _1RC=E(_1RB);if(!_1RC._){return __Z;}else{var _1RD=E(_1RC.a);return new T2(1,_1RD.a,new T2(1,_1RD.b,new T(function(){return B(_1RA(_1RC.b));})));}},_1RE=B(_1RA(_1Hi));if(!_1RE._){return __Z;}else{return B(_1D4(new T2(1,_1RE.a,new T(function(){return B(_1E1(_1Dn,_1RE.b));}))));}});return B(_1E1(_1Do,new T2(1,_1Rz,new T2(1,_1Rx,_S))));});return B(_q(B(_1D4(new T2(1,new T(function(){return B(_A(0,_1H8,_S));}),_1Rw))),_1DD));}),_1RF=__app2(E(_1EV),toJSStr(E(_1Dp)),B(_1qT(B(_1GU(B(unAppCStr("\"",_1Rv)))))));return new F(function(){return _1PY(_,_1D9);});break;default:return new F(function(){return _1PY(_,_1Dq);});}},_1RG=E(_1Hw);if(!_1RG._){var _1RH=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Mp(_);});}else{var _1RI=new T(function(){return B(_A(0,E(_1RG.a),new T(function(){return B(_1EX(_1RG.b));})));}),_1RJ=B(_1CZ(_1GS,new T2(1,_2u,_1RI),_));return new F(function(){return _1Mp(_);});}};if(!E(_1Mk.f)){var _1RK=B(_1CZ(_1GS,_1Fm,_));return new F(function(){return _1Mm(_);});}else{var _1RL=B(_1CZ(_1GS,_1Fl,_));return new F(function(){return _1Mm(_);});}},_1RM=E(_1Hk);if(!_1RM._){var _1RN=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Mg(_);});}else{var _1RO=new T(function(){var _1RP=E(_1RM.a),_1RQ=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1RR){return new F(function(){return _1DG(_1RP.a,_1RR);});},new T2(1,function(_1RS){return new F(function(){return _1DG(_1RP.b,_1RS);});},_S)),new T2(1,_y,new T(function(){return B(_1F1(_1RM.b));}))));});return new T2(1,_z,_1RQ);}),_1RT=B(_1CZ(_1GS,new T2(1,_2u,_1RO),_));return new F(function(){return _1Mg(_);});}},_1RU=E(_1Hj);if(!_1RU._){var _1RV=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Mf(_);});}else{var _1RW=new T(function(){return B(_A(0,E(_1RU.a),new T(function(){return B(_1F9(_1RU.b));})));}),_1RX=B(_1CZ(_1GS,new T2(1,_2u,_1RW),_));return new F(function(){return _1Mf(_);});}},_1RY=E(_1Hi);if(!_1RY._){var _1RZ=B(_1CZ(_1GS,_1DC,_));return new F(function(){return _1Me(_);});}else{var _1S0=new T(function(){var _1S1=E(_1RY.a),_1S2=new T(function(){return B(A3(_sl,_6D,new T2(1,function(_1S3){return new F(function(){return _1DG(_1S1.a,_1S3);});},new T2(1,function(_1S4){return new F(function(){return _1DG(_1S1.b,_1S4);});},_S)),new T2(1,_y,new T(function(){return B(_1Fd(_1RY.b));}))));});return new T2(1,_z,_1S2);}),_1S5=B(_1CZ(_1GS,new T2(1,_2u,_1S0),_));return new F(function(){return _1Me(_);});}}else{return new F(function(){return _1HR(_,_1H3,_1H4,_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1HM,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HL,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_S,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HJ,_1HI);});}}}}}}}else{if(!E(_1HG)){return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:_1Hs,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E({_:0,a:E(_1HA),b:E(_1HB),c:E(_1HC),d:E(_wD),e:E(_1HE),f:E(_wD),g:E(_wD),h:E(_1HH)}),v:E(_1HI)};}else{var _1S6=E(_1GY),_1S7=new T(function(){var _1S8=new T(function(){var _1S9=B(_1qX(_1Hr));return new T2(0,_1S9.a,_1S9.b);}),_1Sa=new T(function(){return B(_mz(E(_1S8).a,0))-1|0;}),_1Sb=function(_1Sc){var _1Sd=E(_1Sc);switch(_1Sd){case  -2:return E(_1HO);case  -1:return {_:0,a:E(_1HN),b:E(_1HM),c:E(B(_1jP(_S,new T(function(){return B(_6X(E(_1S8).b,_1Hs));})))),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:_1Hs,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E({_:0,a:E(_1HA),b:E(_1HB),c:E(_wE),d:E(_wD),e:E(_1HE),f:E(_wD),g:E(_wD),h:E(_1HH)}),v:E(_1HI)};default:return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:_1Sd,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};}};switch(E(B(_1rT(E(_1H2))))){case 32:return {_:0,a:E(_1HN),b:E(_1HM),c:E(B(_1jP(_S,new T(function(){return B(_6X(E(_1S8).b,_1Hs));})))),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:_1Hs,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E({_:0,a:E(_1HA),b:E(_1HB),c:E(_wE),d:E(_wD),e:E(_1HE),f:E(_wD),g:E(_wD),h:E(_1HH)}),v:E(_1HI)};break;case 72:var _1Se=E(_1Hs);if(!_1Se){return B(_1Sb(E(_1Sa)));}else{return B(_1Sb(_1Se-1|0));}break;case 75:if(_1Hs!=E(_1Sa)){return B(_1Sb(_1Hs+1|0));}else{return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:0,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};}break;case 77:var _1Sf=E(_1Hs);if(!_1Sf){return B(_1Sb(E(_1Sa)));}else{return B(_1Sb(_1Sf-1|0));}break;case 80:if(_1Hs!=E(_1Sa)){return B(_1Sb(_1Hs+1|0));}else{return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:0,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};}break;case 104:if(_1Hs!=E(_1Sa)){return B(_1Sb(_1Hs+1|0));}else{return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:0,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};}break;case 106:if(_1Hs!=E(_1Sa)){return B(_1Sb(_1Hs+1|0));}else{return {_:0,a:E(_1HN),b:E(_1HM),c:E(_1Hg),d:E(_1Hh),e:E(_1Hi),f:E(_1Hj),g:E(_1Hk),h:E(_1HL),i:_1Hn,j:_1Ho,k:_1Hp,l:_1Hq,m:E(_1Hr),n:0,o:E(_1Ht),p:E(_1Hu),q:_1Hv,r:E(_1Hw),s:E(_1HK),t:_1Hz,u:E(_1HJ),v:E(_1HI)};}break;case 107:var _1Sg=E(_1Hs);if(!_1Sg){return B(_1Sb(E(_1Sa)));}else{return B(_1Sb(_1Sg-1|0));}break;case 108:var _1Sh=E(_1Hs);if(!_1Sh){return B(_1Sb(E(_1Sa)));}else{return B(_1Sb(_1Sh-1|0));}break;default:return E(_1HO);}});return new F(function(){return _1d7(_1S6.a,_1S6.b,_1GZ,_1H0,_1H1,_1S7,_);});}}};if(!E(_1HC)){return new F(function(){return _1HP(_);});}else{if(!E(_1HD)){return new F(function(){return _10w(_1GY,_1GZ,_1H0,_1HN,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1Hw,_1HK,_1Hz,_1HA,_1HB,_wD,_1HE,_wE,_1HG,_1HH,_1HI,_);});}else{return new F(function(){return _1HP(_);});}}}else{return _1HO;}},_1Si=function(_1Sj){var _1Sk=E(_1Sj),_1Sl=E(_1Sk.a),_1Sm=new T(function(){return B(_q(_1Sl.b,new T(function(){return B(unAppCStr(" >>",_1Sl.c));},1)));});return new T2(0,new T2(1,_1Sk.b,_1r3),_1Sm);},_1Sn=function(_1So,_1Sp,_1Sq,_1Sr,_1Ss,_1St,_1Su,_1Sv,_1Sw,_1Sx,_1Sy,_1Sz,_1SA,_1SB,_1SC,_1SD,_1SE,_1SF,_1SG,_1SH,_1SI,_1SJ,_1SK,_1SL,_1SM,_1SN,_1SO,_1SP,_1SQ,_1SR,_1SS,_1ST,_1SU,_1SV,_1SW,_1SX,_1SY,_1SZ,_1T0,_1T1,_1T2,_1T3,_1T4,_){var _1T5=function(_1T6){var _1T7=new T(function(){var _1T8=function(_1T9){var _1Ta=E(_1T9);return (_1Ta==30)?{_:0,a:E({_:0,a:E(_1Ss),b:E(_1St),c:E(_1Su),d:_1Sv,e:_1Sw,f:_1Sx,g:E(_1Sy),h:_1Sz,i:E(_1SA),j:E(_1SB),k:E(_1SC)}),b:E(_1SD),c:E(_1SE),d:E(B(_q(B(_68(_S,B(_1CP(B(_6k(_1Fn,_1SR)),B(_15m(_1SF)))))),new T(function(){return B(_6k(_1Si,_1SR));},1)))),e:E(_1SG),f:E(_1SH),g:E(_1SI),h:E(_1SJ),i:_1SK,j:_1SL,k:_1SM,l:_1SN,m:E(_1SO),n:_1SP,o:E(_1SQ),p:E(_1SR),q:30,r:E(_1ST),s:E(_1SU),t:_1T6,u:E({_:0,a:E(_1SW),b:E(_1SX),c:E(_1SY),d:E(_1SZ),e:E(_1T0),f:E(_1T1),g:E(_1T2),h:E(_1T3)}),v:E(_1T4)}:{_:0,a:E({_:0,a:E(_1Ss),b:E(_1St),c:E(_1Su),d:_1Sv,e:_1Sw,f:_1Sx,g:E(_1Sy),h:_1Sz,i:E(_1SA),j:E(_1SB),k:E(_1SC)}),b:E(_1SD),c:E(_1SE),d:E(_1SF),e:E(_1SG),f:E(_1SH),g:E(_1SI),h:E(_1SJ),i:_1SK,j:_1SL,k:_1SM,l:_1SN,m:E(_1SO),n:_1SP,o:E(_1SQ),p:E(_1SR),q:_1Ta,r:E(_1ST),s:E(_1SU),t:_1T6,u:E({_:0,a:E(_1SW),b:E(_1SX),c:E(_1SY),d:E(_1SZ),e:E(_1T0),f:E(_1T1),g:E(_1T2),h:E(_1T3)}),v:E(_1T4)};};if(!E(_1SR)._){return B(_1T8(_1SS));}else{if(!B(_au(_1T6,20))){return B(_1T8(_1SS+1|0));}else{return B(_1T8(_1SS));}}});if(!E(_1T3)){var _1Tb=E(_1T7),_1Tc=E(_1Tb.b),_1Td=E(_1Tb.h),_1Te=E(_1Tb.u);return new F(function(){return _Ym(_1So,_1Sp,_1Sq,_1Tb.a,_1Tc.a,_1Tc.b,_1Tb.c,_1Tb.d,_1Tb.e,_1Tb.f,_1Tb.g,_1Td.a,_1Td.b,_1Tb.i,_1Tb.j,_1Tb.k,_1Tb.l,_1Tb.m,_1Tb.n,_1Tb.o,_1Tb.p,_1Tb.q,_1Tb.r,_1Tb.s,_1Tb.t,_1Te.a,_1Te.b,_1Te.c,_1Te.d,_1Te.e,_1Te.f,_1Te.g,_1Te.h,_1Tb.v,_);});}else{if(!B(_au(_1T6,10))){if(!E(_1SY)){if(_1Sx!=E(_1Dk)){var _1Tf=E(_1So);return new F(function(){return _1d7(_1Tf.a,_1Tf.b,_1Sp,_1Sq,_1Sr,_1T7,_);});}else{var _1Tg=E(_1T7),_1Th=E(_1Tg.b),_1Ti=E(_1Tg.h),_1Tj=E(_1Tg.u);return new F(function(){return _Ym(_1So,_1Sp,_1Sq,_1Tg.a,_1Th.a,_1Th.b,_1Tg.c,_1Tg.d,_1Tg.e,_1Tg.f,_1Tg.g,_1Ti.a,_1Ti.b,_1Tg.i,_1Tg.j,_1Tg.k,_1Tg.l,_1Tg.m,_1Tg.n,_1Tg.o,_1Tg.p,_1Tg.q,_1Tg.r,_1Tg.s,_1Tg.t,_1Tj.a,_1Tj.b,_1Tj.c,_1Tj.d,_1Tj.e,_1Tj.f,_1Tj.g,_1Tj.h,_1Tg.v,_);});}}else{var _1Tk=E(_1T7),_1Tl=E(_1Tk.b),_1Tm=E(_1Tk.h),_1Tn=E(_1Tk.u);return new F(function(){return _Ym(_1So,_1Sp,_1Sq,_1Tk.a,_1Tl.a,_1Tl.b,_1Tk.c,_1Tk.d,_1Tk.e,_1Tk.f,_1Tk.g,_1Tm.a,_1Tm.b,_1Tk.i,_1Tk.j,_1Tk.k,_1Tk.l,_1Tk.m,_1Tk.n,_1Tk.o,_1Tk.p,_1Tk.q,_1Tk.r,_1Tk.s,_1Tk.t,_1Tn.a,_1Tn.b,_1Tn.c,_1Tn.d,_1Tn.e,_1Tn.f,_1Tn.g,_1Tn.h,_1Tk.v,_);});}}else{var _1To=E(_1T7),_1Tp=E(_1To.b),_1Tq=E(_1To.h),_1Tr=E(_1To.u);return new F(function(){return _Ym(_1So,_1Sp,_1Sq,_1To.a,_1Tp.a,_1Tp.b,_1To.c,_1To.d,_1To.e,_1To.f,_1To.g,_1Tq.a,_1Tq.b,_1To.i,_1To.j,_1To.k,_1To.l,_1To.m,_1To.n,_1To.o,_1To.p,_1To.q,_1To.r,_1To.s,_1To.t,_1Tr.a,_1Tr.b,_1Tr.c,_1Tr.d,_1Tr.e,_1Tr.f,_1Tr.g,_1Tr.h,_1To.v,_);});}}};if(_1SV<=298){return new F(function(){return _1T5(_1SV+1|0);});}else{return new F(function(){return _1T5(0);});}},_1Ts=function(_1Tt,_1Tu,_1Tv){var _1Tw=E(_1Tv);if(!_1Tw._){return 0;}else{var _1Tx=_1Tw.b,_1Ty=E(_1Tw.a),_1Tz=_1Ty.a,_1TA=_1Ty.b;return (_1Tt<=_1Tz)?1+B(_1Ts(_1Tt,_1Tu,_1Tx))|0:(_1Tt>=_1Tz+_1Ty.c)?1+B(_1Ts(_1Tt,_1Tu,_1Tx))|0:(_1Tu<=_1TA)?1+B(_1Ts(_1Tt,_1Tu,_1Tx))|0:(_1Tu>=_1TA+_1Ty.d)?1+B(_1Ts(_1Tt,_1Tu,_1Tx))|0:1;}},_1TB=function(_1TC,_1TD,_1TE){var _1TF=E(_1TE);if(!_1TF._){return 0;}else{var _1TG=_1TF.b,_1TH=E(_1TF.a),_1TI=_1TH.a,_1TJ=_1TH.b;if(_1TC<=_1TI){return 1+B(_1TB(_1TC,_1TD,_1TG))|0;}else{if(_1TC>=_1TI+_1TH.c){return 1+B(_1TB(_1TC,_1TD,_1TG))|0;}else{var _1TK=E(_1TD);return (_1TK<=_1TJ)?1+B(_1Ts(_1TC,_1TK,_1TG))|0:(_1TK>=_1TJ+_1TH.d)?1+B(_1Ts(_1TC,_1TK,_1TG))|0:1;}}}},_1TL=function(_1TM,_1TN,_1TO){var _1TP=E(_1TO);if(!_1TP._){return 0;}else{var _1TQ=_1TP.b,_1TR=E(_1TP.a),_1TS=_1TR.a,_1TT=_1TR.b,_1TU=E(_1TM);if(_1TU<=_1TS){return 1+B(_1TB(_1TU,_1TN,_1TQ))|0;}else{if(_1TU>=_1TS+_1TR.c){return 1+B(_1TB(_1TU,_1TN,_1TQ))|0;}else{var _1TV=E(_1TN);return (_1TV<=_1TT)?1+B(_1Ts(_1TU,_1TV,_1TQ))|0:(_1TV>=_1TT+_1TR.d)?1+B(_1Ts(_1TU,_1TV,_1TQ))|0:1;}}}},_1TW=function(_1TX,_1TY){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1TY)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1TY)-100,E(_1TX),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1TX),100);}),new T2(1,new T(function(){return new T4(0,E(_1TX)-100,100,100,E(_1TY)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1TX)-200,E(_1TY)-200);}),_S)))));},_1TZ=32,_1U0=76,_1U1=75,_1U2=74,_1U3=72,_1U4=64,_1U5=function(_1U6,_1U7,_1U8,_1U9,_1Ua){var _1Ub=new T(function(){var _1Uc=E(_1U7),_1Ud=E(_1Uc.a),_1Ue=_1Ud.a,_1Uf=_1Ud.b,_1Ug=B(_1TW(_1Ue,_1Uf)),_1Uh=new T(function(){var _1Ui=E(_1Uc.b);return new T2(0,new T(function(){return B(_ge(_1Ue,_1Ui.a));}),new T(function(){return B(_ge(_1Uf,_1Ui.b));}));});switch(B(_1TL(new T(function(){return E(_1U9)*E(E(_1Uh).a);},1),new T(function(){return E(_1Ua)*E(E(_1Uh).b);},1),new T2(1,_1Ug.a,_1Ug.b)))){case 1:return E(_1U3);break;case 2:return E(_1U2);break;case 3:return E(_1U1);break;case 4:return E(_1U0);break;case 5:return E(_1TZ);break;default:return E(_1U4);}});return function(_1Uj,_){var _1Uk=E(E(_1U7).a),_1Ul=E(_1Uj),_1Um=E(_1Ul.a),_1Un=E(_1Ul.b),_1Uo=E(_1Ul.h),_1Up=E(_1Ul.s),_1Uq=E(_1Ul.u);return new F(function(){return _1GX(_1U6,_1Uk.a,_1Uk.b,_1U8,_1Ub,_1Um.a,_1Um.b,_1Um.c,_1Um.d,_1Um.e,_1Um.f,_1Um.g,_1Um.h,_1Um.i,_1Um.j,_1Um.k,_1Un.a,_1Un.b,_1Ul.c,_1Ul.d,_1Ul.e,_1Ul.f,_1Ul.g,_1Uo.a,_1Uo.b,_1Ul.i,_1Ul.j,_1Ul.k,_1Ul.l,_1Ul.m,_1Ul.n,_1Ul.o,_1Ul.p,_1Ul.q,_1Ul.r,_1Up.a,_1Up.b,_1Ul.t,_1Uq.a,_1Uq.b,_1Uq.c,_1Uq.d,_1Uq.e,_1Uq.f,_1Uq.g,_1Uq.h,_1Ul.v,_);});};},_1Ur=0,_1Us=2,_1Ut=2,_1Uu=0,_1Uv=new T(function(){return eval("document");}),_1Uw=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Ux=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1Uy=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1Uz=function(_1UA){return E(E(_1UA).b);},_1UB=function(_1UC,_1UD){return new F(function(){return A2(_1Uz,_1UC,function(_){var _1UE=E(_1UD),_1UF=__app1(E(_1Uy),_1UE);if(!_1UF){return _2N;}else{var _1UG=__app1(E(_1Ux),_1UE);return new T1(1,new T2(0,_1UG,_1UE));}});});},_1UH=1,_1UI=new T(function(){var _1UJ=E(_1kI);if(!_1UJ._){return E(_nn);}else{return {_:0,a:E(_1km),b:E(B(_1fC(_1k6,5,_1lc))),c:E(_1UH),d:E(_1UJ.a),e:32,f:0,g:E(_S),h:0,i:E(_S),j:E(_wD),k:E(_wD)};}}),_1UK=0,_1UL=4,_1UM=new T2(0,_1UL,_1UK),_1UN=new T2(0,_1UK,_1UK),_1UO={_:0,a:E(_wD),b:E(_wD),c:E(_wE),d:E(_wD),e:E(_wD),f:E(_wD),g:E(_wD),h:E(_wD)},_1UP=new T(function(){return {_:0,a:E(_1UI),b:E(_1k7),c:E(_1gN),d:E(_S),e:E(_S),f:E(_S),g:E(_S),h:E(_1UN),i:0,j:0,k:0,l: -1,m:E(_S),n:0,o:E(_S),p:E(_S),q:0,r:E(_S),s:E(_1UM),t:0,u:E(_1UO),v:E(_S)};}),_1UQ=new T1(0,100),_1UR=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1US=new T6(0,_2N,_2O,_S,_1UR,_2N,_2N),_1UT=new T(function(){return B(_2L(_1US));}),_1UU=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1UV=new T6(0,_2N,_2O,_S,_1UU,_2N,_2N),_1UW=new T(function(){return B(_2L(_1UV));}),_1UX=new T1(1,50),_1UY=function(_1UZ){return E(E(_1UZ).a);},_1V0=function(_1V1){return E(E(_1V1).a);},_1V2=function(_1V3){return E(E(_1V3).b);},_1V4=function(_1V5){return E(E(_1V5).b);},_1V6=function(_1V7){return E(E(_1V7).a);},_1V8=function(_){return new F(function(){return nMV(_2N);});},_1V9=new T(function(){return B(_36(_1V8));}),_1Va=function(_1Vb){return E(E(_1Vb).b);},_1Vc=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Vd=function(_1Ve){return E(E(_1Ve).d);},_1Vf=function(_1Vg,_1Vh,_1Vi,_1Vj,_1Vk,_1Vl){var _1Vm=B(_1UY(_1Vg)),_1Vn=B(_1V0(_1Vm)),_1Vo=new T(function(){return B(_1Uz(_1Vm));}),_1Vp=new T(function(){return B(_1Vd(_1Vn));}),_1Vq=new T(function(){return B(A1(_1Vh,_1Vj));}),_1Vr=new T(function(){return B(A2(_1V6,_1Vi,_1Vk));}),_1Vs=function(_1Vt){return new F(function(){return A1(_1Vp,new T3(0,_1Vr,_1Vq,_1Vt));});},_1Vu=function(_1Vv){var _1Vw=new T(function(){var _1Vx=new T(function(){var _1Vy=__createJSFunc(2,function(_1Vz,_){var _1VA=B(A2(E(_1Vv),_1Vz,_));return _3a;}),_1VB=_1Vy;return function(_){return new F(function(){return __app3(E(_1Vc),E(_1Vq),E(_1Vr),_1VB);});};});return B(A1(_1Vo,_1Vx));});return new F(function(){return A3(_1V2,_1Vn,_1Vw,_1Vs);});},_1VC=new T(function(){var _1VD=new T(function(){return B(_1Uz(_1Vm));}),_1VE=function(_1VF){var _1VG=new T(function(){return B(A1(_1VD,function(_){var _=wMV(E(_1V9),new T1(1,_1VF));return new F(function(){return A(_1V4,[_1Vi,_1Vk,_1VF,_]);});}));});return new F(function(){return A3(_1V2,_1Vn,_1VG,_1Vl);});};return B(A2(_1Va,_1Vg,_1VE));});return new F(function(){return A3(_1V2,_1Vn,_1VC,_1Vu);});},_1VH=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1VI=function(_){var _1VJ=rMV(E(_1V9)),_1VK=E(_1VJ);if(!_1VK._){var _1VL=__app1(E(_1VH),E(_3a));return new F(function(){return _gL(_);});}else{var _1VM=__app1(E(_1VH),E(_1VK.a));return new F(function(){return _gL(_);});}},_1VN="src",_1VO=new T(function(){return B(unCStr("img"));}),_1VP=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1VQ=function(_1VR,_1VS){return new F(function(){return A2(_1Uz,_1VR,function(_){var _1VT=__app1(E(_1VP),toJSStr(E(_1VO))),_1VU=__app3(E(_i7),_1VT,E(_1VN),E(_1VS));return _1VT;});});},_1VV=new T(function(){return B(unCStr(".png"));}),_1VW=function(_1VX,_1VY){var _1VZ=E(_1VX);if(_1VZ==( -1)){return __Z;}else{var _1W0=new T(function(){var _1W1=new T(function(){return toJSStr(B(_q(_1VY,new T(function(){return B(_q(B(_A(0,_1VZ,_S)),_1VV));},1))));});return B(_1VQ(_5W,_1W1));});return new F(function(){return _q(B(_1VW(_1VZ-1|0,_1VY)),new T2(1,_1W0,_S));});}},_1W2=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1W3=new T(function(){return B(_1VW(120,_1W2));}),_1W4=function(_1W5,_){var _1W6=E(_1W5);if(!_1W6._){return _S;}else{var _1W7=B(A1(_1W6.a,_)),_1W8=B(_1W4(_1W6.b,_));return new T2(1,_1W7,_1W8);}},_1W9=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1Wa=new T(function(){return B(_1VW(56,_1W9));}),_1Wb=function(_1Wc,_){var _1Wd=E(_1Wc);if(!_1Wd._){return _S;}else{var _1We=B(A1(_1Wd.a,_)),_1Wf=B(_1Wb(_1Wd.b,_));return new T2(1,_1We,_1Wf);}},_1Wg=new T(function(){return B(unCStr("Images/img"));}),_1Wh=new T(function(){return B(_1VW(5,_1Wg));}),_1Wi=function(_1Wj,_){var _1Wk=E(_1Wj);if(!_1Wk._){return _S;}else{var _1Wl=B(A1(_1Wk.a,_)),_1Wm=B(_1Wi(_1Wk.b,_));return new T2(1,_1Wl,_1Wm);}},_1Wn=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1Wo=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1Wp=function(_1Wq,_1Wr,_1Ws){var _1Wt=B(_1UY(_1Wq)),_1Wu=new T(function(){return B(_1Uz(_1Wt));}),_1Wv=function(_1Ww){var _1Wx=function(_){var _1Wy=E(_1Wr);if(!_1Wy._){var _1Wz=B(A1(_1Ww,_gK)),_1WA=__createJSFunc(0,function(_){var _1WB=B(A1(_1Wz,_));return _3a;}),_1WC=__app2(E(_1Wo),_1Wy.a,_1WA);return new T(function(){var _1WD=Number(_1WC),_1WE=jsTrunc(_1WD);return new T2(0,_1WE,E(_1Wy));});}else{var _1WF=B(A1(_1Ww,_gK)),_1WG=__createJSFunc(0,function(_){var _1WH=B(A1(_1WF,_));return _3a;}),_1WI=__app2(E(_1Wn),_1Wy.a,_1WG);return new T(function(){var _1WJ=Number(_1WI),_1WK=jsTrunc(_1WJ);return new T2(0,_1WK,E(_1Wy));});}};return new F(function(){return A1(_1Wu,_1Wx);});},_1WL=new T(function(){return B(A2(_1Va,_1Wq,function(_1WM){return E(_1Ws);}));});return new F(function(){return A3(_1V2,B(_1V0(_1Wt)),_1WL,_1Wv);});},_1WN=function(_){var _1WO=B(_1Wi(_1Wh,_)),_1WP=B(_1Wb(_1Wa,_)),_1WQ=B(_1W4(_1W3,_)),_1WR=__app1(E(_1Uw),"canvas"),_1WS=__eq(_1WR,E(_3a));if(!E(_1WS)){var _1WT=__isUndef(_1WR);if(!E(_1WT)){var _1WU=B(A3(_1UB,_5W,_1WR,_)),_1WV=E(_1WU);if(!_1WV._){return new F(function(){return die(_1UW);});}else{var _1WW=E(_1WV.a),_1WX=B(_62(_1WW.b,_)),_1WY=_1WX,_1WZ=nMV(_1UP),_1X0=_1WZ,_1X1=new T3(0,_1WO,_1WP,_1WQ),_1X2=B(A(_1Vf,[_5X,_3D,_m,_1Uv,_1Us,function(_1X3,_){var _1X4=B(_1VI(_)),_1X5=rMV(_1X0),_1X6=E(E(_1WY).a),_1X7=E(_1X5),_1X8=E(_1X7.a),_1X9=E(_1X7.b),_1Xa=E(_1X7.h),_1Xb=E(_1X7.s),_1Xc=E(_1X7.u),_1Xd=B(_1GX(_1WW,_1X6.a,_1X6.b,_1X1,E(_1X3).a,_1X8.a,_1X8.b,_1X8.c,_1X8.d,_1X8.e,_1X8.f,_1X8.g,_1X8.h,_1X8.i,_1X8.j,_1X8.k,_1X9.a,_1X9.b,_1X7.c,_1X7.d,_1X7.e,_1X7.f,_1X7.g,_1Xa.a,_1Xa.b,_1X7.i,_1X7.j,_1X7.k,_1X7.l,_1X7.m,_1X7.n,_1X7.o,_1X7.p,_1X7.q,_1X7.r,_1Xb.a,_1Xb.b,_1X7.t,_1Xc.a,_1Xc.b,_1Xc.c,_1Xc.d,_1Xc.e,_1Xc.f,_1Xc.g,_1Xc.h,_1X7.v,_)),_=wMV(_1X0,_1Xd);return _gK;},_])),_1Xe=B(A(_1Vf,[_5X,_3D,_3C,_1WR,_1Ur,function(_1Xf,_){var _1Xg=E(E(_1Xf).a),_1Xh=rMV(_1X0),_1Xi=B(A(_1U5,[_1WW,_1WY,_1X1,_1Xg.a,_1Xg.b,_1Xh,_])),_=wMV(_1X0,_1Xi);return _gK;},_])),_1Xj=B(A(_1Vf,[_5X,_3D,_5c,_1WR,_1Uu,function(_1Xk,_){var _1Xl=E(_1Xk),_1Xm=rMV(_1X0),_1Xn=E(_1Xm);if(!E(E(_1Xn.u).e)){var _=wMV(_1X0,_1Xn);return _gK;}else{var _1Xo=B(_1VI(_)),_=wMV(_1X0,_1Xn);return _gK;}},_])),_1Xp=function(_){var _1Xq=rMV(_1X0),_=wMV(_1X0,new T(function(){var _1Xr=E(_1Xq),_1Xs=E(_1Xr.u);return {_:0,a:E(_1Xr.a),b:E(_1Xr.b),c:E(_1Xr.c),d:E(_1Xr.d),e:E(_1Xr.e),f:E(_1Xr.f),g:E(_1Xr.g),h:E(_1Xr.h),i:_1Xr.i,j:_1Xr.j,k:_1Xr.k,l:_1Xr.l,m:E(_1Xr.m),n:_1Xr.n,o:E(_1Xr.o),p:E(_1Xr.p),q:_1Xr.q,r:E(_1Xr.r),s:E(_1Xr.s),t:_1Xr.t,u:E({_:0,a:E(_1Xs.a),b:E(_1Xs.b),c:E(_1Xs.c),d:E(_1Xs.d),e:E(_wD),f:E(_1Xs.f),g:E(_1Xs.g),h:E(_1Xs.h)}),v:E(_1Xr.v)};}));return _gK;},_1Xt=function(_1Xu,_){var _1Xv=E(_1Xu),_1Xw=rMV(_1X0),_=wMV(_1X0,new T(function(){var _1Xx=E(_1Xw),_1Xy=E(_1Xx.u);return {_:0,a:E(_1Xx.a),b:E(_1Xx.b),c:E(_1Xx.c),d:E(_1Xx.d),e:E(_1Xx.e),f:E(_1Xx.f),g:E(_1Xx.g),h:E(_1Xx.h),i:_1Xx.i,j:_1Xx.j,k:_1Xx.k,l:_1Xx.l,m:E(_1Xx.m),n:_1Xx.n,o:E(_1Xx.o),p:E(_1Xx.p),q:_1Xx.q,r:E(_1Xx.r),s:E(_1Xx.s),t:_1Xx.t,u:E({_:0,a:E(_1Xy.a),b:E(_1Xy.b),c:E(_1Xy.c),d:E(_1Xy.d),e:E(_wE),f:E(_1Xy.f),g:E(_1Xy.g),h:E(_1Xy.h)}),v:E(_1Xx.v)};})),_1Xz=B(A(_1Wp,[_5X,_1UQ,_1Xp,_]));return _gK;},_1XA=B(A(_1Vf,[_5X,_3D,_5c,_1WR,_1Ut,_1Xt,_])),_1XB=B(A(_1Wp,[_5X,_1UX,function(_){var _1XC=rMV(_1X0),_1XD=E(E(_1WY).a),_1XE=E(_1XC),_1XF=E(_1XE.a),_1XG=E(_1XE.u),_1XH=B(_1Sn(_1WW,_1XD.a,_1XD.b,_1X1,_1XF.a,_1XF.b,_1XF.c,_1XF.d,_1XF.e,_1XF.f,_1XF.g,_1XF.h,_1XF.i,_1XF.j,_1XF.k,_1XE.b,_1XE.c,_1XE.d,_1XE.e,_1XE.f,_1XE.g,_1XE.h,_1XE.i,_1XE.j,_1XE.k,_1XE.l,_1XE.m,_1XE.n,_1XE.o,_1XE.p,_1XE.q,_1XE.r,_1XE.s,_1XE.t,_1XG.a,_1XG.b,_1XG.c,_1XG.d,_1XG.e,_1XG.f,_1XG.g,_1XG.h,_1XE.v,_)),_=wMV(_1X0,_1XH);return _gK;},_]));return _gK;}}else{return new F(function(){return die(_1UT);});}}else{return new F(function(){return die(_1UT);});}},_1XI=function(_){return new F(function(){return _1WN(_);});};
var hasteMain = function() {B(A(_1XI, [0]));};window.onload = hasteMain;