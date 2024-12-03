"use strict";
var __haste_prog_id = '030880ed1a995f0d12cab000f15ee95ff9f3fd1d04c882e586c15e7f0a84664f';
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

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8="metaKey",_9="shiftKey",_a="altKey",_b="ctrlKey",_c="keyCode",_d=function(_e,_){var _f=__get(_e,E(_c)),_g=__get(_e,E(_b)),_h=__get(_e,E(_a)),_i=__get(_e,E(_9)),_j=__get(_e,E(_8));return new T(function(){var _k=Number(_f),_l=jsTrunc(_k);return new T5(0,_l,E(_g),E(_h),E(_i),E(_j));});},_m=function(_n,_o,_){return new F(function(){return _d(E(_o),_);});},_p="keydown",_q="keyup",_r="keypress",_s=function(_t){switch(E(_t)){case 0:return E(_r);case 1:return E(_q);default:return E(_p);}},_u=new T2(0,_s,_m),_v="deltaZ",_w="deltaY",_x="deltaX",_y=function(_z,_A){var _B=E(_z);return (_B._==0)?E(_A):new T2(1,_B.a,new T(function(){return B(_y(_B.b,_A));}));},_C=function(_D,_E){var _F=jsShowI(_D);return new F(function(){return _y(fromJSStr(_F),_E);});},_G=41,_H=40,_I=function(_J,_K,_L){if(_K>=0){return new F(function(){return _C(_K,_L);});}else{if(_J<=6){return new F(function(){return _C(_K,_L);});}else{return new T2(1,_H,new T(function(){var _M=jsShowI(_K);return B(_y(fromJSStr(_M),new T2(1,_G,_L)));}));}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_I(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_I(0,_R,_P));}))));});},_S=function(_T,_){return new T(function(){var _U=Number(E(_T)),_V=jsTrunc(_U);if(_V<0){return B(_Q(_V));}else{if(_V>2){return B(_Q(_V));}else{return _V;}}});},_W=0,_X=new T3(0,_W,_W,_W),_Y="button",_Z=new T(function(){return eval("jsGetMouseCoords");}),_10=__Z,_11=function(_12,_){var _13=E(_12);if(!_13._){return _10;}else{var _14=B(_11(_13.b,_));return new T2(1,new T(function(){var _15=Number(E(_13.a));return jsTrunc(_15);}),_14);}},_16=function(_17,_){var _18=__arr2lst(0,_17);return new F(function(){return _11(_18,_);});},_19=function(_1a,_){return new F(function(){return _16(E(_1a),_);});},_1b=function(_1c,_){return new T(function(){var _1d=Number(E(_1c));return jsTrunc(_1d);});},_1e=new T2(0,_1b,_19),_1f=function(_1g,_){var _1h=E(_1g);if(!_1h._){return _10;}else{var _1i=B(_1f(_1h.b,_));return new T2(1,_1h.a,_1i);}},_1j=new T(function(){return B(unCStr("base"));}),_1k=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1l=new T(function(){return B(unCStr("IOException"));}),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1j,_1k,_1l),_1n=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_10,_10),_1o=function(_1p){return E(_1n);},_1q=function(_1r){return E(E(_1r).a);},_1s=function(_1t,_1u,_1v){var _1w=B(A1(_1t,_)),_1x=B(A1(_1u,_)),_1y=hs_eqWord64(_1w.a,_1x.a);if(!_1y){return __Z;}else{var _1z=hs_eqWord64(_1w.b,_1x.b);return (!_1z)?__Z:new T1(1,_1v);}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1s(B(_1q(_1C.a)),_1o,_1C.b);});},_1D=new T(function(){return B(unCStr(": "));}),_1E=new T(function(){return B(unCStr(")"));}),_1F=new T(function(){return B(unCStr(" ("));}),_1G=new T(function(){return B(unCStr("interrupted"));}),_1H=new T(function(){return B(unCStr("system error"));}),_1I=new T(function(){return B(unCStr("unsatisified constraints"));}),_1J=new T(function(){return B(unCStr("user error"));}),_1K=new T(function(){return B(unCStr("permission denied"));}),_1L=new T(function(){return B(unCStr("illegal operation"));}),_1M=new T(function(){return B(unCStr("end of file"));}),_1N=new T(function(){return B(unCStr("resource exhausted"));}),_1O=new T(function(){return B(unCStr("resource busy"));}),_1P=new T(function(){return B(unCStr("does not exist"));}),_1Q=new T(function(){return B(unCStr("already exists"));}),_1R=new T(function(){return B(unCStr("resource vanished"));}),_1S=new T(function(){return B(unCStr("timeout"));}),_1T=new T(function(){return B(unCStr("unsupported operation"));}),_1U=new T(function(){return B(unCStr("hardware fault"));}),_1V=new T(function(){return B(unCStr("inappropriate type"));}),_1W=new T(function(){return B(unCStr("invalid argument"));}),_1X=new T(function(){return B(unCStr("failed"));}),_1Y=new T(function(){return B(unCStr("protocol error"));}),_1Z=function(_20,_21){switch(E(_20)){case 0:return new F(function(){return _y(_1Q,_21);});break;case 1:return new F(function(){return _y(_1P,_21);});break;case 2:return new F(function(){return _y(_1O,_21);});break;case 3:return new F(function(){return _y(_1N,_21);});break;case 4:return new F(function(){return _y(_1M,_21);});break;case 5:return new F(function(){return _y(_1L,_21);});break;case 6:return new F(function(){return _y(_1K,_21);});break;case 7:return new F(function(){return _y(_1J,_21);});break;case 8:return new F(function(){return _y(_1I,_21);});break;case 9:return new F(function(){return _y(_1H,_21);});break;case 10:return new F(function(){return _y(_1Y,_21);});break;case 11:return new F(function(){return _y(_1X,_21);});break;case 12:return new F(function(){return _y(_1W,_21);});break;case 13:return new F(function(){return _y(_1V,_21);});break;case 14:return new F(function(){return _y(_1U,_21);});break;case 15:return new F(function(){return _y(_1T,_21);});break;case 16:return new F(function(){return _y(_1S,_21);});break;case 17:return new F(function(){return _y(_1R,_21);});break;default:return new F(function(){return _y(_1G,_21);});}},_22=new T(function(){return B(unCStr("}"));}),_23=new T(function(){return B(unCStr("{handle: "));}),_24=function(_25,_26,_27,_28,_29,_2a){var _2b=new T(function(){var _2c=new T(function(){var _2d=new T(function(){var _2e=E(_28);if(!_2e._){return E(_2a);}else{var _2f=new T(function(){return B(_y(_2e,new T(function(){return B(_y(_1E,_2a));},1)));},1);return B(_y(_1F,_2f));}},1);return B(_1Z(_26,_2d));}),_2g=E(_27);if(!_2g._){return E(_2c);}else{return B(_y(_2g,new T(function(){return B(_y(_1D,_2c));},1)));}}),_2h=E(_29);if(!_2h._){var _2i=E(_25);if(!_2i._){return E(_2b);}else{var _2j=E(_2i.a);if(!_2j._){var _2k=new T(function(){var _2l=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2l));},1);return new F(function(){return _y(_23,_2k);});}else{var _2m=new T(function(){var _2n=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2n));},1);return new F(function(){return _y(_23,_2m);});}}}else{return new F(function(){return _y(_2h.a,new T(function(){return B(_y(_1D,_2b));},1));});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _24(_2q.a,_2q.b,_2q.c,_2q.d,_2q.f,_10);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _24(_2v.a,_2v.b,_2v.c,_2v.d,_2v.f,_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _24(_2z.a,_2z.b,_2z.c,_2z.d,_2z.f,_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H._){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=new T(function(){var _2J=new T(function(){var _2K=function(_2L){var _2M=E(_2L);if(!_2M._){return E(new T2(1,_2B,_2G));}else{var _2N=new T(function(){return B(A2(_2E,_2M.a,new T(function(){return B(_2K(_2M.b));})));});return new T2(1,_2A,_2N);}};return B(_2K(_2H.b));});return B(A2(_2E,_2H.a,_2J));});return new T2(1,_2C,_2I);}},_2O=function(_2P,_2Q){return new F(function(){return _2D(_2w,_2P,_2Q);});},_2R=new T3(0,_2r,_2o,_2O),_2S=new T(function(){return new T5(0,_1o,_2R,_2T,_1A,_2o);}),_2T=function(_2U){return new T2(0,_2S,_2U);},_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_0,_2V,_10,_2W,_0,_0),_2Y=new T(function(){return B(_2T(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1f(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_3d,_3e,_){if(E(_3d)==7){var _3f=__app1(E(_Z),_3e),_3g=B(_32(_1e,_1e,_3f,_)),_3h=__get(_3e,E(_x)),_3i=__get(_3e,E(_w)),_3j=__get(_3e,E(_v));return new T(function(){return new T3(0,E(_3g),E(_0),E(new T3(0,_3h,_3i,_3j)));});}else{var _3k=__app1(E(_Z),_3e),_3l=B(_32(_1e,_1e,_3k,_)),_3m=__get(_3e,E(_Y)),_3n=__eq(_3m,E(_7));if(!E(_3n)){var _3o=__isUndef(_3m);if(!E(_3o)){var _3p=B(_S(_3m,_));return new T(function(){return new T3(0,E(_3l),E(new T1(1,_3p)),E(_X));});}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}},_3q=function(_3r,_3s,_){return new F(function(){return _3c(_3r,E(_3s),_);});},_3t="mouseout",_3u="mouseover",_3v="mousemove",_3w="mouseup",_3x="mousedown",_3y="dblclick",_3z="click",_3A="wheel",_3B=function(_3C){switch(E(_3C)){case 0:return E(_3z);case 1:return E(_3y);case 2:return E(_3x);case 3:return E(_3w);case 4:return E(_3v);case 5:return E(_3u);case 6:return E(_3t);default:return E(_3A);}},_3D=new T2(0,_3B,_3q),_3E=function(_3F){return E(_3F);},_3G=function(_3H,_3I){return E(_3H)==E(_3I);},_3J=function(_3K,_3L){return E(_3K)!=E(_3L);},_3M=new T2(0,_3G,_3J),_3N="screenY",_3O="screenX",_3P="clientY",_3Q="clientX",_3R="pageY",_3S="pageX",_3T="target",_3U="identifier",_3V=function(_3W,_){var _3X=__get(_3W,E(_3U)),_3Y=__get(_3W,E(_3T)),_3Z=__get(_3W,E(_3S)),_40=__get(_3W,E(_3R)),_41=__get(_3W,E(_3Q)),_42=__get(_3W,E(_3P)),_43=__get(_3W,E(_3O)),_44=__get(_3W,E(_3N));return new T(function(){var _45=Number(_3X),_46=jsTrunc(_45);return new T5(0,_46,_3Y,E(new T2(0,new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}),new T(function(){var _48=Number(_40);return jsTrunc(_48);}))),E(new T2(0,new T(function(){var _49=Number(_41);return jsTrunc(_49);}),new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}))),E(new T2(0,new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}),new T(function(){var _4c=Number(_44);return jsTrunc(_4c);}))));});},_4d=function(_4e,_){var _4f=E(_4e);if(!_4f._){return _10;}else{var _4g=B(_3V(E(_4f.a),_)),_4h=B(_4d(_4f.b,_));return new T2(1,_4g,_4h);}},_4i="touches",_4j=function(_4k){return E(E(_4k).b);},_4l=function(_4m,_4n,_){var _4o=__arr2lst(0,_4n),_4p=new T(function(){return B(_4j(_4m));}),_4q=function(_4r,_){var _4s=E(_4r);if(!_4s._){return _10;}else{var _4t=B(A2(_4p,_4s.a,_)),_4u=B(_4q(_4s.b,_));return new T2(1,_4t,_4u);}};return new F(function(){return _4q(_4o,_);});},_4v=function(_4w,_){return new F(function(){return _4l(_1e,E(_4w),_);});},_4x=new T2(0,_19,_4v),_4y=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4z=function(_4A){return E(E(_4A).a);},_4B=function(_4C,_4D,_4E){while(1){var _4F=E(_4E);if(!_4F._){return false;}else{if(!B(A3(_4z,_4C,_4D,_4F.a))){_4E=_4F.b;continue;}else{return true;}}}},_4G=function(_4H,_4I){while(1){var _4J=B((function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=_4M.b;if(!B(A1(_4K,_4N))){var _4P=_4K;_4H=_4P;_4I=_4O;return __continue;}else{return new T2(1,_4N,new T(function(){return B(_4G(_4K,_4O));}));}}})(_4H,_4I));if(_4J!=__continue){return _4J;}}},_4Q=function(_4R,_){var _4S=__get(_4R,E(_4i)),_4T=__arr2lst(0,_4S),_4U=B(_4d(_4T,_)),_4V=__app1(E(_4y),_4R),_4W=B(_32(_4x,_4x,_4V,_)),_4X=E(_4W),_4Y=new T(function(){var _4Z=function(_50){return new F(function(){return _4B(_3M,new T(function(){return E(_50).a;}),_4X.a);});};return B(_4G(_4Z,_4U));}),_51=new T(function(){var _52=function(_53){return new F(function(){return _4B(_3M,new T(function(){return E(_53).a;}),_4X.b);});};return B(_4G(_52,_4U));});return new T3(0,_4U,_51,_4Y);},_54=function(_55,_56,_){return new F(function(){return _4Q(E(_56),_);});},_57="touchcancel",_58="touchend",_59="touchmove",_5a="touchstart",_5b=function(_5c){switch(E(_5c)){case 0:return E(_5a);case 1:return E(_59);case 2:return E(_58);default:return E(_57);}},_5d=new T2(0,_5b,_54),_5e=function(_5f,_5g,_){var _5h=B(A1(_5f,_)),_5i=B(A1(_5g,_));return _5h;},_5j=function(_5k,_5l,_){var _5m=B(A1(_5k,_)),_5n=B(A1(_5l,_));return new T(function(){return B(A1(_5m,_5n));});},_5o=function(_5p,_5q,_){var _5r=B(A1(_5q,_));return _5p;},_5s=function(_5t,_5u,_){var _5v=B(A1(_5u,_));return new T(function(){return B(A1(_5t,_5v));});},_5w=new T2(0,_5s,_5o),_5x=function(_5y,_){return _5y;},_5z=function(_5A,_5B,_){var _5C=B(A1(_5A,_));return new F(function(){return A1(_5B,_);});},_5D=new T5(0,_5w,_5x,_5j,_5z,_5e),_5E=new T(function(){return E(_2S);}),_5F=function(_5G){return E(E(_5G).c);},_5H=function(_5I){return new T6(0,_0,_2V,_10,_5I,_0,_0);},_5J=function(_5K,_){var _5L=new T(function(){return B(A2(_5F,_5E,new T(function(){return B(A1(_5H,_5K));})));});return new F(function(){return die(_5L);});},_5M=function(_5N,_){return new F(function(){return _5J(_5N,_);});},_5O=function(_5P){return new F(function(){return A1(_5M,_5P);});},_5Q=function(_5R,_5S,_){var _5T=B(A1(_5R,_));return new F(function(){return A2(_5S,_5T,_);});},_5U=new T5(0,_5D,_5Q,_5z,_5x,_5O),_5V=function(_5W){return E(_5W);},_5X=new T2(0,_5U,_5V),_5Y=new T2(0,_5X,_5x),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_60=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_61=new T(function(){return eval("(function(cv){return cv.height})");}),_62=new T(function(){return eval("(function(cv){return cv.width})");}),_63=function(_64,_){var _65=__app1(E(_62),_64),_66=__app1(E(_61),_64),_67=__app1(E(_60),_64),_68=__app1(E(_5Z),_64);return new T2(0,new T2(0,_65,_66),new T2(0,_67,_68));},_69=function(_6a,_6b){while(1){var _6c=E(_6a);if(!_6c._){return (E(_6b)._==0)?true:false;}else{var _6d=E(_6b);if(!_6d._){return false;}else{if(E(_6c.a)!=E(_6d.a)){return false;}else{_6a=_6c.b;_6b=_6d.b;continue;}}}}},_6e=function(_6f,_6g){var _6h=E(_6g);return (_6h._==0)?__Z:new T2(1,new T(function(){return B(A1(_6f,_6h.a));}),new T(function(){return B(_6e(_6f,_6h.b));}));},_6i=function(_6j){return new T1(3,E(B(_6e(_5V,_6j))));},_6k="Tried to deserialie a non-array to a list!",_6l=new T1(0,_6k),_6m=new T1(1,_10),_6n=function(_6o){var _6p=E(_6o);if(!_6p._){return E(_6m);}else{var _6q=B(_6n(_6p.b));return (_6q._==0)?new T1(0,_6q.a):new T1(1,new T2(1,_6p.a,_6q.a));}},_6r=function(_6s){var _6t=E(_6s);if(_6t._==3){return new F(function(){return _6n(_6t.a);});}else{return E(_6l);}},_6u=function(_6v){return new T1(1,_6v);},_6w=new T4(0,_5V,_6i,_6u,_6r),_6x=function(_6y,_6z,_6A){return new F(function(){return A1(_6y,new T2(1,_2A,new T(function(){return B(A1(_6z,_6A));})));});},_6B=function(_6C){return new F(function(){return _I(0,E(_6C),_10);});},_6D=34,_6E=new T2(1,_6D,_10),_6F=new T(function(){return B(unCStr("!!: negative index"));}),_6G=new T(function(){return B(unCStr("Prelude."));}),_6H=new T(function(){return B(_y(_6G,_6F));}),_6I=new T(function(){return B(err(_6H));}),_6J=new T(function(){return B(unCStr("!!: index too large"));}),_6K=new T(function(){return B(_y(_6G,_6J));}),_6L=new T(function(){return B(err(_6K));}),_6M=function(_6N,_6O){while(1){var _6P=E(_6N);if(!_6P._){return E(_6L);}else{var _6Q=E(_6O);if(!_6Q){return E(_6P.a);}else{_6N=_6P.b;_6O=_6Q-1|0;continue;}}}},_6R=function(_6S,_6T){if(_6T>=0){return new F(function(){return _6M(_6S,_6T);});}else{return E(_6I);}},_6U=new T(function(){return B(unCStr("ACK"));}),_6V=new T(function(){return B(unCStr("BEL"));}),_6W=new T(function(){return B(unCStr("BS"));}),_6X=new T(function(){return B(unCStr("SP"));}),_6Y=new T2(1,_6X,_10),_6Z=new T(function(){return B(unCStr("US"));}),_70=new T2(1,_6Z,_6Y),_71=new T(function(){return B(unCStr("RS"));}),_72=new T2(1,_71,_70),_73=new T(function(){return B(unCStr("GS"));}),_74=new T2(1,_73,_72),_75=new T(function(){return B(unCStr("FS"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("ESC"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("SUB"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("EM"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("CAN"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("ETB"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("SYN"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("NAK"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("DC4"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("DC3"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("DC2"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("DC1"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DLE"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("SI"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("SO"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("CR"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("FF"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("VT"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("LF"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("HT"));}),_7I=new T2(1,_7H,_7G),_7J=new T2(1,_6W,_7I),_7K=new T2(1,_6V,_7J),_7L=new T2(1,_6U,_7K),_7M=new T(function(){return B(unCStr("ENQ"));}),_7N=new T2(1,_7M,_7L),_7O=new T(function(){return B(unCStr("EOT"));}),_7P=new T2(1,_7O,_7N),_7Q=new T(function(){return B(unCStr("ETX"));}),_7R=new T2(1,_7Q,_7P),_7S=new T(function(){return B(unCStr("STX"));}),_7T=new T2(1,_7S,_7R),_7U=new T(function(){return B(unCStr("SOH"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("NUL"));}),_7X=new T2(1,_7W,_7V),_7Y=92,_7Z=new T(function(){return B(unCStr("\\DEL"));}),_80=new T(function(){return B(unCStr("\\a"));}),_81=new T(function(){return B(unCStr("\\\\"));}),_82=new T(function(){return B(unCStr("\\SO"));}),_83=new T(function(){return B(unCStr("\\r"));}),_84=new T(function(){return B(unCStr("\\f"));}),_85=new T(function(){return B(unCStr("\\v"));}),_86=new T(function(){return B(unCStr("\\n"));}),_87=new T(function(){return B(unCStr("\\t"));}),_88=new T(function(){return B(unCStr("\\b"));}),_89=function(_8a,_8b){if(_8a<=127){var _8c=E(_8a);switch(_8c){case 92:return new F(function(){return _y(_81,_8b);});break;case 127:return new F(function(){return _y(_7Z,_8b);});break;default:if(_8c<32){var _8d=E(_8c);switch(_8d){case 7:return new F(function(){return _y(_80,_8b);});break;case 8:return new F(function(){return _y(_88,_8b);});break;case 9:return new F(function(){return _y(_87,_8b);});break;case 10:return new F(function(){return _y(_86,_8b);});break;case 11:return new F(function(){return _y(_85,_8b);});break;case 12:return new F(function(){return _y(_84,_8b);});break;case 13:return new F(function(){return _y(_83,_8b);});break;case 14:return new F(function(){return _y(_82,new T(function(){var _8e=E(_8b);if(!_8e._){return __Z;}else{if(E(_8e.a)==72){return B(unAppCStr("\\&",_8e));}else{return E(_8e);}}},1));});break;default:return new F(function(){return _y(new T2(1,_7Y,new T(function(){return B(_6R(_7X,_8d));})),_8b);});}}else{return new T2(1,_8c,_8b);}}}else{var _8f=new T(function(){var _8g=jsShowI(_8a);return B(_y(fromJSStr(_8g),new T(function(){var _8h=E(_8b);if(!_8h._){return __Z;}else{var _8i=E(_8h.a);if(_8i<48){return E(_8h);}else{if(_8i>57){return E(_8h);}else{return B(unAppCStr("\\&",_8h));}}}},1)));});return new T2(1,_7Y,_8f);}},_8j=new T(function(){return B(unCStr("\\\""));}),_8k=function(_8l,_8m){var _8n=E(_8l);if(!_8n._){return E(_8m);}else{var _8o=_8n.b,_8p=E(_8n.a);if(_8p==34){return new F(function(){return _y(_8j,new T(function(){return B(_8k(_8o,_8m));},1));});}else{return new F(function(){return _89(_8p,new T(function(){return B(_8k(_8o,_8m));}));});}}},_8q=function(_8r){return new T2(1,_6D,new T(function(){return B(_8k(_8r,_6E));}));},_8s=function(_8t,_8u){if(_8t<=_8u){var _8v=function(_8w){return new T2(1,_8w,new T(function(){if(_8w!=_8u){return B(_8v(_8w+1|0));}else{return __Z;}}));};return new F(function(){return _8v(_8t);});}else{return __Z;}},_8x=function(_8y){return new F(function(){return _8s(E(_8y),2147483647);});},_8z=function(_8A,_8B,_8C){if(_8C<=_8B){var _8D=new T(function(){var _8E=_8B-_8A|0,_8F=function(_8G){return (_8G>=(_8C-_8E|0))?new T2(1,_8G,new T(function(){return B(_8F(_8G+_8E|0));})):new T2(1,_8G,_10);};return B(_8F(_8B));});return new T2(1,_8A,_8D);}else{return (_8C<=_8A)?new T2(1,_8A,_10):__Z;}},_8H=function(_8I,_8J,_8K){if(_8K>=_8J){var _8L=new T(function(){var _8M=_8J-_8I|0,_8N=function(_8O){return (_8O<=(_8K-_8M|0))?new T2(1,_8O,new T(function(){return B(_8N(_8O+_8M|0));})):new T2(1,_8O,_10);};return B(_8N(_8J));});return new T2(1,_8I,_8L);}else{return (_8K>=_8I)?new T2(1,_8I,_10):__Z;}},_8P=function(_8Q,_8R){if(_8R<_8Q){return new F(function(){return _8z(_8Q,_8R, -2147483648);});}else{return new F(function(){return _8H(_8Q,_8R,2147483647);});}},_8S=function(_8T,_8U){return new F(function(){return _8P(E(_8T),E(_8U));});},_8V=function(_8W,_8X,_8Y){if(_8X<_8W){return new F(function(){return _8z(_8W,_8X,_8Y);});}else{return new F(function(){return _8H(_8W,_8X,_8Y);});}},_8Z=function(_90,_91,_92){return new F(function(){return _8V(E(_90),E(_91),E(_92));});},_93=function(_94,_95){return new F(function(){return _8s(E(_94),E(_95));});},_96=function(_97){return E(_97);},_98=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_99=new T(function(){return B(err(_98));}),_9a=function(_9b){var _9c=E(_9b);return (_9c==( -2147483648))?E(_99):_9c-1|0;},_9d=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9e=new T(function(){return B(err(_9d));}),_9f=function(_9g){var _9h=E(_9g);return (_9h==2147483647)?E(_9e):_9h+1|0;},_9i={_:0,a:_9f,b:_9a,c:_96,d:_96,e:_8x,f:_8S,g:_93,h:_8Z},_9j=function(_9k,_9l){if(_9k<=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{if(_9l>=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{return quot(_9k-1|0,_9l)-1|0;}}},_9m=new T(function(){return B(unCStr("base"));}),_9n=new T(function(){return B(unCStr("GHC.Exception"));}),_9o=new T(function(){return B(unCStr("ArithException"));}),_9p=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9m,_9n,_9o),_9q=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9p,_10,_10),_9r=function(_9s){return E(_9q);},_9t=function(_9u){var _9v=E(_9u);return new F(function(){return _1s(B(_1q(_9v.a)),_9r,_9v.b);});},_9w=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9x=new T(function(){return B(unCStr("denormal"));}),_9y=new T(function(){return B(unCStr("divide by zero"));}),_9z=new T(function(){return B(unCStr("loss of precision"));}),_9A=new T(function(){return B(unCStr("arithmetic underflow"));}),_9B=new T(function(){return B(unCStr("arithmetic overflow"));}),_9C=function(_9D,_9E){switch(E(_9D)){case 0:return new F(function(){return _y(_9B,_9E);});break;case 1:return new F(function(){return _y(_9A,_9E);});break;case 2:return new F(function(){return _y(_9z,_9E);});break;case 3:return new F(function(){return _y(_9y,_9E);});break;case 4:return new F(function(){return _y(_9x,_9E);});break;default:return new F(function(){return _y(_9w,_9E);});}},_9F=function(_9G){return new F(function(){return _9C(_9G,_10);});},_9H=function(_9I,_9J,_9K){return new F(function(){return _9C(_9J,_9K);});},_9L=function(_9M,_9N){return new F(function(){return _2D(_9C,_9M,_9N);});},_9O=new T3(0,_9H,_9F,_9L),_9P=new T(function(){return new T5(0,_9r,_9O,_9Q,_9t,_9F);}),_9Q=function(_9R){return new T2(0,_9P,_9R);},_9S=3,_9T=new T(function(){return B(_9Q(_9S));}),_9U=new T(function(){return die(_9T);}),_9V=0,_9W=new T(function(){return B(_9Q(_9V));}),_9X=new T(function(){return die(_9W);}),_9Y=function(_9Z,_a0){var _a1=E(_a0);switch(_a1){case  -1:var _a2=E(_9Z);if(_a2==( -2147483648)){return E(_9X);}else{return new F(function(){return _9j(_a2, -1);});}break;case 0:return E(_9U);default:return new F(function(){return _9j(_9Z,_a1);});}},_a3=function(_a4,_a5){return new F(function(){return _9Y(E(_a4),E(_a5));});},_a6=0,_a7=new T2(0,_9X,_a6),_a8=function(_a9,_aa){var _ab=E(_a9),_ac=E(_aa);switch(_ac){case  -1:var _ad=E(_ab);if(_ad==( -2147483648)){return E(_a7);}else{if(_ad<=0){if(_ad>=0){var _ae=quotRemI(_ad, -1);return new T2(0,_ae.a,_ae.b);}else{var _af=quotRemI(_ad, -1);return new T2(0,_af.a,_af.b);}}else{var _ag=quotRemI(_ad-1|0, -1);return new T2(0,_ag.a-1|0,(_ag.b+( -1)|0)+1|0);}}break;case 0:return E(_9U);default:if(_ab<=0){if(_ab>=0){var _ah=quotRemI(_ab,_ac);return new T2(0,_ah.a,_ah.b);}else{if(_ac<=0){var _ai=quotRemI(_ab,_ac);return new T2(0,_ai.a,_ai.b);}else{var _aj=quotRemI(_ab+1|0,_ac);return new T2(0,_aj.a-1|0,(_aj.b+_ac|0)-1|0);}}}else{if(_ac>=0){if(_ab>=0){var _ak=quotRemI(_ab,_ac);return new T2(0,_ak.a,_ak.b);}else{if(_ac<=0){var _al=quotRemI(_ab,_ac);return new T2(0,_al.a,_al.b);}else{var _am=quotRemI(_ab+1|0,_ac);return new T2(0,_am.a-1|0,(_am.b+_ac|0)-1|0);}}}else{var _an=quotRemI(_ab-1|0,_ac);return new T2(0,_an.a-1|0,(_an.b+_ac|0)+1|0);}}}},_ao=function(_ap,_aq){var _ar=_ap%_aq;if(_ap<=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _as=E(_ar);return (_as==0)?0:_as+_aq|0;}}}else{if(_aq>=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _at=E(_ar);return (_at==0)?0:_at+_aq|0;}}}else{var _au=E(_ar);return (_au==0)?0:_au+_aq|0;}}},_av=function(_aw,_ax){var _ay=E(_ax);switch(_ay){case  -1:return E(_a6);case 0:return E(_9U);default:return new F(function(){return _ao(E(_aw),_ay);});}},_az=function(_aA,_aB){var _aC=E(_aA),_aD=E(_aB);switch(_aD){case  -1:var _aE=E(_aC);if(_aE==( -2147483648)){return E(_9X);}else{return new F(function(){return quot(_aE, -1);});}break;case 0:return E(_9U);default:return new F(function(){return quot(_aC,_aD);});}},_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=E(_aH);switch(_aJ){case  -1:var _aK=E(_aI);if(_aK==( -2147483648)){return E(_a7);}else{var _aL=quotRemI(_aK, -1);return new T2(0,_aL.a,_aL.b);}break;case 0:return E(_9U);default:var _aM=quotRemI(_aI,_aJ);return new T2(0,_aM.a,_aM.b);}},_aN=function(_aO,_aP){var _aQ=E(_aP);switch(_aQ){case  -1:return E(_a6);case 0:return E(_9U);default:return E(_aO)%_aQ;}},_aR=function(_aS){return new T1(0,_aS);},_aT=function(_aU){return new F(function(){return _aR(E(_aU));});},_aV=new T1(0,1),_aW=function(_aX){return new T2(0,E(B(_aR(E(_aX)))),E(_aV));},_aY=function(_aZ,_b0){return imul(E(_aZ),E(_b0))|0;},_b1=function(_b2,_b3){return E(_b2)+E(_b3)|0;},_b4=function(_b5,_b6){return E(_b5)-E(_b6)|0;},_b7=function(_b8){var _b9=E(_b8);return (_b9<0)? -_b9:E(_b9);},_ba=function(_bb){var _bc=E(_bb);if(!_bc._){return E(_bc.a);}else{return new F(function(){return I_toInt(_bc.a);});}},_bd=function(_be){return new F(function(){return _ba(_be);});},_bf=function(_bg){return  -E(_bg);},_bh= -1,_bi=0,_bj=1,_bk=function(_bl){var _bm=E(_bl);return (_bm>=0)?(E(_bm)==0)?E(_bi):E(_bj):E(_bh);},_bn={_:0,a:_b1,b:_b4,c:_aY,d:_bf,e:_b7,f:_bk,g:_bd},_bo=function(_bp,_bq){var _br=E(_bp),_bs=E(_bq);return (_br>_bs)?E(_br):E(_bs);},_bt=function(_bu,_bv){var _bw=E(_bu),_bx=E(_bv);return (_bw>_bx)?E(_bx):E(_bw);},_by=function(_bz,_bA){return (_bz>=_bA)?(_bz!=_bA)?2:1:0;},_bB=function(_bC,_bD){return new F(function(){return _by(E(_bC),E(_bD));});},_bE=function(_bF,_bG){return E(_bF)>=E(_bG);},_bH=function(_bI,_bJ){return E(_bI)>E(_bJ);},_bK=function(_bL,_bM){return E(_bL)<=E(_bM);},_bN=function(_bO,_bP){return E(_bO)<E(_bP);},_bQ={_:0,a:_3M,b:_bB,c:_bN,d:_bK,e:_bH,f:_bE,g:_bo,h:_bt},_bR=new T3(0,_bn,_bQ,_aW),_bS={_:0,a:_bR,b:_9i,c:_az,d:_aN,e:_a3,f:_av,g:_aF,h:_a8,i:_aT},_bT=function(_bU){var _bV=E(_bU);return new F(function(){return Math.log(_bV+(_bV+1)*Math.sqrt((_bV-1)/(_bV+1)));});},_bW=function(_bX){var _bY=E(_bX);return new F(function(){return Math.log(_bY+Math.sqrt(1+_bY*_bY));});},_bZ=function(_c0){var _c1=E(_c0);return 0.5*Math.log((1+_c1)/(1-_c1));},_c2=function(_c3,_c4){return Math.log(E(_c4))/Math.log(E(_c3));},_c5=3.141592653589793,_c6=new T1(0,1),_c7=function(_c8,_c9){var _ca=E(_c8);if(!_ca._){var _cb=_ca.a,_cc=E(_c9);if(!_cc._){var _cd=_cc.a;return (_cb!=_cd)?(_cb>_cd)?2:0:1;}else{var _ce=I_compareInt(_cc.a,_cb);return (_ce<=0)?(_ce>=0)?1:2:0;}}else{var _cf=_ca.a,_cg=E(_c9);if(!_cg._){var _ch=I_compareInt(_cf,_cg.a);return (_ch>=0)?(_ch<=0)?1:2:0;}else{var _ci=I_compare(_cf,_cg.a);return (_ci>=0)?(_ci<=0)?1:2:0;}}},_cj=function(_ck,_cl){var _cm=E(_ck);return (_cm._==0)?_cm.a*Math.pow(2,_cl):I_toNumber(_cm.a)*Math.pow(2,_cl);},_cn=function(_co,_cp){var _cq=E(_co);if(!_cq._){var _cr=_cq.a,_cs=E(_cp);return (_cs._==0)?_cr==_cs.a:(I_compareInt(_cs.a,_cr)==0)?true:false;}else{var _ct=_cq.a,_cu=E(_cp);return (_cu._==0)?(I_compareInt(_ct,_cu.a)==0)?true:false:(I_compare(_ct,_cu.a)==0)?true:false;}},_cv=function(_cw,_cx){while(1){var _cy=E(_cw);if(!_cy._){var _cz=_cy.a,_cA=E(_cx);if(!_cA._){var _cB=_cA.a,_cC=addC(_cz,_cB);if(!E(_cC.b)){return new T1(0,_cC.a);}else{_cw=new T1(1,I_fromInt(_cz));_cx=new T1(1,I_fromInt(_cB));continue;}}else{_cw=new T1(1,I_fromInt(_cz));_cx=_cA;continue;}}else{var _cD=E(_cx);if(!_cD._){_cw=_cy;_cx=new T1(1,I_fromInt(_cD.a));continue;}else{return new T1(1,I_add(_cy.a,_cD.a));}}}},_cE=function(_cF,_cG){while(1){var _cH=E(_cF);if(!_cH._){var _cI=E(_cH.a);if(_cI==( -2147483648)){_cF=new T1(1,I_fromInt( -2147483648));continue;}else{var _cJ=E(_cG);if(!_cJ._){var _cK=_cJ.a;return new T2(0,new T1(0,quot(_cI,_cK)),new T1(0,_cI%_cK));}else{_cF=new T1(1,I_fromInt(_cI));_cG=_cJ;continue;}}}else{var _cL=E(_cG);if(!_cL._){_cF=_cH;_cG=new T1(1,I_fromInt(_cL.a));continue;}else{var _cM=I_quotRem(_cH.a,_cL.a);return new T2(0,new T1(1,_cM.a),new T1(1,_cM.b));}}}},_cN=new T1(0,0),_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR._){_cP=new T1(1,I_fromInt(_cR.a));continue;}else{return new T1(1,I_shiftLeft(_cR.a,_cQ));}}},_cS=function(_cT,_cU,_cV){if(!B(_cn(_cV,_cN))){var _cW=B(_cE(_cU,_cV)),_cX=_cW.a;switch(B(_c7(B(_cO(_cW.b,1)),_cV))){case 0:return new F(function(){return _cj(_cX,_cT);});break;case 1:if(!(B(_ba(_cX))&1)){return new F(function(){return _cj(_cX,_cT);});}else{return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}break;default:return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}}else{return E(_9U);}},_cY=function(_cZ,_d0){var _d1=E(_cZ);if(!_d1._){var _d2=_d1.a,_d3=E(_d0);return (_d3._==0)?_d2>_d3.a:I_compareInt(_d3.a,_d2)<0;}else{var _d4=_d1.a,_d5=E(_d0);return (_d5._==0)?I_compareInt(_d4,_d5.a)>0:I_compare(_d4,_d5.a)>0;}},_d6=new T1(0,1),_d7=function(_d8,_d9){var _da=E(_d8);if(!_da._){var _db=_da.a,_dc=E(_d9);return (_dc._==0)?_db<_dc.a:I_compareInt(_dc.a,_db)>0;}else{var _dd=_da.a,_de=E(_d9);return (_de._==0)?I_compareInt(_dd,_de.a)<0:I_compare(_dd,_de.a)<0;}},_df=new T(function(){return B(unCStr("base"));}),_dg=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dh=new T(function(){return B(unCStr("PatternMatchFail"));}),_di=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_df,_dg,_dh),_dj=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_di,_10,_10),_dk=function(_dl){return E(_dj);},_dm=function(_dn){var _do=E(_dn);return new F(function(){return _1s(B(_1q(_do.a)),_dk,_do.b);});},_dp=function(_dq){return E(E(_dq).a);},_dr=function(_ds){return new T2(0,_dt,_ds);},_du=function(_dv,_dw){return new F(function(){return _y(E(_dv).a,_dw);});},_dx=function(_dy,_dz){return new F(function(){return _2D(_du,_dy,_dz);});},_dA=function(_dB,_dC,_dD){return new F(function(){return _y(E(_dC).a,_dD);});},_dE=new T3(0,_dA,_dp,_dx),_dt=new T(function(){return new T5(0,_dk,_dE,_dr,_dm,_dp);}),_dF=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dG=function(_dH,_dI){return new F(function(){return die(new T(function(){return B(A2(_5F,_dI,_dH));}));});},_dJ=function(_dK,_9R){return new F(function(){return _dG(_dK,_9R);});},_dL=function(_dM,_dN){var _dO=E(_dN);if(!_dO._){return new T2(0,_10,_10);}else{var _dP=_dO.a;if(!B(A1(_dM,_dP))){return new T2(0,_10,_dO);}else{var _dQ=new T(function(){var _dR=B(_dL(_dM,_dO.b));return new T2(0,_dR.a,_dR.b);});return new T2(0,new T2(1,_dP,new T(function(){return E(E(_dQ).a);})),new T(function(){return E(E(_dQ).b);}));}}},_dS=32,_dT=new T(function(){return B(unCStr("\n"));}),_dU=function(_dV){return (E(_dV)==124)?false:true;},_dW=function(_dX,_dY){var _dZ=B(_dL(_dU,B(unCStr(_dX)))),_e0=_dZ.a,_e1=function(_e2,_e3){var _e4=new T(function(){var _e5=new T(function(){return B(_y(_dY,new T(function(){return B(_y(_e3,_dT));},1)));});return B(unAppCStr(": ",_e5));},1);return new F(function(){return _y(_e2,_e4);});},_e6=E(_dZ.b);if(!_e6._){return new F(function(){return _e1(_e0,_10);});}else{if(E(_e6.a)==124){return new F(function(){return _e1(_e0,new T2(1,_dS,_e6.b));});}else{return new F(function(){return _e1(_e0,_10);});}}},_e7=function(_e8){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_e8,_dF));})),_dt);});},_e9=function(_ea){var _eb=function(_ec,_ed){while(1){if(!B(_d7(_ec,_ea))){if(!B(_cY(_ec,_ea))){if(!B(_cn(_ec,_ea))){return new F(function(){return _e7("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ed);}}else{return _ed-1|0;}}else{var _ee=B(_cO(_ec,1)),_ef=_ed+1|0;_ec=_ee;_ed=_ef;continue;}}};return new F(function(){return _eb(_d6,0);});},_eg=function(_eh){var _ei=E(_eh);if(!_ei._){var _ej=_ei.a>>>0;if(!_ej){return  -1;}else{var _ek=function(_el,_em){while(1){if(_el>=_ej){if(_el<=_ej){if(_el!=_ej){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_em);}}else{return _em-1|0;}}else{var _en=imul(_el,2)>>>0,_eo=_em+1|0;_el=_en;_em=_eo;continue;}}};return new F(function(){return _ek(1,0);});}}else{return new F(function(){return _e9(_ei);});}},_ep=function(_eq){var _er=E(_eq);if(!_er._){var _es=_er.a>>>0;if(!_es){return new T2(0, -1,0);}else{var _et=function(_eu,_ev){while(1){if(_eu>=_es){if(_eu<=_es){if(_eu!=_es){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ev);}}else{return _ev-1|0;}}else{var _ew=imul(_eu,2)>>>0,_ex=_ev+1|0;_eu=_ew;_ev=_ex;continue;}}};return new T2(0,B(_et(1,0)),(_es&_es-1>>>0)>>>0&4294967295);}}else{var _ey=_er.a;return new T2(0,B(_eg(_er)),I_compareInt(I_and(_ey,I_sub(_ey,I_fromInt(1))),0));}},_ez=function(_eA,_eB){var _eC=E(_eA);if(!_eC._){var _eD=_eC.a,_eE=E(_eB);return (_eE._==0)?_eD<=_eE.a:I_compareInt(_eE.a,_eD)>=0;}else{var _eF=_eC.a,_eG=E(_eB);return (_eG._==0)?I_compareInt(_eF,_eG.a)<=0:I_compare(_eF,_eG.a)<=0;}},_eH=function(_eI,_eJ){while(1){var _eK=E(_eI);if(!_eK._){var _eL=_eK.a,_eM=E(_eJ);if(!_eM._){return new T1(0,(_eL>>>0&_eM.a>>>0)>>>0&4294967295);}else{_eI=new T1(1,I_fromInt(_eL));_eJ=_eM;continue;}}else{var _eN=E(_eJ);if(!_eN._){_eI=_eK;_eJ=new T1(1,I_fromInt(_eN.a));continue;}else{return new T1(1,I_and(_eK.a,_eN.a));}}}},_eO=function(_eP,_eQ){while(1){var _eR=E(_eP);if(!_eR._){var _eS=_eR.a,_eT=E(_eQ);if(!_eT._){var _eU=_eT.a,_eV=subC(_eS,_eU);if(!E(_eV.b)){return new T1(0,_eV.a);}else{_eP=new T1(1,I_fromInt(_eS));_eQ=new T1(1,I_fromInt(_eU));continue;}}else{_eP=new T1(1,I_fromInt(_eS));_eQ=_eT;continue;}}else{var _eW=E(_eQ);if(!_eW._){_eP=_eR;_eQ=new T1(1,I_fromInt(_eW.a));continue;}else{return new T1(1,I_sub(_eR.a,_eW.a));}}}},_eX=new T1(0,2),_eY=function(_eZ,_f0){var _f1=E(_eZ);if(!_f1._){var _f2=(_f1.a>>>0&(2<<_f0>>>0)-1>>>0)>>>0,_f3=1<<_f0>>>0;return (_f3<=_f2)?(_f3>=_f2)?1:2:0;}else{var _f4=B(_eH(_f1,B(_eO(B(_cO(_eX,_f0)),_d6)))),_f5=B(_cO(_d6,_f0));return (!B(_cY(_f5,_f4)))?(!B(_d7(_f5,_f4)))?1:2:0;}},_f6=function(_f7,_f8){while(1){var _f9=E(_f7);if(!_f9._){_f7=new T1(1,I_fromInt(_f9.a));continue;}else{return new T1(1,I_shiftRight(_f9.a,_f8));}}},_fa=function(_fb,_fc,_fd,_fe){var _ff=B(_ep(_fe)),_fg=_ff.a;if(!E(_ff.b)){var _fh=B(_eg(_fd));if(_fh<((_fg+_fb|0)-1|0)){var _fi=_fg+(_fb-_fc|0)|0;if(_fi>0){if(_fi>_fh){if(_fi<=(_fh+1|0)){if(!E(B(_ep(_fd)).b)){return 0;}else{return new F(function(){return _cj(_c6,_fb-_fc|0);});}}else{return 0;}}else{var _fj=B(_f6(_fd,_fi));switch(B(_eY(_fd,_fi-1|0))){case 0:return new F(function(){return _cj(_fj,_fb-_fc|0);});break;case 1:if(!(B(_ba(_fj))&1)){return new F(function(){return _cj(_fj,_fb-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}break;default:return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}}}else{return new F(function(){return _cj(_fd,(_fb-_fc|0)-_fi|0);});}}else{if(_fh>=_fc){var _fk=B(_f6(_fd,(_fh+1|0)-_fc|0));switch(B(_eY(_fd,_fh-_fc|0))){case 0:return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});break;case 2:return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});break;default:if(!(B(_ba(_fk))&1)){return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});}}}else{return new F(function(){return _cj(_fd, -_fg);});}}}else{var _fl=B(_eg(_fd))-_fg|0,_fm=function(_fn){var _fo=function(_fp,_fq){if(!B(_ez(B(_cO(_fq,_fc)),_fp))){return new F(function(){return _cS(_fn-_fc|0,_fp,_fq);});}else{return new F(function(){return _cS((_fn-_fc|0)+1|0,_fp,B(_cO(_fq,1)));});}};if(_fn>=_fc){if(_fn!=_fc){return new F(function(){return _fo(_fd,new T(function(){return B(_cO(_fe,_fn-_fc|0));}));});}else{return new F(function(){return _fo(_fd,_fe);});}}else{return new F(function(){return _fo(new T(function(){return B(_cO(_fd,_fc-_fn|0));}),_fe);});}};if(_fb>_fl){return new F(function(){return _fm(_fb);});}else{return new F(function(){return _fm(_fl);});}}},_fr=new T1(0,2147483647),_fs=new T(function(){return B(_cv(_fr,_d6));}),_ft=function(_fu){var _fv=E(_fu);if(!_fv._){var _fw=E(_fv.a);return (_fw==( -2147483648))?E(_fs):new T1(0, -_fw);}else{return new T1(1,I_negate(_fv.a));}},_fx=new T(function(){return 0/0;}),_fy=new T(function(){return  -1/0;}),_fz=new T(function(){return 1/0;}),_fA=0,_fB=function(_fC,_fD){if(!B(_cn(_fD,_cN))){if(!B(_cn(_fC,_cN))){if(!B(_d7(_fC,_cN))){return new F(function(){return _fa( -1021,53,_fC,_fD);});}else{return  -B(_fa( -1021,53,B(_ft(_fC)),_fD));}}else{return E(_fA);}}else{return (!B(_cn(_fC,_cN)))?(!B(_d7(_fC,_cN)))?E(_fz):E(_fy):E(_fx);}},_fE=function(_fF){var _fG=E(_fF);return new F(function(){return _fB(_fG.a,_fG.b);});},_fH=function(_fI){return 1/E(_fI);},_fJ=function(_fK){var _fL=E(_fK);return (_fL!=0)?(_fL<=0)? -_fL:E(_fL):E(_fA);},_fM=function(_fN){var _fO=E(_fN);if(!_fO._){return _fO.a;}else{return new F(function(){return I_toNumber(_fO.a);});}},_fP=function(_fQ){return new F(function(){return _fM(_fQ);});},_fR=1,_fS= -1,_fT=function(_fU){var _fV=E(_fU);return (_fV<=0)?(_fV>=0)?E(_fV):E(_fS):E(_fR);},_fW=function(_fX,_fY){return E(_fX)-E(_fY);},_fZ=function(_g0){return  -E(_g0);},_g1=function(_g2,_g3){return E(_g2)+E(_g3);},_g4=function(_g5,_g6){return E(_g5)*E(_g6);},_g7={_:0,a:_g1,b:_fW,c:_g4,d:_fZ,e:_fJ,f:_fT,g:_fP},_g8=function(_g9,_ga){return E(_g9)/E(_ga);},_gb=new T4(0,_g7,_g8,_fH,_fE),_gc=function(_gd){return new F(function(){return Math.acos(E(_gd));});},_ge=function(_gf){return new F(function(){return Math.asin(E(_gf));});},_gg=function(_gh){return new F(function(){return Math.atan(E(_gh));});},_gi=function(_gj){return new F(function(){return Math.cos(E(_gj));});},_gk=function(_gl){return new F(function(){return cosh(E(_gl));});},_gm=function(_gn){return new F(function(){return Math.exp(E(_gn));});},_go=function(_gp){return new F(function(){return Math.log(E(_gp));});},_gq=function(_gr,_gs){return new F(function(){return Math.pow(E(_gr),E(_gs));});},_gt=function(_gu){return new F(function(){return Math.sin(E(_gu));});},_gv=function(_gw){return new F(function(){return sinh(E(_gw));});},_gx=function(_gy){return new F(function(){return Math.sqrt(E(_gy));});},_gz=function(_gA){return new F(function(){return Math.tan(E(_gA));});},_gB=function(_gC){return new F(function(){return tanh(E(_gC));});},_gD={_:0,a:_gb,b:_c5,c:_gm,d:_go,e:_gx,f:_gq,g:_c2,h:_gt,i:_gi,j:_gz,k:_ge,l:_gc,m:_gg,n:_gv,o:_gk,p:_gB,q:_bW,r:_bT,s:_bZ},_gE=0,_gF=function(_){return _gE;},_gG=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gH=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gI=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gJ=function(_gK,_gL,_gM,_){var _gN=__app1(E(_gH),_gM),_gO=__app2(E(_gI),_gM,E(_gK)),_gP=B(A2(_gL,_gM,_)),_gQ=__app1(E(_gG),_gM);return new F(function(){return _gF(_);});},_gR=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gS=function(_gT,_gU,_gV,_gW,_){var _gX=__app1(E(_gH),_gW),_gY=__app3(E(_gR),_gW,E(_gT),E(_gU)),_gZ=B(A2(_gV,_gW,_)),_h0=__app1(E(_gG),_gW);return new F(function(){return _gF(_);});},_h1=function(_h2,_h3){return E(_h2)!=E(_h3);},_h4=function(_h5,_h6){return E(_h5)==E(_h6);},_h7=new T2(0,_h4,_h1),_h8=function(_h9){return E(E(_h9).a);},_ha=function(_hb){return E(E(_hb).a);},_hc=function(_hd){return E(E(_hd).b);},_he=function(_hf){return E(E(_hf).g);},_hg=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hh=0,_hi=3.3333333333333335,_hj=16.666666666666668,_hk=function(_hl){return E(E(_hl).b);},_hm=new T1(0,0),_hn=new T1(0,2),_ho=function(_hp){return E(E(_hp).i);},_hq=function(_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy){var _hz=new T(function(){var _hA=E(_hy);if(_hA<=31){return B(_4B(_h7,_hA,_hg));}else{if(_hA>=128){return B(_4B(_h7,_hA,_hg));}else{return true;}}}),_hB=new T(function(){if(E(_hu)==8){return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28+20;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20+8*(E(_hv)-1);}));}else{return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20;}));}}),_hC=new T(function(){var _hD=B(_h8(_hr));if(!E(_hz)){return B(A2(_he,B(_ha(_hD)),_hm));}else{return B(A3(_hc,_hD,new T(function(){return B(_hk(_hr));}),new T(function(){return B(A2(_he,B(_ha(_hD)),_hn));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hB).a);}),new T(function(){return E(E(_hB).b);})),new T2(0,new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hi);}}),new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hj);}})),_hC);},_hE=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hF=function(_hG,_hH,_hI){var _hJ=new T(function(){return toJSStr(E(_hI));});return function(_hK,_){var _hL=__app4(E(_hE),E(_hK),E(_hJ),E(_hG),E(_hH));return new F(function(){return _gF(_);});};},_hM=0,_hN=",",_hO="rgba(",_hP=new T(function(){return toJSStr(_10);}),_hQ="rgb(",_hR=")",_hS=new T2(1,_hR,_10),_hT=function(_hU){var _hV=E(_hU);if(!_hV._){var _hW=jsCat(new T2(1,_hQ,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),_hS)))))),E(_hP));return E(_hW);}else{var _hX=jsCat(new T2(1,_hO,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.d);}),_hS)))))))),E(_hP));return E(_hX);}},_hY="strokeStyle",_hZ="fillStyle",_i0=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i1=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i2=function(_i3,_i4){var _i5=new T(function(){return B(_hT(_i3));});return function(_i6,_){var _i7=E(_i6),_i8=E(_hZ),_i9=E(_i0),_ia=__app2(_i9,_i7,_i8),_ib=E(_hY),_ic=__app2(_i9,_i7,_ib),_id=E(_i5),_ie=E(_i1),_if=__app3(_ie,_i7,_i8,_id),_ig=__app3(_ie,_i7,_ib,_id),_ih=B(A2(_i4,_i7,_)),_ii=String(_ia),_ij=__app3(_ie,_i7,_i8,_ii),_ik=String(_ic),_il=__app3(_ie,_i7,_ib,_ik);return new F(function(){return _gF(_);});};},_im="font",_in=function(_io,_ip){var _iq=new T(function(){return toJSStr(E(_io));});return function(_ir,_){var _is=E(_ir),_it=E(_im),_iu=__app2(E(_i0),_is,_it),_iv=E(_i1),_iw=__app3(_iv,_is,_it,E(_iq)),_ix=B(A2(_ip,_is,_)),_iy=String(_iu),_iz=__app3(_iv,_is,_it,_iy);return new F(function(){return _gF(_);});};},_iA=new T(function(){return B(unCStr("px IPAGothic"));}),_iB=function(_iC,_iD,_iE,_iF,_iG,_iH,_iI,_){var _iJ=new T(function(){var _iK=new T(function(){var _iL=B(_hq(_gD,_bS,_bS,_iE,_iF,_iG,_iH,_iI)),_iM=E(_iL.a),_iN=E(_iL.b);return new T5(0,_iM.a,_iM.b,_iN.a,_iN.b,_iL.c);}),_iO=new T(function(){var _iP=E(_iK);return E(_iP.a)+E(_iP.c);}),_iQ=new T(function(){var _iR=E(_iK);return E(_iR.b)-E(_iR.d);}),_iS=new T(function(){return E(E(_iK).e);}),_iT=new T(function(){return B(_hF(_hM,_hM,new T2(1,_iI,_10)));}),_iU=function(_iV,_){return new F(function(){return _gJ(_iS,_iT,E(_iV),_);});};return B(_in(new T(function(){return B(_y(B(_I(0,E(_iE),_10)),_iA));},1),function(_iW,_){return new F(function(){return _gS(_iO,_iQ,_iU,E(_iW),_);});}));});return new F(function(){return A(_i2,[_iD,_iJ,_iC,_]);});},_iX=new T3(0,153,255,255),_iY=new T2(1,_iX,_10),_iZ=new T3(0,255,153,204),_j0=new T2(1,_iZ,_iY),_j1=new T3(0,255,204,153),_j2=new T2(1,_j1,_j0),_j3=new T3(0,200,255,200),_j4=new T2(1,_j3,_j2),_j5=20,_j6=64,_j7=1,_j8=2,_j9=8,_ja=function(_jb,_jc,_jd,_je,_jf,_jg,_jh,_){while(1){var _ji=B((function(_jj,_jk,_jl,_jm,_jn,_jo,_jp,_){var _jq=E(_jp);if(!_jq._){return _gE;}else{var _jr=_jq.b,_js=E(_jq.a),_jt=E(_js);switch(_jt){case 10:var _ju=_jj,_jv=_jk,_jw=_jm,_jx=_jm;_jb=_ju;_jc=_jv;_jd=0;_je=_jw;_jf=new T(function(){return E(_jn)-1|0;});_jg=_jx;_jh=_jr;return __continue;case 123:return new F(function(){return _jy(_jj,_jk,_jl,_jm,_jn,_jo,_jr,_);});break;case 65306:var _jz=new T(function(){return B(_6R(_j4,_jl));}),_jA=function(_jB,_jC,_jD,_jE,_jF,_jG,_){while(1){var _jH=B((function(_jI,_jJ,_jK,_jL,_jM,_jN,_){var _jO=E(_jN);if(!_jO._){return _gE;}else{var _jP=_jO.b,_jQ=E(_jO.a);if(E(_jQ)==65306){var _jR=new T(function(){var _jS=E(_jM);if((_jS+1)*20<=E(_jk)-10){return new T2(0,_jL,_jS+1|0);}else{return new T2(0,new T(function(){return E(_jL)-1|0;}),_jJ);}});return new F(function(){return _ja(_jI,_jk,_jl,_jJ,new T(function(){return E(E(_jR).a);}),new T(function(){return E(E(_jR).b);}),_jP,_);});}else{var _jT=E(_jI),_jU=B(_iB(_jT.a,_jz,_j9,_jK,_jL,_jM,_jQ,_)),_jV=_jJ,_jW=_jK+1,_jX=_jL,_jY=_jM;_jB=_jT;_jC=_jV;_jD=_jW;_jE=_jX;_jF=_jY;_jG=_jP;return __continue;}}})(_jB,_jC,_jD,_jE,_jF,_jG,_));if(_jH!=__continue){return _jH;}}};return new F(function(){return _jA(_jj,_jm,0,new T(function(){if(E(_jm)!=E(_jo)){return E(_jn);}else{return E(_jn)+1|0;}}),new T(function(){var _jZ=E(_jo);if(E(_jm)!=_jZ){return _jZ-1|0;}else{var _k0=(E(_jk)-10)/20,_k1=_k0&4294967295;if(_k0>=_k1){return _k1;}else{return _k1-1|0;}}}),_jr,_);});break;default:var _k2=function(_k3,_k4){var _k5=new T(function(){switch(E(_jt)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _jl;}}),_k6=new T(function(){var _k7=E(_jo);if((_k7+1)*20<=E(_jk)-10){return new T2(0,_jn,_k7+1|0);}else{return new T2(0,new T(function(){return E(_jn)-1|0;}),_jm);}});if(E(_k3)==64){return new F(function(){return _k8(_jj,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}else{var _k9=E(_jj),_ka=B(_iB(_k9.a,new T(function(){return B(_6R(_j4,E(_k5)));},1),_j5,_hM,_jn,_jo,_k4,_));return new F(function(){return _k8(_k9,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}},_kb=E(_jt);switch(_kb){case 42:return new F(function(){return _k2(64,_j6);});break;case 12289:return new F(function(){return _k2(64,_j6);});break;case 12290:return new F(function(){return _k2(64,_j6);});break;default:return new F(function(){return _k2(_kb,_js);});}}}})(_jb,_jc,_jd,_je,_jf,_jg,_jh,_));if(_ji!=__continue){return _ji;}}},_k8=function(_kc,_kd,_ke,_kf,_kg,_kh,_ki,_){var _kj=E(_ki);if(!_kj._){return _gE;}else{var _kk=_kj.b,_kl=E(_kj.a),_km=E(_kl);switch(_km){case 10:return new F(function(){return _ja(_kc,_kd,0,_kf,new T(function(){return E(_kg)-1|0;}),_kf,_kk,_);});break;case 123:return new F(function(){return _jy(_kc,_kd,_ke,_kf,_kg,_kh,_kk,_);});break;case 65306:var _kn=new T(function(){return B(_6R(_j4,E(_ke)));}),_ko=function(_kp,_kq,_kr,_ks,_kt,_ku,_){while(1){var _kv=B((function(_kw,_kx,_ky,_kz,_kA,_kB,_){var _kC=E(_kB);if(!_kC._){return _gE;}else{var _kD=_kC.b,_kE=E(_kC.a);if(E(_kE)==65306){var _kF=new T(function(){var _kG=E(_kA);if((_kG+1)*20<=E(_kd)-10){return new T2(0,_kz,_kG+1|0);}else{return new T2(0,new T(function(){return E(_kz)-1|0;}),_kx);}});return new F(function(){return _k8(_kw,_kd,_ke,_kx,new T(function(){return E(E(_kF).a);}),new T(function(){return E(E(_kF).b);}),_kD,_);});}else{var _kH=E(_kw),_kI=B(_iB(_kH.a,_kn,_j9,_ky,_kz,_kA,_kE,_)),_kJ=_kx,_kK=_ky+1,_kL=_kz,_kM=_kA;_kp=_kH;_kq=_kJ;_kr=_kK;_ks=_kL;_kt=_kM;_ku=_kD;return __continue;}}})(_kp,_kq,_kr,_ks,_kt,_ku,_));if(_kv!=__continue){return _kv;}}};return new F(function(){return _ko(_kc,_kf,0,new T(function(){if(E(_kf)!=E(_kh)){return E(_kg);}else{return E(_kg)+1|0;}}),new T(function(){var _kN=E(_kh);if(E(_kf)!=_kN){return _kN-1|0;}else{var _kO=(E(_kd)-10)/20,_kP=_kO&4294967295;if(_kO>=_kP){return _kP;}else{return _kP-1|0;}}}),_kk,_);});break;default:var _kQ=function(_kR,_kS){var _kT=new T(function(){switch(E(_km)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return E(_ke);}}),_kU=new T(function(){var _kV=E(_kh);if((_kV+1)*20<=E(_kd)-10){return new T2(0,_kg,_kV+1|0);}else{return new T2(0,new T(function(){return E(_kg)-1|0;}),_kf);}});if(E(_kR)==64){return new F(function(){return _k8(_kc,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}else{var _kW=E(_kc),_kX=B(_iB(_kW.a,new T(function(){return B(_6R(_j4,E(_kT)));},1),_j5,_hM,_kg,_kh,_kS,_));return new F(function(){return _k8(_kW,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}},_kY=E(_km);switch(_kY){case 42:return new F(function(){return _kQ(64,_j6);});break;case 12289:return new F(function(){return _kQ(64,_j6);});break;case 12290:return new F(function(){return _kQ(64,_j6);});break;default:return new F(function(){return _kQ(_kY,_kl);});}}}},_jy=function(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_){while(1){var _l6=B((function(_l7,_l8,_l9,_la,_lb,_lc,_ld,_){var _le=E(_ld);if(!_le._){return _gE;}else{var _lf=_le.b;if(E(_le.a)==125){var _lg=new T(function(){var _lh=E(_lc);if((_lh+1)*20<=E(_l8)-10){return new T2(0,_lb,_lh+1|0);}else{return new T2(0,new T(function(){return E(_lb)-1|0;}),_la);}});return new F(function(){return _k8(_l7,_l8,_l9,_la,new T(function(){return E(E(_lg).a);}),new T(function(){return E(E(_lg).b);}),_lf,_);});}else{var _li=_l7,_lj=_l8,_lk=_l9,_ll=_la,_lm=_lb,_ln=_lc;_kZ=_li;_l0=_lj;_l1=_lk;_l2=_ll;_l3=_lm;_l4=_ln;_l5=_lf;return __continue;}}})(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_));if(_l6!=__continue){return _l6;}}},_lo=function(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_){while(1){var _lx=B((function(_ly,_lz,_lA,_lB,_lC,_lD,_lE,_lF,_){var _lG=E(_lF);if(!_lG._){return _gE;}else{var _lH=_lG.b,_lI=E(_lG.a),_lJ=E(_lI);switch(_lJ){case 10:var _lK=_ly,_lL=_lz,_lM=_lA,_lN=_lC,_lO=_lC;_lp=_lK;_lq=_lL;_lr=_lM;_ls=0;_lt=_lN;_lu=new T(function(){return E(_lD)-1|0;});_lv=_lO;_lw=_lH;return __continue;case 123:return new F(function(){return _jy(new T2(0,_ly,_lz),_lA,_lB,_lC,_lD,_lE,_lH,_);});break;case 65306:var _lP=new T(function(){return B(_6R(_j4,_lB));}),_lQ=function(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_){while(1){var _lY=B((function(_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_){var _m6=E(_m5);if(!_m6._){return _gE;}else{var _m7=_m6.b,_m8=E(_m6.a);if(E(_m8)==65306){var _m9=new T(function(){var _ma=E(_m4);if((_ma+1)*20<=E(_lA)-10){return new T2(0,_m3,_ma+1|0);}else{return new T2(0,new T(function(){return E(_m3)-1|0;}),_m1);}});return new F(function(){return _lo(_lZ,_m0,_lA,_lB,_m1,new T(function(){return E(E(_m9).a);}),new T(function(){return E(E(_m9).b);}),_m7,_);});}else{var _mb=B(_iB(_lZ,_lP,_j9,_m2,_m3,_m4,_m8,_)),_mc=_lZ,_md=_m0,_me=_m1,_mf=_m2+1,_mg=_m3,_mh=_m4;_lR=_mc;_lS=_md;_lT=_me;_lU=_mf;_lV=_mg;_lW=_mh;_lX=_m7;return __continue;}}})(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_));if(_lY!=__continue){return _lY;}}};return new F(function(){return _lQ(_ly,_lz,_lC,0,new T(function(){if(E(_lC)!=E(_lE)){return E(_lD);}else{return E(_lD)+1|0;}}),new T(function(){var _mi=E(_lE);if(E(_lC)!=_mi){return _mi-1|0;}else{var _mj=(E(_lA)-10)/20,_mk=_mj&4294967295;if(_mj>=_mk){return _mk;}else{return _mk-1|0;}}}),_lH,_);});break;default:var _ml=function(_mm,_mn){var _mo=new T(function(){switch(E(_lJ)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _lB;}}),_mp=new T(function(){var _mq=E(_lE);if((_mq+1)*20<=E(_lA)-10){return new T2(0,_lD,_mq+1|0);}else{return new T2(0,new T(function(){return E(_lD)-1|0;}),_lC);}});if(E(_mm)==64){return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}else{var _mr=B(_iB(_ly,new T(function(){return B(_6R(_j4,E(_mo)));},1),_j5,_hM,_lD,_lE,_mn,_));return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}},_ms=E(_lJ);switch(_ms){case 42:return new F(function(){return _ml(64,_j6);});break;case 12289:return new F(function(){return _ml(64,_j6);});break;case 12290:return new F(function(){return _ml(64,_j6);});break;default:return new F(function(){return _ml(_ms,_lI);});}}}})(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_));if(_lx!=__continue){return _lx;}}},_mt=function(_mu,_mv){while(1){var _mw=E(_mu);if(!_mw._){return E(_mv);}else{var _mx=_mv+1|0;_mu=_mw.b;_mv=_mx;continue;}}},_my=function(_mz){return E(E(_mz).a);},_mA=function(_mB,_mC){var _mD=E(_mC),_mE=new T(function(){var _mF=B(_ha(_mB)),_mG=B(_mA(_mB,B(A3(_my,_mF,_mD,new T(function(){return B(A2(_he,_mF,_aV));})))));return new T2(1,_mG.a,_mG.b);});return new T2(0,_mD,_mE);},_mH=new T(function(){var _mI=B(_mA(_gb,_hM));return new T2(1,_mI.a,_mI.b);}),_mJ=new T(function(){return B(unCStr("px Courier"));}),_mK=new T(function(){return B(_I(0,20,_10));}),_mL=new T(function(){return B(_y(_mK,_mJ));}),_mM=function(_mN,_){return _gE;},_mO=function(_mP,_mQ,_mR,_mS,_mT){var _mU=new T(function(){return E(_mR)*16;}),_mV=new T(function(){return E(_mS)*20;}),_mW=function(_mX,_mY){var _mZ=E(_mX);if(!_mZ._){return E(_mM);}else{var _n0=E(_mY);if(!_n0._){return E(_mM);}else{var _n1=new T(function(){return B(_mW(_mZ.b,_n0.b));}),_n2=new T(function(){var _n3=new T(function(){var _n4=new T(function(){return B(_hF(new T(function(){return E(_mU)+16*E(_n0.a);}),_mV,new T2(1,_mZ.a,_10)));});return B(_in(_mL,_n4));});return B(_i2(_mQ,_n3));});return function(_n5,_){var _n6=B(A2(_n2,_n5,_));return new F(function(){return A2(_n1,_n5,_);});};}}};return new F(function(){return A3(_mW,_mT,_mH,_mP);});},_n7=45,_n8=new T(function(){return B(unCStr("-"));}),_n9=new T2(1,_n7,_n8),_na=function(_nb){var _nc=E(_nb);return (_nc==1)?E(_n9):new T2(1,_n7,new T(function(){return B(_na(_nc-1|0));}));},_nd=new T(function(){return B(unCStr(": empty list"));}),_ne=function(_nf){return new F(function(){return err(B(_y(_6G,new T(function(){return B(_y(_nf,_nd));},1))));});},_ng=new T(function(){return B(unCStr("head"));}),_nh=new T(function(){return B(_ne(_ng));}),_ni=new T(function(){return eval("(function(e){e.width = e.width;})");}),_nj=new T(function(){return B(_hF(_hM,_hM,_10));}),_nk=32,_nl=new T(function(){return B(unCStr("|"));}),_nm=function(_nn){var _no=E(_nn);return (_no._==0)?E(_nl):new T2(1,new T(function(){var _np=E(_no.a);switch(E(_np.b)){case 7:return E(_nk);break;case 8:return E(_nk);break;default:return E(_np.a);}}),new T(function(){return B(_nm(_no.b));}));},_nq=function(_nr,_ns,_nt,_nu,_nv,_){var _nw=__app1(E(_ni),_ns),_nx=B(A2(_nj,_nr,_)),_ny=B(unAppCStr("-",new T(function(){var _nz=E(_nv);if(!_nz._){return E(_nh);}else{var _nA=B(_mt(_nz.a,0));if(0>=_nA){return E(_n8);}else{return B(_na(_nA));}}}))),_nB=B(A(_mO,[_nr,_j3,_nt,_nu,_ny,_])),_nC=function(_nD,_nE,_nF,_){while(1){var _nG=B((function(_nH,_nI,_nJ,_){var _nK=E(_nJ);if(!_nK._){return new F(function(){return A(_mO,[_nr,_j3,_nH,_nI,_ny,_]);});}else{var _nL=B(A(_mO,[_nr,_j3,_nH,_nI,B(unAppCStr("|",new T(function(){return B(_nm(_nK.a));}))),_])),_nM=_nH;_nD=_nM;_nE=new T(function(){return E(_nI)+1|0;});_nF=_nK.b;return __continue;}})(_nD,_nE,_nF,_));if(_nG!=__continue){return _nG;}}};return new F(function(){return _nC(_nt,new T(function(){return E(_nu)+1|0;}),_nv,_);});},_nN=new T(function(){return B(_6R(_j4,1));}),_nO=new T(function(){return B(_6R(_j4,2));}),_nP=2,_nQ=function(_nR,_nS,_nT,_nU,_){var _nV=__app1(E(_ni),_nS),_nW=B(A2(_nj,_nR,_)),_nX=E(_nU),_nY=E(_nX.b).a,_nZ=E(_nX.a),_o0=_nZ.a;if(!E(E(_nX.p).h)){return _gE;}else{var _o1=B(_nq(_nR,_nS,new T(function(){return E(_nT)-E(_nY)|0;}),_nP,_nZ.b,_));return new F(function(){return A(_mO,[_nR,new T(function(){if(E(_nZ.d)==32){return E(_nN);}else{return E(_nO);}}),new T(function(){return ((E(E(_o0).a)+1|0)+E(_nT)|0)-E(_nY)|0;},1),new T(function(){return (E(E(_o0).b)+2|0)+1|0;},1),new T2(1,_nZ.c,_10),_]);});}},_o2=function(_o3){return E(E(_o3).a);},_o4=function(_o5){return E(E(_o5).a);},_o6=function(_o7,_o8){while(1){var _o9=E(_o7);if(!_o9._){return E(_o8);}else{_o7=_o9.b;_o8=_o9.a;continue;}}},_oa=function(_ob,_oc,_od){return new F(function(){return _o6(_oc,_ob);});},_oe=new T1(0,2),_of=function(_og,_oh){while(1){var _oi=E(_og);if(!_oi._){var _oj=_oi.a,_ok=E(_oh);if(!_ok._){var _ol=_ok.a;if(!(imul(_oj,_ol)|0)){return new T1(0,imul(_oj,_ol)|0);}else{_og=new T1(1,I_fromInt(_oj));_oh=new T1(1,I_fromInt(_ol));continue;}}else{_og=new T1(1,I_fromInt(_oj));_oh=_ok;continue;}}else{var _om=E(_oh);if(!_om._){_og=_oi;_oh=new T1(1,I_fromInt(_om.a));continue;}else{return new T1(1,I_mul(_oi.a,_om.a));}}}},_on=function(_oo,_op,_oq){while(1){if(!(_op%2)){var _or=B(_of(_oo,_oo)),_os=quot(_op,2);_oo=_or;_op=_os;continue;}else{var _ot=E(_op);if(_ot==1){return new F(function(){return _of(_oo,_oq);});}else{var _or=B(_of(_oo,_oo)),_ou=B(_of(_oo,_oq));_oo=_or;_op=quot(_ot-1|0,2);_oq=_ou;continue;}}}},_ov=function(_ow,_ox){while(1){if(!(_ox%2)){var _oy=B(_of(_ow,_ow)),_oz=quot(_ox,2);_ow=_oy;_ox=_oz;continue;}else{var _oA=E(_ox);if(_oA==1){return E(_ow);}else{return new F(function(){return _on(B(_of(_ow,_ow)),quot(_oA-1|0,2),_ow);});}}}},_oB=function(_oC){return E(E(_oC).c);},_oD=function(_oE){return E(E(_oE).a);},_oF=function(_oG){return E(E(_oG).b);},_oH=function(_oI){return E(E(_oI).b);},_oJ=function(_oK){return E(E(_oK).c);},_oL=new T1(0,0),_oM=new T1(0,2),_oN=function(_oO){return E(E(_oO).d);},_oP=function(_oQ,_oR){var _oS=B(_o2(_oQ)),_oT=new T(function(){return B(_o4(_oS));}),_oU=new T(function(){return B(A3(_oN,_oQ,_oR,new T(function(){return B(A2(_he,_oT,_oM));})));});return new F(function(){return A3(_4z,B(_oD(B(_oF(_oS)))),_oU,new T(function(){return B(A2(_he,_oT,_oL));}));});},_oV=new T(function(){return B(unCStr("Negative exponent"));}),_oW=new T(function(){return B(err(_oV));}),_oX=function(_oY){return E(E(_oY).c);},_oZ=function(_p0,_p1,_p2,_p3){var _p4=B(_o2(_p1)),_p5=new T(function(){return B(_o4(_p4));}),_p6=B(_oF(_p4));if(!B(A3(_oJ,_p6,_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){if(!B(A3(_4z,B(_oD(_p6)),_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){var _p7=new T(function(){return B(A2(_he,_p5,_oM));}),_p8=new T(function(){return B(A2(_he,_p5,_aV));}),_p9=B(_oD(_p6)),_pa=function(_pb,_pc,_pd){while(1){var _pe=B((function(_pf,_pg,_ph){if(!B(_oP(_p1,_pg))){if(!B(A3(_4z,_p9,_pg,_p8))){var _pi=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pg,_p8));}),_p7));});_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=_pi;_pd=new T(function(){return B(A3(_oB,_p0,_pf,_ph));});return __continue;}else{return new F(function(){return A3(_oB,_p0,_pf,_ph);});}}else{var _pj=_ph;_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=new T(function(){return B(A3(_oX,_p1,_pg,_p7));});_pd=_pj;return __continue;}})(_pb,_pc,_pd));if(_pe!=__continue){return _pe;}}},_pk=function(_pl,_pm){while(1){var _pn=B((function(_po,_pp){if(!B(_oP(_p1,_pp))){if(!B(A3(_4z,_p9,_pp,_p8))){var _pq=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pp,_p8));}),_p7));});return new F(function(){return _pa(new T(function(){return B(A3(_oB,_p0,_po,_po));}),_pq,_po);});}else{return E(_po);}}else{_pl=new T(function(){return B(A3(_oB,_p0,_po,_po));});_pm=new T(function(){return B(A3(_oX,_p1,_pp,_p7));});return __continue;}})(_pl,_pm));if(_pn!=__continue){return _pn;}}};return new F(function(){return _pk(_p2,_p3);});}else{return new F(function(){return A2(_he,_p0,_aV);});}}else{return E(_oW);}},_pr=new T(function(){return B(err(_oV));}),_ps=function(_pt){var _pu=I_decodeDouble(_pt);return new T2(0,new T1(1,_pu.b),_pu.a);},_pv=function(_pw,_px){var _py=B(_ps(_px)),_pz=_py.a,_pA=_py.b,_pB=new T(function(){return B(_o4(new T(function(){return B(_o2(_pw));})));});if(_pA<0){var _pC= -_pA;if(_pC>=0){var _pD=E(_pC);if(!_pD){var _pE=E(_aV);}else{var _pE=B(_ov(_oe,_pD));}if(!B(_cn(_pE,_cN))){var _pF=B(_cE(_pz,_pE));return new T2(0,new T(function(){return B(A2(_he,_pB,_pF.a));}),new T(function(){return B(_cj(_pF.b,_pA));}));}else{return E(_9U);}}else{return E(_pr);}}else{var _pG=new T(function(){var _pH=new T(function(){return B(_oZ(_pB,_bS,new T(function(){return B(A2(_he,_pB,_oe));}),_pA));});return B(A3(_oB,_pB,new T(function(){return B(A2(_he,_pB,_pz));}),_pH));});return new T2(0,_pG,_fA);}},_pI=function(_pJ,_pK){while(1){var _pL=E(_pK);if(!_pL._){return __Z;}else{var _pM=_pL.b,_pN=E(_pJ);if(_pN==1){return E(_pM);}else{_pJ=_pN-1|0;_pK=_pM;continue;}}}},_pO=function(_pP,_pQ){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.a,_pT=E(_pP);return (_pT==1)?new T2(1,_pS,_10):new T2(1,_pS,new T(function(){return B(_pO(_pT-1|0,_pR.b));}));}},_pU=function(_pV,_pW,_pX,_pY){while(1){if(B(_6R(new T2(1,_pX,_pY),_pW))!=_pV){var _pZ=_pW+1|0;_pW=_pZ;continue;}else{if(0>=_pW){return __Z;}else{return new F(function(){return _pO(_pW,new T2(1,_pX,_pY));});}}}},_q0=function(_q1,_q2,_q3){var _q4=E(_q3);if(!_q4._){return __Z;}else{var _q5=E(_q1);if(B(_6R(_q4,_q2))!=_q5){return new F(function(){return _pU(_q5,_q2+1|0,_q4.a,_q4.b);});}else{if(0>=_q2){return __Z;}else{return new F(function(){return _pO(_q2,_q4);});}}}},_q6=function(_q7,_q8,_q9){var _qa=_q8+1|0;if(_qa>0){return new F(function(){return _pI(_qa,B(_q0(_q7,_qa,_q9)));});}else{return new F(function(){return _q0(_q7,_qa,_q9);});}},_qb=function(_qc,_qd){return (!B(_69(_qc,_qd)))?true:false;},_qe=new T2(0,_69,_qb),_qf=new T(function(){return B(_e7("Event.hs:(65,1)-(66,68)|function addEvent"));}),_qg=0,_qh=function(_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz){while(1){var _qA=E(_qi);if(!_qA._){return {_:0,a:_qj,b:_qk,c:_ql,d:_qm,e:_qn,f:_qo,g:_qp,h:_qq,i:_qr,j:_qs,k:_qt,l:_qu,m:_qv,n:_qw,o:_qx,p:_qy,q:_qz};}else{var _qB=E(_qA.b);if(!_qB._){return E(_qf);}else{var _qC=new T2(1,new T2(0,_qA.a,_qB.a),_qn),_qD=new T2(1,_qg,_qo);_qi=_qB.b;_qn=_qC;_qo=_qD;continue;}}}},_qE=function(_qF,_qG,_qH){var _qI=E(_qH);if(!_qI._){return __Z;}else{var _qJ=_qI.a,_qK=_qI.b;return (!B(A2(_qF,_qG,_qJ)))?new T2(1,_qJ,new T(function(){return B(_qE(_qF,_qG,_qK));})):E(_qK);}},_qL=function(_qM,_qN){while(1){var _qO=E(_qM);if(!_qO._){return (E(_qN)._==0)?true:false;}else{var _qP=E(_qN);if(!_qP._){return false;}else{if(E(_qO.a)!=E(_qP.a)){return false;}else{_qM=_qO.b;_qN=_qP.b;continue;}}}}},_qQ=function(_qR,_qS){while(1){var _qT=E(_qR);if(!_qT._){return (E(_qS)._==0)?true:false;}else{var _qU=E(_qS);if(!_qU._){return false;}else{if(!B(_69(_qT.a,_qU.a))){return false;}else{_qR=_qT.b;_qS=_qU.b;continue;}}}}},_qV=function(_qW,_qX){switch(E(_qW)){case 0:return (E(_qX)==0)?true:false;case 1:return (E(_qX)==1)?true:false;case 2:return (E(_qX)==2)?true:false;case 3:return (E(_qX)==3)?true:false;case 4:return (E(_qX)==4)?true:false;case 5:return (E(_qX)==5)?true:false;case 6:return (E(_qX)==6)?true:false;case 7:return (E(_qX)==7)?true:false;default:return (E(_qX)==8)?true:false;}},_qY=function(_qZ,_r0,_r1,_r2){if(_qZ!=_r1){return false;}else{return new F(function(){return _qV(_r0,_r2);});}},_r3=function(_r4,_r5){var _r6=E(_r4),_r7=E(_r5);return new F(function(){return _qY(E(_r6.a),_r6.b,E(_r7.a),_r7.b);});},_r8=function(_r9,_ra,_rb,_rc){if(_r9!=_rb){return true;}else{switch(E(_ra)){case 0:return (E(_rc)==0)?false:true;case 1:return (E(_rc)==1)?false:true;case 2:return (E(_rc)==2)?false:true;case 3:return (E(_rc)==3)?false:true;case 4:return (E(_rc)==4)?false:true;case 5:return (E(_rc)==5)?false:true;case 6:return (E(_rc)==6)?false:true;case 7:return (E(_rc)==7)?false:true;default:return (E(_rc)==8)?false:true;}}},_rd=function(_re,_rf){var _rg=E(_re),_rh=E(_rf);return new F(function(){return _r8(E(_rg.a),_rg.b,E(_rh.a),_rh.b);});},_ri=new T2(0,_r3,_rd),_rj=0,_rk=function(_rl,_rm){var _rn=E(_rm);if(!_rn._){return 0;}else{var _ro=_rn.b,_rp=E(_rl),_rq=E(_rn.a),_rr=_rq.b;if(E(_rp.a)!=E(_rq.a)){return 1+B(_rk(_rp,_ro))|0;}else{switch(E(_rp.b)){case 0:return (E(_rr)==0)?0:1+B(_rk(_rp,_ro))|0;case 1:return (E(_rr)==1)?0:1+B(_rk(_rp,_ro))|0;case 2:return (E(_rr)==2)?0:1+B(_rk(_rp,_ro))|0;case 3:return (E(_rr)==3)?0:1+B(_rk(_rp,_ro))|0;case 4:return (E(_rr)==4)?0:1+B(_rk(_rp,_ro))|0;case 5:return (E(_rr)==5)?0:1+B(_rk(_rp,_ro))|0;case 6:return (E(_rr)==6)?0:1+B(_rk(_rp,_ro))|0;case 7:return (E(_rr)==7)?0:1+B(_rk(_rp,_ro))|0;default:return (E(_rr)==8)?0:1+B(_rk(_rp,_ro))|0;}}}},_rs=function(_rt,_ru){return new F(function(){return _rk(_rt,_ru);});},_rv=function(_rw,_rx){var _ry=E(_rx);if(!_ry._){return new T2(0,_rj,_rj);}else{var _rz=_ry.a,_rA=_ry.b;return (!B(_4B(_ri,_rw,_rz)))?new T2(0,new T(function(){return E(B(_rv(_rw,_rA)).a);}),new T(function(){return 1+E(B(_rv(_rw,_rA)).b)|0;})):new T2(0,new T(function(){return B(_rs(_rw,_rz));}),_rj);}},_rB=function(_rC,_rD){while(1){var _rE=E(_rD);if(!_rE._){return __Z;}else{var _rF=_rE.b,_rG=E(_rC);if(_rG==1){return E(_rF);}else{_rC=_rG-1|0;_rD=_rF;continue;}}}},_rH=new T(function(){return B(unCStr("getch"));}),_rI=new T(function(){return B(unCStr("=="));}),_rJ=new T(function(){return B(unCStr("&&"));}),_rK=new T(function(){return B(unCStr("||"));}),_rL=new T(function(){return B(unCStr("getpos"));}),_rM=new T(function(){return B(unCStr("ch"));}),_rN=new T(function(){return B(unCStr("tp"));}),_rO=new T2(1,_rN,_10),_rP=new T2(1,_rM,_rO),_rQ=new T2(0,_rL,_rP),_rR=new T(function(){return B(unCStr("a"));}),_rS=new T(function(){return B(unCStr("b"));}),_rT=new T2(1,_rS,_10),_rU=new T2(1,_rR,_rT),_rV=new T2(0,_rI,_rU),_rW=new T2(0,_rJ,_rU),_rX=new T2(0,_rK,_rU),_rY=new T2(1,_rX,_10),_rZ=new T2(1,_rW,_rY),_s0=new T2(1,_rV,_rZ),_s1=new T2(1,_rQ,_s0),_s2=new T(function(){return B(unCStr("p"));}),_s3=new T(function(){return B(unCStr("q"));}),_s4=new T2(1,_s3,_10),_s5=new T2(1,_s2,_s4),_s6=new T2(0,_rH,_s5),_s7=new T2(1,_s6,_s1),_s8=new T(function(){return B(unCStr("foldr1"));}),_s9=new T(function(){return B(_ne(_s8));}),_sa=function(_sb,_sc){var _sd=E(_sc);if(!_sd._){return E(_s9);}else{var _se=_sd.a,_sf=E(_sd.b);if(!_sf._){return E(_se);}else{return new F(function(){return A2(_sb,_se,new T(function(){return B(_sa(_sb,_sf));}));});}}},_sg=function(_sh){return E(E(_sh).a);},_si=function(_sj,_sk,_sl){while(1){var _sm=E(_sl);if(!_sm._){return __Z;}else{var _sn=E(_sm.a);if(!B(A3(_4z,_sj,_sk,_sn.a))){_sl=_sm.b;continue;}else{return new T1(1,_sn.b);}}}},_so=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sp=new T(function(){return B(err(_so));}),_sq=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_sr=new T(function(){return B(err(_sq));}),_ss=new T(function(){return B(unCStr("T"));}),_st=new T(function(){return B(unCStr("F"));}),_su=new T(function(){return B(_e7("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sv=function(_sw,_sx){while(1){var _sy=B((function(_sz,_sA){var _sB=E(_sz);switch(_sB._){case 0:var _sC=E(_sA);if(!_sC._){return __Z;}else{_sw=B(A1(_sB.a,_sC.a));_sx=_sC.b;return __continue;}break;case 1:var _sD=B(A1(_sB.a,_sA)),_sE=_sA;_sw=_sD;_sx=_sE;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sB.a,_sA),new T(function(){return B(_sv(_sB.b,_sA));}));default:return E(_sB.a);}})(_sw,_sx));if(_sy!=__continue){return _sy;}}},_sF=function(_sG,_sH){var _sI=function(_sJ){var _sK=E(_sH);if(_sK._==3){return new T2(3,_sK.a,new T(function(){return B(_sF(_sG,_sK.b));}));}else{var _sL=E(_sG);if(_sL._==2){return E(_sK);}else{var _sM=E(_sK);if(_sM._==2){return E(_sL);}else{var _sN=function(_sO){var _sP=E(_sM);if(_sP._==4){var _sQ=function(_sR){return new T1(4,new T(function(){return B(_y(B(_sv(_sL,_sR)),_sP.a));}));};return new T1(1,_sQ);}else{var _sS=E(_sL);if(_sS._==1){var _sT=_sS.a,_sU=E(_sP);if(!_sU._){return new T1(1,function(_sV){return new F(function(){return _sF(B(A1(_sT,_sV)),_sU);});});}else{var _sW=function(_sX){return new F(function(){return _sF(B(A1(_sT,_sX)),new T(function(){return B(A1(_sU.a,_sX));}));});};return new T1(1,_sW);}}else{var _sY=E(_sP);if(!_sY._){return E(_su);}else{var _sZ=function(_t0){return new F(function(){return _sF(_sS,new T(function(){return B(A1(_sY.a,_t0));}));});};return new T1(1,_sZ);}}}},_t1=E(_sL);switch(_t1._){case 1:var _t2=E(_sM);if(_t2._==4){var _t3=function(_t4){return new T1(4,new T(function(){return B(_y(B(_sv(B(A1(_t1.a,_t4)),_t4)),_t2.a));}));};return new T1(1,_t3);}else{return new F(function(){return _sN(_);});}break;case 4:var _t5=_t1.a,_t6=E(_sM);switch(_t6._){case 0:var _t7=function(_t8){var _t9=new T(function(){return B(_y(_t5,new T(function(){return B(_sv(_t6,_t8));},1)));});return new T1(4,_t9);};return new T1(1,_t7);case 1:var _ta=function(_tb){var _tc=new T(function(){return B(_y(_t5,new T(function(){return B(_sv(B(A1(_t6.a,_tb)),_tb));},1)));});return new T1(4,_tc);};return new T1(1,_ta);default:return new T1(4,new T(function(){return B(_y(_t5,_t6.a));}));}break;default:return new F(function(){return _sN(_);});}}}}},_td=E(_sG);switch(_td._){case 0:var _te=E(_sH);if(!_te._){var _tf=function(_tg){return new F(function(){return _sF(B(A1(_td.a,_tg)),new T(function(){return B(A1(_te.a,_tg));}));});};return new T1(0,_tf);}else{return new F(function(){return _sI(_);});}break;case 3:return new T2(3,_td.a,new T(function(){return B(_sF(_td.b,_sH));}));default:return new F(function(){return _sI(_);});}},_th=new T(function(){return B(unCStr("("));}),_ti=new T(function(){return B(unCStr(")"));}),_tj=function(_tk,_tl){var _tm=E(_tk);switch(_tm._){case 0:return new T1(0,function(_tn){return new F(function(){return _tj(B(A1(_tm.a,_tn)),_tl);});});case 1:return new T1(1,function(_to){return new F(function(){return _tj(B(A1(_tm.a,_to)),_tl);});});case 2:return new T0(2);case 3:return new F(function(){return _sF(B(A1(_tl,_tm.a)),new T(function(){return B(_tj(_tm.b,_tl));}));});break;default:var _tp=function(_tq){var _tr=E(_tq);if(!_tr._){return __Z;}else{var _ts=E(_tr.a);return new F(function(){return _y(B(_sv(B(A1(_tl,_ts.a)),_ts.b)),new T(function(){return B(_tp(_tr.b));},1));});}},_tt=B(_tp(_tm.a));return (_tt._==0)?new T0(2):new T1(4,_tt);}},_tu=new T0(2),_tv=function(_tw){return new T2(3,_tw,_tu);},_tx=function(_ty,_tz){var _tA=E(_ty);if(!_tA){return new F(function(){return A1(_tz,_gE);});}else{var _tB=new T(function(){return B(_tx(_tA-1|0,_tz));});return new T1(0,function(_tC){return E(_tB);});}},_tD=function(_tE,_tF,_tG){var _tH=new T(function(){return B(A1(_tE,_tv));}),_tI=function(_tJ,_tK,_tL,_tM){while(1){var _tN=B((function(_tO,_tP,_tQ,_tR){var _tS=E(_tO);switch(_tS._){case 0:var _tT=E(_tP);if(!_tT._){return new F(function(){return A1(_tF,_tR);});}else{var _tU=_tQ+1|0,_tV=_tR;_tJ=B(A1(_tS.a,_tT.a));_tK=_tT.b;_tL=_tU;_tM=_tV;return __continue;}break;case 1:var _tW=B(A1(_tS.a,_tP)),_tX=_tP,_tU=_tQ,_tV=_tR;_tJ=_tW;_tK=_tX;_tL=_tU;_tM=_tV;return __continue;case 2:return new F(function(){return A1(_tF,_tR);});break;case 3:var _tY=new T(function(){return B(_tj(_tS,_tR));});return new F(function(){return _tx(_tQ,function(_tZ){return E(_tY);});});break;default:return new F(function(){return _tj(_tS,_tR);});}})(_tJ,_tK,_tL,_tM));if(_tN!=__continue){return _tN;}}};return function(_u0){return new F(function(){return _tI(_tH,_u0,0,_tG);});};},_u1=function(_u2){return new F(function(){return A1(_u2,_10);});},_u3=function(_u4,_u5){var _u6=function(_u7){var _u8=E(_u7);if(!_u8._){return E(_u1);}else{var _u9=_u8.a;if(!B(A1(_u4,_u9))){return E(_u1);}else{var _ua=new T(function(){return B(_u6(_u8.b));}),_ub=function(_uc){var _ud=new T(function(){return B(A1(_ua,function(_ue){return new F(function(){return A1(_uc,new T2(1,_u9,_ue));});}));});return new T1(0,function(_uf){return E(_ud);});};return E(_ub);}}};return function(_ug){return new F(function(){return A2(_u6,_ug,_u5);});};},_uh=new T0(6),_ui=new T(function(){return B(unCStr("valDig: Bad base"));}),_uj=new T(function(){return B(err(_ui));}),_uk=function(_ul,_um){var _un=function(_uo,_up){var _uq=E(_uo);if(!_uq._){var _ur=new T(function(){return B(A1(_up,_10));});return function(_us){return new F(function(){return A1(_us,_ur);});};}else{var _ut=E(_uq.a),_uu=function(_uv){var _uw=new T(function(){return B(_un(_uq.b,function(_ux){return new F(function(){return A1(_up,new T2(1,_uv,_ux));});}));}),_uy=function(_uz){var _uA=new T(function(){return B(A1(_uw,_uz));});return new T1(0,function(_uB){return E(_uA);});};return E(_uy);};switch(E(_ul)){case 8:if(48>_ut){var _uC=new T(function(){return B(A1(_up,_10));});return function(_uD){return new F(function(){return A1(_uD,_uC);});};}else{if(_ut>55){var _uE=new T(function(){return B(A1(_up,_10));});return function(_uF){return new F(function(){return A1(_uF,_uE);});};}else{return new F(function(){return _uu(_ut-48|0);});}}break;case 10:if(48>_ut){var _uG=new T(function(){return B(A1(_up,_10));});return function(_uH){return new F(function(){return A1(_uH,_uG);});};}else{if(_ut>57){var _uI=new T(function(){return B(A1(_up,_10));});return function(_uJ){return new F(function(){return A1(_uJ,_uI);});};}else{return new F(function(){return _uu(_ut-48|0);});}}break;case 16:if(48>_ut){if(97>_ut){if(65>_ut){var _uK=new T(function(){return B(A1(_up,_10));});return function(_uL){return new F(function(){return A1(_uL,_uK);});};}else{if(_ut>70){var _uM=new T(function(){return B(A1(_up,_10));});return function(_uN){return new F(function(){return A1(_uN,_uM);});};}else{return new F(function(){return _uu((_ut-65|0)+10|0);});}}}else{if(_ut>102){if(65>_ut){var _uO=new T(function(){return B(A1(_up,_10));});return function(_uP){return new F(function(){return A1(_uP,_uO);});};}else{if(_ut>70){var _uQ=new T(function(){return B(A1(_up,_10));});return function(_uR){return new F(function(){return A1(_uR,_uQ);});};}else{return new F(function(){return _uu((_ut-65|0)+10|0);});}}}else{return new F(function(){return _uu((_ut-97|0)+10|0);});}}}else{if(_ut>57){if(97>_ut){if(65>_ut){var _uS=new T(function(){return B(A1(_up,_10));});return function(_uT){return new F(function(){return A1(_uT,_uS);});};}else{if(_ut>70){var _uU=new T(function(){return B(A1(_up,_10));});return function(_uV){return new F(function(){return A1(_uV,_uU);});};}else{return new F(function(){return _uu((_ut-65|0)+10|0);});}}}else{if(_ut>102){if(65>_ut){var _uW=new T(function(){return B(A1(_up,_10));});return function(_uX){return new F(function(){return A1(_uX,_uW);});};}else{if(_ut>70){var _uY=new T(function(){return B(A1(_up,_10));});return function(_uZ){return new F(function(){return A1(_uZ,_uY);});};}else{return new F(function(){return _uu((_ut-65|0)+10|0);});}}}else{return new F(function(){return _uu((_ut-97|0)+10|0);});}}}else{return new F(function(){return _uu(_ut-48|0);});}}break;default:return E(_uj);}}},_v0=function(_v1){var _v2=E(_v1);if(!_v2._){return new T0(2);}else{return new F(function(){return A1(_um,_v2);});}};return function(_v3){return new F(function(){return A3(_un,_v3,_5V,_v0);});};},_v4=16,_v5=8,_v6=function(_v7){var _v8=function(_v9){return new F(function(){return A1(_v7,new T1(5,new T2(0,_v5,_v9)));});},_va=function(_vb){return new F(function(){return A1(_v7,new T1(5,new T2(0,_v4,_vb)));});},_vc=function(_vd){switch(E(_vd)){case 79:return new T1(1,B(_uk(_v5,_v8)));case 88:return new T1(1,B(_uk(_v4,_va)));case 111:return new T1(1,B(_uk(_v5,_v8)));case 120:return new T1(1,B(_uk(_v4,_va)));default:return new T0(2);}};return function(_ve){return (E(_ve)==48)?E(new T1(0,_vc)):new T0(2);};},_vf=function(_vg){return new T1(0,B(_v6(_vg)));},_vh=function(_vi){return new F(function(){return A1(_vi,_0);});},_vj=function(_vk){return new F(function(){return A1(_vk,_0);});},_vl=10,_vm=new T1(0,10),_vn=function(_vo){return new F(function(){return _aR(E(_vo));});},_vp=new T(function(){return B(unCStr("this should not happen"));}),_vq=new T(function(){return B(err(_vp));}),_vr=function(_vs,_vt){var _vu=E(_vt);if(!_vu._){return __Z;}else{var _vv=E(_vu.b);return (_vv._==0)?E(_vq):new T2(1,B(_cv(B(_of(_vu.a,_vs)),_vv.a)),new T(function(){return B(_vr(_vs,_vv.b));}));}},_vw=new T1(0,0),_vx=function(_vy,_vz,_vA){while(1){var _vB=B((function(_vC,_vD,_vE){var _vF=E(_vE);if(!_vF._){return E(_vw);}else{if(!E(_vF.b)._){return E(_vF.a);}else{var _vG=E(_vD);if(_vG<=40){var _vH=function(_vI,_vJ){while(1){var _vK=E(_vJ);if(!_vK._){return E(_vI);}else{var _vL=B(_cv(B(_of(_vI,_vC)),_vK.a));_vI=_vL;_vJ=_vK.b;continue;}}};return new F(function(){return _vH(_vw,_vF);});}else{var _vM=B(_of(_vC,_vC));if(!(_vG%2)){var _vN=B(_vr(_vC,_vF));_vy=_vM;_vz=quot(_vG+1|0,2);_vA=_vN;return __continue;}else{var _vN=B(_vr(_vC,new T2(1,_vw,_vF)));_vy=_vM;_vz=quot(_vG+1|0,2);_vA=_vN;return __continue;}}}}})(_vy,_vz,_vA));if(_vB!=__continue){return _vB;}}},_vO=function(_vP,_vQ){return new F(function(){return _vx(_vP,new T(function(){return B(_mt(_vQ,0));},1),B(_6e(_vn,_vQ)));});},_vR=function(_vS){var _vT=new T(function(){var _vU=new T(function(){var _vV=function(_vW){return new F(function(){return A1(_vS,new T1(1,new T(function(){return B(_vO(_vm,_vW));})));});};return new T1(1,B(_uk(_vl,_vV)));}),_vX=function(_vY){if(E(_vY)==43){var _vZ=function(_w0){return new F(function(){return A1(_vS,new T1(1,new T(function(){return B(_vO(_vm,_w0));})));});};return new T1(1,B(_uk(_vl,_vZ)));}else{return new T0(2);}},_w1=function(_w2){if(E(_w2)==45){var _w3=function(_w4){return new F(function(){return A1(_vS,new T1(1,new T(function(){return B(_ft(B(_vO(_vm,_w4))));})));});};return new T1(1,B(_uk(_vl,_w3)));}else{return new T0(2);}};return B(_sF(B(_sF(new T1(0,_w1),new T1(0,_vX))),_vU));});return new F(function(){return _sF(new T1(0,function(_w5){return (E(_w5)==101)?E(_vT):new T0(2);}),new T1(0,function(_w6){return (E(_w6)==69)?E(_vT):new T0(2);}));});},_w7=function(_w8){var _w9=function(_wa){return new F(function(){return A1(_w8,new T1(1,_wa));});};return function(_wb){return (E(_wb)==46)?new T1(1,B(_uk(_vl,_w9))):new T0(2);};},_wc=function(_wd){return new T1(0,B(_w7(_wd)));},_we=function(_wf){var _wg=function(_wh){var _wi=function(_wj){return new T1(1,B(_tD(_vR,_vh,function(_wk){return new F(function(){return A1(_wf,new T1(5,new T3(1,_wh,_wj,_wk)));});})));};return new T1(1,B(_tD(_wc,_vj,_wi)));};return new F(function(){return _uk(_vl,_wg);});},_wl=function(_wm){return new T1(1,B(_we(_wm)));},_wn=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wo=function(_wp){return new F(function(){return _4B(_h7,_wp,_wn);});},_wq=false,_wr=true,_ws=function(_wt){var _wu=new T(function(){return B(A1(_wt,_v5));}),_wv=new T(function(){return B(A1(_wt,_v4));});return function(_ww){switch(E(_ww)){case 79:return E(_wu);case 88:return E(_wv);case 111:return E(_wu);case 120:return E(_wv);default:return new T0(2);}};},_wx=function(_wy){return new T1(0,B(_ws(_wy)));},_wz=function(_wA){return new F(function(){return A1(_wA,_vl);});},_wB=function(_wC){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_I(9,_wC,_10));}))));});},_wD=function(_wE){return new T0(2);},_wF=function(_wG){var _wH=E(_wG);if(!_wH._){return E(_wD);}else{var _wI=_wH.a,_wJ=E(_wH.b);if(!_wJ._){return E(_wI);}else{var _wK=new T(function(){return B(_wF(_wJ));}),_wL=function(_wM){return new F(function(){return _sF(B(A1(_wI,_wM)),new T(function(){return B(A1(_wK,_wM));}));});};return E(_wL);}}},_wN=function(_wO,_wP){var _wQ=function(_wR,_wS,_wT){var _wU=E(_wR);if(!_wU._){return new F(function(){return A1(_wT,_wO);});}else{var _wV=E(_wS);if(!_wV._){return new T0(2);}else{if(E(_wU.a)!=E(_wV.a)){return new T0(2);}else{var _wW=new T(function(){return B(_wQ(_wU.b,_wV.b,_wT));});return new T1(0,function(_wX){return E(_wW);});}}}};return function(_wY){return new F(function(){return _wQ(_wO,_wY,_wP);});};},_wZ=new T(function(){return B(unCStr("SO"));}),_x0=14,_x1=function(_x2){var _x3=new T(function(){return B(A1(_x2,_x0));});return new T1(1,B(_wN(_wZ,function(_x4){return E(_x3);})));},_x5=new T(function(){return B(unCStr("SOH"));}),_x6=1,_x7=function(_x8){var _x9=new T(function(){return B(A1(_x8,_x6));});return new T1(1,B(_wN(_x5,function(_xa){return E(_x9);})));},_xb=function(_xc){return new T1(1,B(_tD(_x7,_x1,_xc)));},_xd=new T(function(){return B(unCStr("NUL"));}),_xe=0,_xf=function(_xg){var _xh=new T(function(){return B(A1(_xg,_xe));});return new T1(1,B(_wN(_xd,function(_xi){return E(_xh);})));},_xj=new T(function(){return B(unCStr("STX"));}),_xk=2,_xl=function(_xm){var _xn=new T(function(){return B(A1(_xm,_xk));});return new T1(1,B(_wN(_xj,function(_xo){return E(_xn);})));},_xp=new T(function(){return B(unCStr("ETX"));}),_xq=3,_xr=function(_xs){var _xt=new T(function(){return B(A1(_xs,_xq));});return new T1(1,B(_wN(_xp,function(_xu){return E(_xt);})));},_xv=new T(function(){return B(unCStr("EOT"));}),_xw=4,_xx=function(_xy){var _xz=new T(function(){return B(A1(_xy,_xw));});return new T1(1,B(_wN(_xv,function(_xA){return E(_xz);})));},_xB=new T(function(){return B(unCStr("ENQ"));}),_xC=5,_xD=function(_xE){var _xF=new T(function(){return B(A1(_xE,_xC));});return new T1(1,B(_wN(_xB,function(_xG){return E(_xF);})));},_xH=new T(function(){return B(unCStr("ACK"));}),_xI=6,_xJ=function(_xK){var _xL=new T(function(){return B(A1(_xK,_xI));});return new T1(1,B(_wN(_xH,function(_xM){return E(_xL);})));},_xN=new T(function(){return B(unCStr("BEL"));}),_xO=7,_xP=function(_xQ){var _xR=new T(function(){return B(A1(_xQ,_xO));});return new T1(1,B(_wN(_xN,function(_xS){return E(_xR);})));},_xT=new T(function(){return B(unCStr("BS"));}),_xU=8,_xV=function(_xW){var _xX=new T(function(){return B(A1(_xW,_xU));});return new T1(1,B(_wN(_xT,function(_xY){return E(_xX);})));},_xZ=new T(function(){return B(unCStr("HT"));}),_y0=9,_y1=function(_y2){var _y3=new T(function(){return B(A1(_y2,_y0));});return new T1(1,B(_wN(_xZ,function(_y4){return E(_y3);})));},_y5=new T(function(){return B(unCStr("LF"));}),_y6=10,_y7=function(_y8){var _y9=new T(function(){return B(A1(_y8,_y6));});return new T1(1,B(_wN(_y5,function(_ya){return E(_y9);})));},_yb=new T(function(){return B(unCStr("VT"));}),_yc=11,_yd=function(_ye){var _yf=new T(function(){return B(A1(_ye,_yc));});return new T1(1,B(_wN(_yb,function(_yg){return E(_yf);})));},_yh=new T(function(){return B(unCStr("FF"));}),_yi=12,_yj=function(_yk){var _yl=new T(function(){return B(A1(_yk,_yi));});return new T1(1,B(_wN(_yh,function(_ym){return E(_yl);})));},_yn=new T(function(){return B(unCStr("CR"));}),_yo=13,_yp=function(_yq){var _yr=new T(function(){return B(A1(_yq,_yo));});return new T1(1,B(_wN(_yn,function(_ys){return E(_yr);})));},_yt=new T(function(){return B(unCStr("SI"));}),_yu=15,_yv=function(_yw){var _yx=new T(function(){return B(A1(_yw,_yu));});return new T1(1,B(_wN(_yt,function(_yy){return E(_yx);})));},_yz=new T(function(){return B(unCStr("DLE"));}),_yA=16,_yB=function(_yC){var _yD=new T(function(){return B(A1(_yC,_yA));});return new T1(1,B(_wN(_yz,function(_yE){return E(_yD);})));},_yF=new T(function(){return B(unCStr("DC1"));}),_yG=17,_yH=function(_yI){var _yJ=new T(function(){return B(A1(_yI,_yG));});return new T1(1,B(_wN(_yF,function(_yK){return E(_yJ);})));},_yL=new T(function(){return B(unCStr("DC2"));}),_yM=18,_yN=function(_yO){var _yP=new T(function(){return B(A1(_yO,_yM));});return new T1(1,B(_wN(_yL,function(_yQ){return E(_yP);})));},_yR=new T(function(){return B(unCStr("DC3"));}),_yS=19,_yT=function(_yU){var _yV=new T(function(){return B(A1(_yU,_yS));});return new T1(1,B(_wN(_yR,function(_yW){return E(_yV);})));},_yX=new T(function(){return B(unCStr("DC4"));}),_yY=20,_yZ=function(_z0){var _z1=new T(function(){return B(A1(_z0,_yY));});return new T1(1,B(_wN(_yX,function(_z2){return E(_z1);})));},_z3=new T(function(){return B(unCStr("NAK"));}),_z4=21,_z5=function(_z6){var _z7=new T(function(){return B(A1(_z6,_z4));});return new T1(1,B(_wN(_z3,function(_z8){return E(_z7);})));},_z9=new T(function(){return B(unCStr("SYN"));}),_za=22,_zb=function(_zc){var _zd=new T(function(){return B(A1(_zc,_za));});return new T1(1,B(_wN(_z9,function(_ze){return E(_zd);})));},_zf=new T(function(){return B(unCStr("ETB"));}),_zg=23,_zh=function(_zi){var _zj=new T(function(){return B(A1(_zi,_zg));});return new T1(1,B(_wN(_zf,function(_zk){return E(_zj);})));},_zl=new T(function(){return B(unCStr("CAN"));}),_zm=24,_zn=function(_zo){var _zp=new T(function(){return B(A1(_zo,_zm));});return new T1(1,B(_wN(_zl,function(_zq){return E(_zp);})));},_zr=new T(function(){return B(unCStr("EM"));}),_zs=25,_zt=function(_zu){var _zv=new T(function(){return B(A1(_zu,_zs));});return new T1(1,B(_wN(_zr,function(_zw){return E(_zv);})));},_zx=new T(function(){return B(unCStr("SUB"));}),_zy=26,_zz=function(_zA){var _zB=new T(function(){return B(A1(_zA,_zy));});return new T1(1,B(_wN(_zx,function(_zC){return E(_zB);})));},_zD=new T(function(){return B(unCStr("ESC"));}),_zE=27,_zF=function(_zG){var _zH=new T(function(){return B(A1(_zG,_zE));});return new T1(1,B(_wN(_zD,function(_zI){return E(_zH);})));},_zJ=new T(function(){return B(unCStr("FS"));}),_zK=28,_zL=function(_zM){var _zN=new T(function(){return B(A1(_zM,_zK));});return new T1(1,B(_wN(_zJ,function(_zO){return E(_zN);})));},_zP=new T(function(){return B(unCStr("GS"));}),_zQ=29,_zR=function(_zS){var _zT=new T(function(){return B(A1(_zS,_zQ));});return new T1(1,B(_wN(_zP,function(_zU){return E(_zT);})));},_zV=new T(function(){return B(unCStr("RS"));}),_zW=30,_zX=function(_zY){var _zZ=new T(function(){return B(A1(_zY,_zW));});return new T1(1,B(_wN(_zV,function(_A0){return E(_zZ);})));},_A1=new T(function(){return B(unCStr("US"));}),_A2=31,_A3=function(_A4){var _A5=new T(function(){return B(A1(_A4,_A2));});return new T1(1,B(_wN(_A1,function(_A6){return E(_A5);})));},_A7=new T(function(){return B(unCStr("SP"));}),_A8=32,_A9=function(_Aa){var _Ab=new T(function(){return B(A1(_Aa,_A8));});return new T1(1,B(_wN(_A7,function(_Ac){return E(_Ab);})));},_Ad=new T(function(){return B(unCStr("DEL"));}),_Ae=127,_Af=function(_Ag){var _Ah=new T(function(){return B(A1(_Ag,_Ae));});return new T1(1,B(_wN(_Ad,function(_Ai){return E(_Ah);})));},_Aj=new T2(1,_Af,_10),_Ak=new T2(1,_A9,_Aj),_Al=new T2(1,_A3,_Ak),_Am=new T2(1,_zX,_Al),_An=new T2(1,_zR,_Am),_Ao=new T2(1,_zL,_An),_Ap=new T2(1,_zF,_Ao),_Aq=new T2(1,_zz,_Ap),_Ar=new T2(1,_zt,_Aq),_As=new T2(1,_zn,_Ar),_At=new T2(1,_zh,_As),_Au=new T2(1,_zb,_At),_Av=new T2(1,_z5,_Au),_Aw=new T2(1,_yZ,_Av),_Ax=new T2(1,_yT,_Aw),_Ay=new T2(1,_yN,_Ax),_Az=new T2(1,_yH,_Ay),_AA=new T2(1,_yB,_Az),_AB=new T2(1,_yv,_AA),_AC=new T2(1,_yp,_AB),_AD=new T2(1,_yj,_AC),_AE=new T2(1,_yd,_AD),_AF=new T2(1,_y7,_AE),_AG=new T2(1,_y1,_AF),_AH=new T2(1,_xV,_AG),_AI=new T2(1,_xP,_AH),_AJ=new T2(1,_xJ,_AI),_AK=new T2(1,_xD,_AJ),_AL=new T2(1,_xx,_AK),_AM=new T2(1,_xr,_AL),_AN=new T2(1,_xl,_AM),_AO=new T2(1,_xf,_AN),_AP=new T2(1,_xb,_AO),_AQ=new T(function(){return B(_wF(_AP));}),_AR=34,_AS=new T1(0,1114111),_AT=92,_AU=39,_AV=function(_AW){var _AX=new T(function(){return B(A1(_AW,_xO));}),_AY=new T(function(){return B(A1(_AW,_xU));}),_AZ=new T(function(){return B(A1(_AW,_y0));}),_B0=new T(function(){return B(A1(_AW,_y6));}),_B1=new T(function(){return B(A1(_AW,_yc));}),_B2=new T(function(){return B(A1(_AW,_yi));}),_B3=new T(function(){return B(A1(_AW,_yo));}),_B4=new T(function(){return B(A1(_AW,_AT));}),_B5=new T(function(){return B(A1(_AW,_AU));}),_B6=new T(function(){return B(A1(_AW,_AR));}),_B7=new T(function(){var _B8=function(_B9){var _Ba=new T(function(){return B(_aR(E(_B9)));}),_Bb=function(_Bc){var _Bd=B(_vO(_Ba,_Bc));if(!B(_ez(_Bd,_AS))){return new T0(2);}else{return new F(function(){return A1(_AW,new T(function(){var _Be=B(_ba(_Bd));if(_Be>>>0>1114111){return B(_wB(_Be));}else{return _Be;}}));});}};return new T1(1,B(_uk(_B9,_Bb)));},_Bf=new T(function(){var _Bg=new T(function(){return B(A1(_AW,_A2));}),_Bh=new T(function(){return B(A1(_AW,_zW));}),_Bi=new T(function(){return B(A1(_AW,_zQ));}),_Bj=new T(function(){return B(A1(_AW,_zK));}),_Bk=new T(function(){return B(A1(_AW,_zE));}),_Bl=new T(function(){return B(A1(_AW,_zy));}),_Bm=new T(function(){return B(A1(_AW,_zs));}),_Bn=new T(function(){return B(A1(_AW,_zm));}),_Bo=new T(function(){return B(A1(_AW,_zg));}),_Bp=new T(function(){return B(A1(_AW,_za));}),_Bq=new T(function(){return B(A1(_AW,_z4));}),_Br=new T(function(){return B(A1(_AW,_yY));}),_Bs=new T(function(){return B(A1(_AW,_yS));}),_Bt=new T(function(){return B(A1(_AW,_yM));}),_Bu=new T(function(){return B(A1(_AW,_yG));}),_Bv=new T(function(){return B(A1(_AW,_yA));}),_Bw=new T(function(){return B(A1(_AW,_yu));}),_Bx=new T(function(){return B(A1(_AW,_x0));}),_By=new T(function(){return B(A1(_AW,_xI));}),_Bz=new T(function(){return B(A1(_AW,_xC));}),_BA=new T(function(){return B(A1(_AW,_xw));}),_BB=new T(function(){return B(A1(_AW,_xq));}),_BC=new T(function(){return B(A1(_AW,_xk));}),_BD=new T(function(){return B(A1(_AW,_x6));}),_BE=new T(function(){return B(A1(_AW,_xe));}),_BF=function(_BG){switch(E(_BG)){case 64:return E(_BE);case 65:return E(_BD);case 66:return E(_BC);case 67:return E(_BB);case 68:return E(_BA);case 69:return E(_Bz);case 70:return E(_By);case 71:return E(_AX);case 72:return E(_AY);case 73:return E(_AZ);case 74:return E(_B0);case 75:return E(_B1);case 76:return E(_B2);case 77:return E(_B3);case 78:return E(_Bx);case 79:return E(_Bw);case 80:return E(_Bv);case 81:return E(_Bu);case 82:return E(_Bt);case 83:return E(_Bs);case 84:return E(_Br);case 85:return E(_Bq);case 86:return E(_Bp);case 87:return E(_Bo);case 88:return E(_Bn);case 89:return E(_Bm);case 90:return E(_Bl);case 91:return E(_Bk);case 92:return E(_Bj);case 93:return E(_Bi);case 94:return E(_Bh);case 95:return E(_Bg);default:return new T0(2);}};return B(_sF(new T1(0,function(_BH){return (E(_BH)==94)?E(new T1(0,_BF)):new T0(2);}),new T(function(){return B(A1(_AQ,_AW));})));});return B(_sF(new T1(1,B(_tD(_wx,_wz,_B8))),_Bf));});return new F(function(){return _sF(new T1(0,function(_BI){switch(E(_BI)){case 34:return E(_B6);case 39:return E(_B5);case 92:return E(_B4);case 97:return E(_AX);case 98:return E(_AY);case 102:return E(_B2);case 110:return E(_B0);case 114:return E(_B3);case 116:return E(_AZ);case 118:return E(_B1);default:return new T0(2);}}),_B7);});},_BJ=function(_BK){return new F(function(){return A1(_BK,_gE);});},_BL=function(_BM){var _BN=E(_BM);if(!_BN._){return E(_BJ);}else{var _BO=E(_BN.a),_BP=_BO>>>0,_BQ=new T(function(){return B(_BL(_BN.b));});if(_BP>887){var _BR=u_iswspace(_BO);if(!E(_BR)){return E(_BJ);}else{var _BS=function(_BT){var _BU=new T(function(){return B(A1(_BQ,_BT));});return new T1(0,function(_BV){return E(_BU);});};return E(_BS);}}else{var _BW=E(_BP);if(_BW==32){var _BX=function(_BY){var _BZ=new T(function(){return B(A1(_BQ,_BY));});return new T1(0,function(_C0){return E(_BZ);});};return E(_BX);}else{if(_BW-9>>>0>4){if(E(_BW)==160){var _C1=function(_C2){var _C3=new T(function(){return B(A1(_BQ,_C2));});return new T1(0,function(_C4){return E(_C3);});};return E(_C1);}else{return E(_BJ);}}else{var _C5=function(_C6){var _C7=new T(function(){return B(A1(_BQ,_C6));});return new T1(0,function(_C8){return E(_C7);});};return E(_C5);}}}}},_C9=function(_Ca){var _Cb=new T(function(){return B(_C9(_Ca));}),_Cc=function(_Cd){return (E(_Cd)==92)?E(_Cb):new T0(2);},_Ce=function(_Cf){return E(new T1(0,_Cc));},_Cg=new T1(1,function(_Ch){return new F(function(){return A2(_BL,_Ch,_Ce);});}),_Ci=new T(function(){return B(_AV(function(_Cj){return new F(function(){return A1(_Ca,new T2(0,_Cj,_wr));});}));}),_Ck=function(_Cl){var _Cm=E(_Cl);if(_Cm==38){return E(_Cb);}else{var _Cn=_Cm>>>0;if(_Cn>887){var _Co=u_iswspace(_Cm);return (E(_Co)==0)?new T0(2):E(_Cg);}else{var _Cp=E(_Cn);return (_Cp==32)?E(_Cg):(_Cp-9>>>0>4)?(E(_Cp)==160)?E(_Cg):new T0(2):E(_Cg);}}};return new F(function(){return _sF(new T1(0,function(_Cq){return (E(_Cq)==92)?E(new T1(0,_Ck)):new T0(2);}),new T1(0,function(_Cr){var _Cs=E(_Cr);if(E(_Cs)==92){return E(_Ci);}else{return new F(function(){return A1(_Ca,new T2(0,_Cs,_wq));});}}));});},_Ct=function(_Cu,_Cv){var _Cw=new T(function(){return B(A1(_Cv,new T1(1,new T(function(){return B(A1(_Cu,_10));}))));}),_Cx=function(_Cy){var _Cz=E(_Cy),_CA=E(_Cz.a);if(E(_CA)==34){if(!E(_Cz.b)){return E(_Cw);}else{return new F(function(){return _Ct(function(_CB){return new F(function(){return A1(_Cu,new T2(1,_CA,_CB));});},_Cv);});}}else{return new F(function(){return _Ct(function(_CC){return new F(function(){return A1(_Cu,new T2(1,_CA,_CC));});},_Cv);});}};return new F(function(){return _C9(_Cx);});},_CD=new T(function(){return B(unCStr("_\'"));}),_CE=function(_CF){var _CG=u_iswalnum(_CF);if(!E(_CG)){return new F(function(){return _4B(_h7,_CF,_CD);});}else{return true;}},_CH=function(_CI){return new F(function(){return _CE(E(_CI));});},_CJ=new T(function(){return B(unCStr(",;()[]{}`"));}),_CK=new T(function(){return B(unCStr("=>"));}),_CL=new T2(1,_CK,_10),_CM=new T(function(){return B(unCStr("~"));}),_CN=new T2(1,_CM,_CL),_CO=new T(function(){return B(unCStr("@"));}),_CP=new T2(1,_CO,_CN),_CQ=new T(function(){return B(unCStr("->"));}),_CR=new T2(1,_CQ,_CP),_CS=new T(function(){return B(unCStr("<-"));}),_CT=new T2(1,_CS,_CR),_CU=new T(function(){return B(unCStr("|"));}),_CV=new T2(1,_CU,_CT),_CW=new T(function(){return B(unCStr("\\"));}),_CX=new T2(1,_CW,_CV),_CY=new T(function(){return B(unCStr("="));}),_CZ=new T2(1,_CY,_CX),_D0=new T(function(){return B(unCStr("::"));}),_D1=new T2(1,_D0,_CZ),_D2=new T(function(){return B(unCStr(".."));}),_D3=new T2(1,_D2,_D1),_D4=function(_D5){var _D6=new T(function(){return B(A1(_D5,_uh));}),_D7=new T(function(){var _D8=new T(function(){var _D9=function(_Da){var _Db=new T(function(){return B(A1(_D5,new T1(0,_Da)));});return new T1(0,function(_Dc){return (E(_Dc)==39)?E(_Db):new T0(2);});};return B(_AV(_D9));}),_Dd=function(_De){var _Df=E(_De);switch(E(_Df)){case 39:return new T0(2);case 92:return E(_D8);default:var _Dg=new T(function(){return B(A1(_D5,new T1(0,_Df)));});return new T1(0,function(_Dh){return (E(_Dh)==39)?E(_Dg):new T0(2);});}},_Di=new T(function(){var _Dj=new T(function(){return B(_Ct(_5V,_D5));}),_Dk=new T(function(){var _Dl=new T(function(){var _Dm=new T(function(){var _Dn=function(_Do){var _Dp=E(_Do),_Dq=u_iswalpha(_Dp);return (E(_Dq)==0)?(E(_Dp)==95)?new T1(1,B(_u3(_CH,function(_Dr){return new F(function(){return A1(_D5,new T1(3,new T2(1,_Dp,_Dr)));});}))):new T0(2):new T1(1,B(_u3(_CH,function(_Ds){return new F(function(){return A1(_D5,new T1(3,new T2(1,_Dp,_Ds)));});})));};return B(_sF(new T1(0,_Dn),new T(function(){return new T1(1,B(_tD(_vf,_wl,_D5)));})));}),_Dt=function(_Du){return (!B(_4B(_h7,_Du,_wn)))?new T0(2):new T1(1,B(_u3(_wo,function(_Dv){var _Dw=new T2(1,_Du,_Dv);if(!B(_4B(_qe,_Dw,_D3))){return new F(function(){return A1(_D5,new T1(4,_Dw));});}else{return new F(function(){return A1(_D5,new T1(2,_Dw));});}})));};return B(_sF(new T1(0,_Dt),_Dm));});return B(_sF(new T1(0,function(_Dx){if(!B(_4B(_h7,_Dx,_CJ))){return new T0(2);}else{return new F(function(){return A1(_D5,new T1(2,new T2(1,_Dx,_10)));});}}),_Dl));});return B(_sF(new T1(0,function(_Dy){return (E(_Dy)==34)?E(_Dj):new T0(2);}),_Dk));});return B(_sF(new T1(0,function(_Dz){return (E(_Dz)==39)?E(new T1(0,_Dd)):new T0(2);}),_Di));});return new F(function(){return _sF(new T1(1,function(_DA){return (E(_DA)._==0)?E(_D6):new T0(2);}),_D7);});},_DB=0,_DC=function(_DD,_DE){var _DF=new T(function(){var _DG=new T(function(){var _DH=function(_DI){var _DJ=new T(function(){var _DK=new T(function(){return B(A1(_DE,_DI));});return B(_D4(function(_DL){var _DM=E(_DL);return (_DM._==2)?(!B(_qL(_DM.a,_ti)))?new T0(2):E(_DK):new T0(2);}));}),_DN=function(_DO){return E(_DJ);};return new T1(1,function(_DP){return new F(function(){return A2(_BL,_DP,_DN);});});};return B(A2(_DD,_DB,_DH));});return B(_D4(function(_DQ){var _DR=E(_DQ);return (_DR._==2)?(!B(_qL(_DR.a,_th)))?new T0(2):E(_DG):new T0(2);}));}),_DS=function(_DT){return E(_DF);};return function(_DU){return new F(function(){return A2(_BL,_DU,_DS);});};},_DV=function(_DW,_DX){var _DY=function(_DZ){var _E0=new T(function(){return B(A1(_DW,_DZ));}),_E1=function(_E2){return new F(function(){return _sF(B(A1(_E0,_E2)),new T(function(){return new T1(1,B(_DC(_DY,_E2)));}));});};return E(_E1);},_E3=new T(function(){return B(A1(_DW,_DX));}),_E4=function(_E5){return new F(function(){return _sF(B(A1(_E3,_E5)),new T(function(){return new T1(1,B(_DC(_DY,_E5)));}));});};return E(_E4);},_E6=0,_E7=function(_E8,_E9){return new F(function(){return A1(_E9,_E6);});},_Ea=new T(function(){return B(unCStr("Fr"));}),_Eb=new T2(0,_Ea,_E7),_Ec=1,_Ed=function(_Ee,_Ef){return new F(function(){return A1(_Ef,_Ec);});},_Eg=new T(function(){return B(unCStr("Bl"));}),_Eh=new T2(0,_Eg,_Ed),_Ei=2,_Ej=function(_Ek,_El){return new F(function(){return A1(_El,_Ei);});},_Em=new T(function(){return B(unCStr("Ex"));}),_En=new T2(0,_Em,_Ej),_Eo=3,_Ep=function(_Eq,_Er){return new F(function(){return A1(_Er,_Eo);});},_Es=new T(function(){return B(unCStr("Mv"));}),_Et=new T2(0,_Es,_Ep),_Eu=4,_Ev=function(_Ew,_Ex){return new F(function(){return A1(_Ex,_Eu);});},_Ey=new T(function(){return B(unCStr("Pn"));}),_Ez=new T2(0,_Ey,_Ev),_EA=8,_EB=function(_EC,_ED){return new F(function(){return A1(_ED,_EA);});},_EE=new T(function(){return B(unCStr("DF"));}),_EF=new T2(0,_EE,_EB),_EG=new T2(1,_EF,_10),_EH=7,_EI=function(_EJ,_EK){return new F(function(){return A1(_EK,_EH);});},_EL=new T(function(){return B(unCStr("DB"));}),_EM=new T2(0,_EL,_EI),_EN=new T2(1,_EM,_EG),_EO=6,_EP=function(_EQ,_ER){return new F(function(){return A1(_ER,_EO);});},_ES=new T(function(){return B(unCStr("Cm"));}),_ET=new T2(0,_ES,_EP),_EU=new T2(1,_ET,_EN),_EV=5,_EW=function(_EX,_EY){return new F(function(){return A1(_EY,_EV);});},_EZ=new T(function(){return B(unCStr("Wn"));}),_F0=new T2(0,_EZ,_EW),_F1=new T2(1,_F0,_EU),_F2=new T2(1,_Ez,_F1),_F3=new T2(1,_Et,_F2),_F4=new T2(1,_En,_F3),_F5=new T2(1,_Eh,_F4),_F6=new T2(1,_Eb,_F5),_F7=function(_F8,_F9,_Fa){var _Fb=E(_F8);if(!_Fb._){return new T0(2);}else{var _Fc=E(_Fb.a),_Fd=_Fc.a,_Fe=new T(function(){return B(A2(_Fc.b,_F9,_Fa));}),_Ff=new T(function(){return B(_D4(function(_Fg){var _Fh=E(_Fg);switch(_Fh._){case 3:return (!B(_qL(_Fd,_Fh.a)))?new T0(2):E(_Fe);case 4:return (!B(_qL(_Fd,_Fh.a)))?new T0(2):E(_Fe);default:return new T0(2);}}));}),_Fi=function(_Fj){return E(_Ff);};return new F(function(){return _sF(new T1(1,function(_Fk){return new F(function(){return A2(_BL,_Fk,_Fi);});}),new T(function(){return B(_F7(_Fb.b,_F9,_Fa));}));});}},_Fl=function(_Fm,_Fn){return new F(function(){return _F7(_F6,_Fm,_Fn);});},_Fo=function(_Fp){var _Fq=function(_Fr){return E(new T2(3,_Fp,_tu));};return new T1(1,function(_Fs){return new F(function(){return A2(_BL,_Fs,_Fq);});});},_Ft=new T(function(){return B(A3(_DV,_Fl,_DB,_Fo));}),_Fu=new T(function(){return B(unCStr("empty"));}),_Fv=new T2(1,_Fu,_10),_Fw=new T(function(){return B(err(_so));}),_Fx=new T(function(){return B(err(_sq));}),_Fy=function(_Fz,_FA){var _FB=function(_FC,_FD){var _FE=function(_FF){return new F(function(){return A1(_FD,new T(function(){return  -E(_FF);}));});},_FG=new T(function(){return B(_D4(function(_FH){return new F(function(){return A3(_Fz,_FH,_FC,_FE);});}));}),_FI=function(_FJ){return E(_FG);},_FK=function(_FL){return new F(function(){return A2(_BL,_FL,_FI);});},_FM=new T(function(){return B(_D4(function(_FN){var _FO=E(_FN);if(_FO._==4){var _FP=E(_FO.a);if(!_FP._){return new F(function(){return A3(_Fz,_FO,_FC,_FD);});}else{if(E(_FP.a)==45){if(!E(_FP.b)._){return E(new T1(1,_FK));}else{return new F(function(){return A3(_Fz,_FO,_FC,_FD);});}}else{return new F(function(){return A3(_Fz,_FO,_FC,_FD);});}}}else{return new F(function(){return A3(_Fz,_FO,_FC,_FD);});}}));}),_FQ=function(_FR){return E(_FM);};return new T1(1,function(_FS){return new F(function(){return A2(_BL,_FS,_FQ);});});};return new F(function(){return _DV(_FB,_FA);});},_FT=function(_FU){var _FV=E(_FU);if(!_FV._){var _FW=_FV.b,_FX=new T(function(){return B(_vx(new T(function(){return B(_aR(E(_FV.a)));}),new T(function(){return B(_mt(_FW,0));},1),B(_6e(_vn,_FW))));});return new T1(1,_FX);}else{return (E(_FV.b)._==0)?(E(_FV.c)._==0)?new T1(1,new T(function(){return B(_vO(_vm,_FV.a));})):__Z:__Z;}},_FY=function(_FZ,_G0){return new T0(2);},_G1=function(_G2){var _G3=E(_G2);if(_G3._==5){var _G4=B(_FT(_G3.a));if(!_G4._){return E(_FY);}else{var _G5=new T(function(){return B(_ba(_G4.a));});return function(_G6,_G7){return new F(function(){return A1(_G7,_G5);});};}}else{return E(_FY);}},_G8=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_G9=new T2(1,_G,_10),_Ga=function(_Gb){while(1){var _Gc=B((function(_Gd){var _Ge=E(_Gd);if(!_Ge._){return __Z;}else{var _Gf=_Ge.b,_Gg=E(_Ge.a);if(!E(_Gg.b)._){return new T2(1,_Gg.a,new T(function(){return B(_Ga(_Gf));}));}else{_Gb=_Gf;return __continue;}}})(_Gb));if(_Gc!=__continue){return _Gc;}}},_Gh=function(_Gi,_Gj){while(1){var _Gk=E(_Gi);if(!_Gk._){return E(_Gj);}else{var _Gl=new T2(1,_Gk.a,_Gj);_Gi=_Gk.b;_Gj=_Gl;continue;}}},_Gm=function(_Gn,_Go){var _Gp=E(_Gn);if(!_Gp._){return __Z;}else{var _Gq=E(_Go);return (_Gq._==0)?__Z:new T2(1,new T2(0,_Gp.a,_Gq.a),new T(function(){return B(_Gm(_Gp.b,_Gq.b));}));}},_Gr=function(_Gs,_Gt,_Gu){while(1){var _Gv=B((function(_Gw,_Gx,_Gy){var _Gz=E(_Gy);if(!_Gz._){return E(_Gx);}else{var _GA=_Gz.a,_GB=_Gz.b,_GC=B(_si(_qe,_GA,_s7));if(!_GC._){var _GD=E(_Fv);}else{var _GD=E(_GC.a);}if(!B(_qQ(_GD,_Fv))){var _GE=B(_Gh(B(_Gm(B(_Gh(_Gx,_10)),new T(function(){return B(_Gh(_GD,_10));},1))),_10)),_GF=B(_mt(_GE,0)),_GG=new T(function(){var _GH=B(_6e(_sg,_GE));if(!_GH._){return __Z;}else{var _GI=_GH.a,_GJ=E(_GH.b);if(!_GJ._){return __Z;}else{var _GK=_GJ.a;if(!E(_GJ.b)._){if(!B(_qL(_GA,_rJ))){if(!B(_qL(_GA,_rI))){if(!B(_qL(_GA,_rH))){if(!B(_qL(_GA,_rL))){if(!B(_qL(_GA,_rK))){return __Z;}else{if(!B(_qL(_GI,_ss))){if(!B(_qL(_GK,_ss))){return E(_st);}else{return E(_ss);}}else{return E(_ss);}}}else{var _GL=B(_rv(new T2(0,new T(function(){var _GM=E(_GI);if(!_GM._){return E(_nh);}else{return E(_GM.a);}}),new T(function(){var _GN=B(_Ga(B(_sv(_Ft,_GK))));if(!_GN._){return E(_sp);}else{if(!E(_GN.b)._){return E(_GN.a);}else{return E(_sr);}}})),E(E(_Gw).a).b)),_GO=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_GP){return new F(function(){return _I(0,E(_GL.a),_GP);});},new T2(1,function(_GQ){return new F(function(){return _I(0,E(_GL.b),_GQ);});},_10)),_G9));});return new T2(1,_H,_GO);}}else{return new T2(1,new T(function(){var _GR=B(_Ga(B(_sv(_G8,_GI))));if(!_GR._){return E(_Fw);}else{if(!E(_GR.b)._){var _GS=B(_Ga(B(_sv(_G8,_GK))));if(!_GS._){return E(_Fw);}else{if(!E(_GS.b)._){return E(B(_6R(B(_6R(E(E(_Gw).a).b,E(_GS.a))),E(_GR.a))).a);}else{return E(_Fx);}}}else{return E(_Fx);}}}),_10);}}else{if(!B(_qL(_GI,_GK))){return E(_st);}else{return E(_ss);}}}else{if(!B(_qL(_GI,_ss))){return E(_st);}else{if(!B(_qL(_GK,_ss))){return E(_st);}else{return E(_ss);}}}}else{return __Z;}}}});if(_GF>0){var _GT=_Gw,_GU=B(_y(B(_Gh(B(_rB(_GF,B(_Gh(_Gx,_10)))),_10)),new T2(1,_GG,_10)));_Gs=_GT;_Gt=_GU;_Gu=_GB;return __continue;}else{var _GT=_Gw,_GU=B(_y(B(_Gh(B(_Gh(_Gx,_10)),_10)),new T2(1,_GG,_10)));_Gs=_GT;_Gt=_GU;_Gu=_GB;return __continue;}}else{var _GT=_Gw,_GU=B(_y(_Gx,new T2(1,_GA,_10)));_Gs=_GT;_Gt=_GU;_Gu=_GB;return __continue;}}})(_Gs,_Gt,_Gu));if(_Gv!=__continue){return _Gv;}}},_GV=new T(function(){return B(_e7("Event.hs:(86,1)-(90,73)|function addMemory"));}),_GW=function(_GX,_GY){var _GZ=E(_GX),_H0=E(_GY);if(!B(_qL(_GZ.a,_H0.a))){return false;}else{return new F(function(){return _qL(_GZ.b,_H0.b);});}},_H1=new T2(1,_10,_10),_H2=function(_H3,_H4,_H5){var _H6=E(_H5);if(!_H6._){return new T2(0,new T2(1,_H4,_10),_10);}else{var _H7=E(_H4),_H8=new T(function(){var _H9=B(_H2(_H3,_H6.a,_H6.b));return new T2(0,_H9.a,_H9.b);});return (_H3!=_H7)?new T2(0,new T2(1,_H7,new T(function(){return E(E(_H8).a);})),new T(function(){return E(E(_H8).b);})):new T2(0,_10,new T2(1,new T(function(){return E(E(_H8).a);}),new T(function(){return E(E(_H8).b);})));}},_Ha=32,_Hb=function(_Hc){var _Hd=E(_Hc);if(!_Hd._){return __Z;}else{var _He=new T(function(){return B(_y(_Hd.a,new T(function(){return B(_Hb(_Hd.b));},1)));});return new T2(1,_Ha,_He);}},_Hf=function(_Hg,_Hh,_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx){while(1){var _Hy=B((function(_Hz,_HA,_HB,_HC,_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_HQ){var _HR=E(_Hz);if(!_HR._){return {_:0,a:_HA,b:_HB,c:_HC,d:_HD,e:_HE,f:_HF,g:_HG,h:_HH,i:_HI,j:_HJ,k:_HK,l:_HL,m:_HM,n:_HN,o:_HO,p:_HP,q:_HQ};}else{var _HS=_HR.a,_HT=E(_HR.b);if(!_HT._){return E(_GV);}else{var _HU=new T(function(){var _HV=E(_HT.a);if(!_HV._){var _HW=B(_Gr({_:0,a:E(_HA),b:E(_HB),c:E(_HC),d:E(_HD),e:E(_HE),f:E(_HF),g:E(_HG),h:E(_HH),i:_HI,j:_HJ,k:_HK,l:_HL,m:E(_HM),n:_HN,o:E(_HO),p:E(_HP),q:E(_HQ)},_10,_H1));if(!_HW._){return __Z;}else{return B(_y(_HW.a,new T(function(){return B(_Hb(_HW.b));},1)));}}else{var _HX=_HV.a,_HY=E(_HV.b);if(!_HY._){var _HZ=B(_Gr({_:0,a:E(_HA),b:E(_HB),c:E(_HC),d:E(_HD),e:E(_HE),f:E(_HF),g:E(_HG),h:E(_HH),i:_HI,j:_HJ,k:_HK,l:_HL,m:E(_HM),n:_HN,o:E(_HO),p:E(_HP),q:E(_HQ)},_10,new T2(1,new T2(1,_HX,_10),_10)));if(!_HZ._){return __Z;}else{return B(_y(_HZ.a,new T(function(){return B(_Hb(_HZ.b));},1)));}}else{var _I0=E(_HX),_I1=new T(function(){var _I2=B(_H2(95,_HY.a,_HY.b));return new T2(0,_I2.a,_I2.b);});if(E(_I0)==95){var _I3=B(_Gr({_:0,a:E(_HA),b:E(_HB),c:E(_HC),d:E(_HD),e:E(_HE),f:E(_HF),g:E(_HG),h:E(_HH),i:_HI,j:_HJ,k:_HK,l:_HL,m:E(_HM),n:_HN,o:E(_HO),p:E(_HP),q:E(_HQ)},_10,new T2(1,_10,new T2(1,new T(function(){return E(E(_I1).a);}),new T(function(){return E(E(_I1).b);})))));if(!_I3._){return __Z;}else{return B(_y(_I3.a,new T(function(){return B(_Hb(_I3.b));},1)));}}else{var _I4=B(_Gr({_:0,a:E(_HA),b:E(_HB),c:E(_HC),d:E(_HD),e:E(_HE),f:E(_HF),g:E(_HG),h:E(_HH),i:_HI,j:_HJ,k:_HK,l:_HL,m:E(_HM),n:_HN,o:E(_HO),p:E(_HP),q:E(_HQ)},_10,new T2(1,new T2(1,_I0,new T(function(){return E(E(_I1).a);})),new T(function(){return E(E(_I1).b);}))));if(!_I4._){return __Z;}else{return B(_y(_I4.a,new T(function(){return B(_Hb(_I4.b));},1)));}}}}}),_I5=_HA,_I6=_HB,_I7=_HC,_I8=_HD,_I9=_HE,_Ia=_HF,_Ib=_HH,_Ic=_HI,_Id=_HJ,_Ie=_HK,_If=_HL,_Ig=_HM,_Ih=_HN,_Ii=_HO,_Ij=_HP,_Ik=_HQ;_Hg=_HT.b;_Hh=_I5;_Hi=_I6;_Hj=_I7;_Hk=_I8;_Hl=_I9;_Hm=_Ia;_Hn=new T2(1,new T2(0,_HS,_HU),new T(function(){var _Il=B(_si(_qe,_HS,_HG));if(!_Il._){var _Im=__Z;}else{var _Im=E(_Il.a);}if(!B(_qL(_Im,_10))){return B(_qE(_GW,new T2(0,_HS,_Im),_HG));}else{return E(_HG);}}));_Ho=_Ib;_Hp=_Ic;_Hq=_Id;_Hr=_Ie;_Hs=_If;_Ht=_Ig;_Hu=_Ih;_Hv=_Ii;_Hw=_Ij;_Hx=_Ik;return __continue;}}})(_Hg,_Hh,_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx));if(_Hy!=__continue){return _Hy;}}},_In=function(_Io){var _Ip=E(_Io);if(!_Ip._){return new T2(0,_10,_10);}else{var _Iq=E(_Ip.a),_Ir=new T(function(){var _Is=B(_In(_Ip.b));return new T2(0,_Is.a,_Is.b);});return new T2(0,new T2(1,_Iq.a,new T(function(){return E(E(_Ir).a);})),new T2(1,_Iq.b,new T(function(){return E(E(_Ir).b);})));}},_It=function(_Iu,_Iv,_Iw){while(1){var _Ix=B((function(_Iy,_Iz,_IA){var _IB=E(_IA);if(!_IB._){return __Z;}else{var _IC=_IB.b;if(_Iz!=E(_IB.a)){var _ID=_Iy+1|0,_IE=_Iz;_Iu=_ID;_Iv=_IE;_Iw=_IC;return __continue;}else{return new T2(1,_Iy,new T(function(){return B(_It(_Iy+1|0,_Iz,_IC));}));}}})(_Iu,_Iv,_Iw));if(_Ix!=__continue){return _Ix;}}},_IF=function(_IG,_IH,_II){var _IJ=E(_II);if(!_IJ._){return __Z;}else{var _IK=_IJ.b,_IL=E(_IH);if(_IL!=E(_IJ.a)){return new F(function(){return _It(_IG+1|0,_IL,_IK);});}else{return new T2(1,_IG,new T(function(){return B(_It(_IG+1|0,_IL,_IK));}));}}},_IM=function(_IN,_IO,_IP,_IQ){var _IR=E(_IQ);if(!_IR._){return __Z;}else{var _IS=_IR.b;return (!B(_4B(_3M,_IN,_IP)))?new T2(1,_IR.a,new T(function(){return B(_IM(_IN+1|0,_IO,_IP,_IS));})):new T2(1,_IO,new T(function(){return B(_IM(_IN+1|0,_IO,_IP,_IS));}));}},_IT=function(_IU,_IV,_IW){var _IX=E(_IW);if(!_IX._){return __Z;}else{var _IY=new T(function(){var _IZ=B(_In(_IX.a)),_J0=_IZ.a,_J1=new T(function(){return B(_IM(0,_IV,new T(function(){return B(_IF(0,_IU,_J0));}),_IZ.b));},1);return B(_Gm(_J0,_J1));});return new T2(1,_IY,new T(function(){return B(_IT(_IU,_IV,_IX.b));}));}},_J2=function(_J3){var _J4=E(_J3);return (_J4._==0)?E(_nh):E(_J4.a);},_J5=new T(function(){return B(_e7("Event.hs:(59,1)-(62,93)|function changeType"));}),_J6=new T(function(){return B(_e7("Event.hs:56:16-116|case"));}),_J7=new T(function(){return B(unCStr("Wn"));}),_J8=new T(function(){return B(unCStr("Pn"));}),_J9=new T(function(){return B(unCStr("Mv"));}),_Ja=new T(function(){return B(unCStr("Fr"));}),_Jb=new T(function(){return B(unCStr("Ex"));}),_Jc=new T(function(){return B(unCStr("DF"));}),_Jd=new T(function(){return B(unCStr("DB"));}),_Je=new T(function(){return B(unCStr("Cm"));}),_Jf=new T(function(){return B(unCStr("Bl"));}),_Jg=function(_Jh){return (!B(_qL(_Jh,_Jf)))?(!B(_qL(_Jh,_Je)))?(!B(_qL(_Jh,_Jd)))?(!B(_qL(_Jh,_Jc)))?(!B(_qL(_Jh,_Jb)))?(!B(_qL(_Jh,_Ja)))?(!B(_qL(_Jh,_J9)))?(!B(_qL(_Jh,_J8)))?(!B(_qL(_Jh,_J7)))?E(_J6):5:4:3:0:2:8:7:6:1;},_Ji=function(_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA){while(1){var _JB=B((function(_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK,_JL,_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT){var _JU=E(_JC);if(!_JU._){return {_:0,a:_JD,b:_JE,c:_JF,d:_JG,e:_JH,f:_JI,g:_JJ,h:_JK,i:_JL,j:_JM,k:_JN,l:_JO,m:_JP,n:_JQ,o:_JR,p:_JS,q:_JT};}else{var _JV=E(_JU.b);if(!_JV._){return E(_J5);}else{var _JW=E(_JD),_JX=_JE,_JY=_JF,_JZ=_JG,_K0=_JH,_K1=_JI,_K2=_JJ,_K3=_JK,_K4=_JL,_K5=_JM,_K6=_JN,_K7=_JO,_K8=_JP,_K9=_JQ,_Ka=_JR,_Kb=_JS,_Kc=_JT;_Jj=_JV.b;_Jk={_:0,a:E(_JW.a),b:E(B(_IT(new T(function(){return B(_J2(_JU.a));}),new T(function(){return B(_Jg(_JV.a));}),_JW.b))),c:_JW.c,d:_JW.d,e:_JW.e,f:E(_JW.f),g:_JW.g,h:E(_JW.h),i:E(_JW.i),j:E(_JW.j)};_Jl=_JX;_Jm=_JY;_Jn=_JZ;_Jo=_K0;_Jp=_K1;_Jq=_K2;_Jr=_K3;_Js=_K4;_Jt=_K5;_Ju=_K6;_Jv=_K7;_Jw=_K8;_Jx=_K9;_Jy=_Ka;_Jz=_Kb;_JA=_Kc;return __continue;}}})(_Jj,_Jk,_Jl,_Jm,_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA));if(_JB!=__continue){return _JB;}}},_Kd=function(_Ke,_Kf){while(1){var _Kg=E(_Kf);if(!_Kg._){return __Z;}else{var _Kh=_Kg.b,_Ki=E(_Ke);if(_Ki==1){return E(_Kh);}else{_Ke=_Ki-1|0;_Kf=_Kh;continue;}}}},_Kj=function(_Kk,_Kl){while(1){var _Km=E(_Kl);if(!_Km._){return __Z;}else{var _Kn=_Km.b,_Ko=E(_Kk);if(_Ko==1){return E(_Kn);}else{_Kk=_Ko-1|0;_Kl=_Kn;continue;}}}},_Kp=function(_Kq,_Kr,_Ks,_Kt,_Ku){var _Kv=new T(function(){var _Kw=E(_Kq),_Kx=new T(function(){return B(_6R(_Ku,_Kr));}),_Ky=new T2(1,new T2(0,_Ks,_Kt),new T(function(){var _Kz=_Kw+1|0;if(_Kz>0){return B(_Kj(_Kz,_Kx));}else{return E(_Kx);}}));if(0>=_Kw){return E(_Ky);}else{var _KA=function(_KB,_KC){var _KD=E(_KB);if(!_KD._){return E(_Ky);}else{var _KE=_KD.a,_KF=E(_KC);return (_KF==1)?new T2(1,_KE,_Ky):new T2(1,_KE,new T(function(){return B(_KA(_KD.b,_KF-1|0));}));}};return B(_KA(_Kx,_Kw));}}),_KG=new T2(1,_Kv,new T(function(){var _KH=_Kr+1|0;if(_KH>0){return B(_Kd(_KH,_Ku));}else{return E(_Ku);}}));if(0>=_Kr){return E(_KG);}else{var _KI=function(_KJ,_KK){var _KL=E(_KJ);if(!_KL._){return E(_KG);}else{var _KM=_KL.a,_KN=E(_KK);return (_KN==1)?new T2(1,_KM,_KG):new T2(1,_KM,new T(function(){return B(_KI(_KL.b,_KN-1|0));}));}};return new F(function(){return _KI(_Ku,_Kr);});}},_KO=32,_KP=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_KQ=function(_KR){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_KR,_KP));})),_dt);});},_KS=function(_KT){return new F(function(){return _KQ("Event.hs:42:27-53|(x\' : y\' : _)");});},_KU=new T(function(){return B(_KS(_));}),_KV=function(_KW,_KX,_KY,_KZ,_L0,_L1,_L2,_L3,_L4,_L5,_L6,_L7,_L8,_L9,_La,_Lb,_Lc,_Ld){while(1){var _Le=B((function(_Lf,_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw){var _Lx=E(_Lf);if(!_Lx._){return {_:0,a:_Lg,b:_Lh,c:_Li,d:_Lj,e:_Lk,f:_Ll,g:_Lm,h:_Ln,i:_Lo,j:_Lp,k:_Lq,l:_Lr,m:_Ls,n:_Lt,o:_Lu,p:_Lv,q:_Lw};}else{var _Ly=E(_Lg),_Lz=new T(function(){var _LA=E(_Lx.a);if(!_LA._){return E(_KU);}else{var _LB=E(_LA.b);if(!_LB._){return E(_KU);}else{var _LC=_LB.a,_LD=_LB.b,_LE=E(_LA.a);if(E(_LE)==44){return new T2(0,_10,new T(function(){return E(B(_H2(44,_LC,_LD)).a);}));}else{var _LF=B(_H2(44,_LC,_LD)),_LG=E(_LF.b);if(!_LG._){return E(_KU);}else{return new T2(0,new T2(1,_LE,_LF.a),_LG.a);}}}}}),_LH=B(_Ga(B(_sv(_G8,new T(function(){return E(E(_Lz).b);})))));if(!_LH._){return E(_Fw);}else{if(!E(_LH.b)._){var _LI=new T(function(){var _LJ=B(_Ga(B(_sv(_G8,new T(function(){return E(E(_Lz).a);})))));if(!_LJ._){return E(_Fw);}else{if(!E(_LJ.b)._){return E(_LJ.a);}else{return E(_Fx);}}},1),_LK=_Lh,_LL=_Li,_LM=_Lj,_LN=_Lk,_LO=_Ll,_LP=_Lm,_LQ=_Ln,_LR=_Lo,_LS=_Lp,_LT=_Lq,_LU=_Lr,_LV=_Ls,_LW=_Lt,_LX=_Lu,_LY=_Lv,_LZ=_Lw;_KW=_Lx.b;_KX={_:0,a:E(_Ly.a),b:E(B(_Kp(_LI,E(_LH.a),_KO,_E6,_Ly.b))),c:_Ly.c,d:_Ly.d,e:_Ly.e,f:E(_Ly.f),g:_Ly.g,h:E(_Ly.h),i:E(_Ly.i),j:E(_Ly.j)};_KY=_LK;_KZ=_LL;_L0=_LM;_L1=_LN;_L2=_LO;_L3=_LP;_L4=_LQ;_L5=_LR;_L6=_LS;_L7=_LT;_L8=_LU;_L9=_LV;_La=_LW;_Lb=_LX;_Lc=_LY;_Ld=_LZ;return __continue;}else{return E(_Fx);}}}})(_KW,_KX,_KY,_KZ,_L0,_L1,_L2,_L3,_L4,_L5,_L6,_L7,_L8,_L9,_La,_Lb,_Lc,_Ld));if(_Le!=__continue){return _Le;}}},_M0=function(_M1,_M2,_M3){var _M4=E(_M3);return (_M4._==0)?0:(!B(A3(_4z,_M1,_M2,_M4.a)))?1+B(_M0(_M1,_M2,_M4.b))|0:0;},_M5=function(_M6,_M7){while(1){var _M8=E(_M7);if(!_M8._){return __Z;}else{var _M9=_M8.b,_Ma=E(_M6);if(_Ma==1){return E(_M9);}else{_M6=_Ma-1|0;_M7=_M9;continue;}}}},_Mb=function(_Mc,_Md){var _Me=new T(function(){var _Mf=_Mc+1|0;if(_Mf>0){return B(_M5(_Mf,_Md));}else{return E(_Md);}});if(0>=_Mc){return E(_Me);}else{var _Mg=function(_Mh,_Mi){var _Mj=E(_Mh);if(!_Mj._){return E(_Me);}else{var _Mk=_Mj.a,_Ml=E(_Mi);return (_Ml==1)?new T2(1,_Mk,_Me):new T2(1,_Mk,new T(function(){return B(_Mg(_Mj.b,_Ml-1|0));}));}};return new F(function(){return _Mg(_Md,_Mc);});}},_Mm=function(_Mn,_Mo){return new F(function(){return _Mb(E(_Mn),_Mo);});},_Mp= -1,_Mq=function(_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MG,_MH,_MI){while(1){var _MJ=B((function(_MK,_ML,_MM,_MN,_MO,_MP,_MQ,_MR,_MS,_MT,_MU,_MV,_MW,_MX,_MY,_MZ,_N0,_N1){var _N2=E(_MK);if(!_N2._){return {_:0,a:_ML,b:_MM,c:_MN,d:_MO,e:_MP,f:_MQ,g:_MR,h:_MS,i:_MT,j:_MU,k:_MV,l:_MW,m:_MX,n:_MY,o:_MZ,p:_N0,q:_N1};}else{var _N3=_N2.a,_N4=B(_6e(_sg,_MP)),_N5=B(_4B(_qe,_N3,_N4)),_N6=new T(function(){if(!E(_N5)){return E(_Mp);}else{return B(_M0(_qe,_N3,_N4));}});if(!E(_N5)){var _N7=E(_MP);}else{var _N7=B(_Mm(_N6,_MP));}if(!E(_N5)){var _N8=E(_MQ);}else{var _N8=B(_Mm(_N6,_MQ));}var _N9=_ML,_Na=_MM,_Nb=_MN,_Nc=_MO,_Nd=_MR,_Ne=_MS,_Nf=_MT,_Ng=_MU,_Nh=_MV,_Ni=_MW,_Nj=_MX,_Nk=_MY,_Nl=_MZ,_Nm=_N0,_Nn=_N1;_Mr=_N2.b;_Ms=_N9;_Mt=_Na;_Mu=_Nb;_Mv=_Nc;_Mw=_N7;_Mx=_N8;_My=_Nd;_Mz=_Ne;_MA=_Nf;_MB=_Ng;_MC=_Nh;_MD=_Ni;_ME=_Nj;_MF=_Nk;_MG=_Nl;_MH=_Nm;_MI=_Nn;return __continue;}})(_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MG,_MH,_MI));if(_MJ!=__continue){return _MJ;}}},_No=function(_Np){var _Nq=E(_Np);if(!_Nq._){return new T2(0,_10,_10);}else{var _Nr=E(_Nq.a),_Ns=new T(function(){var _Nt=B(_No(_Nq.b));return new T2(0,_Nt.a,_Nt.b);});return new T2(0,new T2(1,_Nr.a,new T(function(){return E(E(_Ns).a);})),new T2(1,_Nr.b,new T(function(){return E(E(_Ns).b);})));}},_Nu=function(_Nv){return new F(function(){return _KQ("Event.hs:103:28-52|(c : d : _)");});},_Nw=new T(function(){return B(_Nu(_));}),_Nx=function(_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW){while(1){var _NX=B((function(_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om){var _On=E(_NY);if(!_On._){return {_:0,a:E(_NZ),b:E(_O0),c:E(_O1),d:E(_O2),e:E(_O3),f:E(_O4),g:E(_O5),h:E(_O6),i:_O7,j:_O8,k:_O9,l:_Oa,m:E(_Ob),n:_Oc,o:E(_Od),p:E({_:0,a:E(_Oe),b:E(_Of),c:E(_Og),d:E(_wr),e:E(_Oi),f:E(_Oj),g:E(_wr),h:E(_Ol)}),q:E(_Om)};}else{var _Oo=new T(function(){var _Op=E(_On.a);if(!_Op._){return E(_Nw);}else{var _Oq=E(_Op.b);if(!_Oq._){return E(_Nw);}else{var _Or=_Oq.a,_Os=_Oq.b,_Ot=E(_Op.a);if(E(_Ot)==44){return new T2(0,_10,new T(function(){return E(B(_H2(44,_Or,_Os)).a);}));}else{var _Ou=B(_H2(44,_Or,_Os)),_Ov=E(_Ou.b);if(!_Ov._){return E(_Nw);}else{return new T2(0,new T2(1,_Ot,_Ou.a),_Ov.a);}}}}}),_Ow=_NZ,_Ox=_O0,_Oy=_O1,_Oz=_O2,_OA=_O3,_OB=_O4,_OC=_O5,_OD=_O6,_OE=_O7,_OF=_O8,_OG=_O9,_OH=_Oa,_OI=B(_y(_Ob,new T2(1,new T2(0,new T(function(){return E(E(_Oo).a);}),new T(function(){return E(E(_Oo).b);})),_10))),_OJ=_Oc,_OK=_Od,_OL=_Oe,_OM=_Of,_ON=_Og,_OO=_Oh,_OP=_Oi,_OQ=_Oj,_OR=_Ok,_OS=_Ol,_OT=_Om;_Ny=_On.b;_Nz=_Ow;_NA=_Ox;_NB=_Oy;_NC=_Oz;_ND=_OA;_NE=_OB;_NF=_OC;_NG=_OD;_NH=_OE;_NI=_OF;_NJ=_OG;_NK=_OH;_NL=_OI;_NM=_OJ;_NN=_OK;_NO=_OL;_NP=_OM;_NQ=_ON;_NR=_OO;_NS=_OP;_NT=_OQ;_NU=_OR;_NV=_OS;_NW=_OT;return __continue;}})(_Ny,_Nz,_NA,_NB,_NC,_ND,_NE,_NF,_NG,_NH,_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW));if(_NX!=__continue){return _NX;}}},_OU=function(_OV){return new F(function(){return _KQ("Event.hs:49:27-53|(x\' : y\' : _)");});},_OW=new T(function(){return B(_OU(_));}),_OX=function(_OY){return new F(function(){return _KQ("Event.hs:50:27-55|(chs : tps : _)");});},_OZ=new T(function(){return B(_OX(_));}),_P0=new T(function(){return B(_e7("Event.hs:(47,1)-(53,83)|function putCell"));}),_P1=function(_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb,_Pc,_Pd,_Pe,_Pf,_Pg,_Ph,_Pi,_Pj){while(1){var _Pk=B((function(_Pl,_Pm,_Pn,_Po,_Pp,_Pq,_Pr,_Ps,_Pt,_Pu,_Pv,_Pw,_Px,_Py,_Pz,_PA,_PB,_PC){var _PD=E(_Pl);if(!_PD._){return {_:0,a:_Pm,b:_Pn,c:_Po,d:_Pp,e:_Pq,f:_Pr,g:_Ps,h:_Pt,i:_Pu,j:_Pv,k:_Pw,l:_Px,m:_Py,n:_Pz,o:_PA,p:_PB,q:_PC};}else{var _PE=E(_PD.b);if(!_PE._){return E(_P0);}else{var _PF=E(_Pm),_PG=new T(function(){var _PH=E(_PD.a);if(!_PH._){return E(_OW);}else{var _PI=E(_PH.b);if(!_PI._){return E(_OW);}else{var _PJ=_PI.a,_PK=_PI.b,_PL=E(_PH.a);if(E(_PL)==44){return new T2(0,_10,new T(function(){return E(B(_H2(44,_PJ,_PK)).a);}));}else{var _PM=B(_H2(44,_PJ,_PK)),_PN=E(_PM.b);if(!_PN._){return E(_OW);}else{return new T2(0,new T2(1,_PL,_PM.a),_PN.a);}}}}}),_PO=B(_Ga(B(_sv(_G8,new T(function(){return E(E(_PG).b);})))));if(!_PO._){return E(_Fw);}else{if(!E(_PO.b)._){var _PP=new T(function(){var _PQ=E(_PE.a);if(!_PQ._){return E(_OZ);}else{var _PR=E(_PQ.b);if(!_PR._){return E(_OZ);}else{var _PS=_PR.a,_PT=_PR.b,_PU=E(_PQ.a);if(E(_PU)==44){return new T2(0,_10,new T(function(){return E(B(_H2(44,_PS,_PT)).a);}));}else{var _PV=B(_H2(44,_PS,_PT)),_PW=E(_PV.b);if(!_PW._){return E(_OZ);}else{return new T2(0,new T2(1,_PU,_PV.a),_PW.a);}}}}}),_PX=new T(function(){var _PY=B(_Ga(B(_sv(_G8,new T(function(){return E(E(_PG).a);})))));if(!_PY._){return E(_Fw);}else{if(!E(_PY.b)._){return E(_PY.a);}else{return E(_Fx);}}},1),_PZ=_Pn,_Q0=_Po,_Q1=_Pp,_Q2=_Pq,_Q3=_Pr,_Q4=_Ps,_Q5=_Pt,_Q6=_Pu,_Q7=_Pv,_Q8=_Pw,_Q9=_Px,_Qa=_Py,_Qb=_Pz,_Qc=_PA,_Qd=_PB,_Qe=_PC;_P2=_PE.b;_P3={_:0,a:E(_PF.a),b:E(B(_Kp(_PX,E(_PO.a),new T(function(){return B(_J2(E(_PP).a));}),new T(function(){return B(_Jg(E(_PP).b));}),_PF.b))),c:_PF.c,d:_PF.d,e:_PF.e,f:E(_PF.f),g:_PF.g,h:E(_PF.h),i:E(_PF.i),j:E(_PF.j)};_P4=_PZ;_P5=_Q0;_P6=_Q1;_P7=_Q2;_P8=_Q3;_P9=_Q4;_Pa=_Q5;_Pb=_Q6;_Pc=_Q7;_Pd=_Q8;_Pe=_Q9;_Pf=_Qa;_Pg=_Qb;_Ph=_Qc;_Pi=_Qd;_Pj=_Qe;return __continue;}else{return E(_Fx);}}}}})(_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9,_Pa,_Pb,_Pc,_Pd,_Pe,_Pf,_Pg,_Ph,_Pi,_Pj));if(_Pk!=__continue){return _Pk;}}},_Qf=function(_Qg){var _Qh=E(_Qg);if(!_Qh._){return new T2(0,_10,_10);}else{var _Qi=E(_Qh.a),_Qj=new T(function(){var _Qk=B(_Qf(_Qh.b));return new T2(0,_Qk.a,_Qk.b);});return new T2(0,new T2(1,_Qi.a,new T(function(){return E(E(_Qj).a);})),new T2(1,_Qi.b,new T(function(){return E(E(_Qj).b);})));}},_Ql=32,_Qm=function(_Qn,_Qo,_Qp,_Qq){var _Qr=E(_Qq);if(!_Qr._){return __Z;}else{var _Qs=_Qr.b;if(!B(_4B(_3M,_Qn,_Qp))){var _Qt=new T(function(){return B(_Qm(new T(function(){return E(_Qn)+1|0;}),_Qo,_Qp,_Qs));});return new T2(1,_Qr.a,_Qt);}else{var _Qu=new T(function(){return B(_Qm(new T(function(){return E(_Qn)+1|0;}),_Qo,_Qp,_Qs));});return new T2(1,_Qo,_Qu);}}},_Qv=function(_Qw,_Qx){var _Qy=E(_Qx);if(!_Qy._){return __Z;}else{var _Qz=new T(function(){var _QA=B(_Qf(_Qy.a)),_QB=_QA.a,_QC=new T(function(){return B(_IF(0,_Qw,_QB));});return B(_Gm(B(_Qm(_rj,_Ql,_QC,_QB)),new T(function(){return B(_IM(0,_E6,_QC,_QA.b));},1)));});return new T2(1,_Qz,new T(function(){return B(_Qv(_Qw,_Qy.b));}));}},_QD=function(_QE,_QF){var _QG=E(_QF);return (_QG._==0)?__Z:new T2(1,_QE,new T(function(){return B(_QD(_QG.a,_QG.b));}));},_QH=new T(function(){return B(unCStr("init"));}),_QI=new T(function(){return B(_ne(_QH));}),_QJ=function(_QK,_QL){var _QM=function(_QN){var _QO=E(_QN);if(!_QO._){return __Z;}else{var _QP=new T(function(){return B(_y(new T2(1,_QK,_10),new T(function(){return B(_QM(_QO.b));},1)));},1);return new F(function(){return _y(_QO.a,_QP);});}},_QQ=B(_QM(_QL));if(!_QQ._){return E(_QI);}else{return new F(function(){return _QD(_QQ.a,_QQ.b);});}},_QR=61,_QS=46,_QT=new T(function(){return B(_e7("Event.hs:(93,1)-(99,61)|function makeDecision"));}),_QU=new T(function(){return B(unCStr("sm"));}),_QV=new T(function(){return B(unCStr("rk"));}),_QW=new T(function(){return B(unCStr("if"));}),_QX=new T(function(){return B(unCStr("hm"));}),_QY=new T(function(){return B(unCStr("cleq"));}),_QZ=new T(function(){return B(unCStr("da"));}),_R0=new T(function(){return B(unCStr("ct"));}),_R1=function(_R2,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj){var _Rk=function(_Rl,_Rm){var _Rn=function(_Ro){if(!B(_qL(_Rl,_R0))){if(!B(_qL(_Rl,_QZ))){var _Rp=function(_Rq){if(!B(_qL(_Rl,_QY))){var _Rr=function(_Rs){if(!B(_qL(_Rl,_rM))){if(!B(_qL(_Rl,_QX))){if(!B(_qL(_Rl,_QW))){if(!B(_qL(_Rl,_QV))){if(!B(_qL(_Rl,_QU))){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{var _Rt=E(_Ri);return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E({_:0,a:E(_Rt.a),b:E(_Rt.b),c:E(_Rt.c),d:E(_Rt.d),e:E(_Rt.e),f:E(_Rt.f),g:E(_Rt.g),h:E(_wr)}),q:E(_Rj)};}}else{return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rm),p:E(_Ri),q:E(_Rj)};}}else{var _Ru=E(_Rm);if(!_Ru._){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{var _Rv=_Ru.a,_Rw=E(_Ru.b);if(!_Rw._){return E(_QT);}else{var _Rx=_Rw.a,_Ry=B(_No(_R9)),_Rz=_Ry.a,_RA=_Ry.b,_RB=function(_RC){if(!B(_4B(_qe,_Rv,_Rz))){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{if(!B(_qL(_Rx,B(_6R(_RA,B(_M0(_qe,_Rv,_Rz))))))){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{return new F(function(){return _R1(_RC,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}}},_RD=B(_QJ(_QS,_Rw.b));if(!_RD._){return new F(function(){return _RB(_10);});}else{var _RE=_RD.a,_RF=E(_RD.b);if(!_RF._){return new F(function(){return _RB(new T2(1,_RE,_10));});}else{var _RG=_RF.a,_RH=_RF.b,_RI=E(_RE);if(E(_RI)==47){if(!B(_4B(_qe,_Rv,_Rz))){return new F(function(){return _R1(B(_H2(47,_RG,_RH)).a,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}else{if(!B(_qL(_Rx,B(_6R(_RA,B(_M0(_qe,_Rv,_Rz))))))){return new F(function(){return _R1(B(_H2(47,_RG,_RH)).a,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}else{return new F(function(){return _R1(_10,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}}}else{if(!B(_4B(_qe,_Rv,_Rz))){var _RJ=E(B(_H2(47,_RG,_RH)).b);if(!_RJ._){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{return new F(function(){return _R1(_RJ.a,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}}else{if(!B(_qL(_Rx,B(_6R(_RA,B(_M0(_qe,_Rv,_Rz))))))){var _RK=E(B(_H2(47,_RG,_RH)).b);if(!_RK._){return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}else{return new F(function(){return _R1(_RK.a,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}}else{return new F(function(){return _R1(new T2(1,_RI,new T(function(){return E(B(_H2(47,_RG,_RH)).a);})),_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj);});}}}}}}}}}else{var _RL=E(_Ri);return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E({_:0,a:E(_RL.a),b:E(_RL.b),c:E(_RL.c),d:E(_RL.d),e:E(_RL.e),f:E(_RL.f),g:E(_RL.g),h:E(_wq)}),q:E(_Rj)};}}else{var _RM=E(_Ri);return new F(function(){return _Nx(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_10,_Rg,_Rh,_RM.a,_RM.b,_RM.c,_RM.d,_RM.e,_RM.f,_RM.g,_RM.h,_Rj);});}},_RN=E(_Rl);if(!_RN._){return new F(function(){return _Rr(_);});}else{if(E(_RN.a)==109){if(!E(_RN.b)._){var _RO=B(_Hf(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RO.a),b:E(_RO.b),c:E(_RO.c),d:E(_RO.d),e:E(_RO.e),f:E(_RO.f),g:E(_RO.g),h:E(_RO.h),i:_RO.i,j:_RO.j,k:_RO.k,l:_RO.l,m:E(_RO.m),n:_RO.n,o:E(_RO.o),p:E(_RO.p),q:E(_RO.q)};}else{return new F(function(){return _Rr(_);});}}else{return new F(function(){return _Rr(_);});}}}else{var _RP=E(_R3);return {_:0,a:E({_:0,a:E(_RP.a),b:E(B(_Qv(_QR,_RP.b))),c:_RP.c,d:_RP.d,e:_RP.e,f:E(_RP.f),g:_RP.g,h:E(_RP.h),i:E(_RP.i),j:E(_RP.j)}),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_R7),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}},_RQ=E(_Rl);if(!_RQ._){return new F(function(){return _Rp(_);});}else{var _RR=_RQ.b;switch(E(_RQ.a)){case 99:if(!E(_RR)._){var _RS=B(_KV(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RS.a),b:E(_RS.b),c:E(_RS.c),d:E(_RS.d),e:E(_RS.e),f:E(_RS.f),g:E(_RS.g),h:E(_RS.h),i:_RS.i,j:_RS.j,k:_RS.k,l:_RS.l,m:E(_RS.m),n:_RS.n,o:E(_RS.o),p:E(_RS.p),q:E(_RS.q)};}else{return new F(function(){return _Rp(_);});}break;case 112:if(!E(_RR)._){var _RT=B(_P1(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RT.a),b:E(_RT.b),c:E(_RT.c),d:E(_RT.d),e:E(_RT.e),f:E(_RT.f),g:E(_RT.g),h:E(_RT.h),i:_RT.i,j:_RT.j,k:_RT.k,l:_RT.l,m:E(_RT.m),n:_RT.n,o:E(_RT.o),p:E(_RT.p),q:E(_RT.q)};}else{return new F(function(){return _Rp(_);});}break;default:return new F(function(){return _Rp(_);});}}}else{return {_:0,a:E(_R3),b:E(_R4),c:E(_R5),d:E(_R6),e:E(_10),f:E(_R8),g:E(_R9),h:E(_Ra),i:_Rb,j:_Rc,k:_Rd,l:_Re,m:E(_Rf),n:_Rg,o:E(_Rh),p:E(_Ri),q:E(_Rj)};}}else{var _RU=B(_Ji(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RU.a),b:E(_RU.b),c:E(_RU.c),d:E(_RU.d),e:E(_RU.e),f:E(_RU.f),g:E(_RU.g),h:E(_RU.h),i:_RU.i,j:_RU.j,k:_RU.k,l:_RU.l,m:E(_RU.m),n:_RU.n,o:E(_RU.o),p:E(_RU.p),q:E(_RU.q)};}},_RV=E(_Rl);if(!_RV._){return new F(function(){return _Rn(_);});}else{var _RW=_RV.b;switch(E(_RV.a)){case 100:if(!E(_RW)._){var _RX=B(_Mq(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RX.a),b:E(_RX.b),c:E(_RX.c),d:E(_RX.d),e:E(_RX.e),f:E(_RX.f),g:E(_RX.g),h:E(_RX.h),i:_RX.i,j:_RX.j,k:_RX.k,l:_RX.l,m:E(_RX.m),n:_RX.n,o:E(_RX.o),p:E(_RX.p),q:E(_RX.q)};}else{return new F(function(){return _Rn(_);});}break;case 101:if(!E(_RW)._){var _RY=B(_qh(_Rm,_R3,_R4,_R5,_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj));return {_:0,a:E(_RY.a),b:E(_RY.b),c:E(_RY.c),d:E(_RY.d),e:E(_RY.e),f:E(_RY.f),g:E(_RY.g),h:E(_RY.h),i:_RY.i,j:_RY.j,k:_RY.k,l:_RY.l,m:E(_RY.m),n:_RY.n,o:E(_RY.o),p:E(_RY.p),q:E(_RY.q)};}else{return new F(function(){return _Rn(_);});}break;default:return new F(function(){return _Rn(_);});}}},_RZ=E(_R2);if(!_RZ._){return new F(function(){return _Rk(_10,_10);});}else{var _S0=_RZ.a,_S1=E(_RZ.b);if(!_S1._){return new F(function(){return _Rk(new T2(1,_S0,_10),_10);});}else{var _S2=E(_S0),_S3=new T(function(){var _S4=B(_H2(46,_S1.a,_S1.b));return new T2(0,_S4.a,_S4.b);});if(E(_S2)==46){return new F(function(){return _Rk(_10,new T2(1,new T(function(){return E(E(_S3).a);}),new T(function(){return E(E(_S3).b);})));});}else{return new F(function(){return _Rk(new T2(1,_S2,new T(function(){return E(E(_S3).a);})),new T(function(){return E(E(_S3).b);}));});}}}},_S5=new T(function(){return B(unCStr("last"));}),_S6=new T(function(){return B(_ne(_S5));}),_S7=32,_S8=0,_S9=65306,_Sa=125,_Sb=new T1(0,1),_Sc=function(_Sd,_Se,_Sf,_Sg,_Sh){var _Si=new T(function(){return E(_Sh).i;}),_Sj=new T(function(){return E(E(_Sh).c);}),_Sk=new T(function(){var _Sl=E(_Si)+1|0;if(0>=_Sl){return E(_S7);}else{var _Sm=B(_pO(_Sl,_Sj));if(!_Sm._){return E(_S7);}else{return B(_oa(_Sm.a,_Sm.b,_S6));}}}),_Sn=new T(function(){var _So=E(_Sk);switch(E(_So)){case 125:return E(_S7);break;case 12289:return E(_S7);break;case 12290:return E(_S7);break;default:return E(_So);}}),_Sp=new T(function(){if(E(_Sn)==10){return true;}else{return false;}}),_Sq=new T(function(){if(!E(_Sp)){if(E(_Sn)==12300){return E(_j7);}else{return E(_Sh).j;}}else{return E(_S8);}}),_Sr=new T(function(){var _Ss=E(_Se)/28,_St=_Ss&4294967295;if(_Ss>=_St){return _St-1|0;}else{return (_St-1|0)-1|0;}}),_Su=new T(function(){if(!E(E(_Sg).h)){return E(_j8);}else{return 2+(E(E(E(_Sh).b).b)+3|0)|0;}}),_Sv=new T(function(){if(!E(_Si)){return new T2(0,_Sr,_Su);}else{return E(E(_Sh).h);}}),_Sw=new T(function(){return E(E(_Sv).b);}),_Sx=new T(function(){return E(E(_Sv).a);}),_Sy=new T(function(){if(E(_Sn)==65306){return true;}else{return false;}}),_Sz=new T(function(){if(!E(_Sy)){if(!E(_Sp)){var _SA=E(_Sw);if((_SA+1)*20<=E(_Sf)-10){return new T2(0,_Sx,_SA+1|0);}else{return new T2(0,new T(function(){return E(_Sx)-1|0;}),_Su);}}else{return new T2(0,new T(function(){return E(_Sx)-1|0;}),_Su);}}else{return new T2(0,_Sx,_Sw);}}),_SB=new T(function(){if(E(E(_Sz).a)==1){if(E(_Sx)==1){return false;}else{return true;}}else{return false;}}),_SC=new T(function(){if(!E(_Sy)){return __Z;}else{return B(_q6(_S9,E(_Si),_Sj));}}),_SD=new T(function(){if(E(_Sn)==123){return true;}else{return false;}}),_SE=new T(function(){if(!E(_SD)){return __Z;}else{return B(_q6(_Sa,E(_Si),_Sj));}}),_SF=new T(function(){if(!E(_SD)){var _SG=E(_Sh),_SH=E(_Sg);if(E(_Sk)==12290){var _SI=true;}else{var _SI=false;}return {_:0,a:E(_SG.a),b:E(_SG.b),c:E(_SG.c),d:E(_SG.d),e:E(_SG.e),f:E(_SG.f),g:E(_SG.g),h:E(_SG.h),i:_SG.i,j:_SG.j,k:_SG.k,l:_SG.l,m:E(_SG.m),n:_SG.n,o:E(_SG.o),p:E({_:0,a:E(_SH.a),b:E(_SH.b),c:E(_SH.c),d:E(_SI),e:E(_SH.e),f:E(_SH.f),g:E(_SH.g),h:E(_SH.h)}),q:E(_SG.q)};}else{var _SJ=E(_Sh),_SK=E(_Sg);if(E(_Sk)==12290){var _SL=true;}else{var _SL=false;}return B(_R1(_SE,_SJ.a,_SJ.b,_SJ.c,_SJ.d,_SJ.e,_SJ.f,_SJ.g,_SJ.h,_SJ.i,_SJ.j,_SJ.k,_SJ.l,_SJ.m,_SJ.n,_SJ.o,{_:0,a:E(_SK.a),b:E(_SK.b),c:E(_SK.c),d:E(_SL),e:E(_SK.e),f:E(_SK.f),g:E(_SK.g),h:E(_SK.h)},_SJ.q));}}),_SM=new T(function(){return E(E(_SF).p);}),_SN=new T(function(){if(!E(_Si)){return E(_S8);}else{return E(_SF).k;}}),_SO=new T(function(){var _SP=E(_SF),_SQ=_SP.a,_SR=_SP.b,_SS=_SP.c,_ST=_SP.d,_SU=_SP.e,_SV=_SP.f,_SW=_SP.g,_SX=_SP.l,_SY=_SP.m,_SZ=_SP.n,_T0=_SP.o,_T1=_SP.q;if(!E(_SB)){var _T2=E(_Sz);}else{var _T2=new T2(0,_Sx,_Su);}var _T3=E(_Si),_T4=function(_T5){var _T6=B(_mt(_Sj,0))-1|0,_T7=function(_T8){var _T9=E(_Sq);if(!E(_SB)){var _Ta=E(_SM);return {_:0,a:E(_SQ),b:E(_SR),c:E(_SS),d:E(_ST),e:E(_SU),f:E(_SV),g:E(_SW),h:E(_T2),i:_T8,j:_T9,k:E(_SN),l:_SX,m:E(_SY),n:_SZ,o:E(_T0),p:E({_:0,a:E(_Ta.a),b:E(_Ta.b),c:(_T3+_T5|0)<=_T6,d:E(_Ta.d),e:E(_Ta.e),f:E(_Ta.f),g:E(_Ta.g),h:E(_Ta.h)}),q:E(_T1)};}else{var _Tb=E(_SM);return {_:0,a:E(_SQ),b:E(_SR),c:E(_SS),d:E(_ST),e:E(_SU),f:E(_SV),g:E(_SW),h:E(_T2),i:_T8,j:_T9,k:E(_SN)+1|0,l:_SX,m:E(_SY),n:_SZ,o:E(_T0),p:E({_:0,a:E(_Tb.a),b:E(_Tb.b),c:(_T3+_T5|0)<=_T6,d:E(_Tb.d),e:E(_Tb.e),f:E(_Tb.f),g:E(_Tb.g),h:E(_Tb.h)}),q:E(_T1)};}};if((_T3+_T5|0)<=_T6){return new F(function(){return _T7(_T3+_T5|0);});}else{return new F(function(){return _T7(0);});}};if(!E(_Sy)){if(!E(_SD)){return B(_T4(1));}else{return B(_T4(B(_mt(_SE,0))+2|0));}}else{return B(_T4(B(_mt(_SC,0))+2|0));}}),_Tc=new T(function(){var _Td=B(_o4(B(_o2(_Sd)))),_Te=new T(function(){var _Tf=B(_pv(_Sd,E(_Se)/16)),_Tg=_Tf.a;if(E(_Tf.b)>=0){return E(_Tg);}else{return B(A3(_oH,_Td,_Tg,new T(function(){return B(A2(_he,_Td,_Sb));})));}});return B(A3(_oH,_Td,_Te,new T(function(){return B(A2(_he,_Td,_hn));})));});return {_:0,a:_Sn,b:_Sx,c:_Sw,d:new T(function(){if(E(_Su)!=E(_Sw)){return E(_Sx);}else{return E(_Sx)+1|0;}}),e:new T(function(){var _Th=E(_Sw);if(E(_Su)!=_Th){return _Th-1|0;}else{var _Ti=(E(_Sf)-10)/20,_Tj=_Ti&4294967295;if(_Ti>=_Tj){return _Tj;}else{return _Tj-1|0;}}}),f:_Su,g:_Si,h:_Sj,i:new T(function(){return B(_6R(_j4,E(_Sq)));}),j:_SC,k:_Sr,l:_Tc,m:_SN,n:_j9,o:_Sy,p:_SD,q:_SB,r:_SM,s:_SF,t:_SO};},_Tk=function(_Tl){var _Tm=E(_Tl);if(!_Tm._){return new T2(0,_10,_10);}else{var _Tn=E(_Tm.a),_To=new T(function(){var _Tp=B(_Tk(_Tm.b));return new T2(0,_Tp.a,_Tp.b);});return new T2(0,new T2(1,_Tn.a,new T(function(){return E(E(_To).a);})),new T2(1,_Tn.b,new T(function(){return E(E(_To).b);})));}},_Tq=42,_Tr=32,_Ts=function(_Tt,_Tu,_Tv){var _Tw=E(_Tt);if(!_Tw._){return __Z;}else{var _Tx=_Tw.a,_Ty=_Tw.b;if(_Tu!=_Tv){var _Tz=E(_Tx);return (_Tz._==0)?E(_nh):(E(_Tz.a)==42)?new T2(1,new T2(1,_Tr,_Tz.b),new T(function(){return B(_Ts(_Ty,_Tu,_Tv+1|0));})):new T2(1,new T2(1,_Tr,_Tz),new T(function(){return B(_Ts(_Ty,_Tu,_Tv+1|0));}));}else{var _TA=E(_Tx);return (_TA._==0)?E(_nh):(E(_TA.a)==42)?new T2(1,new T2(1,_Tr,_TA),new T(function(){return B(_Ts(_Ty,_Tu,_Tv+1|0));})):new T2(1,new T2(1,_Tq,_TA),new T(function(){return B(_Ts(_Ty,_Tu,_Tv+1|0));}));}}},_TB=new T(function(){return B(unCStr("\n\n"));}),_TC=function(_TD){var _TE=E(_TD);if(!_TE._){return __Z;}else{var _TF=new T(function(){return B(_y(_TB,new T(function(){return B(_TC(_TE.b));},1)));},1);return new F(function(){return _y(_TE.a,_TF);});}},_TG=function(_TH,_TI,_TJ){var _TK=new T(function(){var _TL=new T(function(){var _TM=E(_TI);if(!_TM._){return B(_TC(_10));}else{var _TN=_TM.a,_TO=_TM.b,_TP=E(_TJ);if(!_TP){var _TQ=E(_TN);if(!_TQ._){return E(_nh);}else{if(E(_TQ.a)==42){return B(_TC(new T2(1,new T2(1,_Tr,_TQ),new T(function(){return B(_Ts(_TO,0,1));}))));}else{return B(_TC(new T2(1,new T2(1,_Tq,_TQ),new T(function(){return B(_Ts(_TO,0,1));}))));}}}else{var _TR=E(_TN);if(!_TR._){return E(_nh);}else{if(E(_TR.a)==42){return B(_TC(new T2(1,new T2(1,_Tr,_TR.b),new T(function(){return B(_Ts(_TO,_TP,1));}))));}else{return B(_TC(new T2(1,new T2(1,_Tr,_TR),new T(function(){return B(_Ts(_TO,_TP,1));}))));}}}}});return B(unAppCStr("\n\n",_TL));},1);return new F(function(){return _y(_TH,_TK);});},_TS=function(_TT){return E(E(_TT).c);},_TU=function(_TV,_TW,_TX,_TY,_TZ,_U0,_U1,_U2,_U3){var _U4=new T(function(){if(!E(_TW)){return E(_TX);}else{return false;}}),_U5=new T(function(){if(!E(_TW)){return false;}else{return E(E(_U2).g);}}),_U6=new T(function(){if(!E(_U5)){if(!E(_U4)){return B(A2(_he,_TV,_hm));}else{return B(A3(_my,_TV,new T(function(){return B(A3(_my,_TV,_U0,_U1));}),new T(function(){return B(A2(_he,_TV,_Sb));})));}}else{return B(A3(_my,_TV,_U0,_U1));}}),_U7=new T(function(){if(!E(_U5)){if(!E(_U4)){return __Z;}else{var _U8=E(_TY)+1|0;if(0>=_U8){return __Z;}else{return B(_pO(_U8,_TZ));}}}else{return B(_TG(B(_TS(_U3)),new T(function(){return E(B(_Tk(E(_U3).m)).a);},1),new T(function(){return E(_U3).n;},1)));}});return new T4(0,_U5,_U4,_U7,_U6);},_U9=function(_Ua,_Ub,_Uc){var _Ud=E(_Ub),_Ue=E(_Uc),_Uf=new T(function(){var _Ug=B(_ha(_Ua)),_Uh=B(_U9(_Ua,_Ue,B(A3(_oH,_Ug,new T(function(){return B(A3(_my,_Ug,_Ue,_Ue));}),_Ud))));return new T2(1,_Uh.a,_Uh.b);});return new T2(0,_Ud,_Uf);},_Ui=1,_Uj=new T(function(){var _Uk=B(_U9(_gb,_hM,_Ui));return new T2(1,_Uk.a,_Uk.b);}),_Ul=function(_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_){var _UY={_:0,a:E(_UP),b:E(_UQ),c:E(_UR),d:E(_US),e:E(_UT),f:E(_UU),g:E(_UV),h:E(_UW)};if(!E(_UR)){return {_:0,a:E({_:0,a:E(_Up),b:E(_Uq),c:_Ur,d:_Us,e:_Ut,f:E(_Uu),g:_Uv,h:E(_Uw),i:E(_Ux),j:E(_Uy)}),b:E(new T2(0,_Uz,_UA)),c:E(_UB),d:E(_UC),e:E(_UD),f:E(_UE),g:E(_UF),h:E(new T2(0,_UG,_UH)),i:_UI,j:_UJ,k:_UK,l:_UL,m:E(_UM),n:_UN,o:E(_UO),p:E(_UY),q:E(_UX)};}else{if(!E(_US)){var _UZ=B(_Sc(_bS,_Un,_Uo,_UY,{_:0,a:E({_:0,a:E(_Up),b:E(_Uq),c:_Ur,d:_Us,e:_Ut,f:E(_Uu),g:_Uv,h:E(_Uw),i:E(_Ux),j:E(_Uy)}),b:E(new T2(0,_Uz,_UA)),c:E(_UB),d:E(_UC),e:E(_UD),f:E(_UE),g:E(_UF),h:E(new T2(0,_UG,_UH)),i:_UI,j:_UJ,k:_UK,l:_UL,m:E(_UM),n:_UN,o:E(_UO),p:E(_UY),q:E(_UX)})),_V0=_UZ.d,_V1=_UZ.e,_V2=_UZ.f,_V3=_UZ.i,_V4=_UZ.n,_V5=_UZ.p,_V6=_UZ.q,_V7=_UZ.s,_V8=_UZ.t;if(!E(_UZ.o)){var _V9=B(_TU(_bn,_V5,_V6,_UZ.g,_UZ.h,_UZ.k,_UZ.m,_UZ.r,_V7)),_Va=function(_){if(!E(_V5)){if(!E(_V6)){var _Vb=B(_iB(E(_Um).a,_V3,_j5,_hM,_UZ.b,_UZ.c,_UZ.a,_));return _V8;}else{return _V8;}}else{return _V8;}},_Vc=function(_Vd){var _Ve=E(_Um),_Vf=_Ve.a,_Vg=_Ve.b,_Vh=B(_nQ(_Vf,_Vg,_UZ.l,_V7,_)),_Vi=B(_lo(_Vf,_Vg,_Uo,0,_V2,_V9.d,_V2,_V9.c,_));return new F(function(){return _Va(_);});};if(!E(_V9.a)){if(!E(_V9.b)){return new F(function(){return _Va(_);});}else{return new F(function(){return _Vc(_);});}}else{return new F(function(){return _Vc(_);});}}else{var _Vj=E(_UZ.j);if(!_Vj._){return _V8;}else{var _Vk=E(_Uj);if(!_Vk._){return _V8;}else{var _Vl=E(_Um).a,_Vm=B(_iB(_Vl,_V3,_V4,_Vk.a,_V0,_V1,_Vj.a,_)),_Vn=function(_Vo,_Vp,_){while(1){var _Vq=E(_Vo);if(!_Vq._){return _gE;}else{var _Vr=E(_Vp);if(!_Vr._){return _gE;}else{var _Vs=B(_iB(_Vl,_V3,_V4,_Vr.a,_V0,_V1,_Vq.a,_));_Vo=_Vq.b;_Vp=_Vr.b;continue;}}}},_Vt=B(_Vn(_Vj.b,_Vk.b,_));return _V8;}}}}else{return {_:0,a:E({_:0,a:E(_Up),b:E(_Uq),c:_Ur,d:_Us,e:_Ut,f:E(_Uu),g:_Uv,h:E(_Uw),i:E(_Ux),j:E(_Uy)}),b:E(new T2(0,_Uz,_UA)),c:E(_UB),d:E(_UC),e:E(_UD),f:E(_UE),g:E(_UF),h:E(new T2(0,_UG,_UH)),i:_UI,j:_UJ,k:_UK,l:_UL,m:E(_UM),n:_UN,o:E(_UO),p:E(_UY),q:E(_UX)};}}},_Vu=function(_Vv,_Vw,_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE,_VF,_VG,_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_){while(1){var _W7=B(_Ul(_Vv,_Vw,_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE,_VF,_VG,_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_)),_W8=E(_W7),_W9=_W8.c,_Wa=_W8.d,_Wb=_W8.e,_Wc=_W8.f,_Wd=_W8.g,_We=_W8.i,_Wf=_W8.j,_Wg=_W8.k,_Wh=_W8.l,_Wi=_W8.m,_Wj=_W8.n,_Wk=_W8.o,_Wl=_W8.q,_Wm=E(_W8.p),_Wn=_Wm.a,_Wo=_Wm.b,_Wp=_Wm.c,_Wq=_Wm.e,_Wr=_Wm.g,_Ws=_Wm.h,_Wt=E(_W8.a),_Wu=E(_W8.b),_Wv=E(_W8.h);if(!E(_Wm.d)){if(!E(_W0)){return {_:0,a:E(_Wt),b:E(_Wu),c:E(_W9),d:E(_Wa),e:E(_Wb),f:E(_Wc),g:E(_Wd),h:E(_Wv),i:_We,j:_Wf,k:_Wg,l:_Wh,m:E(_Wi),n:_Wj,o:E(_Wk),p:E({_:0,a:E(_Wn),b:E(_Wo),c:E(_Wp),d:E(_wq),e:E(_Wq),f:E(_wq),g:E(_Wr),h:E(_Ws)}),q:E(_Wl)};}else{_Vy=_Wt.a;_Vz=_Wt.b;_VA=_Wt.c;_VB=_Wt.d;_VC=_Wt.e;_VD=_Wt.f;_VE=_Wt.g;_VF=_Wt.h;_VG=_Wt.i;_VH=_Wt.j;_VI=_Wu.a;_VJ=_Wu.b;_VK=_W9;_VL=_Wa;_VM=_Wb;_VN=_Wc;_VO=_Wd;_VP=_Wv.a;_VQ=_Wv.b;_VR=_We;_VS=_Wf;_VT=_Wg;_VU=_Wh;_VV=_Wi;_VW=_Wj;_VX=_Wk;_VY=_Wn;_VZ=_Wo;_W0=_Wp;_W1=_wq;_W2=_Wq;_W3=_Wm.f;_W4=_Wr;_W5=_Ws;_W6=_Wl;continue;}}else{return {_:0,a:E(_Wt),b:E(_Wu),c:E(_W9),d:E(_Wa),e:E(_Wb),f:E(_Wc),g:E(_Wd),h:E(_Wv),i:_We,j:_Wf,k:_Wg,l:_Wh,m:E(_Wi),n:_Wj,o:E(_Wk),p:E({_:0,a:E(_Wn),b:E(_Wo),c:E(_Wp),d:E(_wr),e:E(_Wq),f:E(_wq),g:E(_Wr),h:E(_Ws)}),q:E(_Wl)};}}},_Ww=function(_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_X2,_X3,_X4,_X5,_X6,_X7,_){var _X8=B(_Ul(_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1,_wr,_X2,_X3,_X4,_X5,_X6,_X7,_)),_X9=E(_X8),_Xa=_X9.c,_Xb=_X9.d,_Xc=_X9.e,_Xd=_X9.f,_Xe=_X9.g,_Xf=_X9.i,_Xg=_X9.j,_Xh=_X9.k,_Xi=_X9.l,_Xj=_X9.m,_Xk=_X9.n,_Xl=_X9.o,_Xm=_X9.q,_Xn=E(_X9.p),_Xo=_Xn.a,_Xp=_Xn.b,_Xq=_Xn.c,_Xr=_Xn.e,_Xs=_Xn.g,_Xt=_Xn.h,_Xu=E(_X9.a),_Xv=E(_X9.b),_Xw=E(_X9.h);if(!E(_Xn.d)){return new F(function(){return _Vu(_Wx,_Wy,_Wz,_Xu.a,_Xu.b,_Xu.c,_Xu.d,_Xu.e,_Xu.f,_Xu.g,_Xu.h,_Xu.i,_Xu.j,_Xv.a,_Xv.b,_Xa,_Xb,_Xc,_Xd,_Xe,_Xw.a,_Xw.b,_Xf,_Xg,_Xh,_Xi,_Xj,_Xk,_Xl,_Xo,_Xp,_Xq,_wq,_Xr,_Xn.f,_Xs,_Xt,_Xm,_);});}else{return {_:0,a:E(_Xu),b:E(_Xv),c:E(_Xa),d:E(_Xb),e:E(_Xc),f:E(_Xd),g:E(_Xe),h:E(_Xw),i:_Xf,j:_Xg,k:_Xh,l:_Xi,m:E(_Xj),n:_Xk,o:E(_Xl),p:E({_:0,a:E(_Xo),b:E(_Xp),c:E(_Xq),d:E(_wr),e:E(_Xr),f:E(_wq),g:E(_Xs),h:E(_Xt)}),q:E(_Xm)};}},_Xx=function(_Xy){var _Xz=E(_Xy);if(!_Xz._){return __Z;}else{var _XA=E(_Xz.b);return (_XA._==0)?__Z:new T2(1,new T2(0,_Xz.a,_XA.a),new T(function(){return B(_Xx(_XA.b));}));}},_XB=function(_XC,_XD,_XE){return new T2(1,new T2(0,_XC,_XD),new T(function(){return B(_Xx(_XE));}));},_XF=function(_XG,_XH){var _XI=E(_XH);return (_XI._==0)?__Z:new T2(1,new T2(0,_XG,_XI.a),new T(function(){return B(_Xx(_XI.b));}));},_XJ=new T(function(){return B(err(_so));}),_XK=new T(function(){return B(err(_sq));}),_XL=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_XM=function(_XN){var _XO=B(_Ga(B(_sv(_XL,_XN))));return (_XO._==0)?E(_XJ):(E(_XO.b)._==0)?E(_XO.a):E(_XK);},_XP="Invalid JSON!",_XQ=new T1(0,_XP),_XR="No such value",_XS=new T1(0,_XR),_XT=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_XU=function(_XV){return E(E(_XV).c);},_XW=function(_XX,_XY,_){var _XZ=__app1(E(_XT),_XY),_Y0=__eq(_XZ,E(_7));if(!E(_Y0)){var _Y1=__isUndef(_XZ);return (E(_Y1)==0)?new T(function(){var _Y2=String(_XZ),_Y3=jsParseJSON(_Y2);if(!_Y3._){return E(_XQ);}else{return B(A2(_XU,_XX,_Y3.a));}}):_XS;}else{return _XS;}},_Y4=new T1(0,0),_Y5=function(_Y6,_Y7){while(1){var _Y8=E(_Y6);if(!_Y8._){var _Y9=_Y8.a,_Ya=E(_Y7);if(!_Ya._){return new T1(0,(_Y9>>>0|_Ya.a>>>0)>>>0&4294967295);}else{_Y6=new T1(1,I_fromInt(_Y9));_Y7=_Ya;continue;}}else{var _Yb=E(_Y7);if(!_Yb._){_Y6=_Y8;_Y7=new T1(1,I_fromInt(_Yb.a));continue;}else{return new T1(1,I_or(_Y8.a,_Yb.a));}}}},_Yc=function(_Yd){var _Ye=E(_Yd);if(!_Ye._){return E(_Y4);}else{return new F(function(){return _Y5(new T1(0,E(_Ye.a)),B(_cO(B(_Yc(_Ye.b)),31)));});}},_Yf=function(_Yg,_Yh){if(!E(_Yg)){return new F(function(){return _ft(B(_Yc(_Yh)));});}else{return new F(function(){return _Yc(_Yh);});}},_Yi=1420103680,_Yj=465,_Yk=new T2(1,_Yj,_10),_Yl=new T2(1,_Yi,_Yk),_Ym=new T(function(){return B(_Yf(_wr,_Yl));}),_Yn=function(_Yo){return E(_Ym);},_Yp=new T(function(){return B(unCStr("s"));}),_Yq=function(_Yr,_Ys){while(1){var _Yt=E(_Yr);if(!_Yt._){return E(_Ys);}else{_Yr=_Yt.b;_Ys=_Yt.a;continue;}}},_Yu=function(_Yv,_Yw,_Yx){return new F(function(){return _Yq(_Yw,_Yv);});},_Yy=new T1(0,1),_Yz=function(_YA,_YB){var _YC=E(_YA);return new T2(0,_YC,new T(function(){var _YD=B(_Yz(B(_cv(_YC,_YB)),_YB));return new T2(1,_YD.a,_YD.b);}));},_YE=function(_YF){var _YG=B(_Yz(_YF,_Yy));return new T2(1,_YG.a,_YG.b);},_YH=function(_YI,_YJ){var _YK=B(_Yz(_YI,new T(function(){return B(_eO(_YJ,_YI));})));return new T2(1,_YK.a,_YK.b);},_YL=new T1(0,0),_YM=function(_YN,_YO){var _YP=E(_YN);if(!_YP._){var _YQ=_YP.a,_YR=E(_YO);return (_YR._==0)?_YQ>=_YR.a:I_compareInt(_YR.a,_YQ)<=0;}else{var _YS=_YP.a,_YT=E(_YO);return (_YT._==0)?I_compareInt(_YS,_YT.a)>=0:I_compare(_YS,_YT.a)>=0;}},_YU=function(_YV,_YW,_YX){if(!B(_YM(_YW,_YL))){var _YY=function(_YZ){return (!B(_d7(_YZ,_YX)))?new T2(1,_YZ,new T(function(){return B(_YY(B(_cv(_YZ,_YW))));})):__Z;};return new F(function(){return _YY(_YV);});}else{var _Z0=function(_Z1){return (!B(_cY(_Z1,_YX)))?new T2(1,_Z1,new T(function(){return B(_Z0(B(_cv(_Z1,_YW))));})):__Z;};return new F(function(){return _Z0(_YV);});}},_Z2=function(_Z3,_Z4,_Z5){return new F(function(){return _YU(_Z3,B(_eO(_Z4,_Z3)),_Z5);});},_Z6=function(_Z7,_Z8){return new F(function(){return _YU(_Z7,_Yy,_Z8);});},_Z9=function(_Za){return new F(function(){return _ba(_Za);});},_Zb=function(_Zc){return new F(function(){return _eO(_Zc,_Yy);});},_Zd=function(_Ze){return new F(function(){return _cv(_Ze,_Yy);});},_Zf=function(_Zg){return new F(function(){return _aR(E(_Zg));});},_Zh={_:0,a:_Zd,b:_Zb,c:_Zf,d:_Z9,e:_YE,f:_YH,g:_Z6,h:_Z2},_Zi=function(_Zj,_Zk){while(1){var _Zl=E(_Zj);if(!_Zl._){var _Zm=E(_Zl.a);if(_Zm==( -2147483648)){_Zj=new T1(1,I_fromInt( -2147483648));continue;}else{var _Zn=E(_Zk);if(!_Zn._){return new T1(0,B(_9j(_Zm,_Zn.a)));}else{_Zj=new T1(1,I_fromInt(_Zm));_Zk=_Zn;continue;}}}else{var _Zo=_Zl.a,_Zp=E(_Zk);return (_Zp._==0)?new T1(1,I_div(_Zo,I_fromInt(_Zp.a))):new T1(1,I_div(_Zo,_Zp.a));}}},_Zq=function(_Zr,_Zs){if(!B(_cn(_Zs,_oL))){return new F(function(){return _Zi(_Zr,_Zs);});}else{return E(_9U);}},_Zt=function(_Zu,_Zv){while(1){var _Zw=E(_Zu);if(!_Zw._){var _Zx=E(_Zw.a);if(_Zx==( -2147483648)){_Zu=new T1(1,I_fromInt( -2147483648));continue;}else{var _Zy=E(_Zv);if(!_Zy._){var _Zz=_Zy.a;return new T2(0,new T1(0,B(_9j(_Zx,_Zz))),new T1(0,B(_ao(_Zx,_Zz))));}else{_Zu=new T1(1,I_fromInt(_Zx));_Zv=_Zy;continue;}}}else{var _ZA=E(_Zv);if(!_ZA._){_Zu=_Zw;_Zv=new T1(1,I_fromInt(_ZA.a));continue;}else{var _ZB=I_divMod(_Zw.a,_ZA.a);return new T2(0,new T1(1,_ZB.a),new T1(1,_ZB.b));}}}},_ZC=function(_ZD,_ZE){if(!B(_cn(_ZE,_oL))){var _ZF=B(_Zt(_ZD,_ZE));return new T2(0,_ZF.a,_ZF.b);}else{return E(_9U);}},_ZG=function(_ZH,_ZI){while(1){var _ZJ=E(_ZH);if(!_ZJ._){var _ZK=E(_ZJ.a);if(_ZK==( -2147483648)){_ZH=new T1(1,I_fromInt( -2147483648));continue;}else{var _ZL=E(_ZI);if(!_ZL._){return new T1(0,B(_ao(_ZK,_ZL.a)));}else{_ZH=new T1(1,I_fromInt(_ZK));_ZI=_ZL;continue;}}}else{var _ZM=_ZJ.a,_ZN=E(_ZI);return (_ZN._==0)?new T1(1,I_mod(_ZM,I_fromInt(_ZN.a))):new T1(1,I_mod(_ZM,_ZN.a));}}},_ZO=function(_ZP,_ZQ){if(!B(_cn(_ZQ,_oL))){return new F(function(){return _ZG(_ZP,_ZQ);});}else{return E(_9U);}},_ZR=function(_ZS,_ZT){while(1){var _ZU=E(_ZS);if(!_ZU._){var _ZV=E(_ZU.a);if(_ZV==( -2147483648)){_ZS=new T1(1,I_fromInt( -2147483648));continue;}else{var _ZW=E(_ZT);if(!_ZW._){return new T1(0,quot(_ZV,_ZW.a));}else{_ZS=new T1(1,I_fromInt(_ZV));_ZT=_ZW;continue;}}}else{var _ZX=_ZU.a,_ZY=E(_ZT);return (_ZY._==0)?new T1(0,I_toInt(I_quot(_ZX,I_fromInt(_ZY.a)))):new T1(1,I_quot(_ZX,_ZY.a));}}},_ZZ=function(_100,_101){if(!B(_cn(_101,_oL))){return new F(function(){return _ZR(_100,_101);});}else{return E(_9U);}},_102=function(_103,_104){if(!B(_cn(_104,_oL))){var _105=B(_cE(_103,_104));return new T2(0,_105.a,_105.b);}else{return E(_9U);}},_106=function(_107,_108){while(1){var _109=E(_107);if(!_109._){var _10a=E(_109.a);if(_10a==( -2147483648)){_107=new T1(1,I_fromInt( -2147483648));continue;}else{var _10b=E(_108);if(!_10b._){return new T1(0,_10a%_10b.a);}else{_107=new T1(1,I_fromInt(_10a));_108=_10b;continue;}}}else{var _10c=_109.a,_10d=E(_108);return (_10d._==0)?new T1(1,I_rem(_10c,I_fromInt(_10d.a))):new T1(1,I_rem(_10c,_10d.a));}}},_10e=function(_10f,_10g){if(!B(_cn(_10g,_oL))){return new F(function(){return _106(_10f,_10g);});}else{return E(_9U);}},_10h=function(_10i){return E(_10i);},_10j=function(_10k){return E(_10k);},_10l=function(_10m){var _10n=E(_10m);if(!_10n._){var _10o=E(_10n.a);return (_10o==( -2147483648))?E(_fs):(_10o<0)?new T1(0, -_10o):E(_10n);}else{var _10p=_10n.a;return (I_compareInt(_10p,0)>=0)?E(_10n):new T1(1,I_negate(_10p));}},_10q=new T1(0, -1),_10r=function(_10s){var _10t=E(_10s);if(!_10t._){var _10u=_10t.a;return (_10u>=0)?(E(_10u)==0)?E(_Y4):E(_d6):E(_10q);}else{var _10v=I_compareInt(_10t.a,0);return (_10v<=0)?(E(_10v)==0)?E(_Y4):E(_10q):E(_d6);}},_10w={_:0,a:_cv,b:_eO,c:_of,d:_ft,e:_10l,f:_10r,g:_10j},_10x=function(_10y,_10z){var _10A=E(_10y);if(!_10A._){var _10B=_10A.a,_10C=E(_10z);return (_10C._==0)?_10B!=_10C.a:(I_compareInt(_10C.a,_10B)==0)?false:true;}else{var _10D=_10A.a,_10E=E(_10z);return (_10E._==0)?(I_compareInt(_10D,_10E.a)==0)?false:true:(I_compare(_10D,_10E.a)==0)?false:true;}},_10F=new T2(0,_cn,_10x),_10G=function(_10H,_10I){return (!B(_ez(_10H,_10I)))?E(_10H):E(_10I);},_10J=function(_10K,_10L){return (!B(_ez(_10K,_10L)))?E(_10L):E(_10K);},_10M={_:0,a:_10F,b:_c7,c:_d7,d:_ez,e:_cY,f:_YM,g:_10G,h:_10J},_10N=function(_10O){return new T2(0,E(_10O),E(_aV));},_10P=new T3(0,_10w,_10M,_10N),_10Q={_:0,a:_10P,b:_Zh,c:_ZZ,d:_10e,e:_Zq,f:_ZO,g:_102,h:_ZC,i:_10h},_10R=new T1(0,0),_10S=function(_10T,_10U,_10V){var _10W=B(A1(_10T,_10U));if(!B(_cn(_10W,_10R))){return new F(function(){return _Zi(B(_of(_10U,_10V)),_10W);});}else{return E(_9U);}},_10X=function(_10Y,_10Z){while(1){if(!B(_cn(_10Z,_oL))){var _110=_10Z,_111=B(_10e(_10Y,_10Z));_10Y=_110;_10Z=_111;continue;}else{return E(_10Y);}}},_112=5,_113=new T(function(){return B(_9Q(_112));}),_114=new T(function(){return die(_113);}),_115=function(_116,_117){if(!B(_cn(_117,_oL))){var _118=B(_10X(B(_10l(_116)),B(_10l(_117))));return (!B(_cn(_118,_oL)))?new T2(0,B(_ZR(_116,_118)),B(_ZR(_117,_118))):E(_9U);}else{return E(_114);}},_119=function(_11a,_11b,_11c,_11d){var _11e=B(_of(_11b,_11c));return new F(function(){return _115(B(_of(B(_of(_11a,_11d)),B(_10r(_11e)))),B(_10l(_11e)));});},_11f=function(_11g,_11h,_11i){var _11j=new T(function(){if(!B(_cn(_11i,_oL))){var _11k=B(_cE(_11h,_11i));return new T2(0,_11k.a,_11k.b);}else{return E(_9U);}}),_11l=new T(function(){return B(A2(_he,B(_o4(B(_o2(_11g)))),new T(function(){return E(E(_11j).a);})));});return new T2(0,_11l,new T(function(){return new T2(0,E(E(_11j).b),E(_11i));}));},_11m=function(_11n,_11o,_11p){var _11q=B(_11f(_11n,_11o,_11p)),_11r=_11q.a,_11s=E(_11q.b);if(!B(_d7(B(_of(_11s.a,_aV)),B(_of(_oL,_11s.b))))){return E(_11r);}else{var _11t=B(_o4(B(_o2(_11n))));return new F(function(){return A3(_oH,_11t,_11r,new T(function(){return B(A2(_he,_11t,_aV));}));});}},_11u=479723520,_11v=40233135,_11w=new T2(1,_11v,_10),_11x=new T2(1,_11u,_11w),_11y=new T(function(){return B(_Yf(_wr,_11x));}),_11z=new T1(0,40587),_11A=function(_11B){var _11C=new T(function(){var _11D=B(_119(_11B,_aV,_Ym,_aV)),_11E=B(_119(_11y,_aV,_Ym,_aV)),_11F=B(_119(_11D.a,_11D.b,_11E.a,_11E.b));return B(_11m(_10Q,_11F.a,_11F.b));});return new T2(0,new T(function(){return B(_cv(_11z,_11C));}),new T(function(){return B(_eO(_11B,B(_10S(_Yn,B(_of(_11C,_Ym)),_11y))));}));},_11G=function(_11H,_){var _11I=__get(_11H,0),_11J=__get(_11H,1),_11K=Number(_11I),_11L=jsTrunc(_11K),_11M=Number(_11J),_11N=jsTrunc(_11M);return new T2(0,_11L,_11N);},_11O=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_11P=660865024,_11Q=465661287,_11R=new T2(1,_11Q,_10),_11S=new T2(1,_11P,_11R),_11T=new T(function(){return B(_Yf(_wr,_11S));}),_11U=function(_){var _11V=__app0(E(_11O)),_11W=B(_11G(_11V,_));return new T(function(){var _11X=E(_11W);if(!B(_cn(_11T,_10R))){return B(_cv(B(_of(B(_aR(E(_11X.a))),_Ym)),B(_Zi(B(_of(B(_of(B(_aR(E(_11X.b))),_Ym)),_Ym)),_11T))));}else{return E(_9U);}});},_11Y=new T(function(){return B(err(_sq));}),_11Z=new T(function(){return B(err(_so));}),_120=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_121=new T1(0,1),_122=new T1(0,10),_123=function(_124){while(1){var _125=E(_124);if(!_125._){_124=new T1(1,I_fromInt(_125.a));continue;}else{return new F(function(){return I_toString(_125.a);});}}},_126=function(_127,_128){return new F(function(){return _y(fromJSStr(B(_123(_127))),_128);});},_129=new T1(0,0),_12a=function(_12b,_12c,_12d){if(_12b<=6){return new F(function(){return _126(_12c,_12d);});}else{if(!B(_d7(_12c,_129))){return new F(function(){return _126(_12c,_12d);});}else{return new T2(1,_H,new T(function(){return B(_y(fromJSStr(B(_123(_12c))),new T2(1,_G,_12d)));}));}}},_12e=function(_12f){return new F(function(){return _12a(0,_12f,_10);});},_12g=new T(function(){return B(_cn(_122,_10R));}),_12h=function(_12i){while(1){if(!B(_cn(_12i,_10R))){if(!E(_12g)){if(!B(_cn(B(_ZG(_12i,_122)),_10R))){return new F(function(){return _12e(_12i);});}else{var _12j=B(_Zi(_12i,_122));_12i=_12j;continue;}}else{return E(_9U);}}else{return __Z;}}},_12k=46,_12l=48,_12m=function(_12n,_12o,_12p){if(!B(_d7(_12p,_10R))){var _12q=B(A1(_12n,_12p));if(!B(_cn(_12q,_10R))){var _12r=B(_Zt(_12p,_12q)),_12s=_12r.b,_12t=new T(function(){var _12u=Math.log(B(_fM(_12q)))/Math.log(10),_12v=_12u&4294967295,_12w=function(_12x){if(_12x>=0){var _12y=E(_12x);if(!_12y){var _12z=B(_Zi(B(_eO(B(_cv(B(_of(_12s,_aV)),_12q)),_121)),_12q));}else{var _12z=B(_Zi(B(_eO(B(_cv(B(_of(_12s,B(_ov(_122,_12y)))),_12q)),_121)),_12q));}var _12A=function(_12B){var _12C=B(_12a(0,_12z,_10)),_12D=_12x-B(_mt(_12C,0))|0;if(0>=_12D){if(!E(_12o)){return E(_12C);}else{return new F(function(){return _12h(_12z);});}}else{var _12E=new T(function(){if(!E(_12o)){return E(_12C);}else{return B(_12h(_12z));}}),_12F=function(_12G){var _12H=E(_12G);return (_12H==1)?E(new T2(1,_12l,_12E)):new T2(1,_12l,new T(function(){return B(_12F(_12H-1|0));}));};return new F(function(){return _12F(_12D);});}};if(!E(_12o)){var _12I=B(_12A(_));return (_12I._==0)?__Z:new T2(1,_12k,_12I);}else{if(!B(_cn(_12z,_10R))){var _12J=B(_12A(_));return (_12J._==0)?__Z:new T2(1,_12k,_12J);}else{return __Z;}}}else{return E(_pr);}};if(_12v>=_12u){return B(_12w(_12v));}else{return B(_12w(_12v+1|0));}},1);return new F(function(){return _y(B(_12a(0,_12r.a,_10)),_12t);});}else{return E(_9U);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_12m(_12n,_12o,B(_ft(_12p))));}));});}},_12K=function(_12L,_12M,_){var _12N=B(_11U(_)),_12O=new T(function(){var _12P=new T(function(){var _12Q=new T(function(){var _12R=B(_y(B(_12m(_Yn,_wr,B(_11A(_12N)).b)),_Yp));if(!_12R._){return E(_QI);}else{var _12S=B(_QD(_12R.a,_12R.b));if(!_12S._){return B(_Yu(_10,_10,_S6));}else{var _12T=_12S.a,_12U=E(_12S.b);if(!_12U._){return B(_Yu(new T2(1,_12T,_10),_10,_S6));}else{var _12V=E(_12T),_12W=new T(function(){var _12X=B(_H2(46,_12U.a,_12U.b));return new T2(0,_12X.a,_12X.b);});if(E(_12V)==46){return B(_Yu(_10,new T2(1,new T(function(){return E(E(_12W).a);}),new T(function(){return E(E(_12W).b);})),_S6));}else{return B(_Yu(new T2(1,_12V,new T(function(){return E(E(_12W).a);})),new T(function(){return E(E(_12W).b);}),_S6));}}}}}),_12Y=B(_Ga(B(_sv(_120,_12Q))));if(!_12Y._){return E(_11Z);}else{if(!E(_12Y.b)._){return B(_pO(3,B(_I(0,E(_12Y.a)+(imul(E(_12M),E(_12L)-1|0)|0)|0,_10))));}else{return E(_11Y);}}}),_12Z=B(_Ga(B(_sv(_120,_12P))));if(!_12Z._){return E(_11Z);}else{if(!E(_12Z.b)._){return E(_12Z.a);}else{return E(_11Y);}}});return new T2(0,new T(function(){return B(_av(_12O,_12L));}),_12O);},_130=function(_131,_132){while(1){var _133=E(_132);if(!_133._){return __Z;}else{var _134=_133.b,_135=E(_131);if(_135==1){return E(_134);}else{_131=_135-1|0;_132=_134;continue;}}}},_136=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_137=new T(function(){return B(err(_136));}),_138=0,_139=function(_13a,_13b,_13c){return new F(function(){return _I(E(_13a),E(_13b),_13c);});},_13d=function(_13e,_13f){return new F(function(){return _I(0,E(_13e),_13f);});},_13g=function(_13h,_13i){return new F(function(){return _2D(_13d,_13h,_13i);});},_13j=new T3(0,_139,_6B,_13g),_13k=0,_13l=new T(function(){return B(unCStr(" out of range "));}),_13m=new T(function(){return B(unCStr("}.index: Index "));}),_13n=new T(function(){return B(unCStr("Ix{"));}),_13o=new T2(1,_G,_10),_13p=new T2(1,_G,_13o),_13q=0,_13r=function(_13s){return E(E(_13s).a);},_13t=function(_13u,_13v,_13w,_13x,_13y){var _13z=new T(function(){var _13A=new T(function(){var _13B=new T(function(){var _13C=new T(function(){var _13D=new T(function(){return B(A3(_sa,_6x,new T2(1,new T(function(){return B(A3(_13r,_13w,_13q,_13x));}),new T2(1,new T(function(){return B(A3(_13r,_13w,_13q,_13y));}),_10)),_13p));});return B(_y(_13l,new T2(1,_H,new T2(1,_H,_13D))));});return B(A(_13r,[_13w,_13k,_13v,new T2(1,_G,_13C)]));});return B(_y(_13m,new T2(1,_H,_13B)));},1);return B(_y(_13u,_13A));},1);return new F(function(){return err(B(_y(_13n,_13z)));});},_13E=function(_13F,_13G,_13H,_13I,_13J){return new F(function(){return _13t(_13F,_13G,_13J,_13H,_13I);});},_13K=function(_13L,_13M,_13N,_13O){var _13P=E(_13N);return new F(function(){return _13E(_13L,_13M,_13P.a,_13P.b,_13O);});},_13Q=function(_13R,_13S,_13T,_13U){return new F(function(){return _13K(_13U,_13T,_13S,_13R);});},_13V=new T(function(){return B(unCStr("Int"));}),_13W=function(_13X,_13Y,_13Z){return new F(function(){return _13Q(_13j,new T2(0,_13Y,_13Z),_13X,_13V);});},_140=new T(function(){return B(unCStr("Negative range size"));}),_141=new T(function(){return B(err(_140));}),_142=function(_143){var _144=B(A1(_143,_));return E(_144);},_145=function(_146,_147,_148,_){var _149=E(_146);if(!_149){return new T2(0,_10,_147);}else{var _14a=new T(function(){return B(_mt(_148,0))-1|0;}),_14b=B(_12K(new T(function(){return E(_14a)+1|0;}),_147,_)),_14c=E(_14b),_14d=_14c.a,_14e=_14c.b,_14f=new T(function(){var _14g=E(_14d);if(B(_mt(_148,0))>=(_14g+1|0)){var _14h=new T(function(){var _14i=_14g+1|0;if(_14i>0){return B(_130(_14i,_148));}else{return E(_148);}});if(0>=_14g){return E(_14h);}else{var _14j=function(_14k,_14l){var _14m=E(_14k);if(!_14m._){return E(_14h);}else{var _14n=_14m.a,_14o=E(_14l);return (_14o==1)?new T2(1,_14n,_14h):new T2(1,_14n,new T(function(){return B(_14j(_14m.b,_14o-1|0));}));}};return B(_14j(_148,_14g));}}else{return E(_148);}}),_14p=B(_145(_149-1|0,_14e,_14f,_)),_14q=new T(function(){var _14r=function(_){var _14s=E(_14a),_14t=function(_14u){if(_14u>=0){var _14v=newArr(_14u,_137),_14w=_14v,_14x=E(_14u);if(!_14x){return new T4(0,E(_138),E(_14s),0,_14w);}else{var _14y=function(_14z,_14A,_){while(1){var _14B=E(_14z);if(!_14B._){return E(_);}else{var _=_14w[_14A]=_14B.a;if(_14A!=(_14x-1|0)){var _14C=_14A+1|0;_14z=_14B.b;_14A=_14C;continue;}else{return E(_);}}}},_=B(_14y(_148,0,_));return new T4(0,E(_138),E(_14s),_14x,_14w);}}else{return E(_141);}};if(0>_14s){return new F(function(){return _14t(0);});}else{return new F(function(){return _14t(_14s+1|0);});}},_14D=B(_142(_14r)),_14E=E(_14D.a),_14F=E(_14D.b),_14G=E(_14d);if(_14E>_14G){return B(_13W(_14G,_14E,_14F));}else{if(_14G>_14F){return B(_13W(_14G,_14E,_14F));}else{return E(_14D.d[_14G-_14E|0]);}}});return new T2(0,new T2(1,_14q,new T(function(){return B(_sg(_14p));})),_14e);}},_14H=function(_14I,_14J){while(1){var _14K=E(_14I);if(!_14K._){return E(_14J);}else{_14I=_14K.b;_14J=_14K.a;continue;}}},_14L=function(_14M,_14N,_14O){return new F(function(){return _14H(_14N,_14M);});},_14P=function(_14Q,_14R){while(1){var _14S=E(_14Q);if(!_14S._){return E(_14R);}else{_14Q=_14S.b;_14R=_14S.a;continue;}}},_14T=function(_14U,_14V,_14W){return new F(function(){return _14P(_14V,_14U);});},_14X=function(_14Y,_14Z){while(1){var _150=E(_14Z);if(!_150._){return __Z;}else{var _151=_150.b,_152=E(_14Y);if(_152==1){return E(_151);}else{_14Y=_152-1|0;_14Z=_151;continue;}}}},_153=function(_154,_155){var _156=new T(function(){var _157=_154+1|0;if(_157>0){return B(_14X(_157,_155));}else{return E(_155);}});if(0>=_154){return E(_156);}else{var _158=function(_159,_15a){var _15b=E(_159);if(!_15b._){return E(_156);}else{var _15c=_15b.a,_15d=E(_15a);return (_15d==1)?new T2(1,_15c,_156):new T2(1,_15c,new T(function(){return B(_158(_15b.b,_15d-1|0));}));}};return new F(function(){return _158(_155,_154);});}},_15e=new T(function(){return B(unCStr(":"));}),_15f=function(_15g){var _15h=E(_15g);if(!_15h._){return __Z;}else{var _15i=new T(function(){return B(_y(_15e,new T(function(){return B(_15f(_15h.b));},1)));},1);return new F(function(){return _y(_15h.a,_15i);});}},_15j=function(_15k,_15l){var _15m=new T(function(){return B(_y(_15e,new T(function(){return B(_15f(_15l));},1)));},1);return new F(function(){return _y(_15k,_15m);});},_15n=function(_15o){return new F(function(){return _KQ("Check.hs:173:7-35|(co : na : xs)");});},_15p=new T(function(){return B(_15n(_));}),_15q=new T(function(){return B(err(_so));}),_15r=new T(function(){return B(err(_sq));}),_15s=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_15t=0,_15u=new T(function(){return B(unCStr("!"));}),_15v=function(_15w,_15x){var _15y=E(_15x);if(!_15y._){return E(_15p);}else{var _15z=E(_15y.b);if(!_15z._){return E(_15p);}else{var _15A=E(_15y.a),_15B=new T(function(){var _15C=B(_H2(58,_15z.a,_15z.b));return new T2(0,_15C.a,_15C.b);}),_15D=function(_15E,_15F,_15G){var _15H=function(_15I){if((_15w+1|0)!=_15I){return new T3(0,_15w+1|0,_15F,_15y);}else{var _15J=E(_15G);return (_15J._==0)?new T3(0,_15t,_15F,_10):new T3(0,_15t,_15F,new T(function(){var _15K=B(_15j(_15J.a,_15J.b));if(!_15K._){return E(_QI);}else{return B(_QD(_15K.a,_15K.b));}}));}};if(!B(_qL(_15E,_15u))){var _15L=B(_Ga(B(_sv(_15s,_15E))));if(!_15L._){return E(_15q);}else{if(!E(_15L.b)._){return new F(function(){return _15H(E(_15L.a));});}else{return E(_15r);}}}else{return new F(function(){return _15H( -1);});}};if(E(_15A)==58){return new F(function(){return _15D(_10,new T(function(){return E(E(_15B).a);}),new T(function(){return E(E(_15B).b);}));});}else{var _15M=E(_15B),_15N=E(_15M.b);if(!_15N._){return E(_15p);}else{return new F(function(){return _15D(new T2(1,_15A,_15M.a),_15N.a,_15N.b);});}}}}},_15O=function(_15P,_15Q){while(1){var _15R=E(_15Q);if(!_15R._){return __Z;}else{var _15S=_15R.b,_15T=E(_15P);if(_15T==1){return E(_15S);}else{_15P=_15T-1|0;_15Q=_15S;continue;}}}},_15U=function(_15V,_15W,_15X){var _15Y=new T2(1,_15W,new T(function(){var _15Z=_15V+1|0;if(_15Z>0){return B(_15O(_15Z,_15X));}else{return E(_15X);}}));if(0>=_15V){return E(_15Y);}else{var _160=function(_161,_162){var _163=E(_161);if(!_163._){return E(_15Y);}else{var _164=_163.a,_165=E(_162);return (_165==1)?new T2(1,_164,_15Y):new T2(1,_164,new T(function(){return B(_160(_163.b,_165-1|0));}));}};return new F(function(){return _160(_15X,_15V);});}},_166=new T2(0,_Ql,_E6),_167=function(_168,_169,_16a){while(1){var _16b=E(_16a);if(!_16b._){return E(_166);}else{var _16c=_16b.b,_16d=E(_16b.a),_16e=E(_16d.a);if(_168!=E(_16e.a)){_16a=_16c;continue;}else{if(_169!=E(_16e.b)){_16a=_16c;continue;}else{return E(_16d.b);}}}}},_16f=function(_16g,_16h){while(1){var _16i=E(_16h);if(!_16i._){return __Z;}else{var _16j=_16i.b,_16k=E(_16g);if(_16k==1){return E(_16j);}else{_16g=_16k-1|0;_16h=_16j;continue;}}}},_16l=function(_16m,_16n,_16o){var _16p=E(_16m);if(_16p==1){return E(_16o);}else{return new F(function(){return _16f(_16p-1|0,_16o);});}},_16q=function(_16r,_16s,_16t){return new T2(1,new T(function(){if(0>=_16r){return __Z;}else{return B(_pO(_16r,new T2(1,_16s,_16t)));}}),new T(function(){if(_16r>0){return B(_16u(_16r,B(_16l(_16r,_16s,_16t))));}else{return B(_16q(_16r,_16s,_16t));}}));},_16u=function(_16v,_16w){var _16x=E(_16w);if(!_16x._){return __Z;}else{var _16y=_16x.a,_16z=_16x.b;return new T2(1,new T(function(){if(0>=_16v){return __Z;}else{return B(_pO(_16v,_16x));}}),new T(function(){if(_16v>0){return B(_16u(_16v,B(_16l(_16v,_16y,_16z))));}else{return B(_16q(_16v,_16y,_16z));}}));}},_16A=function(_16B,_16C,_16D){var _16E=_16C-1|0;if(0<=_16E){var _16F=E(_16B),_16G=function(_16H){var _16I=new T(function(){if(_16H!=_16E){return B(_16G(_16H+1|0));}else{return __Z;}}),_16J=function(_16K){var _16L=E(_16K);return (_16L._==0)?E(_16I):new T2(1,new T(function(){var _16M=E(_16D);if(!_16M._){return E(_166);}else{var _16N=_16M.b,_16O=E(_16M.a),_16P=E(_16O.a),_16Q=E(_16L.a);if(_16Q!=E(_16P.a)){return B(_167(_16Q,_16H,_16N));}else{if(_16H!=E(_16P.b)){return B(_167(_16Q,_16H,_16N));}else{return E(_16O.b);}}}}),new T(function(){return B(_16J(_16L.b));}));};return new F(function(){return _16J(B(_8s(0,_16F-1|0)));});};return new F(function(){return _16u(_16F,B(_16G(0)));});}else{return __Z;}},_16R=function(_16S){return new F(function(){return _KQ("Check.hs:72:21-47|(l : r : _)");});},_16T=new T(function(){return B(_16R(_));}),_16U=61,_16V=function(_16W,_16X){while(1){var _16Y=E(_16W);if(!_16Y._){return E(_16X);}else{_16W=_16Y.b;_16X=_16Y.a;continue;}}},_16Z=function(_170,_171,_172){return new F(function(){return _16V(_171,_170);});},_173=function(_174,_175){var _176=E(_175);if(!_176._){return new T2(0,_10,_10);}else{var _177=_176.a;if(!B(A1(_174,_177))){var _178=new T(function(){var _179=B(_173(_174,_176.b));return new T2(0,_179.a,_179.b);});return new T2(0,new T2(1,_177,new T(function(){return E(E(_178).a);})),new T(function(){return E(E(_178).b);}));}else{return new T2(0,_10,_176);}}},_17a=function(_17b,_17c){while(1){var _17d=E(_17c);if(!_17d._){return __Z;}else{if(!B(A1(_17b,_17d.a))){return E(_17d);}else{_17c=_17d.b;continue;}}}},_17e=function(_17f){var _17g=_17f>>>0;if(_17g>887){var _17h=u_iswspace(_17f);return (E(_17h)==0)?false:true;}else{var _17i=E(_17g);return (_17i==32)?true:(_17i-9>>>0>4)?(E(_17i)==160)?true:false:true;}},_17j=function(_17k){return new F(function(){return _17e(E(_17k));});},_17l=function(_17m){var _17n=B(_17a(_17j,_17m));if(!_17n._){return __Z;}else{var _17o=new T(function(){var _17p=B(_173(_17j,_17n));return new T2(0,_17p.a,_17p.b);});return new T2(1,new T(function(){return E(E(_17o).a);}),new T(function(){return B(_17l(E(_17o).b));}));}},_17q=function(_17r){if(!B(_4B(_h7,_16U,_17r))){return new T2(0,_17r,_10);}else{var _17s=new T(function(){var _17t=E(_17r);if(!_17t._){return E(_16T);}else{var _17u=E(_17t.b);if(!_17u._){return E(_16T);}else{var _17v=_17u.a,_17w=_17u.b,_17x=E(_17t.a);if(E(_17x)==61){return new T2(0,_10,new T(function(){return E(B(_H2(61,_17v,_17w)).a);}));}else{var _17y=B(_H2(61,_17v,_17w)),_17z=E(_17y.b);if(!_17z._){return E(_16T);}else{return new T2(0,new T2(1,_17x,_17y.a),_17z.a);}}}}});return new T2(0,new T(function(){var _17A=B(_17l(E(_17s).a));if(!_17A._){return __Z;}else{return B(_16Z(_17A.a,_17A.b,_S6));}}),new T(function(){var _17B=B(_17l(E(_17s).b));if(!_17B._){return __Z;}else{return E(_17B.a);}}));}},_17C=function(_17D,_17E){return new F(function(){return _153(E(_17D),_17E);});},_17F=function(_17G){var _17H=E(_17G);if(!_17H._){return new T2(0,_10,_10);}else{var _17I=E(_17H.a),_17J=new T(function(){var _17K=B(_17F(_17H.b));return new T2(0,_17K.a,_17K.b);});return new T2(0,new T2(1,_17I.a,new T(function(){return E(E(_17J).a);})),new T2(1,_17I.b,new T(function(){return E(E(_17J).b);})));}},_17L=new T(function(){return B(unCStr("\u306d\u3048 \u8d77\u304d\u3066\u3088\u30fb\u30fb\u30fb\u3002 {ch.\u8d77\u304d\u308b,s0.\u8d77\u304d\u306a\u3044,initMsg}"));}),_17M=new T(function(){return B(unCStr("nubatama"));}),_17N=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_17O=new T2(0,_17M,_17N),_17P=new T(function(){return B(unCStr("s1"));}),_17Q=new T(function(){return B(unCStr("\n\u3082\u306e\u3092 \u304b\u305e\u3078\u308b\u306e\u304c \u6578\uff1a\u304b\u305a\uff1a\u3067\u3059\u3002\n\u3082\u3057 \u79c1\u305f\u3061\u304c \u3053\u306e\u4e16\u754c\u3092 \u5206\uff1a\u308f\uff1a\u3051\u3066\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u306a\u3044\u306a\u3089 \u6578\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3084\u3046\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u5206\u3051\u3089\u308c\u3066\u3090\u308b\u304b\u3089 \u6578\u3078\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059 {da}{e.b0.m0:s100}"));}),_17R=new T2(0,_17P,_17Q),_17S=new T(function(){return B(unCStr("s100"));}),_17T=new T(function(){return B(unCStr("\n\u3053\u308c\u306f \u5206\u3051\u3089\u308c\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_0.\u3044\u3044\u3048,s1_1}"));}),_17U=new T2(0,_17S,_17T),_17V=new T(function(){return B(unCStr("s1_0"));}),_17W=new T(function(){return B(unCStr("\n\u3067\u306f \u5206\u3051\u3066\u304f\u3060\u3055\u3044 {ct.0.Fr}{d.b0}{e.e0.m0:s101}"));}),_17X=new T2(0,_17V,_17W),_17Y=new T(function(){return B(unCStr("s4"));}),_17Z=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_180=new T2(0,_17Y,_17Z),_181=new T2(1,_180,_10),_182=new T(function(){return B(unCStr("s3"));}),_183=new T(function(){return B(unCStr("\n\u3053\u306e\u4e16\u754c\u306b\u907a\uff1a\u306e\u3053\uff1a\u3055\u308c\u305f\u8a00\uff1a\u3053\u3068\uff1a\u8449\uff1a\u3070\uff1a \u305d\u308c\u304c \u53f2\uff1a\u3075\u307f\uff1a \u3067\u3059\u3002\n\u79c1\u305f\u3061\u306f \u305d\u308c\u306b\u3088\u3063\u3066 \u4eba\uff1a\u3058\u3093\uff1a\u751f\uff1a\u305b\u3044\uff1a\u306e\u9577\u3055\u3092\u306f\u308b\u304b\u306b\u8d8a\uff1a\u3053\uff1a\u3048\u305f \u8a18\uff1a\u304d\uff1a\u61b6\uff1a\u304a\u304f\uff1a\u3092\u8fbf\uff1a\u305f\u3069\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_184=new T2(0,_182,_183),_185=new T2(1,_184,_181),_186=new T(function(){return B(unCStr("s2"));}),_187=new T(function(){return B(unCStr("\n\u3082\u306e\u3054\u3068\u306e\u7b4b\uff1a\u3059\u3058\uff1a\u9053\uff1a\u307f\u3061\uff1a\u304c \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u3067\u3059\u3002\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306e\u3053\u3068 \u5618\uff1a\u3046\u305d\uff1a\u306e\u3053\u3068\u3002\n\u6b63\uff1a\u305f\u3060\uff1a\u3057\u3044\u3053\u3068 \u9593\uff1a\u307e\uff1a\u9055\uff1a\u3061\u304c\uff1a\u3063\u3066\u3090\u308b\u3053\u3068\u3002\n\u305d\u308c\u3092 \u306f\u3063\u304d\u308a\u3055\u305b\u308b\u306e\u304c \u7406 \u3067\u3059"));}),_188=new T2(0,_186,_187),_189=new T2(1,_188,_185),_18a=new T(function(){return B(unCStr("s1c"));}),_18b=new T(function(){return B(unCStr("\n\u6249\u304c\u958b\u304b\u308c\u305f\u3084\u3046\u3067\u3059 {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"));}),_18c=new T2(0,_18a,_18b),_18d=new T2(1,_18c,_189),_18e=new T(function(){return B(unCStr("s104"));}),_18f=new T(function(){return B(unCStr("\n\u706b\uff1a\u3072\uff1a(\uff11)\u3068\u6c34\uff1a\u307f\u3065\uff1a(\uff12)\u3092\u5408\u306f\u305b\u308b\u3068 \u3072\u307f\u3064(\uff13) \u306b\u306a\u308a\u307e\u3059\u3002\n\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u306f \u307e\u3046\u958b\uff1a\u3072\u3089\uff1a\u304b\u308c\u308b\u3067\u305b\u3046\u3002\n\u9375\uff1a\u304b\u304e\uff1a\u3092\u624b\u306b\u5165\u308c\u305f\u306e\u3067\u3059\u304b\u3089 {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"));}),_18g=new T2(0,_18e,_18f),_18h=new T2(1,_18g,_18d),_18i=new T(function(){return B(unCStr("s103"));}),_18j=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u304c\u5b58\u5728\u3059\u308b\u9650\uff1a\u304b\u304e\uff1a\u308a \u6578\u306f\u7121\uff1a\u3080\uff1a\u9650\uff1a\u3052\u3093\uff1a\u306b\u3064\u304f\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3053\u308c\u3089\u304c\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u306b\u7f6e\uff1a\u304a\uff1a\u304b\u308c\u3066\u3090\u305f\u4f4d\uff1a\u3044\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u5165\uff1a\u3044\uff1a\u308c\u66ff\uff1a\u304b\uff1a\u3078\u305f\u3089 \u4f55\uff1a\u306a\u306b\uff1a\u304b\u8d77\uff1a\u304a\uff1a\u3053\u308a\u3055\u3046\u3067\u3059 {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"));}),_18k=new T2(0,_18i,_18j),_18l=new T2(1,_18k,_18h),_18m=new T(function(){return B(unCStr("s102"));}),_18n=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u3068\u3044\u3075\u5b58\u5728\u3068 \uff1c\u7121\u3044\uff1e\u3068\u3044\u3075\u5b58\u5728\u304c\u3067\u304d\u307e\u3057\u305f\u3002\n\uff1c\u5b58\u5728\uff1e\u3092 1 \u3068\u3059\u308b\u306a\u3089 \u3053\u308c\u3089\u3092\u5408\u306f\u305b\u305f\u540d\u524d\u3092\u3064\u304f\u308a\u307e\u305b\u3046 {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"));}),_18o=new T2(0,_18m,_18n),_18p=new T2(1,_18o,_18l),_18q=new T(function(){return B(unCStr("s1_3"));}),_18r=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u5206\u3051\u305f\u3068\u601d\uff1a\u304a\u3082\uff1a\u306f\u306a\u3044\u306e\u3067\u3042\u308c\u3070\u3002\n\u305d\u308c\u306f \u5206\u304b\u308c\u3066\u3090\u307e\u305b\u3093"));}),_18s=new T2(0,_18q,_18r),_18t=new T2(1,_18s,_18p),_18u=new T(function(){return B(unCStr("s1_2"));}),_18v=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u4e16\u754c\u3092 \u5206\u3051\u3066\n\u300c\u5728\uff1a\u3042\uff1a\u308b\u3002\n\u300c\u7121\uff1a\u306a\uff1a\u3044\u3002\n\u3092\u3064\u304f\u308a\u307e\u3057\u305f\u3002\n\u305d\u308c\u3067\u306f \u3053\u306e \uff1c\u5728\u308b\uff1e\u3092 1 \u3068\u547c\uff1a\u3088\uff1a\u3073\u307e\u305b\u3046 {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"));}),_18w=new T2(0,_18u,_18v),_18x=new T2(1,_18w,_18t),_18y=new T(function(){return B(unCStr("s101"));}),_18z=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u3053\u308c\u3092\u53d6\uff1a\u3068\uff1a\u3063\u305f\u306e\u3067 \u305d\u308c\u306f \u307e\u3046\u3053\u3053\u306b\u3042\u308a\u307e\u305b\u3093\u3002\n\u3053\u308c\u306f \u5206\u3051\u305f\u3053\u3068\u306b\u306a\u308a\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_2.\u3044\u3044\u3048,s1_3}"));}),_18A=new T2(0,_18y,_18z),_18B=new T2(1,_18A,_18x),_18C=new T(function(){return B(unCStr("s1_1"));}),_18D=new T(function(){return B(unCStr("\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306b\u5206\u3051\u3089\u308c\u306a\u3044\u306e\u3067\u305b\u3046\u304b"));}),_18E=new T2(0,_18C,_18D),_18F=new T2(1,_18E,_18B),_18G=new T2(1,_17X,_18F),_18H=new T2(1,_17U,_18G),_18I=new T2(1,_17R,_18H),_18J=new T2(1,_17O,_18I),_18K=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_18L=new T(function(){return B(unCStr("msgW"));}),_18M=new T2(0,_18L,_18K),_18N=new T2(1,_18M,_18J),_18O=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_18P=new T(function(){return B(unCStr("msgR"));}),_18Q=new T2(0,_18P,_18O),_18R=new T2(1,_18Q,_18N),_18S=new T(function(){return B(unCStr("sc0"));}),_18T=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002"));}),_18U=new T2(0,_18S,_18T),_18V=new T2(1,_18U,_18R),_18W=new T(function(){return B(unCStr("s0"));}),_18X=new T(function(){return B(unCStr("\n{sm}\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066 {rk.1.z.abc.sc0}"));}),_18Y=new T2(0,_18W,_18X),_18Z=new T2(1,_18Y,_18V),_190=new T(function(){return B(unCStr("initMsg"));}),_191=function(_192,_193){var _194=new T(function(){var _195=B(_17F(_192));return new T2(0,_195.a,_195.b);}),_196=function(_197){var _198=E(_197);if(!_198._){return E(_194);}else{var _199=E(_198.a),_19a=new T(function(){return B(_196(_198.b));});return new T2(0,new T2(1,_199.a,new T(function(){return E(E(_19a).a);})),new T2(1,_199.b,new T(function(){return E(E(_19a).b);})));}},_19b=function(_19c,_19d,_19e){var _19f=new T(function(){return B(_196(_19e));});return new T2(0,new T2(1,_19c,new T(function(){return E(E(_19f).a);})),new T2(1,_19d,new T(function(){return E(E(_19f).b);})));},_19g=B(_19b(_190,_17L,_18Z)),_19h=_19g.a;if(!B(_4B(_qe,_193,_19h))){return __Z;}else{return new F(function(){return _6R(_19g.b,B(_M0(_qe,_193,_19h)));});}},_19i=7,_19j=new T2(0,_19i,_19i),_19k=new T2(1,_19j,_10),_19l=5,_19m=new T2(0,_19l,_19i),_19n=new T2(1,_19m,_19k),_19o=new T2(0,_19l,_19l),_19p=new T2(1,_19o,_19n),_19q=new T2(1,_19o,_19p),_19r=new T2(1,_19o,_19q),_19s=2,_19t=4,_19u=new T2(0,_19t,_19s),_19v=new T2(1,_19u,_10),_19w=new T2(0,_19s,_19s),_19x=new T2(1,_19w,_19v),_19y=new T2(1,_19w,_19x),_19z=new T2(1,_19w,_19y),_19A=new T2(1,_19w,_19z),_19B=new T(function(){return B(unCStr("Int"));}),_19C=function(_19D,_19E,_19F){return new F(function(){return _13Q(_13j,new T2(0,_19E,_19F),_19D,_19B);});},_19G=new T(function(){return B(unCStr("msgR"));}),_19H=new T(function(){return B(_191(_10,_19G));}),_19I=new T(function(){return B(unCStr("msgW"));}),_19J=new T(function(){return B(_191(_10,_19I));}),_19K=function(_19L){var _19M=E(_19L);return 0;},_19N=new T(function(){return B(unCStr("@@@@@"));}),_19O=new T(function(){var _19P=E(_19N);if(!_19P._){return E(_nh);}else{return E(_19P.a);}}),_19Q=122,_19R=new T2(0,_19Q,_Ec),_19S=0,_19T=new T2(0,_19S,_19S),_19U=new T2(0,_19T,_19R),_19V=61,_19W=new T2(0,_19V,_Ec),_19X=1,_19Y=new T2(0,_19X,_19S),_19Z=new T2(0,_19Y,_19W),_1a0=99,_1a1=new T2(0,_1a0,_E6),_1a2=new T2(0,_19t,_19t),_1a3=new T2(0,_1a2,_1a1),_1a4=new T2(1,_1a3,_10),_1a5=98,_1a6=new T2(0,_1a5,_E6),_1a7=new T2(0,_19s,_19t),_1a8=new T2(0,_1a7,_1a6),_1a9=new T2(1,_1a8,_1a4),_1aa=97,_1ab=new T2(0,_1aa,_E6),_1ac=new T2(0,_19S,_19t),_1ad=new T2(0,_1ac,_1ab),_1ae=new T2(1,_1ad,_1a9),_1af=new T2(1,_19Z,_1ae),_1ag=new T2(1,_19U,_1af),_1ah=new T(function(){return B(_16A(_19l,5,_1ag));}),_1ai=new T(function(){return B(_KQ("Check.hs:142:22-33|(ch : po)"));}),_1aj=new T(function(){return B(_e7("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1ak=48,_1al=new T2(0,_1ak,_Ec),_1am=new T2(0,_19s,_19S),_1an=new T2(0,_1am,_1al),_1ao=new T2(1,_1an,_10),_1ap=6,_1aq=new T2(0,_19S,_1ap),_1ar=new T2(0,_1aq,_1ab),_1as=new T2(0,_19s,_1ap),_1at=new T2(0,_1as,_1a6),_1au=new T2(0,_19t,_1ap),_1av=new T2(0,_1au,_1a1),_1aw=new T2(1,_1av,_10),_1ax=new T2(1,_1at,_1aw),_1ay=new T2(1,_1ar,_1ax),_1az=new T2(1,_19Z,_1ay),_1aA=new T2(1,_19U,_1az),_1aB=new T2(1,_10,_10),_1aC=new T2(1,_1aA,_1aB),_1aD=new T2(1,_10,_1aC),_1aE=new T2(1,_1ao,_1aD),_1aF=new T2(1,_1ag,_1aE),_1aG=function(_1aH){var _1aI=E(_1aH);if(!_1aI._){return __Z;}else{var _1aJ=_1aI.b,_1aK=E(_1aI.a),_1aL=_1aK.b,_1aM=E(_1aK.a),_1aN=function(_1aO){if(E(_1aM)==32){return new T2(1,_1aK,new T(function(){return B(_1aG(_1aJ));}));}else{switch(E(_1aL)){case 0:return new T2(1,new T2(0,_1aM,_E6),new T(function(){return B(_1aG(_1aJ));}));case 1:return new T2(1,new T2(0,_1aM,_EH),new T(function(){return B(_1aG(_1aJ));}));case 2:return new T2(1,new T2(0,_1aM,_Ei),new T(function(){return B(_1aG(_1aJ));}));case 3:return new T2(1,new T2(0,_1aM,_Eo),new T(function(){return B(_1aG(_1aJ));}));case 4:return new T2(1,new T2(0,_1aM,_Eu),new T(function(){return B(_1aG(_1aJ));}));case 5:return new T2(1,new T2(0,_1aM,_EV),new T(function(){return B(_1aG(_1aJ));}));case 6:return new T2(1,new T2(0,_1aM,_EO),new T(function(){return B(_1aG(_1aJ));}));case 7:return new T2(1,new T2(0,_1aM,_EH),new T(function(){return B(_1aG(_1aJ));}));default:return new T2(1,new T2(0,_1aM,_EA),new T(function(){return B(_1aG(_1aJ));}));}}};if(E(_1aM)==32){return new F(function(){return _1aN(_);});}else{switch(E(_1aL)){case 0:return new T2(1,new T2(0,_1aM,_EA),new T(function(){return B(_1aG(_1aJ));}));case 1:return new F(function(){return _1aN(_);});break;case 2:return new F(function(){return _1aN(_);});break;case 3:return new F(function(){return _1aN(_);});break;case 4:return new F(function(){return _1aN(_);});break;case 5:return new F(function(){return _1aN(_);});break;case 6:return new F(function(){return _1aN(_);});break;case 7:return new F(function(){return _1aN(_);});break;default:return new F(function(){return _1aN(_);});}}}},_1aP=function(_1aQ){var _1aR=E(_1aQ);return (_1aR._==0)?__Z:new T2(1,new T(function(){return B(_1aG(_1aR.a));}),new T(function(){return B(_1aP(_1aR.b));}));},_1aS=function(_1aT){var _1aU=E(_1aT);if(!_1aU._){return __Z;}else{var _1aV=_1aU.b,_1aW=E(_1aU.a),_1aX=_1aW.b,_1aY=E(_1aW.a),_1aZ=function(_1b0){if(E(_1aY)==32){return new T2(1,_1aW,new T(function(){return B(_1aS(_1aV));}));}else{switch(E(_1aX)){case 0:return new T2(1,new T2(0,_1aY,_E6),new T(function(){return B(_1aS(_1aV));}));case 1:return new T2(1,new T2(0,_1aY,_Ec),new T(function(){return B(_1aS(_1aV));}));case 2:return new T2(1,new T2(0,_1aY,_Ei),new T(function(){return B(_1aS(_1aV));}));case 3:return new T2(1,new T2(0,_1aY,_Eo),new T(function(){return B(_1aS(_1aV));}));case 4:return new T2(1,new T2(0,_1aY,_Eu),new T(function(){return B(_1aS(_1aV));}));case 5:return new T2(1,new T2(0,_1aY,_EV),new T(function(){return B(_1aS(_1aV));}));case 6:return new T2(1,new T2(0,_1aY,_EO),new T(function(){return B(_1aS(_1aV));}));case 7:return new T2(1,new T2(0,_1aY,_Ec),new T(function(){return B(_1aS(_1aV));}));default:return new T2(1,new T2(0,_1aY,_EA),new T(function(){return B(_1aS(_1aV));}));}}};if(E(_1aY)==32){return new F(function(){return _1aZ(_);});}else{if(E(_1aX)==8){return new T2(1,new T2(0,_1aY,_E6),new T(function(){return B(_1aS(_1aV));}));}else{return new F(function(){return _1aZ(_);});}}}},_1b1=function(_1b2){var _1b3=E(_1b2);return (_1b3._==0)?__Z:new T2(1,new T(function(){return B(_1aS(_1b3.a));}),new T(function(){return B(_1b1(_1b3.b));}));},_1b4=function(_1b5,_1b6,_1b7,_1b8,_1b9,_1ba,_1bb,_1bc,_1bd,_1be,_1bf,_1bg,_1bh,_1bi,_1bj,_1bk,_1bl,_1bm,_1bn,_1bo,_1bp,_1bq,_1br,_1bs,_1bt,_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA,_1bB,_1bC,_1bD){var _1bE=E(_1b6);if(!_1bE._){return E(_1aj);}else{var _1bF=_1bE.b,_1bG=E(_1bE.a),_1bH=new T(function(){var _1bI=function(_){var _1bJ=B(_mt(_1bl,0))-1|0,_1bK=function(_1bL){if(_1bL>=0){var _1bM=newArr(_1bL,_137),_1bN=_1bM,_1bO=E(_1bL);if(!_1bO){return new T4(0,E(_15t),E(_1bJ),0,_1bN);}else{var _1bP=function(_1bQ,_1bR,_){while(1){var _1bS=E(_1bQ);if(!_1bS._){return E(_);}else{var _=_1bN[_1bR]=_1bS.a;if(_1bR!=(_1bO-1|0)){var _1bT=_1bR+1|0;_1bQ=_1bS.b;_1bR=_1bT;continue;}else{return E(_);}}}},_=B(_1bP(_1bl,0,_));return new T4(0,E(_15t),E(_1bJ),_1bO,_1bN);}}else{return E(_141);}};if(0>_1bJ){return new F(function(){return _1bK(0);});}else{return new F(function(){return _1bK(_1bJ+1|0);});}},_1bU=B(_142(_1bI)),_1bV=E(_1bU.a),_1bW=E(_1bU.b),_1bX=E(_1b5);if(_1bV>_1bX){return B(_19C(_1bX,_1bV,_1bW));}else{if(_1bX>_1bW){return B(_19C(_1bX,_1bV,_1bW));}else{return E(_1bU.d[_1bX-_1bV|0]);}}});switch(E(_1bG)){case 97:var _1bY=new T(function(){var _1bZ=E(_1bF);if(!_1bZ._){return E(_1ai);}else{return new T2(0,_1bZ.a,_1bZ.b);}}),_1c0=new T(function(){var _1c1=B(_17q(E(_1bY).b));return new T2(0,_1c1.a,_1c1.b);}),_1c2=B(_Ga(B(_sv(_15s,new T(function(){return E(E(_1c0).b);})))));if(!_1c2._){return E(_15q);}else{if(!E(_1c2.b)._){var _1c3=new T(function(){var _1c4=B(_Ga(B(_sv(_15s,new T(function(){return E(E(_1c0).a);})))));if(!_1c4._){return E(_15q);}else{if(!E(_1c4.b)._){return E(_1c4.a);}else{return E(_15r);}}},1);return {_:0,a:E({_:0,a:E(_1b7),b:E(B(_Kp(_1c3,E(_1c2.a),new T(function(){return E(E(_1bY).a);}),_E6,_1b8))),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};}else{return E(_15r);}}break;case 104:return {_:0,a:E({_:0,a:E(_1b7),b:E(B(_1aP(_1b8))),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};case 106:var _1c5=E(_1bF);if(!_1c5._){return {_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l: -1,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};}else{if(E(_1c5.a)==108){var _1c6=E(_1b5),_1c7=B(_Ga(B(_sv(_15s,_1c5.b))));return (_1c7._==0)?E(_15q):(E(_1c7.b)._==0)?{_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(B(_153(_1c6,_1bk))),f:E(B(_153(_1c6,_1bl))),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:E(_1c7.a),m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_wr),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)}:E(_15r);}else{var _1c8=B(_Ga(B(_sv(_15s,_1c5))));return (_1c8._==0)?E(_15q):(E(_1c8.b)._==0)?{_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:E(_1c8.a),m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)}:E(_15r);}}break;case 108:var _1c9=E(_1b5);return {_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(B(_153(_1c9,_1bk))),f:E(B(_153(_1c9,_1bl))),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_wr),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};case 109:var _1ca=B(_15v(E(_1bH),_1bF)),_1cb=_1ca.c,_1cc=B(_qL(_1cb,_10));if(!E(_1cc)){var _1cd=E(_1b5),_1ce=new T(function(){var _1cf=function(_){var _1cg=B(_mt(_1bk,0))-1|0,_1ch=function(_1ci){if(_1ci>=0){var _1cj=newArr(_1ci,_137),_1ck=_1cj,_1cl=E(_1ci);if(!_1cl){return new T4(0,E(_15t),E(_1cg),0,_1ck);}else{var _1cm=function(_1cn,_1co,_){while(1){var _1cp=E(_1cn);if(!_1cp._){return E(_);}else{var _=_1ck[_1co]=_1cp.a;if(_1co!=(_1cl-1|0)){var _1cq=_1co+1|0;_1cn=_1cp.b;_1co=_1cq;continue;}else{return E(_);}}}},_=B(_1cm(_1bk,0,_));return new T4(0,E(_15t),E(_1cg),_1cl,_1ck);}}else{return E(_141);}};if(0>_1cg){return new F(function(){return _1ch(0);});}else{return new F(function(){return _1ch(_1cg+1|0);});}},_1cr=B(_142(_1cf)),_1cs=E(_1cr.a),_1ct=E(_1cr.b);if(_1cs>_1cd){return B(_19C(_1cd,_1cs,_1ct));}else{if(_1cd>_1ct){return B(_19C(_1cd,_1cs,_1ct));}else{return E(E(_1cr.d[_1cd-_1cs|0]).a);}}}),_1cu=B(_15U(_1cd,new T2(0,_1ce,new T2(1,_1bG,_1cb)),_1bk));}else{var _1cu=B(_17C(_1b5,_1bk));}if(!E(_1cc)){var _1cv=B(_15U(E(_1b5),_1ca.a,_1bl));}else{var _1cv=B(_17C(_1b5,_1bl));}return {_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(B(_191(_1bj,_1ca.b))),d:E(_1bj),e:E(_1cu),f:E(_1cv),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_wr),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};case 114:var _1cw=B(_6R(_19r,_1bb));return {_:0,a:E({_:0,a:E(B(_6R(_19A,_1bb))),b:E(B(_16A(_1cw.a,E(_1cw.b),new T(function(){return B(_6R(_1aF,_1bb));})))),c:B(_6R(_19N,_1bb)),d:32,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1cw),c:E(_19H),d:E(_1bj),e:E(_1bk),f:E(B(_6e(_19K,_1bl))),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_wr),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};case 115:return {_:0,a:E({_:0,a:E(_1b7),b:E(B(_1b1(_1b8))),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};case 116:var _1cx=E(_1bH),_1cy=B(_15v(_1cx,_1bF)),_1cz=E(_1cy.a);if(!E(_1cz)){var _1cA=true;}else{var _1cA=false;}if(!E(_1cA)){var _1cB=B(_15U(E(_1b5),_1cz,_1bl));}else{var _1cB=B(_15U(E(_1b5),_1cx+1|0,_1bl));}if(!E(_1cA)){var _1cC=__Z;}else{var _1cC=E(_1cy.b);}if(!B(_qL(_1cC,_10))){var _1cD=B(_1b4(_1b5,_1cC,_1b7,_1b8,_1b9,_1ba,_1bb,_1bc,_1bd,_1be,_1bf,_1bg,_1bh,_1bi,_1bj,_1bk,_1cB,_1bm,_1bn,_1bo,_1bp,_1bq,_1br,_1bs,_1bt,_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA,_1bB,_1bC,_1bD)),_1cE=E(_1cD.a);return {_:0,a:E({_:0,a:E(_1cE.a),b:E(_1cE.b),c:_1cE.c,d:_1cE.d,e:_1cE.e,f:E(_1cE.f),g:_1cE.g,h:E(B(_y(_1be,_1bE))),i:E(_1cE.i),j:E(_1cE.j)}),b:E(_1cD.b),c:E(_1cD.c),d:E(_1cD.d),e:E(_1cD.e),f:E(_1cD.f),g:E(_1cD.g),h:E(_1cD.h),i:_1cD.i,j:_1cD.j,k:_1cD.k,l:_1cD.l,m:E(_1cD.m),n:_1cD.n,o:E(_1cD.o),p:E(_1cD.p),q:E(_1cD.q)};}else{return {_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1cB),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};}break;case 119:return {_:0,a:E({_:0,a:E(_19w),b:E(_1ah),c:E(_19O),d:32,e:0,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_19o),c:E(_19J),d:E(_1bj),e:E(_1bk),f:E(B(_6e(_19K,_1bl))),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_wr),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};default:return {_:0,a:E({_:0,a:E(_1b7),b:E(_1b8),c:_1b9,d:_1ba,e:_1bb,f:E(_1bc),g:_1bd,h:E(B(_y(_1be,_1bE))),i:E(_1bf),j:E(_1bg)}),b:E(_1bh),c:E(_1bi),d:E(_1bj),e:E(_1bk),f:E(_1bl),g:E(_1bm),h:E(_1bn),i:_1bo,j:_1bp,k:_1bq,l:_1br,m:E(_1bs),n:_1bt,o:E(_1bu),p:E({_:0,a:E(_1bv),b:E(_1bw),c:E(_1bx),d:E(_1by),e:E(_1bz),f:E(_1bA),g:E(_1bB),h:E(_1bC)}),q:E(_1bD)};}}},_1cF=function(_1cG,_1cH){while(1){var _1cI=E(_1cH);if(!_1cI._){return __Z;}else{var _1cJ=_1cI.b,_1cK=E(_1cG);if(_1cK==1){return E(_1cJ);}else{_1cG=_1cK-1|0;_1cH=_1cJ;continue;}}}},_1cL=new T(function(){return B(unCStr("X"));}),_1cM=new T(function(){return B(_e7("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1cN=38,_1cO=function(_1cP,_1cQ,_1cR,_1cS,_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2,_1d3,_1d4,_1d5,_1d6,_1d7,_1d8){var _1d9=E(_1cR);if(!_1d9._){return {_:0,a:_1cS,b:_1cT,c:_1cU,d:_1cV,e:_1cW,f:_1cX,g:_1cY,h:_1cZ,i:_1d0,j:_1d1,k:_1d2,l:_1d3,m:_1d4,n:_1d5,o:_1d6,p:_1d7,q:_1d8};}else{var _1da=_1d9.b,_1db=E(_1d9.a),_1dc=_1db.a,_1dd=_1db.b,_1de=function(_1df,_1dg,_1dh){var _1di=function(_1dj,_1dk){if(!B(_qL(_1dj,_10))){var _1dl=E(_1cS),_1dm=E(_1d7),_1dn=B(_1b4(_1dk,_1dj,_1dl.a,_1dl.b,_1dl.c,_1dl.d,_1dl.e,_1dl.f,_1dl.g,_1dl.h,_1dl.i,_1dl.j,_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2,_1d3,_1d4,_1d5,_1d6,_1dm.a,_1dm.b,_1dm.c,_1dm.d,_1dm.e,_1dm.f,_1dm.g,_1dm.h,_1d8)),_1do=_1dn.a,_1dp=_1dn.b,_1dq=_1dn.c,_1dr=_1dn.d,_1ds=_1dn.e,_1dt=_1dn.f,_1du=_1dn.g,_1dv=_1dn.h,_1dw=_1dn.i,_1dx=_1dn.j,_1dy=_1dn.k,_1dz=_1dn.l,_1dA=_1dn.m,_1dB=_1dn.n,_1dC=_1dn.o,_1dD=_1dn.p,_1dE=_1dn.q;if(B(_mt(_1dt,0))!=B(_mt(_1cX,0))){return {_:0,a:_1do,b:_1dp,c:_1dq,d:_1dr,e:_1ds,f:_1dt,g:_1du,h:_1dv,i:_1dw,j:_1dx,k:_1dy,l:_1dz,m:_1dA,n:_1dB,o:_1dC,p:_1dD,q:_1dE};}else{return new F(function(){return _1cO(new T(function(){return E(_1cP)+1|0;}),_1cQ,_1da,_1do,_1dp,_1dq,_1dr,_1ds,_1dt,_1du,_1dv,_1dw,_1dx,_1dy,_1dz,_1dA,_1dB,_1dC,_1dD,_1dE);});}}else{return new F(function(){return _1cO(new T(function(){return E(_1cP)+1|0;}),_1cQ,_1da,_1cS,_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2,_1d3,_1d4,_1d5,_1d6,_1d7,_1d8);});}},_1dF=B(_mt(_1cQ,0))-B(_mt(new T2(1,_1df,_1dg),0))|0;if(_1dF>0){var _1dG=B(_1cF(_1dF,_1cQ));}else{var _1dG=E(_1cQ);}if(E(B(_14L(_1df,_1dg,_S6)))==63){var _1dH=B(_QD(_1df,_1dg));}else{var _1dH=new T2(1,_1df,_1dg);}var _1dI=function(_1dJ){if(!B(_4B(_h7,_1cN,_1dc))){return new T2(0,_1dd,_1cP);}else{var _1dK=function(_1dL){while(1){var _1dM=B((function(_1dN){var _1dO=E(_1dN);if(!_1dO._){return true;}else{var _1dP=_1dO.b,_1dQ=E(_1dO.a);if(!_1dQ._){return E(_1cM);}else{switch(E(_1dQ.a)){case 99:var _1dR=E(_1cS);if(!E(_1dR.j)){return false;}else{var _1dS=function(_1dT){while(1){var _1dU=E(_1dT);if(!_1dU._){return true;}else{var _1dV=_1dU.b,_1dW=E(_1dU.a);if(!_1dW._){return E(_1cM);}else{if(E(_1dW.a)==115){var _1dX=B(_Ga(B(_sv(_15s,_1dW.b))));if(!_1dX._){return E(_15q);}else{if(!E(_1dX.b)._){if(_1dR.e!=E(_1dX.a)){return false;}else{_1dT=_1dV;continue;}}else{return E(_15r);}}}else{_1dT=_1dV;continue;}}}}};return new F(function(){return _1dS(_1dP);});}break;case 115:var _1dY=E(_1cS),_1dZ=_1dY.e,_1e0=B(_Ga(B(_sv(_15s,_1dQ.b))));if(!_1e0._){return E(_15q);}else{if(!E(_1e0.b)._){if(_1dZ!=E(_1e0.a)){return false;}else{var _1e1=function(_1e2){while(1){var _1e3=E(_1e2);if(!_1e3._){return true;}else{var _1e4=_1e3.b,_1e5=E(_1e3.a);if(!_1e5._){return E(_1cM);}else{switch(E(_1e5.a)){case 99:if(!E(_1dY.j)){return false;}else{_1e2=_1e4;continue;}break;case 115:var _1e6=B(_Ga(B(_sv(_15s,_1e5.b))));if(!_1e6._){return E(_15q);}else{if(!E(_1e6.b)._){if(_1dZ!=E(_1e6.a)){return false;}else{_1e2=_1e4;continue;}}else{return E(_15r);}}break;default:_1e2=_1e4;continue;}}}}};return new F(function(){return _1e1(_1dP);});}}else{return E(_15r);}}break;default:_1dL=_1dP;return __continue;}}}})(_1dL));if(_1dM!=__continue){return _1dM;}}};return (!B(_1dK(_1dh)))?(!B(_qL(_1dH,_1cL)))?new T2(0,_10,_1cP):new T2(0,_1dd,_1cP):new T2(0,_1dd,_1cP);}};if(E(B(_14T(_1df,_1dg,_S6)))==63){if(!B(_69(_1dG,_10))){var _1e7=E(_1dG);if(!_1e7._){return E(_QI);}else{if(!B(_qL(_1dH,B(_QD(_1e7.a,_1e7.b))))){if(!B(_qL(_1dH,_1cL))){return new F(function(){return _1di(_10,_1cP);});}else{return new F(function(){return _1di(_1dd,_1cP);});}}else{var _1e8=B(_1dI(_));return new F(function(){return _1di(_1e8.a,_1e8.b);});}}}else{if(!B(_qL(_1dH,_1dG))){if(!B(_qL(_1dH,_1cL))){return new F(function(){return _1di(_10,_1cP);});}else{return new F(function(){return _1di(_1dd,_1cP);});}}else{var _1e9=B(_1dI(_));return new F(function(){return _1di(_1e9.a,_1e9.b);});}}}else{if(!B(_qL(_1dH,_1dG))){if(!B(_qL(_1dH,_1cL))){return new F(function(){return _1di(_10,_1cP);});}else{return new F(function(){return _1di(_1dd,_1cP);});}}else{var _1ea=B(_1dI(_));return new F(function(){return _1di(_1ea.a,_1ea.b);});}}},_1eb=E(_1dc);if(!_1eb._){return E(_S6);}else{var _1ec=_1eb.a,_1ed=E(_1eb.b);if(!_1ed._){return new F(function(){return _1de(_1ec,_10,_10);});}else{var _1ee=E(_1ec),_1ef=new T(function(){var _1eg=B(_H2(38,_1ed.a,_1ed.b));return new T2(0,_1eg.a,_1eg.b);});if(E(_1ee)==38){return E(_S6);}else{return new F(function(){return _1de(_1ee,new T(function(){return E(E(_1ef).a);}),new T(function(){return E(E(_1ef).b);}));});}}}}},_1eh="]",_1ei="}",_1ej=":",_1ek=",",_1el=new T(function(){return eval("JSON.stringify");}),_1em="false",_1en="null",_1eo="[",_1ep="{",_1eq="\"",_1er="true",_1es=function(_1et,_1eu){var _1ev=E(_1eu);switch(_1ev._){case 0:return new T2(0,new T(function(){return jsShow(_1ev.a);}),_1et);case 1:return new T2(0,new T(function(){var _1ew=__app1(E(_1el),_1ev.a);return String(_1ew);}),_1et);case 2:return (!E(_1ev.a))?new T2(0,_1em,_1et):new T2(0,_1er,_1et);case 3:var _1ex=E(_1ev.a);if(!_1ex._){return new T2(0,_1eo,new T2(1,_1eh,_1et));}else{var _1ey=new T(function(){var _1ez=new T(function(){var _1eA=function(_1eB){var _1eC=E(_1eB);if(!_1eC._){return E(new T2(1,_1eh,_1et));}else{var _1eD=new T(function(){var _1eE=B(_1es(new T(function(){return B(_1eA(_1eC.b));}),_1eC.a));return new T2(1,_1eE.a,_1eE.b);});return new T2(1,_1ek,_1eD);}};return B(_1eA(_1ex.b));}),_1eF=B(_1es(_1ez,_1ex.a));return new T2(1,_1eF.a,_1eF.b);});return new T2(0,_1eo,_1ey);}break;case 4:var _1eG=E(_1ev.a);if(!_1eG._){return new T2(0,_1ep,new T2(1,_1ei,_1et));}else{var _1eH=E(_1eG.a),_1eI=new T(function(){var _1eJ=new T(function(){var _1eK=function(_1eL){var _1eM=E(_1eL);if(!_1eM._){return E(new T2(1,_1ei,_1et));}else{var _1eN=E(_1eM.a),_1eO=new T(function(){var _1eP=B(_1es(new T(function(){return B(_1eK(_1eM.b));}),_1eN.b));return new T2(1,_1eP.a,_1eP.b);});return new T2(1,_1ek,new T2(1,_1eq,new T2(1,_1eN.a,new T2(1,_1eq,new T2(1,_1ej,_1eO)))));}};return B(_1eK(_1eG.b));}),_1eQ=B(_1es(_1eJ,_1eH.b));return new T2(1,_1eQ.a,_1eQ.b);});return new T2(0,_1ep,new T2(1,new T(function(){var _1eR=__app1(E(_1el),E(_1eH.a));return String(_1eR);}),new T2(1,_1ej,_1eI)));}break;default:return new T2(0,_1en,_1et);}},_1eS=new T(function(){return toJSStr(_10);}),_1eT=function(_1eU){var _1eV=B(_1es(_10,_1eU)),_1eW=jsCat(new T2(1,_1eV.a,_1eV.b),E(_1eS));return E(_1eW);},_1eX=function(_1eY){var _1eZ=E(_1eY);if(!_1eZ._){return new T2(0,_10,_10);}else{var _1f0=E(_1eZ.a),_1f1=new T(function(){var _1f2=B(_1eX(_1eZ.b));return new T2(0,_1f2.a,_1f2.b);});return new T2(0,new T2(1,_1f0.a,new T(function(){return E(E(_1f1).a);})),new T2(1,_1f0.b,new T(function(){return E(E(_1f1).b);})));}},_1f3=new T(function(){return B(unCStr("Rk"));}),_1f4=function(_1f5,_1f6,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_1fd,_1fe,_1ff,_1fg,_1fh,_1fi,_1fj,_1fk,_1fl,_1fm){while(1){var _1fn=B((function(_1fo,_1fp,_1fq,_1fr,_1fs,_1ft,_1fu,_1fv,_1fw,_1fx,_1fy,_1fz,_1fA,_1fB,_1fC,_1fD,_1fE,_1fF){var _1fG=E(_1fo);if(!_1fG._){return {_:0,a:_1fp,b:_1fq,c:_1fr,d:_1fs,e:_1ft,f:_1fu,g:_1fv,h:_1fw,i:_1fx,j:_1fy,k:_1fz,l:_1fA,m:_1fB,n:_1fC,o:_1fD,p:_1fE,q:_1fF};}else{var _1fH=_1fG.a,_1fI=B(_R1(B(unAppCStr("e.e",new T2(1,_1fH,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1fH,_1f3)));})))),_1fp,_1fq,_1fr,_1fs,_1ft,_1fu,_1fv,_1fw,_1fx,_1fy,_1fz,_1fA,_1fB,_1fC,_1fD,_1fE,_1fF));_1f5=_1fG.b;_1f6=_1fI.a;_1f7=_1fI.b;_1f8=_1fI.c;_1f9=_1fI.d;_1fa=_1fI.e;_1fb=_1fI.f;_1fc=_1fI.g;_1fd=_1fI.h;_1fe=_1fI.i;_1ff=_1fI.j;_1fg=_1fI.k;_1fh=_1fI.l;_1fi=_1fI.m;_1fj=_1fI.n;_1fk=_1fI.o;_1fl=_1fI.p;_1fm=_1fI.q;return __continue;}})(_1f5,_1f6,_1f7,_1f8,_1f9,_1fa,_1fb,_1fc,_1fd,_1fe,_1ff,_1fg,_1fh,_1fi,_1fj,_1fk,_1fl,_1fm));if(_1fn!=__continue){return _1fn;}}},_1fJ=function(_1fK){var _1fL=E(_1fK);switch(_1fL){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1fL>>>0>1114111){return new F(function(){return _wB(_1fL);});}else{return _1fL;}}},_1fM=function(_1fN,_1fO,_1fP){while(1){var _1fQ=E(_1fO);if(!_1fQ._){return (E(_1fP)._==0)?true:false;}else{var _1fR=E(_1fP);if(!_1fR._){return false;}else{if(!B(A3(_4z,_1fN,_1fQ.a,_1fR.a))){return false;}else{_1fO=_1fQ.b;_1fP=_1fR.b;continue;}}}}},_1fS=function(_1fT,_1fU){return (!B(_1fM(_ri,_1fT,_1fU)))?true:false;},_1fV=function(_1fW,_1fX){return new F(function(){return _1fM(_ri,_1fW,_1fX);});},_1fY=new T2(0,_1fV,_1fS),_1fZ=function(_1g0){var _1g1=E(_1g0);if(!_1g1._){return new T2(0,_10,_10);}else{var _1g2=E(_1g1.a),_1g3=new T(function(){var _1g4=B(_1fZ(_1g1.b));return new T2(0,_1g4.a,_1g4.b);});return new T2(0,new T2(1,_1g2.a,new T(function(){return E(E(_1g3).a);})),new T2(1,_1g2.b,new T(function(){return E(E(_1g3).b);})));}},_1g5=function(_1g6,_1g7){while(1){var _1g8=E(_1g7);if(!_1g8._){return __Z;}else{var _1g9=_1g8.b,_1ga=E(_1g6);if(_1ga==1){return E(_1g9);}else{_1g6=_1ga-1|0;_1g7=_1g9;continue;}}}},_1gb=function(_1gc,_1gd){while(1){var _1ge=E(_1gd);if(!_1ge._){return __Z;}else{var _1gf=_1ge.b,_1gg=E(_1gc);if(_1gg==1){return E(_1gf);}else{_1gc=_1gg-1|0;_1gd=_1gf;continue;}}}},_1gh=function(_1gi){return new F(function(){return _Gh(_1gi,_10);});},_1gj=function(_1gk,_1gl,_1gm,_1gn){var _1go=new T(function(){return B(_M0(_h7,_1gl,_1gm));}),_1gp=new T(function(){var _1gq=E(_1go),_1gr=new T(function(){var _1gs=_1gq+1|0;if(_1gs>0){return B(_1gb(_1gs,_1gm));}else{return E(_1gm);}});if(0>=_1gq){return E(_1gr);}else{var _1gt=function(_1gu,_1gv){var _1gw=E(_1gu);if(!_1gw._){return E(_1gr);}else{var _1gx=_1gw.a,_1gy=E(_1gv);return (_1gy==1)?new T2(1,_1gx,_1gr):new T2(1,_1gx,new T(function(){return B(_1gt(_1gw.b,_1gy-1|0));}));}};return B(_1gt(_1gm,_1gq));}}),_1gz=new T(function(){var _1gA=E(_1go),_1gB=new T(function(){if(E(_1gl)==94){return B(A2(_1gk,new T(function(){return B(_6R(_1gn,_1gA+1|0));}),new T(function(){return B(_6R(_1gn,_1gA));})));}else{return B(A2(_1gk,new T(function(){return B(_6R(_1gn,_1gA));}),new T(function(){return B(_6R(_1gn,_1gA+1|0));})));}}),_1gC=new T2(1,_1gB,new T(function(){var _1gD=_1gA+2|0;if(_1gD>0){return B(_1g5(_1gD,_1gn));}else{return E(_1gn);}}));if(0>=_1gA){return E(_1gC);}else{var _1gE=function(_1gF,_1gG){var _1gH=E(_1gF);if(!_1gH._){return E(_1gC);}else{var _1gI=_1gH.a,_1gJ=E(_1gG);return (_1gJ==1)?new T2(1,_1gI,_1gC):new T2(1,_1gI,new T(function(){return B(_1gE(_1gH.b,_1gJ-1|0));}));}};return B(_1gE(_1gn,_1gA));}});return (E(_1gl)==94)?new T2(0,new T(function(){return B(_1gh(_1gp));}),new T(function(){return B(_1gh(_1gz));})):new T2(0,_1gp,_1gz);},_1gK=new T(function(){return B(_cn(_oM,_oL));}),_1gL=function(_1gM,_1gN,_1gO){while(1){if(!E(_1gK)){if(!B(_cn(B(_106(_1gN,_oM)),_oL))){if(!B(_cn(_1gN,_aV))){var _1gP=B(_of(_1gM,_1gM)),_1gQ=B(_ZR(B(_eO(_1gN,_aV)),_oM)),_1gR=B(_of(_1gM,_1gO));_1gM=_1gP;_1gN=_1gQ;_1gO=_1gR;continue;}else{return new F(function(){return _of(_1gM,_1gO);});}}else{var _1gP=B(_of(_1gM,_1gM)),_1gQ=B(_ZR(_1gN,_oM));_1gM=_1gP;_1gN=_1gQ;continue;}}else{return E(_9U);}}},_1gS=function(_1gT,_1gU){while(1){if(!E(_1gK)){if(!B(_cn(B(_106(_1gU,_oM)),_oL))){if(!B(_cn(_1gU,_aV))){return new F(function(){return _1gL(B(_of(_1gT,_1gT)),B(_ZR(B(_eO(_1gU,_aV)),_oM)),_1gT);});}else{return E(_1gT);}}else{var _1gV=B(_of(_1gT,_1gT)),_1gW=B(_ZR(_1gU,_oM));_1gT=_1gV;_1gU=_1gW;continue;}}else{return E(_9U);}}},_1gX=function(_1gY,_1gZ){if(!B(_d7(_1gZ,_oL))){if(!B(_cn(_1gZ,_oL))){return new F(function(){return _1gS(_1gY,_1gZ);});}else{return E(_aV);}}else{return E(_pr);}},_1h0=94,_1h1=45,_1h2=43,_1h3=42,_1h4=function(_1h5,_1h6){while(1){var _1h7=B((function(_1h8,_1h9){var _1ha=E(_1h9);if(!_1ha._){return __Z;}else{if((B(_mt(_1h8,0))+1|0)==B(_mt(_1ha,0))){if(!B(_4B(_h7,_1h0,_1h8))){if(!B(_4B(_h7,_1h3,_1h8))){if(!B(_4B(_h7,_1h2,_1h8))){if(!B(_4B(_h7,_1h1,_1h8))){return E(_1ha);}else{var _1hb=B(_1gj(_eO,45,_1h8,_1ha));_1h5=_1hb.a;_1h6=_1hb.b;return __continue;}}else{var _1hc=B(_1gj(_cv,43,_1h8,_1ha));_1h5=_1hc.a;_1h6=_1hc.b;return __continue;}}else{var _1hd=B(_1gj(_of,42,_1h8,_1ha));_1h5=_1hd.a;_1h6=_1hd.b;return __continue;}}else{var _1he=B(_1gj(_1gX,94,new T(function(){return B(_1gh(_1h8));}),new T(function(){return B(_Gh(_1ha,_10));})));_1h5=_1he.a;_1h6=_1he.b;return __continue;}}else{return __Z;}}})(_1h5,_1h6));if(_1h7!=__continue){return _1h7;}}},_1hf=function(_1hg){var _1hh=E(_1hg);if(!_1hh._){return new T2(0,_10,_10);}else{var _1hi=E(_1hh.a),_1hj=new T(function(){var _1hk=B(_1hf(_1hh.b));return new T2(0,_1hk.a,_1hk.b);});return new T2(0,new T2(1,_1hi.a,new T(function(){return E(E(_1hj).a);})),new T2(1,_1hi.b,new T(function(){return E(E(_1hj).b);})));}},_1hl=new T(function(){return B(unCStr("0123456789+-"));}),_1hm=function(_1hn){while(1){var _1ho=E(_1hn);if(!_1ho._){return true;}else{if(!B(_4B(_h7,_1ho.a,_1hl))){return false;}else{_1hn=_1ho.b;continue;}}}},_1hp=new T(function(){return B(err(_so));}),_1hq=new T(function(){return B(err(_sq));}),_1hr=function(_1hs,_1ht){var _1hu=function(_1hv,_1hw){var _1hx=function(_1hy){return new F(function(){return A1(_1hw,new T(function(){return B(_ft(_1hy));}));});},_1hz=new T(function(){return B(_D4(function(_1hA){return new F(function(){return A3(_1hs,_1hA,_1hv,_1hx);});}));}),_1hB=function(_1hC){return E(_1hz);},_1hD=function(_1hE){return new F(function(){return A2(_BL,_1hE,_1hB);});},_1hF=new T(function(){return B(_D4(function(_1hG){var _1hH=E(_1hG);if(_1hH._==4){var _1hI=E(_1hH.a);if(!_1hI._){return new F(function(){return A3(_1hs,_1hH,_1hv,_1hw);});}else{if(E(_1hI.a)==45){if(!E(_1hI.b)._){return E(new T1(1,_1hD));}else{return new F(function(){return A3(_1hs,_1hH,_1hv,_1hw);});}}else{return new F(function(){return A3(_1hs,_1hH,_1hv,_1hw);});}}}else{return new F(function(){return A3(_1hs,_1hH,_1hv,_1hw);});}}));}),_1hJ=function(_1hK){return E(_1hF);};return new T1(1,function(_1hL){return new F(function(){return A2(_BL,_1hL,_1hJ);});});};return new F(function(){return _DV(_1hu,_1ht);});},_1hM=function(_1hN){var _1hO=E(_1hN);if(_1hO._==5){var _1hP=B(_FT(_1hO.a));return (_1hP._==0)?E(_FY):function(_1hQ,_1hR){return new F(function(){return A1(_1hR,_1hP.a);});};}else{return E(_FY);}},_1hS=new T(function(){return B(A3(_1hr,_1hM,_DB,_Fo));}),_1hT=function(_1hU,_1hV){var _1hW=E(_1hV);if(!_1hW._){return __Z;}else{var _1hX=_1hW.a,_1hY=_1hW.b,_1hZ=function(_1i0){var _1i1=B(_1hf(_1hU)),_1i2=_1i1.a;return (!B(_4B(_qe,_1hX,_1i2)))?__Z:new T2(1,new T(function(){return B(_6R(_1i1.b,B(_M0(_qe,_1hX,_1i2))));}),new T(function(){return B(_1hT(_1hU,_1hY));}));};if(!B(_69(_1hX,_10))){if(!B(_1hm(_1hX))){return new F(function(){return _1hZ(_);});}else{return new T2(1,new T(function(){var _1i3=B(_Ga(B(_sv(_1hS,_1hX))));if(!_1i3._){return E(_1hp);}else{if(!E(_1i3.b)._){return E(_1i3.a);}else{return E(_1hq);}}}),new T(function(){return B(_1hT(_1hU,_1hY));}));}}else{return new F(function(){return _1hZ(_);});}}},_1i4=new T(function(){return B(unCStr("+-*^"));}),_1i5=new T(function(){return B(unCStr("0123456789"));}),_1i6=new T(function(){return B(_KQ("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1i7=new T2(1,_10,_10),_1i8=function(_1i9){var _1ia=E(_1i9);if(!_1ia._){return new T2(0,_1i7,_10);}else{var _1ib=_1ia.a,_1ic=new T(function(){var _1id=B(_1i8(_1ia.b)),_1ie=E(_1id.a);if(!_1ie._){return E(_1i6);}else{return new T3(0,_1ie.a,_1ie.b,_1id.b);}});return (!B(_4B(_h7,_1ib,_1i5)))?(!B(_4B(_h7,_1ib,_1i4)))?new T2(0,new T2(1,new T2(1,_1ib,new T(function(){return E(E(_1ic).a);})),new T(function(){return E(E(_1ic).b);})),new T(function(){return E(E(_1ic).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1ic).a);}),new T(function(){return E(E(_1ic).b);}))),new T2(1,_1ib,new T(function(){return E(E(_1ic).c);}))):new T2(0,new T2(1,new T2(1,_1ib,new T(function(){return E(E(_1ic).a);})),new T(function(){return E(E(_1ic).b);})),new T(function(){return E(E(_1ic).c);}));}},_1if=function(_1ig,_1ih){var _1ii=new T(function(){var _1ij=B(_1i8(_1ih)),_1ik=E(_1ij.a);if(!_1ik._){return E(_1i6);}else{return new T3(0,_1ik.a,_1ik.b,_1ij.b);}});return (!B(_4B(_h7,_1ig,_1i5)))?(!B(_4B(_h7,_1ig,_1i4)))?new T2(0,new T2(1,new T2(1,_1ig,new T(function(){return E(E(_1ii).a);})),new T(function(){return E(E(_1ii).b);})),new T(function(){return E(E(_1ii).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1ii).a);}),new T(function(){return E(E(_1ii).b);}))),new T2(1,_1ig,new T(function(){return E(E(_1ii).c);}))):new T2(0,new T2(1,new T2(1,_1ig,new T(function(){return E(E(_1ii).a);})),new T(function(){return E(E(_1ii).b);})),new T(function(){return E(E(_1ii).c);}));},_1il=function(_1im,_1in){while(1){var _1io=E(_1im);if(!_1io._){return E(_1in);}else{_1im=_1io.b;_1in=_1io.a;continue;}}},_1ip=function(_1iq,_1ir,_1is){return new F(function(){return _1il(_1ir,_1iq);});},_1it=function(_1iu,_1iv){var _1iw=E(_1iv);if(!_1iw._){return __Z;}else{var _1ix=B(_1if(_1iw.a,_1iw.b)),_1iy=B(_1h4(_1ix.b,B(_1hT(_1iu,_1ix.a))));if(!_1iy._){return E(_1iw);}else{return new F(function(){return _12a(0,B(_1ip(_1iy.a,_1iy.b,_S6)),_10);});}}},_1iz=function(_1iA,_1iB){var _1iC=function(_1iD,_1iE){while(1){var _1iF=B((function(_1iG,_1iH){var _1iI=E(_1iH);if(!_1iI._){return (!B(_qL(_1iG,_10)))?new T2(0,_wr,_1iG):new T2(0,_wq,_10);}else{var _1iJ=_1iI.b,_1iK=B(_1fZ(_1iI.a)).a;if(!B(_4B(_h7,_16U,_1iK))){var _1iL=_1iG;_1iD=_1iL;_1iE=_1iJ;return __continue;}else{var _1iM=B(_17q(_1iK)),_1iN=_1iM.a,_1iO=_1iM.b;if(!B(_69(_1iO,_10))){if(!B(_qL(B(_1it(_1iA,_1iN)),B(_1it(_1iA,_1iO))))){return new T2(0,_wq,_10);}else{var _1iP=new T(function(){if(!B(_qL(_1iG,_10))){return B(_y(_1iG,new T(function(){return B(unAppCStr(" ",_1iN));},1)));}else{return E(_1iN);}});_1iD=_1iP;_1iE=_1iJ;return __continue;}}else{return new T2(0,_wq,_10);}}}})(_1iD,_1iE));if(_1iF!=__continue){return _1iF;}}};return new F(function(){return _1iC(_10,_1iB);});},_1iQ=function(_1iR,_1iS){var _1iT=new T(function(){var _1iU=B(_Ga(B(_sv(_120,new T(function(){return B(_pO(3,B(_I(0,imul(E(_1iS),E(_1iR)-1|0)|0,_10))));})))));if(!_1iU._){return E(_11Z);}else{if(!E(_1iU.b)._){return E(_1iU.a);}else{return E(_11Y);}}});return new T2(0,new T(function(){return B(_av(_1iT,_1iR));}),_1iT);},_1iV=function(_1iW,_1iX){while(1){var _1iY=E(_1iX);if(!_1iY._){return __Z;}else{var _1iZ=_1iY.b,_1j0=E(_1iW);if(_1j0==1){return E(_1iZ);}else{_1iW=_1j0-1|0;_1iX=_1iZ;continue;}}}},_1j1=function(_1j2,_1j3){while(1){var _1j4=E(_1j3);if(!_1j4._){return __Z;}else{var _1j5=_1j4.b,_1j6=E(_1j2);if(_1j6==1){return E(_1j5);}else{_1j2=_1j6-1|0;_1j3=_1j5;continue;}}}},_1j7=64,_1j8=new T2(1,_1j7,_10),_1j9=function(_1ja,_1jb,_1jc,_1jd){return (!B(_qL(_1ja,_1jc)))?true:(!B(_cn(_1jb,_1jd)))?true:false;},_1je=function(_1jf,_1jg){var _1jh=E(_1jf),_1ji=E(_1jg);return new F(function(){return _1j9(_1jh.a,_1jh.b,_1ji.a,_1ji.b);});},_1jj=function(_1jk,_1jl,_1jm,_1jn){if(!B(_qL(_1jk,_1jm))){return false;}else{return new F(function(){return _cn(_1jl,_1jn);});}},_1jo=function(_1jp,_1jq){var _1jr=E(_1jp),_1js=E(_1jq);return new F(function(){return _1jj(_1jr.a,_1jr.b,_1js.a,_1js.b);});},_1jt=new T2(0,_1jo,_1je),_1ju=function(_1jv){var _1jw=E(_1jv);if(!_1jw._){return new T2(0,_10,_10);}else{var _1jx=E(_1jw.a),_1jy=new T(function(){var _1jz=B(_1ju(_1jw.b));return new T2(0,_1jz.a,_1jz.b);});return new T2(0,new T2(1,_1jx.a,new T(function(){return E(E(_1jy).a);})),new T2(1,_1jx.b,new T(function(){return E(E(_1jy).b);})));}},_1jA=function(_1jB){var _1jC=E(_1jB);if(!_1jC._){return new T2(0,_10,_10);}else{var _1jD=E(_1jC.a),_1jE=new T(function(){var _1jF=B(_1jA(_1jC.b));return new T2(0,_1jF.a,_1jF.b);});return new T2(0,new T2(1,_1jD.a,new T(function(){return E(E(_1jE).a);})),new T2(1,_1jD.b,new T(function(){return E(E(_1jE).b);})));}},_1jG=function(_1jH){var _1jI=E(_1jH);if(!_1jI._){return new T2(0,_10,_10);}else{var _1jJ=E(_1jI.a),_1jK=new T(function(){var _1jL=B(_1jG(_1jI.b));return new T2(0,_1jL.a,_1jL.b);});return new T2(0,new T2(1,_1jJ.a,new T(function(){return E(E(_1jK).a);})),new T2(1,_1jJ.b,new T(function(){return E(E(_1jK).b);})));}},_1jM=function(_1jN,_1jO){return (_1jN<=_1jO)?new T2(1,_1jN,new T(function(){return B(_1jM(_1jN+1|0,_1jO));})):__Z;},_1jP=new T(function(){return B(_1jM(65,90));}),_1jQ=function(_1jR){return (_1jR<=122)?new T2(1,_1jR,new T(function(){return B(_1jQ(_1jR+1|0));})):E(_1jP);},_1jS=new T(function(){return B(_1jQ(97));}),_1jT=function(_1jU){while(1){var _1jV=E(_1jU);if(!_1jV._){return true;}else{if(!B(_4B(_h7,_1jV.a,_1jS))){return false;}else{_1jU=_1jV.b;continue;}}}},_1jW=new T2(0,_10,_10),_1jX=new T(function(){return B(err(_so));}),_1jY=new T(function(){return B(err(_sq));}),_1jZ=new T(function(){return B(A3(_1hr,_1hM,_DB,_Fo));}),_1k0=function(_1k1,_1k2,_1k3){while(1){var _1k4=B((function(_1k5,_1k6,_1k7){var _1k8=E(_1k7);if(!_1k8._){return __Z;}else{var _1k9=_1k8.b,_1ka=B(_1jA(_1k6)),_1kb=_1ka.a,_1kc=B(_1ju(_1kb)),_1kd=_1kc.a,_1ke=new T(function(){return E(B(_1jG(_1k8.a)).a);}),_1kf=new T(function(){return B(_4B(_h7,_16U,_1ke));}),_1kg=new T(function(){if(!E(_1kf)){return E(_1jW);}else{var _1kh=B(_17q(_1ke));return new T2(0,_1kh.a,_1kh.b);}}),_1ki=new T(function(){return E(E(_1kg).a);}),_1kj=new T(function(){return B(_M0(_qe,_1ki,_1kd));}),_1kk=new T(function(){var _1kl=function(_){var _1km=B(_mt(_1k6,0))-1|0,_1kn=function(_1ko){if(_1ko>=0){var _1kp=newArr(_1ko,_137),_1kq=_1kp,_1kr=E(_1ko);if(!_1kr){return new T4(0,E(_15t),E(_1km),0,_1kq);}else{var _1ks=function(_1kt,_1ku,_){while(1){var _1kv=E(_1kt);if(!_1kv._){return E(_);}else{var _=_1kq[_1ku]=_1kv.a;if(_1ku!=(_1kr-1|0)){var _1kw=_1ku+1|0;_1kt=_1kv.b;_1ku=_1kw;continue;}else{return E(_);}}}},_=B(_1ks(_1ka.b,0,_));return new T4(0,E(_15t),E(_1km),_1kr,_1kq);}}else{return E(_141);}};if(0>_1km){return new F(function(){return _1kn(0);});}else{return new F(function(){return _1kn(_1km+1|0);});}};return B(_142(_1kl));});if(!B(_4B(_qe,_1ki,_1kd))){var _1kx=false;}else{var _1ky=E(_1kk),_1kz=E(_1ky.a),_1kA=E(_1ky.b),_1kB=E(_1kj);if(_1kz>_1kB){var _1kC=B(_19C(_1kB,_1kz,_1kA));}else{if(_1kB>_1kA){var _1kD=B(_19C(_1kB,_1kz,_1kA));}else{var _1kD=E(_1ky.d[_1kB-_1kz|0])==E(_1k5);}var _1kC=_1kD;}var _1kx=_1kC;}var _1kE=new T(function(){return E(E(_1kg).b);}),_1kF=new T(function(){return B(_M0(_qe,_1kE,_1kd));}),_1kG=new T(function(){if(!B(_4B(_qe,_1kE,_1kd))){return false;}else{var _1kH=E(_1kk),_1kI=E(_1kH.a),_1kJ=E(_1kH.b),_1kK=E(_1kF);if(_1kI>_1kK){return B(_19C(_1kK,_1kI,_1kJ));}else{if(_1kK>_1kJ){return B(_19C(_1kK,_1kI,_1kJ));}else{return E(_1kH.d[_1kK-_1kI|0])==E(_1k5);}}}}),_1kL=new T(function(){var _1kM=function(_){var _1kN=B(_mt(_1kb,0))-1|0,_1kO=function(_1kP){if(_1kP>=0){var _1kQ=newArr(_1kP,_137),_1kR=_1kQ,_1kS=E(_1kP);if(!_1kS){return new T4(0,E(_15t),E(_1kN),0,_1kR);}else{var _1kT=function(_1kU,_1kV,_){while(1){var _1kW=E(_1kU);if(!_1kW._){return E(_);}else{var _=_1kR[_1kV]=_1kW.a;if(_1kV!=(_1kS-1|0)){var _1kX=_1kV+1|0;_1kU=_1kW.b;_1kV=_1kX;continue;}else{return E(_);}}}},_=B(_1kT(_1kc.b,0,_));return new T4(0,E(_15t),E(_1kN),_1kS,_1kR);}}else{return E(_141);}};if(0>_1kN){return new F(function(){return _1kO(0);});}else{return new F(function(){return _1kO(_1kN+1|0);});}};return B(_142(_1kM));}),_1kY=function(_1kZ){var _1l0=function(_1l1){return (!E(_1kx))?__Z:(!E(_1kG))?__Z:new T2(1,new T2(0,_1ki,new T(function(){var _1l2=E(_1kL),_1l3=E(_1l2.a),_1l4=E(_1l2.b),_1l5=E(_1kj);if(_1l3>_1l5){return B(_19C(_1l5,_1l3,_1l4));}else{if(_1l5>_1l4){return B(_19C(_1l5,_1l3,_1l4));}else{return E(_1l2.d[_1l5-_1l3|0]);}}})),new T2(1,new T2(0,_1kE,new T(function(){var _1l6=E(_1kL),_1l7=E(_1l6.a),_1l8=E(_1l6.b),_1l9=E(_1kF);if(_1l7>_1l9){return B(_19C(_1l9,_1l7,_1l8));}else{if(_1l9>_1l8){return B(_19C(_1l9,_1l7,_1l8));}else{return E(_1l6.d[_1l9-_1l7|0]);}}})),_10));};if(!E(_1kx)){if(!E(_1kG)){return new F(function(){return _1l0(_);});}else{return new T2(1,new T2(0,_1kE,new T(function(){var _1la=E(_1kL),_1lb=E(_1la.a),_1lc=E(_1la.b),_1ld=E(_1kF);if(_1lb>_1ld){return B(_19C(_1ld,_1lb,_1lc));}else{if(_1ld>_1lc){return B(_19C(_1ld,_1lb,_1lc));}else{return E(_1la.d[_1ld-_1lb|0]);}}})),_10);}}else{return new F(function(){return _1l0(_);});}};if(!E(_1kx)){var _1le=B(_1kY(_));}else{if(!E(_1kG)){var _1lf=new T2(1,new T2(0,_1ki,new T(function(){var _1lg=E(_1kL),_1lh=E(_1lg.a),_1li=E(_1lg.b),_1lj=E(_1kj);if(_1lh>_1lj){return B(_19C(_1lj,_1lh,_1li));}else{if(_1lj>_1li){return B(_19C(_1lj,_1lh,_1li));}else{return E(_1lg.d[_1lj-_1lh|0]);}}})),_10);}else{var _1lf=B(_1kY(_));}var _1le=_1lf;}if(!B(_1fM(_1jt,_1le,_10))){return new F(function(){return _y(_1le,new T(function(){return B(_1k0(_1k5,_1k6,_1k9));},1));});}else{if(!E(_1kf)){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{if(!B(_1jT(_1ki))){if(!B(_1jT(_1kE))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{if(!E(_1kx)){if(!E(_1kG)){if(!B(_69(_1ki,_10))){if(!B(_1hm(_1ki))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{return new T2(1,new T2(0,_1kE,new T(function(){var _1lm=B(_Ga(B(_sv(_1jZ,_1ki))));if(!_1lm._){return E(_1jX);}else{if(!E(_1lm.b)._){return E(_1lm.a);}else{return E(_1jY);}}})),new T(function(){return B(_1k0(_1k5,_1k6,_1k9));}));}}else{var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}else{var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}else{var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}}else{if(!E(_1kx)){if(!E(_1kG)){if(!B(_69(_1kE,_10))){if(!B(_1hm(_1kE))){if(!B(_1jT(_1kE))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{if(!B(_69(_1ki,_10))){if(!B(_1hm(_1ki))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{return new T2(1,new T2(0,_1kE,new T(function(){var _1ln=B(_Ga(B(_sv(_1jZ,_1ki))));if(!_1ln._){return E(_1jX);}else{if(!E(_1ln.b)._){return E(_1ln.a);}else{return E(_1jY);}}})),new T(function(){return B(_1k0(_1k5,_1k6,_1k9));}));}}else{var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}}else{return new T2(1,new T2(0,_1ki,new T(function(){var _1lo=B(_Ga(B(_sv(_1jZ,_1kE))));if(!_1lo._){return E(_1jX);}else{if(!E(_1lo.b)._){return E(_1lo.a);}else{return E(_1jY);}}})),new T(function(){return B(_1k0(_1k5,_1k6,_1k9));}));}}else{if(!B(_1jT(_1kE))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{if(!B(_69(_1ki,_10))){if(!B(_1hm(_1ki))){var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}else{return new T2(1,new T2(0,_1kE,new T(function(){var _1lp=B(_Ga(B(_sv(_1jZ,_1ki))));if(!_1lp._){return E(_1jX);}else{if(!E(_1lp.b)._){return E(_1lp.a);}else{return E(_1jY);}}})),new T(function(){return B(_1k0(_1k5,_1k6,_1k9));}));}}else{var _1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}}}else{var _1lq=B(_1jT(_1kE)),_1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}else{var _1lr=B(_1jT(_1kE)),_1lk=_1k5,_1ll=_1k6;_1k1=_1lk;_1k2=_1ll;_1k3=_1k9;return __continue;}}}}}})(_1k1,_1k2,_1k3));if(_1k4!=__continue){return _1k4;}}},_1ls=102,_1lt=101,_1lu=new T(function(){return B(unCStr("=="));}),_1lv=new T(function(){return B(_e7("Action.hs:(103,17)-(107,70)|case"));}),_1lw=new T(function(){return B(_e7("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1lx=5,_1ly=117,_1lz=98,_1lA=110,_1lB=118,_1lC=function(_1lD,_1lE,_1lF,_1lG,_1lH,_1lI,_1lJ,_1lK,_1lL,_1lM,_1lN,_1lO,_1lP){var _1lQ=B(_6R(B(_6R(_1lH,_1lE)),_1lD)),_1lR=_1lQ.a,_1lS=_1lQ.b;if(E(_1lJ)==32){if(!B(_4B(_h7,_1lR,_1j8))){var _1lT=false;}else{switch(E(_1lS)){case 0:var _1lU=true;break;case 1:var _1lU=false;break;case 2:var _1lU=false;break;case 3:var _1lU=false;break;case 4:var _1lU=false;break;case 5:var _1lU=false;break;case 6:var _1lU=false;break;case 7:var _1lU=false;break;default:var _1lU=false;}var _1lT=_1lU;}var _1lV=_1lT;}else{var _1lV=false;}if(E(_1lJ)==32){if(E(_1lR)==32){var _1lW=false;}else{switch(E(_1lS)){case 0:if(!E(_1lV)){var _1lX=true;}else{var _1lX=false;}var _1lY=_1lX;break;case 1:var _1lY=false;break;case 2:var _1lY=false;break;case 3:var _1lY=false;break;case 4:var _1lY=false;break;case 5:var _1lY=false;break;case 6:var _1lY=false;break;case 7:var _1lY=false;break;default:if(!E(_1lV)){var _1lZ=true;}else{var _1lZ=false;}var _1lY=_1lZ;}var _1lW=_1lY;}var _1m0=_1lW;}else{var _1m0=false;}var _1m1=new T(function(){return B(_Kp(_1lD,_1lE,new T(function(){if(!E(_1m0)){if(!E(_1lV)){return E(_1lR);}else{return _1lI;}}else{return E(_Tr);}}),_1lS,_1lH));});switch(E(_1lS)){case 3:var _1m2=true;break;case 4:if(E(_1lJ)==32){var _1m3=true;}else{var _1m3=false;}var _1m2=_1m3;break;default:var _1m2=false;}if(!E(_1m2)){var _1m4=E(_1m1);}else{var _1m5=E(_1lF),_1m6=new T(function(){return B(_6R(_1m1,_1lE));}),_1m7=function(_1m8,_1m9){var _1ma=E(_1m8);if(_1ma==( -1)){return E(_1m1);}else{var _1mb=new T(function(){return B(_Kp(_1lD,_1lE,_Tr,_E6,_1m1));}),_1mc=E(_1m9);if(_1mc==( -1)){var _1md=__Z;}else{var _1md=B(_6R(_1mb,_1mc));}if(E(B(_6R(_1md,_1ma)).a)==32){var _1me=new T(function(){var _1mf=new T(function(){return B(_6R(_1m6,_1lD));}),_1mg=new T2(1,new T2(0,new T(function(){return E(E(_1mf).a);}),new T(function(){return E(E(_1mf).b);})),new T(function(){var _1mh=_1ma+1|0;if(_1mh>0){return B(_1j1(_1mh,_1md));}else{return E(_1md);}}));if(0>=_1ma){return E(_1mg);}else{var _1mi=function(_1mj,_1mk){var _1ml=E(_1mj);if(!_1ml._){return E(_1mg);}else{var _1mm=_1ml.a,_1mn=E(_1mk);return (_1mn==1)?new T2(1,_1mm,_1mg):new T2(1,_1mm,new T(function(){return B(_1mi(_1ml.b,_1mn-1|0));}));}};return B(_1mi(_1md,_1ma));}}),_1mo=new T2(1,_1me,new T(function(){var _1mp=_1m9+1|0;if(_1mp>0){return B(_1iV(_1mp,_1mb));}else{return E(_1mb);}}));if(0>=_1m9){return E(_1mo);}else{var _1mq=function(_1mr,_1ms){var _1mt=E(_1mr);if(!_1mt._){return E(_1mo);}else{var _1mu=_1mt.a,_1mv=E(_1ms);return (_1mv==1)?new T2(1,_1mu,_1mo):new T2(1,_1mu,new T(function(){return B(_1mq(_1mt.b,_1mv-1|0));}));}};return new F(function(){return _1mq(_1mb,_1m9);});}}else{return E(_1m1);}}};if(_1lD<=_1m5){if(_1m5<=_1lD){var _1mw=E(_1lG);if(_1lE<=_1mw){if(_1mw<=_1lE){var _1mx=E(_1lv);}else{var _1my=E(_1lE);if(!_1my){var _1mz=B(_1m7( -1, -1));}else{var _1mz=B(_1m7(_1lD,_1my-1|0));}var _1mx=_1mz;}var _1mA=_1mx;}else{if(_1lE!=(B(_mt(_1m1,0))-1|0)){var _1mB=B(_1m7(_1lD,_1lE+1|0));}else{var _1mB=B(_1m7( -1, -1));}var _1mA=_1mB;}var _1mC=_1mA;}else{var _1mD=E(_1lD);if(!_1mD){var _1mE=B(_1m7( -1, -1));}else{var _1mE=B(_1m7(_1mD-1|0,_1lE));}var _1mC=_1mE;}var _1mF=_1mC;}else{if(_1lD!=(B(_mt(_1m6,0))-1|0)){var _1mG=B(_1m7(_1lD+1|0,_1lE));}else{var _1mG=B(_1m7( -1, -1));}var _1mF=_1mG;}var _1m4=_1mF;}if(!E(_1lO)){var _1mH=E(_1m4);}else{var _1mI=new T(function(){var _1mJ=E(_1m4);if(!_1mJ._){return E(_nh);}else{return B(_mt(_1mJ.a,0));}}),_1mK=new T(function(){return B(_mt(_1m4,0));}),_1mL=function(_1mM,_1mN,_1mO,_1mP,_1mQ,_1mR,_1mS){while(1){var _1mT=B((function(_1mU,_1mV,_1mW,_1mX,_1mY,_1mZ,_1n0){var _1n1=E(_1n0);if(!_1n1._){return E(_1mX);}else{var _1n2=_1n1.b,_1n3=E(_1n1.a);if(!_1n3._){return E(_1lw);}else{var _1n4=_1n3.b,_1n5=E(_1n3.a);if(E(_1n5.b)==5){var _1n6=new T(function(){var _1n7=B(_1iQ(_1lx,_1mU));return new T2(0,_1n7.a,_1n7.b);}),_1n8=new T(function(){var _1n9=function(_1na,_1nb){var _1nc=function(_1nd){return new F(function(){return _Kp(_1mV,_1mW,_Tr,_E6,new T(function(){return B(_Kp(_1na,_1nb,_1n5.a,_EV,_1mX));}));});};if(_1na!=_1mV){return new F(function(){return _1nc(_);});}else{if(_1nb!=_1mW){return new F(function(){return _1nc(_);});}else{return E(_1mX);}}};switch(E(E(_1n6).a)){case 1:var _1ne=_1mV-1|0;if(_1ne<0){return B(_1n9(_1mV,_1mW));}else{if(_1ne>=E(_1mI)){return B(_1n9(_1mV,_1mW));}else{if(_1mW<0){return B(_1n9(_1mV,_1mW));}else{if(_1mW>=E(_1mK)){return B(_1n9(_1mV,_1mW));}else{if(_1ne!=_1mY){if(E(B(_6R(B(_6R(_1mX,_1mW)),_1ne)).a)==32){return B(_1n9(_1ne,_1mW));}else{return B(_1n9(_1mV,_1mW));}}else{if(_1mW!=_1mZ){if(E(B(_6R(B(_6R(_1mX,_1mW)),_1ne)).a)==32){return B(_1n9(_1ne,_1mW));}else{return B(_1n9(_1mV,_1mW));}}else{return B(_1n9(_1mV,_1mW));}}}}}}break;case 2:if(_1mV<0){return B(_1n9(_1mV,_1mW));}else{if(_1mV>=E(_1mI)){return B(_1n9(_1mV,_1mW));}else{var _1nf=_1mW-1|0;if(_1nf<0){return B(_1n9(_1mV,_1mW));}else{if(_1nf>=E(_1mK)){return B(_1n9(_1mV,_1mW));}else{if(_1mV!=_1mY){if(E(B(_6R(B(_6R(_1mX,_1nf)),_1mV)).a)==32){return B(_1n9(_1mV,_1nf));}else{return B(_1n9(_1mV,_1mW));}}else{if(_1nf!=_1mZ){if(E(B(_6R(B(_6R(_1mX,_1nf)),_1mV)).a)==32){return B(_1n9(_1mV,_1nf));}else{return B(_1n9(_1mV,_1mW));}}else{return B(_1n9(_1mV,_1mW));}}}}}}break;case 3:var _1ng=_1mV+1|0;if(_1ng<0){return B(_1n9(_1mV,_1mW));}else{if(_1ng>=E(_1mI)){return B(_1n9(_1mV,_1mW));}else{if(_1mW<0){return B(_1n9(_1mV,_1mW));}else{if(_1mW>=E(_1mK)){return B(_1n9(_1mV,_1mW));}else{if(_1ng!=_1mY){if(E(B(_6R(B(_6R(_1mX,_1mW)),_1ng)).a)==32){return B(_1n9(_1ng,_1mW));}else{return B(_1n9(_1mV,_1mW));}}else{if(_1mW!=_1mZ){if(E(B(_6R(B(_6R(_1mX,_1mW)),_1ng)).a)==32){return B(_1n9(_1ng,_1mW));}else{return B(_1n9(_1mV,_1mW));}}else{return B(_1n9(_1mV,_1mW));}}}}}}break;case 4:if(_1mV<0){return B(_1n9(_1mV,_1mW));}else{if(_1mV>=E(_1mI)){return B(_1n9(_1mV,_1mW));}else{var _1nh=_1mW+1|0;if(_1nh<0){return B(_1n9(_1mV,_1mW));}else{if(_1nh>=E(_1mK)){return B(_1n9(_1mV,_1mW));}else{if(_1mV!=_1mY){if(E(B(_6R(B(_6R(_1mX,_1nh)),_1mV)).a)==32){return B(_1n9(_1mV,_1nh));}else{return B(_1n9(_1mV,_1mW));}}else{if(_1nh!=_1mZ){if(E(B(_6R(B(_6R(_1mX,_1nh)),_1mV)).a)==32){return B(_1n9(_1mV,_1nh));}else{return B(_1n9(_1mV,_1mW));}}else{return B(_1n9(_1mV,_1mW));}}}}}}break;default:if(_1mV<0){return B(_1n9(_1mV,_1mW));}else{if(_1mV>=E(_1mI)){return B(_1n9(_1mV,_1mW));}else{if(_1mW<0){return B(_1n9(_1mV,_1mW));}else{if(_1mW>=E(_1mK)){return B(_1n9(_1mV,_1mW));}else{if(_1mV!=_1mY){var _1ni=E(B(_6R(B(_6R(_1mX,_1mW)),_1mV)).a);return B(_1n9(_1mV,_1mW));}else{if(_1mW!=_1mZ){var _1nj=E(B(_6R(B(_6R(_1mX,_1mW)),_1mV)).a);return B(_1n9(_1mV,_1mW));}else{return B(_1n9(_1mV,_1mW));}}}}}}}}),_1nk=E(_1n4);if(!_1nk._){var _1nl=_1mW+1|0,_1nm=_1mY,_1nn=_1mZ;_1mM=new T(function(){return E(E(_1n6).b);},1);_1mN=0;_1mO=_1nl;_1mP=_1n8;_1mQ=_1nm;_1mR=_1nn;_1mS=_1n2;return __continue;}else{return new F(function(){return _1no(new T(function(){return E(E(_1n6).b);},1),_1mV+1|0,_1mW,_1n8,_1mY,_1mZ,_1nk.a,_1nk.b,_1n2);});}}else{var _1np=E(_1n4);if(!_1np._){var _1nq=_1mU,_1nl=_1mW+1|0,_1nr=_1mX,_1nm=_1mY,_1nn=_1mZ;_1mM=_1nq;_1mN=0;_1mO=_1nl;_1mP=_1nr;_1mQ=_1nm;_1mR=_1nn;_1mS=_1n2;return __continue;}else{return new F(function(){return _1no(_1mU,_1mV+1|0,_1mW,_1mX,_1mY,_1mZ,_1np.a,_1np.b,_1n2);});}}}}})(_1mM,_1mN,_1mO,_1mP,_1mQ,_1mR,_1mS));if(_1mT!=__continue){return _1mT;}}},_1no=function(_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA){while(1){var _1nB=B((function(_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI,_1nJ,_1nK){var _1nL=E(_1nI);if(E(_1nL.b)==5){var _1nM=new T(function(){var _1nN=B(_1iQ(_1lx,_1nC));return new T2(0,_1nN.a,_1nN.b);}),_1nO=new T(function(){var _1nP=function(_1nQ,_1nR){var _1nS=function(_1nT){return new F(function(){return _Kp(_1nD,_1nE,_Tr,_E6,new T(function(){return B(_Kp(_1nQ,_1nR,_1nL.a,_EV,_1nF));}));});};if(_1nQ!=_1nD){return new F(function(){return _1nS(_);});}else{if(_1nR!=_1nE){return new F(function(){return _1nS(_);});}else{return E(_1nF);}}};switch(E(E(_1nM).a)){case 1:var _1nU=_1nD-1|0;if(_1nU<0){return B(_1nP(_1nD,_1nE));}else{if(_1nU>=E(_1mI)){return B(_1nP(_1nD,_1nE));}else{if(_1nE<0){return B(_1nP(_1nD,_1nE));}else{if(_1nE>=E(_1mK)){return B(_1nP(_1nD,_1nE));}else{if(_1nU!=_1nG){if(E(B(_6R(B(_6R(_1nF,_1nE)),_1nU)).a)==32){return B(_1nP(_1nU,_1nE));}else{return B(_1nP(_1nD,_1nE));}}else{if(_1nE!=_1nH){if(E(B(_6R(B(_6R(_1nF,_1nE)),_1nU)).a)==32){return B(_1nP(_1nU,_1nE));}else{return B(_1nP(_1nD,_1nE));}}else{return B(_1nP(_1nD,_1nE));}}}}}}break;case 2:if(_1nD<0){return B(_1nP(_1nD,_1nE));}else{if(_1nD>=E(_1mI)){return B(_1nP(_1nD,_1nE));}else{var _1nV=_1nE-1|0;if(_1nV<0){return B(_1nP(_1nD,_1nE));}else{if(_1nV>=E(_1mK)){return B(_1nP(_1nD,_1nE));}else{if(_1nD!=_1nG){if(E(B(_6R(B(_6R(_1nF,_1nV)),_1nD)).a)==32){return B(_1nP(_1nD,_1nV));}else{return B(_1nP(_1nD,_1nE));}}else{if(_1nV!=_1nH){if(E(B(_6R(B(_6R(_1nF,_1nV)),_1nD)).a)==32){return B(_1nP(_1nD,_1nV));}else{return B(_1nP(_1nD,_1nE));}}else{return B(_1nP(_1nD,_1nE));}}}}}}break;case 3:var _1nW=_1nD+1|0;if(_1nW<0){return B(_1nP(_1nD,_1nE));}else{if(_1nW>=E(_1mI)){return B(_1nP(_1nD,_1nE));}else{if(_1nE<0){return B(_1nP(_1nD,_1nE));}else{if(_1nE>=E(_1mK)){return B(_1nP(_1nD,_1nE));}else{if(_1nW!=_1nG){if(E(B(_6R(B(_6R(_1nF,_1nE)),_1nW)).a)==32){return B(_1nP(_1nW,_1nE));}else{return B(_1nP(_1nD,_1nE));}}else{if(_1nE!=_1nH){if(E(B(_6R(B(_6R(_1nF,_1nE)),_1nW)).a)==32){return B(_1nP(_1nW,_1nE));}else{return B(_1nP(_1nD,_1nE));}}else{return B(_1nP(_1nD,_1nE));}}}}}}break;case 4:if(_1nD<0){return B(_1nP(_1nD,_1nE));}else{if(_1nD>=E(_1mI)){return B(_1nP(_1nD,_1nE));}else{var _1nX=_1nE+1|0;if(_1nX<0){return B(_1nP(_1nD,_1nE));}else{if(_1nX>=E(_1mK)){return B(_1nP(_1nD,_1nE));}else{if(_1nD!=_1nG){if(E(B(_6R(B(_6R(_1nF,_1nX)),_1nD)).a)==32){return B(_1nP(_1nD,_1nX));}else{return B(_1nP(_1nD,_1nE));}}else{if(_1nX!=_1nH){if(E(B(_6R(B(_6R(_1nF,_1nX)),_1nD)).a)==32){return B(_1nP(_1nD,_1nX));}else{return B(_1nP(_1nD,_1nE));}}else{return B(_1nP(_1nD,_1nE));}}}}}}break;default:if(_1nD<0){return B(_1nP(_1nD,_1nE));}else{if(_1nD>=E(_1mI)){return B(_1nP(_1nD,_1nE));}else{if(_1nE<0){return B(_1nP(_1nD,_1nE));}else{if(_1nE>=E(_1mK)){return B(_1nP(_1nD,_1nE));}else{if(_1nD!=_1nG){var _1nY=E(B(_6R(B(_6R(_1nF,_1nE)),_1nD)).a);return B(_1nP(_1nD,_1nE));}else{if(_1nE!=_1nH){var _1nZ=E(B(_6R(B(_6R(_1nF,_1nE)),_1nD)).a);return B(_1nP(_1nD,_1nE));}else{return B(_1nP(_1nD,_1nE));}}}}}}}}),_1o0=E(_1nJ);if(!_1o0._){return new F(function(){return _1mL(new T(function(){return E(E(_1nM).b);},1),0,_1nE+1|0,_1nO,_1nG,_1nH,_1nK);});}else{var _1o1=_1nD+1|0,_1o2=_1nE,_1o3=_1nG,_1o4=_1nH,_1o5=_1nK;_1ns=new T(function(){return E(E(_1nM).b);},1);_1nt=_1o1;_1nu=_1o2;_1nv=_1nO;_1nw=_1o3;_1nx=_1o4;_1ny=_1o0.a;_1nz=_1o0.b;_1nA=_1o5;return __continue;}}else{var _1o6=E(_1nJ);if(!_1o6._){return new F(function(){return _1mL(_1nC,0,_1nE+1|0,_1nF,_1nG,_1nH,_1nK);});}else{var _1o7=_1nC,_1o1=_1nD+1|0,_1o2=_1nE,_1o8=_1nF,_1o3=_1nG,_1o4=_1nH,_1o5=_1nK;_1ns=_1o7;_1nt=_1o1;_1nu=_1o2;_1nv=_1o8;_1nw=_1o3;_1nx=_1o4;_1ny=_1o6.a;_1nz=_1o6.b;_1nA=_1o5;return __continue;}}})(_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA));if(_1nB!=__continue){return _1nB;}}},_1mH=B(_1mL(_1lM,0,0,_1m4,_1lD,_1lE,_1m4));}var _1o9=function(_1oa){var _1ob=function(_1oc){var _1od=new T(function(){switch(E(_1lS)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1oe=new T(function(){if(!E(_1m2)){if(!E(_1od)){return new T2(0,_1lD,_1lE);}else{return new T2(0,_1lF,_1lG);}}else{if(!B(_1fM(_1fY,_1mH,_1m1))){if(!E(_1od)){return new T2(0,_1lD,_1lE);}else{return new T2(0,_1lF,_1lG);}}else{return new T2(0,_1lF,_1lG);}}}),_1of=new T(function(){return E(E(_1oe).b);}),_1og=new T(function(){return E(E(_1oe).a);});if(!E(_1m2)){var _1oh=E(_1lP);}else{var _1oh=E(B(_1iz(new T(function(){return B(_1k0(_1lK,_1lL,_1mH));}),_1mH)).a);}var _1oi=new T(function(){if(!E(_1m0)){if(!E(_1lV)){var _1oj=function(_1ok){var _1ol=function(_1om){var _1on=E(_1lS);if(_1on==4){return new T2(1,_1lA,new T2(1,_1lR,_10));}else{if(!E(_1od)){return (E(_1on)==2)?new T2(1,_1ly,new T2(1,_1lR,_10)):__Z;}else{var _1oo=E(_1lR);return (E(_1oo)==61)?new T2(1,_1lz,new T2(1,_1oo,new T(function(){return B(_I(0,_1lE,_10));}))):new T2(1,_1lz,new T2(1,_1oo,_10));}}};if(!E(_1m2)){return new F(function(){return _1ol(_);});}else{if(E(_1lF)!=E(_1og)){return new T2(1,_1lB,new T2(1,_1lR,_10));}else{if(E(_1lG)!=E(_1of)){return new T2(1,_1lB,new T2(1,_1lR,_10));}else{return new F(function(){return _1ol(_);});}}}};if(!E(_1m2)){return B(_1oj(_));}else{if(!E(_1oh)){return B(_1oj(_));}else{return E(_1lu);}}}else{return new T2(1,_1ls,new T2(1,_1lR,_10));}}else{return new T2(1,_1lt,new T2(1,_1lR,_10));}},1);return {_:0,a:new T2(0,_1og,_1of),b:_1mH,c:_1oa,d:_1oc,e:_1lK,f:_1lL,g:_1lM,h:B(_y(_1lN,_1oi)),i:_1lO,j:E(_1oh)};};if(!E(_1m0)){return new F(function(){return _1ob(_1lJ);});}else{return new F(function(){return _1ob(E(_1lR));});}};if(!E(_1lV)){return new F(function(){return _1o9(_1lI);});}else{return new F(function(){return _1o9(E(_1lR));});}},_1op=new T2(1,_5V,_10),_1oq=5,_1or=new T2(1,_1oq,_10),_1os=function(_1ot,_1ou){while(1){var _1ov=E(_1ot);if(!_1ov._){return E(_1ou);}else{_1ot=_1ov.b;_1ou=_1ov.a;continue;}}},_1ow=57,_1ox=48,_1oy=new T2(1,_1j7,_10),_1oz=new T(function(){return B(err(_sq));}),_1oA=new T(function(){return B(err(_so));}),_1oB=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_1oC=function(_1oD,_1oE){if((_1oE-48|0)>>>0>9){var _1oF=_1oE+_1oD|0,_1oG=function(_1oH){if(!B(_4B(_h7,_1oH,_1oy))){return E(_1oH);}else{return new F(function(){return _1oC(_1oD,_1oH);});}};if(_1oF<=122){if(_1oF>=97){if(_1oF>>>0>1114111){return new F(function(){return _wB(_1oF);});}else{return new F(function(){return _1oG(_1oF);});}}else{if(_1oF<=90){if(_1oF>>>0>1114111){return new F(function(){return _wB(_1oF);});}else{return new F(function(){return _1oG(_1oF);});}}else{var _1oI=65+(_1oF-90|0)|0;if(_1oI>>>0>1114111){return new F(function(){return _wB(_1oI);});}else{return new F(function(){return _1oG(_1oI);});}}}}else{var _1oJ=97+(_1oF-122|0)|0;if(_1oJ>>>0>1114111){return new F(function(){return _wB(_1oJ);});}else{return new F(function(){return _1oG(_1oJ);});}}}else{var _1oK=B(_Ga(B(_sv(_1oB,new T2(1,_1oE,_10)))));if(!_1oK._){return E(_1oA);}else{if(!E(_1oK.b)._){var _1oL=E(_1oK.a)+_1oD|0;switch(_1oL){case  -1:return E(_1ox);case 10:return E(_1ow);default:return new F(function(){return _1os(B(_I(0,_1oL,_10)),_S6);});}}else{return E(_1oz);}}}},_1oM=function(_1oN,_1oO){if((_1oN-48|0)>>>0>9){return _1oO;}else{var _1oP=B(_Ga(B(_sv(_1oB,new T2(1,_1oN,_10)))));if(!_1oP._){return E(_1oA);}else{if(!E(_1oP.b)._){return new F(function(){return _1oC(E(_1oP.a),_1oO);});}else{return E(_1oz);}}}},_1oQ=function(_1oR,_1oS){return new F(function(){return _1oM(E(_1oR),E(_1oS));});},_1oT=new T2(1,_1oQ,_10),_1oU=112,_1oV=111,_1oW=function(_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7){var _1p8=new T(function(){return B(_6R(B(_6R(_1oZ,_1oY)),E(_1oX)));}),_1p9=new T(function(){return E(E(_1p8).b);}),_1pa=new T(function(){if(E(_1p9)==4){return true;}else{return false;}}),_1pb=new T(function(){return E(E(_1p8).a);});if(E(_1p1)==32){var _1pc=false;}else{if(E(_1pb)==32){var _1pd=true;}else{var _1pd=false;}var _1pc=_1pd;}var _1pe=new T(function(){var _1pf=new T(function(){return B(A3(_6R,_1op,B(_M0(_h7,_1p0,_1j8)),_1p1));});if(!E(_1pc)){if(!E(_1pa)){return E(_1pb);}else{if(!B(_4B(_3M,_1p2,_1or))){return E(_1pb);}else{return B(A(_6R,[_1oT,B(_M0(_3M,_1p2,_1or)),_1pf,_1pb]));}}}else{return E(_1pf);}}),_1pg=B(_Kp(_1oX,_1oY,_1pe,_1p9,_1oZ));if(!E(_1pc)){var _1ph=B(_1iz(new T(function(){return B(_1k0(_1p2,_1p3,_1pg));}),_1pg)).a;return {_:0,a:new T2(0,_1oX,_1oY),b:_1pg,c:_1p0,d:_1p1,e:_1p2,f:_1p3,g:_1p4,h:B(_y(_1p5,new T(function(){if(!E(_1ph)){if(!E(_1pa)){return __Z;}else{return new T2(1,_1oU,new T2(1,_1pe,_10));}}else{return E(_1lu);}},1))),i:_1p6,j:E(_1ph)};}else{var _1pi=B(_1iz(new T(function(){return B(_1k0(_1p2,_1p3,_1pg));}),_1pg)).a;return {_:0,a:new T2(0,_1oX,_1oY),b:_1pg,c:_1p0,d:32,e:_1p2,f:_1p3,g:_1p4,h:B(_y(_1p5,new T(function(){if(!E(_1pi)){return new T2(1,_1oV,new T2(1,_1pe,_10));}else{return E(_1lu);}},1))),i:_1p6,j:E(_1pi)};}},_1pj=new T(function(){return B(_e7("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1pk=function(_1pl,_1pm){while(1){var _1pn=E(_1pm);if(!_1pn._){return false;}else{var _1po=_1pn.b,_1pp=E(_1pl),_1pq=_1pp.a,_1pr=_1pp.b,_1ps=E(_1pn.a);if(!_1ps._){return E(_1pj);}else{var _1pt=E(_1ps.a),_1pu=_1pt.a,_1pv=_1pt.b,_1pw=E(_1ps.b);if(!_1pw._){var _1px=E(_1pq),_1py=E(_1px);if(_1py==32){switch(E(_1pr)){case 0:if(!E(_1pv)){return true;}else{_1pl=new T2(0,_1px,_E6);_1pm=_1po;continue;}break;case 1:if(E(_1pv)==1){return true;}else{_1pl=new T2(0,_1px,_Ec);_1pm=_1po;continue;}break;case 2:if(E(_1pv)==2){return true;}else{_1pl=new T2(0,_1px,_Ei);_1pm=_1po;continue;}break;case 3:if(E(_1pv)==3){return true;}else{_1pl=new T2(0,_1px,_Eo);_1pm=_1po;continue;}break;case 4:if(E(_1pv)==4){return true;}else{_1pl=new T2(0,_1px,_Eu);_1pm=_1po;continue;}break;case 5:if(E(_1pv)==5){return true;}else{_1pl=new T2(0,_1px,_EV);_1pm=_1po;continue;}break;case 6:if(E(_1pv)==6){return true;}else{_1pl=new T2(0,_1px,_EO);_1pm=_1po;continue;}break;case 7:if(E(_1pv)==7){return true;}else{_1pl=new T2(0,_1px,_EH);_1pm=_1po;continue;}break;default:if(E(_1pv)==8){return true;}else{_1pl=new T2(0,_1px,_EA);_1pm=_1po;continue;}}}else{if(_1py!=E(_1pu)){_1pl=_1pp;_1pm=_1po;continue;}else{switch(E(_1pr)){case 0:if(!E(_1pv)){return true;}else{_1pl=new T2(0,_1px,_E6);_1pm=_1po;continue;}break;case 1:if(E(_1pv)==1){return true;}else{_1pl=new T2(0,_1px,_Ec);_1pm=_1po;continue;}break;case 2:if(E(_1pv)==2){return true;}else{_1pl=new T2(0,_1px,_Ei);_1pm=_1po;continue;}break;case 3:if(E(_1pv)==3){return true;}else{_1pl=new T2(0,_1px,_Eo);_1pm=_1po;continue;}break;case 4:if(E(_1pv)==4){return true;}else{_1pl=new T2(0,_1px,_Eu);_1pm=_1po;continue;}break;case 5:if(E(_1pv)==5){return true;}else{_1pl=new T2(0,_1px,_EV);_1pm=_1po;continue;}break;case 6:if(E(_1pv)==6){return true;}else{_1pl=new T2(0,_1px,_EO);_1pm=_1po;continue;}break;case 7:if(E(_1pv)==7){return true;}else{_1pl=new T2(0,_1px,_EH);_1pm=_1po;continue;}break;default:if(E(_1pv)==8){return true;}else{_1pl=new T2(0,_1px,_EA);_1pm=_1po;continue;}}}}}else{var _1pz=E(_1pq),_1pA=E(_1pz);if(_1pA==32){switch(E(_1pr)){case 0:if(!E(_1pv)){return true;}else{_1pl=new T2(0,_1pz,_E6);_1pm=new T2(1,_1pw,_1po);continue;}break;case 1:if(E(_1pv)==1){return true;}else{_1pl=new T2(0,_1pz,_Ec);_1pm=new T2(1,_1pw,_1po);continue;}break;case 2:if(E(_1pv)==2){return true;}else{_1pl=new T2(0,_1pz,_Ei);_1pm=new T2(1,_1pw,_1po);continue;}break;case 3:if(E(_1pv)==3){return true;}else{_1pl=new T2(0,_1pz,_Eo);_1pm=new T2(1,_1pw,_1po);continue;}break;case 4:if(E(_1pv)==4){return true;}else{_1pl=new T2(0,_1pz,_Eu);_1pm=new T2(1,_1pw,_1po);continue;}break;case 5:if(E(_1pv)==5){return true;}else{_1pl=new T2(0,_1pz,_EV);_1pm=new T2(1,_1pw,_1po);continue;}break;case 6:if(E(_1pv)==6){return true;}else{_1pl=new T2(0,_1pz,_EO);_1pm=new T2(1,_1pw,_1po);continue;}break;case 7:if(E(_1pv)==7){return true;}else{_1pl=new T2(0,_1pz,_EH);_1pm=new T2(1,_1pw,_1po);continue;}break;default:if(E(_1pv)==8){return true;}else{_1pl=new T2(0,_1pz,_EA);_1pm=new T2(1,_1pw,_1po);continue;}}}else{if(_1pA!=E(_1pu)){_1pl=_1pp;_1pm=new T2(1,_1pw,_1po);continue;}else{switch(E(_1pr)){case 0:if(!E(_1pv)){return true;}else{_1pl=new T2(0,_1pz,_E6);_1pm=new T2(1,_1pw,_1po);continue;}break;case 1:if(E(_1pv)==1){return true;}else{_1pl=new T2(0,_1pz,_Ec);_1pm=new T2(1,_1pw,_1po);continue;}break;case 2:if(E(_1pv)==2){return true;}else{_1pl=new T2(0,_1pz,_Ei);_1pm=new T2(1,_1pw,_1po);continue;}break;case 3:if(E(_1pv)==3){return true;}else{_1pl=new T2(0,_1pz,_Eo);_1pm=new T2(1,_1pw,_1po);continue;}break;case 4:if(E(_1pv)==4){return true;}else{_1pl=new T2(0,_1pz,_Eu);_1pm=new T2(1,_1pw,_1po);continue;}break;case 5:if(E(_1pv)==5){return true;}else{_1pl=new T2(0,_1pz,_EV);_1pm=new T2(1,_1pw,_1po);continue;}break;case 6:if(E(_1pv)==6){return true;}else{_1pl=new T2(0,_1pz,_EO);_1pm=new T2(1,_1pw,_1po);continue;}break;case 7:if(E(_1pv)==7){return true;}else{_1pl=new T2(0,_1pz,_EH);_1pm=new T2(1,_1pw,_1po);continue;}break;default:if(E(_1pv)==8){return true;}else{_1pl=new T2(0,_1pz,_EA);_1pm=new T2(1,_1pw,_1po);continue;}}}}}}}}},_1pB=function(_1pC,_1pD){var _1pE=E(_1pC);if(!_1pE._){return __Z;}else{var _1pF=E(_1pD);return (_1pF._==0)?__Z:new T2(1,new T(function(){return new T2(0,new T2(1,_1pF.a,_1f3),E(_1pE.a).b);}),new T(function(){return B(_1pB(_1pE.b,_1pF.b));}));}},_1pG=new T(function(){return B(unCStr("\n"));}),_1pH=function(_1pI,_1pJ,_){var _1pK=jsWriteHandle(E(_1pI),toJSStr(E(_1pJ)));return _gE;},_1pL=function(_1pM,_1pN,_){var _1pO=E(_1pM),_1pP=jsWriteHandle(_1pO,toJSStr(E(_1pN)));return new F(function(){return _1pH(_1pO,_1pG,_);});},_1pQ=function(_1pR){var _1pS=E(_1pR);if(!_1pS._){return __Z;}else{return new F(function(){return _y(_1pS.a,new T(function(){return B(_1pQ(_1pS.b));},1));});}},_1pT=0,_1pU= -1,_1pV= -2,_1pW=new T(function(){return B(unCStr("removed"));}),_1pX=new T(function(){return B(unCStr("loadError"));}),_1pY=new T(function(){return B(unCStr("saved"));}),_1pZ=new T(function(){var _1q0=E(_19N);if(!_1q0._){return E(_nh);}else{return E(_1q0.a);}}),_1q1=new T(function(){return B(_16A(_19l,5,_1ag));}),_1q2=new T(function(){return B(unCStr("Thank you for playing!"));}),_1q3=17,_1q4=2,_1q5=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1q6=10,_1q7=3,_1q8=new T(function(){return B(unCStr("Coding : yokoP"));}),_1q9=8,_1qa=new T(function(){return B(unCStr("Congratulations!"));}),_1qb=5,_1qc=32,_1qd=new T2(0,_1qc,_EV),_1qe=99,_1qf=64,_1qg=new T(function(){return B(_mt(_1aF,0));}),_1qh=new T(function(){return B(_6R(_j4,1));}),_1qi=new T(function(){return B(_6R(_j4,2));}),_1qj=new T(function(){return B(unCStr("loadError"));}),_1qk=new T(function(){return B(unCStr(","));}),_1ql=new T(function(){return B(unCStr("~"));}),_1qm=new T(function(){return B(unCStr("savedata"));}),_1qn=new T(function(){return B(unCStr("---"));}),_1qo=0,_1qp=new T1(0,333),_1qq=new T(function(){return B(_8s(1,2147483647));}),_1qr=new T(function(){return B(unCStr("choice"));}),_1qs=new T2(1,_6D,_10),_1qt=new T(function(){return B(_8k(_1qr,_1qs));}),_1qu=new T2(1,_6D,_1qt),_1qv=new T(function(){return B(unAppCStr("[]",_10));}),_1qw=new T(function(){return B(unCStr("\""));}),_1qx=new T2(1,_10,_10),_1qy=new T(function(){return B(_6e(_XM,_1qx));}),_1qz=new T2(1,_6D,_10),_1qA=function(_1qB){return E(_1qB).c;},_1qC=function(_1qD,_1qE){var _1qF=E(_1qE);return (_1qF._==0)?__Z:new T2(1,_1qD,new T2(1,_1qF.a,new T(function(){return B(_1qC(_1qD,_1qF.b));})));},_1qG=new T(function(){return B(unCStr("noContent"));}),_1qH=new T(function(){return B(unCStr("noHint"));}),_1qI=new T(function(){return B(err(_sq));}),_1qJ=new T(function(){return B(err(_so));}),_1qK=new T(function(){return B(A3(_Fy,_G1,_DB,_Fo));}),_1qL=function(_1qM,_1qN){var _1qO=E(_1qN);if(!_1qO._){var _1qP=B(_Ga(B(_sv(_1qK,_1qM))));return (_1qP._==0)?E(_1qJ):(E(_1qP.b)._==0)?new T4(0,E(_1qP.a),_10,_10,_10):E(_1qI);}else{var _1qQ=_1qO.a,_1qR=E(_1qO.b);if(!_1qR._){var _1qS=B(_Ga(B(_sv(_1qK,_1qM))));return (_1qS._==0)?E(_1qJ):(E(_1qS.b)._==0)?new T4(0,E(_1qS.a),E(_1qQ),E(_1qH),E(_1qG)):E(_1qI);}else{var _1qT=_1qR.a,_1qU=E(_1qR.b);if(!_1qU._){var _1qV=B(_Ga(B(_sv(_1qK,_1qM))));return (_1qV._==0)?E(_1qJ):(E(_1qV.b)._==0)?new T4(0,E(_1qV.a),E(_1qQ),E(_1qT),E(_1qG)):E(_1qI);}else{if(!E(_1qU.b)._){var _1qW=B(_Ga(B(_sv(_1qK,_1qM))));return (_1qW._==0)?E(_1qJ):(E(_1qW.b)._==0)?new T4(0,E(_1qW.a),E(_1qQ),E(_1qT),E(_1qU.a)):E(_1qI);}else{return new T4(0,0,_10,_10,_10);}}}}},_1qX=function(_1qY){var _1qZ=E(_1qY);if(!_1qZ._){return new F(function(){return _1qL(_10,_10);});}else{var _1r0=_1qZ.a,_1r1=E(_1qZ.b);if(!_1r1._){return new F(function(){return _1qL(new T2(1,_1r0,_10),_10);});}else{var _1r2=E(_1r0),_1r3=new T(function(){var _1r4=B(_H2(44,_1r1.a,_1r1.b));return new T2(0,_1r4.a,_1r4.b);});if(E(_1r2)==44){return new F(function(){return _1qL(_10,new T2(1,new T(function(){return E(E(_1r3).a);}),new T(function(){return E(E(_1r3).b);})));});}else{var _1r5=E(_1r3);return new F(function(){return _1qL(new T2(1,_1r2,_1r5.a),_1r5.b);});}}}},_1r6=function(_1r7){var _1r8=B(_1qX(_1r7));return new T4(0,_1r8.a,E(_1r8.b),E(_1r8.c),E(_1r8.d));},_1r9=function(_1ra){return (E(_1ra)==10)?true:false;},_1rb=function(_1rc){var _1rd=E(_1rc);if(!_1rd._){return __Z;}else{var _1re=new T(function(){var _1rf=B(_173(_1r9,_1rd));return new T2(0,_1rf.a,new T(function(){var _1rg=E(_1rf.b);if(!_1rg._){return __Z;}else{return B(_1rb(_1rg.b));}}));});return new T2(1,new T(function(){return E(E(_1re).a);}),new T(function(){return E(E(_1re).b);}));}},_1rh=new T(function(){return B(unCStr("57,\u5974\u56fd\u738b\u304c\u5f8c\u6f22\u304b\u3089\u91d1\u5370,\u300c\u5f8c\u6f22\u66f8\u300d\u306b\u8a18\u8f09\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\u8cc0\u5cf6\u306b\u3066\u300c\u6f22\u59d4\u5974\u570b\u738b\u300d\u3068\u523b\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\u898b\u3055\u308c\u308b**\u5927\u548c\u671d\u5ef7\u3068\u306e\u95dc\u4fc2\u306f\u4e0d\u660e\n239,\u300c\u5351\u5f25\u547c\u300d\u304c\u9b4f\u306b\u9063\u4f7f,\u652f\u90a3\u306e\u6b74\u53f2\u66f8\u300c\u9b4f\u5fd7\u300d\u306b\u8a18\u8f09\u3055\u308c\u3066\u3090\u308b\u5deb\u5973,\u300c\u9b4f\u5fd7\u300d\u502d\u4eba\u4f1d\u306b\u8a18\u3055\u308c\u3066\u3090\u308b\u300c\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)\u300d\u3082\u300c\u5351\u5f25\u547c\u300d\u3082\u65e5\u672c\u306b\u6b98\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\u5fb3\u5929\u7687 \u7a0e\u3092\u514d\u9664,\u300c\u53e4\u4e8b\u8a18\u300d\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u8a18\u8f09\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c\u300c\u6c11\u306e\u304b\u307e\u3069\u3088\u308a\u7159\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\u3057\u304f\u3066\u708a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b\u300d\u3068\u3057\u3066 \u5bae\u4e2d\u306e\u4fee\u7e55\u3092\u5f8c\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\u304b\u306b\u3059\u308b\u8a71\u304c\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u3042\u308b\n478,\u300c\u502d\u300d\u306e\u6b66\u738b \u5357\u671d\u306e\u5b8b\u3078\u9063\u4f7f,\u96c4\u7565\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\u8aac,\u300c\u5b8b\u66f8\u300d\u502d\u570b\u50b3\u306b\u8a18\u8f09\u304c\u3042\u308b**\u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\u6559\u516c\u4f1d,\u6b3d\u660e\u5929\u7687\u5fa1\u4ee3\u306b\u767e\u6e08\u306e\u8056\u660e\u738b\u304b\u3089\u4f1d\u6765\u3057\u305f\u3068\u306e\u6587\u732e\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\u8aac\u3042\u308b\n604,\u5341\u4e03\u6761\u61b2\u6cd5\u5236\u5b9a,\u8056\u5fb3\u592a\u5b50\u304c\u5236\u5b9a\u3057\u305f\u3068\u3055\u308c\u308b,\u300c\u548c\u3092\u4ee5\u3066\u8cb4\u3057\u3068\u70ba\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\u304d\u3092\u5b97\u3068\u305b\u3088\u300d\n607,\u6cd5\u9686\u5bfa\u304c\u5275\u5efa\u3055\u308c\u308b,\u8056\u5fb3\u592a\u5b50\u3086\u304b\u308a\u306e\u5bfa\u9662,\u897f\u9662\u4f3d\u85cd\u306f\u73fe\u5b58\u3059\u308b\u4e16\u754c\u6700\u53e4\u306e\u6728\u9020\u5efa\u7bc9\u7269\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\u5df3\u306e\u5909,\u3053\u306e\u5f8c\u3059\u3050\u5927\u5316\u306e\u6539\u65b0\u306a\u308b,\u4e2d\u5927\u5144\u7687\u5b50(\u5f8c\u306e38\u4ee3\u5929\u667a\u5929\u7687)\u304c\u8607\u6211\u6c0f\u3092\u4ea1\u307c\u3059\n663,\u767d\u6751\u6c5f\u306e\u6226,\u5510\u3068\u65b0\u7f85\u306b\u6ec5\u307c\u3055\u308c\u305f\u767e\u6e08\u3092\u518d\u8208\u3059\u308b\u76ee\u7684,\u5510\u30fb\u65b0\u7f85\u9023\u5408\u8ecd\u306b\u6557\u308c\u308b\n672,\u58ec\u7533\u306e\u4e71,\u5929\u667a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\u7d99\u8005\u4e89\u3072,\u5f8c\u7d99\u8005\u3067\u3042\u3063\u305f\u5927\u53cb\u7687\u5b50\u306b\u53d4\u7236\u306e\u5927\u6d77\u4eba\u7687\u5b50\u304c\u53cd\u65d7\u3092\u7ffb\u3057 \u5927\u53cb\u7687\u5b50\u3092\u5012\u3057\u3066\u5929\u6b66\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f\u300c\u306a\u3089\u300d\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b\u300c\u82b1\u306e\u5fa1\u6240\u300d\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089\u300c\u5ba4\u753a\u5e55\u5e9c\u300d\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075\u300c\u4e0b\u524b\u4e0a\u300d\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d \u300c\u5929\u4e0b\u5e03\u6b66\u300d\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b\u300c\u9396\u56fd\u300d\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c\u300c\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4\u300d\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1ri=new T(function(){return B(_1rb(_1rh));}),_1rj=new T(function(){return B(_6e(_1r6,_1ri));}),_1rk=new T(function(){return B(_8P(1,2));}),_1rl=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b\u300c\u4e0d\u5e73\u7b49\u300d\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,\u300c\u6276\u6e05\u6ec5\u6d0b\u300d\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***\u300c\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287\u300d\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b\u300c\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42\u300d,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059\u300d\u30fc\u30fc\u5f8c\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059\u300d"));}),_1rm=new T(function(){return B(_1rb(_1rl));}),_1rn=new T(function(){return B(_6e(_1r6,_1rm));}),_1ro=function(_1rp,_1rq){var _1rr=E(_1rp);if(!_1rr._){return __Z;}else{var _1rs=E(_1rq);return (_1rs._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1rr.a).a;}),_1rs.a),new T(function(){return B(_1ro(_1rr.b,_1rs.b));}));}},_1rt=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1ru=new T(function(){return B(unCStr("tail"));}),_1rv=new T(function(){return B(_ne(_1ru));}),_1rw=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1rx=new T2(1,_2B,_10),_1ry=function(_1rz,_1rA){return new T2(1,_6D,new T(function(){return B(_8k(_1rz,new T2(1,_6D,_1rA)));}));},_1rB=function(_1rC){var _1rD=E(_1rC);if(!_1rD._){return E(_1rx);}else{var _1rE=new T(function(){var _1rF=E(_1rD.a),_1rG=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1rH){return new F(function(){return _1ry(_1rF.a,_1rH);});},new T2(1,function(_1rI){return new F(function(){return _1ry(_1rF.b,_1rI);});},_10)),new T2(1,_G,new T(function(){return B(_1rB(_1rD.b));}))));});return new T2(1,_H,_1rG);});return new T2(1,_2A,_1rE);}},_1rJ=function(_1rK){var _1rL=E(_1rK);if(!_1rL._){return E(_1rx);}else{var _1rM=new T(function(){return B(_I(0,E(_1rL.a),new T(function(){return B(_1rJ(_1rL.b));})));});return new T2(1,_2A,_1rM);}},_1rN=function(_1rO){var _1rP=E(_1rO);if(!_1rP._){return E(_1rx);}else{var _1rQ=new T(function(){var _1rR=E(_1rP.a),_1rS=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1rT){return new F(function(){return _1ry(_1rR.a,_1rT);});},new T2(1,function(_1rU){return new F(function(){return _1ry(_1rR.b,_1rU);});},_10)),new T2(1,_G,new T(function(){return B(_1rN(_1rP.b));}))));});return new T2(1,_H,_1rS);});return new T2(1,_2A,_1rQ);}},_1rV=new T(function(){return B(unCStr("True"));}),_1rW=new T(function(){return B(unCStr("False"));}),_1rX=function(_1rY){return E(E(_1rY).b);},_1rZ=function(_1s0,_1s1,_1s2){var _1s3=new T(function(){var _1s4=E(_1s2);if(!_1s4._){return __Z;}else{var _1s5=_1s4.b,_1s6=E(_1s4.a),_1s7=E(_1s6.a);if(_1s7<_1s0){var _1s8=function(_1s9){while(1){var _1sa=B((function(_1sb){var _1sc=E(_1sb);if(!_1sc._){return __Z;}else{var _1sd=_1sc.b,_1se=E(_1sc.a);if(E(_1se.a)<_1s0){_1s9=_1sd;return __continue;}else{return new T2(1,_1se,new T(function(){return B(_1s8(_1sd));}));}}})(_1s9));if(_1sa!=__continue){return _1sa;}}};return B(_1sf(B(_1s8(_1s5))));}else{var _1sg=new T(function(){var _1sh=function(_1si){while(1){var _1sj=B((function(_1sk){var _1sl=E(_1sk);if(!_1sl._){return __Z;}else{var _1sm=_1sl.b,_1sn=E(_1sl.a);if(E(_1sn.a)<_1s0){_1si=_1sm;return __continue;}else{return new T2(1,_1sn,new T(function(){return B(_1sh(_1sm));}));}}})(_1si));if(_1sj!=__continue){return _1sj;}}};return B(_1sh(_1s5));});return B(_1rZ(_1s7,_1s6.b,_1sg));}}}),_1so=E(_1s2);if(!_1so._){return new F(function(){return _y(_10,new T2(1,new T2(0,_1s0,_1s1),_1s3));});}else{var _1sp=_1so.b,_1sq=E(_1so.a),_1sr=E(_1sq.a);if(_1sr>=_1s0){var _1ss=function(_1st){while(1){var _1su=B((function(_1sv){var _1sw=E(_1sv);if(!_1sw._){return __Z;}else{var _1sx=_1sw.b,_1sy=E(_1sw.a);if(E(_1sy.a)>=_1s0){_1st=_1sx;return __continue;}else{return new T2(1,_1sy,new T(function(){return B(_1ss(_1sx));}));}}})(_1st));if(_1su!=__continue){return _1su;}}};return new F(function(){return _y(B(_1sf(B(_1ss(_1sp)))),new T2(1,new T2(0,_1s0,_1s1),_1s3));});}else{var _1sz=new T(function(){var _1sA=function(_1sB){while(1){var _1sC=B((function(_1sD){var _1sE=E(_1sD);if(!_1sE._){return __Z;}else{var _1sF=_1sE.b,_1sG=E(_1sE.a);if(E(_1sG.a)>=_1s0){_1sB=_1sF;return __continue;}else{return new T2(1,_1sG,new T(function(){return B(_1sA(_1sF));}));}}})(_1sB));if(_1sC!=__continue){return _1sC;}}};return B(_1sA(_1sp));});return new F(function(){return _y(B(_1rZ(_1sr,_1sq.b,_1sz)),new T2(1,new T2(0,_1s0,_1s1),_1s3));});}}},_1sf=function(_1sH){var _1sI=E(_1sH);if(!_1sI._){return __Z;}else{var _1sJ=_1sI.b,_1sK=E(_1sI.a),_1sL=_1sK.a,_1sM=new T(function(){var _1sN=E(_1sJ);if(!_1sN._){return __Z;}else{var _1sO=_1sN.b,_1sP=E(_1sN.a),_1sQ=E(_1sP.a),_1sR=E(_1sL);if(_1sQ<_1sR){var _1sS=function(_1sT){while(1){var _1sU=B((function(_1sV){var _1sW=E(_1sV);if(!_1sW._){return __Z;}else{var _1sX=_1sW.b,_1sY=E(_1sW.a);if(E(_1sY.a)<_1sR){_1sT=_1sX;return __continue;}else{return new T2(1,_1sY,new T(function(){return B(_1sS(_1sX));}));}}})(_1sT));if(_1sU!=__continue){return _1sU;}}};return B(_1sf(B(_1sS(_1sO))));}else{var _1sZ=new T(function(){var _1t0=function(_1t1){while(1){var _1t2=B((function(_1t3){var _1t4=E(_1t3);if(!_1t4._){return __Z;}else{var _1t5=_1t4.b,_1t6=E(_1t4.a);if(E(_1t6.a)<_1sR){_1t1=_1t5;return __continue;}else{return new T2(1,_1t6,new T(function(){return B(_1t0(_1t5));}));}}})(_1t1));if(_1t2!=__continue){return _1t2;}}};return B(_1t0(_1sO));});return B(_1rZ(_1sQ,_1sP.b,_1sZ));}}}),_1t7=E(_1sJ);if(!_1t7._){return new F(function(){return _y(_10,new T2(1,_1sK,_1sM));});}else{var _1t8=_1t7.b,_1t9=E(_1t7.a),_1ta=E(_1t9.a),_1tb=E(_1sL);if(_1ta>=_1tb){var _1tc=function(_1td){while(1){var _1te=B((function(_1tf){var _1tg=E(_1tf);if(!_1tg._){return __Z;}else{var _1th=_1tg.b,_1ti=E(_1tg.a);if(E(_1ti.a)>=_1tb){_1td=_1th;return __continue;}else{return new T2(1,_1ti,new T(function(){return B(_1tc(_1th));}));}}})(_1td));if(_1te!=__continue){return _1te;}}};return new F(function(){return _y(B(_1sf(B(_1tc(_1t8)))),new T2(1,_1sK,_1sM));});}else{var _1tj=new T(function(){var _1tk=function(_1tl){while(1){var _1tm=B((function(_1tn){var _1to=E(_1tn);if(!_1to._){return __Z;}else{var _1tp=_1to.b,_1tq=E(_1to.a);if(E(_1tq.a)>=_1tb){_1tl=_1tp;return __continue;}else{return new T2(1,_1tq,new T(function(){return B(_1tk(_1tp));}));}}})(_1tl));if(_1tm!=__continue){return _1tm;}}};return B(_1tk(_1t8));});return new F(function(){return _y(B(_1rZ(_1ta,_1t9.b,_1tj)),new T2(1,_1sK,_1sM));});}}}},_1tr=function(_){return new F(function(){return jsMkStdout();});},_1ts=new T(function(){return B(_3(_1tr));}),_1tt=new T(function(){return B(_KQ("Browser.hs:82:24-56|(Right j)"));}),_1tu=function(_1tv){var _1tw=jsParseJSON(toJSStr(E(_1tv)));return (_1tw._==0)?E(_1tt):E(_1tw.a);},_1tx=function(_1ty,_1tz,_1tA,_1tB,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1tM,_1tN,_1tO,_1tP,_1tQ,_1tR,_1tS,_1tT,_1tU,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_1u1,_1u2,_1u3,_1u4,_1u5,_1u6,_1u7,_1u8,_1u9,_1ua,_){var _1ub={_:0,a:E(_1u2),b:E(_1u3),c:E(_1u4),d:E(_1u5),e:E(_1u6),f:E(_1u7),g:E(_1u8),h:E(_1u9)},_1uc=new T2(0,_1tT,_1tU),_1ud=new T2(0,_1tM,_1tN),_1ue={_:0,a:E(_1tC),b:E(_1tD),c:_1tE,d:_1tF,e:_1tG,f:E(_1tH),g:_1tI,h:E(_1tJ),i:E(_1tK),j:E(_1tL)};if(!E(_1u7)){var _1uf=function(_1ug){var _1uh=new T(function(){var _1ui=E(_1tz)/16,_1uj=_1ui&4294967295;if(_1ui>=_1uj){return _1uj-2|0;}else{return (_1uj-1|0)-2|0;}});if(!E(_1u5)){if(!E(_1u9)){return {_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E(_1ub),q:E(_1ua)};}else{var _1uk=function(_,_1ul,_1um,_1un,_1uo,_1up,_1uq,_1ur,_1us,_1ut,_1uu,_1uv,_1uw,_1ux,_1uy,_1uz,_1uA,_1uB,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK){var _1uL=function(_){var _1uM=function(_){var _1uN=function(_){var _1uO=B(_1pL(_1ts,new T2(1,_6D,new T(function(){return B(_8k(_1us,_1qz));})),_)),_1uP=function(_){var _1uQ=B(_1pL(_1ts,B(_I(0,_1tY,_10)),_)),_1uR=B(_12K(_1qb,_1ur,_)),_1uS=E(_1ty),_1uT=_1uS.a,_1uU=_1uS.b,_1uV=new T(function(){return B(_1fJ(E(_1tB)));}),_1uW=new T(function(){var _1uX=function(_1uY,_1uZ){var _1v0=E(_1ul);return new F(function(){return _1lC(_1uY,_1uZ,_1v0.a,_1v0.b,_1um,_1un,_1uo,_1up,_1uq,_1ur,_1us,_1ut,_1uu);});};switch(E(_1uV)){case 72:var _1v1=E(_1ul),_1v2=_1v1.a,_1v3=E(_1v1.b);if(0<=(_1v3-1|0)){var _1v4=B(_1uX(E(_1v2),_1v3-1|0));return {_:0,a:E(_1v4.a),b:E(_1v4.b),c:_1v4.c,d:_1v4.d,e:_1v4.e,f:E(_1v4.f),g:_1v4.g,h:E(_1v4.h),i:E(_1v4.i),j:E(_1v4.j)};}else{var _1v5=B(_1uX(E(_1v2),_1v3));return {_:0,a:E(_1v5.a),b:E(_1v5.b),c:_1v5.c,d:_1v5.d,e:_1v5.e,f:E(_1v5.f),g:_1v5.g,h:E(_1v5.h),i:E(_1v5.i),j:E(_1v5.j)};}break;case 75:var _1v6=E(_1ul),_1v7=_1v6.b,_1v8=E(_1v6.a);if(0<=(_1v8-1|0)){var _1v9=B(_1uX(_1v8-1|0,E(_1v7)));return {_:0,a:E(_1v9.a),b:E(_1v9.b),c:_1v9.c,d:_1v9.d,e:_1v9.e,f:E(_1v9.f),g:_1v9.g,h:E(_1v9.h),i:E(_1v9.i),j:E(_1v9.j)};}else{var _1va=B(_1uX(_1v8,E(_1v7)));return {_:0,a:E(_1va.a),b:E(_1va.b),c:_1va.c,d:_1va.d,e:_1va.e,f:E(_1va.f),g:_1va.g,h:E(_1va.h),i:E(_1va.i),j:E(_1va.j)};}break;case 77:var _1vb=E(_1ul),_1vc=_1vb.b,_1vd=E(_1vb.a);if(E(_1tM)!=(_1vd+1|0)){var _1ve=B(_1uX(_1vd+1|0,E(_1vc)));return {_:0,a:E(_1ve.a),b:E(_1ve.b),c:_1ve.c,d:_1ve.d,e:_1ve.e,f:E(_1ve.f),g:_1ve.g,h:E(_1ve.h),i:E(_1ve.i),j:E(_1ve.j)};}else{var _1vf=B(_1uX(_1vd,E(_1vc)));return {_:0,a:E(_1vf.a),b:E(_1vf.b),c:_1vf.c,d:_1vf.d,e:_1vf.e,f:E(_1vf.f),g:_1vf.g,h:E(_1vf.h),i:E(_1vf.i),j:E(_1vf.j)};}break;case 80:var _1vg=E(_1ul),_1vh=_1vg.a,_1vi=E(_1vg.b);if(E(_1tN)!=(_1vi+1|0)){var _1vj=B(_1uX(E(_1vh),_1vi+1|0));return {_:0,a:E(_1vj.a),b:E(_1vj.b),c:_1vj.c,d:_1vj.d,e:_1vj.e,f:E(_1vj.f),g:_1vj.g,h:E(_1vj.h),i:E(_1vj.i),j:E(_1vj.j)};}else{var _1vk=B(_1uX(E(_1vh),_1vi));return {_:0,a:E(_1vk.a),b:E(_1vk.b),c:_1vk.c,d:_1vk.d,e:_1vk.e,f:E(_1vk.f),g:_1vk.g,h:E(_1vk.h),i:E(_1vk.i),j:E(_1vk.j)};}break;case 104:var _1vl=E(_1ul),_1vm=_1vl.b,_1vn=E(_1vl.a);if(0<=(_1vn-1|0)){var _1vo=B(_1uX(_1vn-1|0,E(_1vm)));return {_:0,a:E(_1vo.a),b:E(_1vo.b),c:_1vo.c,d:_1vo.d,e:_1vo.e,f:E(_1vo.f),g:_1vo.g,h:E(_1vo.h),i:E(_1vo.i),j:E(_1vo.j)};}else{var _1vp=B(_1uX(_1vn,E(_1vm)));return {_:0,a:E(_1vp.a),b:E(_1vp.b),c:_1vp.c,d:_1vp.d,e:_1vp.e,f:E(_1vp.f),g:_1vp.g,h:E(_1vp.h),i:E(_1vp.i),j:E(_1vp.j)};}break;case 106:var _1vq=E(_1ul),_1vr=_1vq.a,_1vs=E(_1vq.b);if(E(_1tN)!=(_1vs+1|0)){var _1vt=B(_1uX(E(_1vr),_1vs+1|0));return {_:0,a:E(_1vt.a),b:E(_1vt.b),c:_1vt.c,d:_1vt.d,e:_1vt.e,f:E(_1vt.f),g:_1vt.g,h:E(_1vt.h),i:E(_1vt.i),j:E(_1vt.j)};}else{var _1vu=B(_1uX(E(_1vr),_1vs));return {_:0,a:E(_1vu.a),b:E(_1vu.b),c:_1vu.c,d:_1vu.d,e:_1vu.e,f:E(_1vu.f),g:_1vu.g,h:E(_1vu.h),i:E(_1vu.i),j:E(_1vu.j)};}break;case 107:var _1vv=E(_1ul),_1vw=_1vv.a,_1vx=E(_1vv.b);if(0<=(_1vx-1|0)){var _1vy=B(_1uX(E(_1vw),_1vx-1|0));return {_:0,a:E(_1vy.a),b:E(_1vy.b),c:_1vy.c,d:_1vy.d,e:_1vy.e,f:E(_1vy.f),g:_1vy.g,h:E(_1vy.h),i:E(_1vy.i),j:E(_1vy.j)};}else{var _1vz=B(_1uX(E(_1vw),_1vx));return {_:0,a:E(_1vz.a),b:E(_1vz.b),c:_1vz.c,d:_1vz.d,e:_1vz.e,f:E(_1vz.f),g:_1vz.g,h:E(_1vz.h),i:E(_1vz.i),j:E(_1vz.j)};}break;case 108:var _1vA=E(_1ul),_1vB=_1vA.b,_1vC=E(_1vA.a);if(E(_1tM)!=(_1vC+1|0)){var _1vD=B(_1uX(_1vC+1|0,E(_1vB)));return {_:0,a:E(_1vD.a),b:E(_1vD.b),c:_1vD.c,d:_1vD.d,e:_1vD.e,f:E(_1vD.f),g:_1vD.g,h:E(_1vD.h),i:E(_1vD.i),j:E(_1vD.j)};}else{var _1vE=B(_1uX(_1vC,E(_1vB)));return {_:0,a:E(_1vE.a),b:E(_1vE.b),c:_1vE.c,d:_1vE.d,e:_1vE.e,f:E(_1vE.f),g:_1vE.g,h:E(_1vE.h),i:E(_1vE.i),j:E(_1vE.j)};}break;default:var _1vF=E(_1ul),_1vG=B(_1uX(E(_1vF.a),E(_1vF.b)));return {_:0,a:E(_1vG.a),b:E(_1vG.b),c:_1vG.c,d:_1vG.d,e:_1vG.e,f:E(_1vG.f),g:_1vG.g,h:E(_1vG.h),i:E(_1vG.i),j:E(_1vG.j)};}}),_1vH=new T(function(){if(E(_1uV)==32){var _1vI=E(_1uW),_1vJ=E(_1vI.a),_1vK=B(_1oW(_1vJ.a,E(_1vJ.b),_1vI.b,_1vI.c,_1vI.d,_1vI.e,_1vI.f,_1vI.g,_1vI.h,_1vI.i,_1vI.j));return {_:0,a:E(_1vK.a),b:E(_1vK.b),c:_1vK.c,d:_1vK.d,e:_1vK.e,f:E(_1vK.f),g:_1vK.g,h:E(_1vK.h),i:E(_1vK.i),j:E(_1vK.j)};}else{return E(_1uW);}}),_1vL=new T(function(){var _1vM=E(_1vH),_1vN=_1vM.h,_1vO=B(_1cO(_1qo,_1vN,_1uy,{_:0,a:E(_1vM.a),b:E(_1vM.b),c:_1vM.c,d:_1vM.d,e:_1vM.e,f:E(_1vM.f),g:E(E(_1uR).b),h:E(_1vN),i:E(_1vM.i),j:E(_1vM.j)},_1uv,_1uw,_1ux,_1uy,_1uz,_1uA,_1uB,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK));return {_:0,a:E(_1vO.a),b:E(_1vO.b),c:E(_1vO.c),d:E(_1vO.d),e:E(_1vO.e),f:E(_1vO.f),g:E(_1vO.g),h:E(_1vO.h),i:_1vO.i,j:_1vO.j,k:_1vO.k,l:_1vO.l,m:E(_1vO.m),n:_1vO.n,o:E(_1vO.o),p:E(_1vO.p),q:E(_1vO.q)};}),_1vP=B(_nq(_1uT,_1uU,new T(function(){return E(_1uh)-E(E(E(_1vL).b).a)|0;}),_nP,new T(function(){return E(E(E(_1vL).a).b);}),_)),_1vQ=E(_1uV),_1vR=function(_,_1vS){var _1vT=function(_1vU){var _1vV=B(_1pL(_1ts,B(_8q(_1vS)),_)),_1vW=E(_1vL),_1vX=_1vW.d,_1vY=_1vW.e,_1vZ=_1vW.f,_1w0=_1vW.g,_1w1=_1vW.i,_1w2=_1vW.j,_1w3=_1vW.k,_1w4=_1vW.l,_1w5=_1vW.m,_1w6=_1vW.n,_1w7=_1vW.o,_1w8=_1vW.q,_1w9=E(_1vW.p),_1wa=_1w9.a,_1wb=_1w9.d,_1wc=_1w9.e,_1wd=_1w9.f,_1we=_1w9.g,_1wf=_1w9.h,_1wg=E(_1vW.a),_1wh=_1wg.e,_1wi=_1wg.f,_1wj=_1wg.g,_1wk=E(_1vW.h),_1wl=function(_1wm){var _1wn=function(_1wo){if(_1wo!=E(_1qg)){var _1wp=B(_6R(_19r,_1wo)),_1wq=_1wp.a,_1wr=E(_1wp.b),_1ws=B(_16A(_1wq,_1wr,new T(function(){return B(_6R(_1aF,_1wo));})));return new F(function(){return _1tx(_1uS,_1tz,_1tA,_1qf,B(_6R(_19A,_1wo)),_1ws,B(_6R(_19N,_1wo)),32,_1wo,_1wi,_1wj,B(_y(_1wg.h,new T2(1,_1qe,new T(function(){return B(_I(0,_1wh,_10));})))),B(_1pk(_1qd,_1ws)),_wq,_1wq,_1wr,_10,_1vX,_1vY,_1vZ,_1w0,_1wk.a,_1wk.b,_1w1,_1w2,_1w3, -1,_1w5,_1w6,_1w7,_wq,_wq,_wq,_1wb,_1wc,_1wd,_1we,_1wf,_1w8,_);});}else{var _1wt=__app1(E(_ni),_1uU),_1wu=B(A2(_nj,_1uT,_)),_1wv=B(A(_mO,[_1uT,_j3,_1q4,_1qb,_1qa,_])),_1ww=B(A(_mO,[_1uT,_j3,_1q7,_1q9,_1q8,_])),_1wx=B(A(_mO,[_1uT,_j3,_1q7,_1q6,_1q5,_])),_1wy=B(A(_mO,[_1uT,_j3,_1q4,_1q3,_1q2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_19w),b:E(_1q1),c:E(_1pZ),d:32,e:0,f:E(_1wi),g:_1wj,h:E(_10),i:E(_1wg.i),j:E(_wq)}),b:E(_19o),c:E(_1vW.c),d:E(_1vX),e:E(_1vY),f:E(_1vZ),g:E(_1w0),h:E(_1wk),i:_1w1,j:_1w2,k:_1w3,l:_1w4,m:E(_1w5),n:_1w6,o:E(_1w7),p:E({_:0,a:E(_1wa),b:E(_wq),c:E(_wq),d:E(_1wb),e:E(_1wc),f:E(_1wd),g:E(_1we),h:E(_1wf)}),q:E(_1w8)};});}};if(_1w4>=0){return new F(function(){return _1wn(_1w4);});}else{return new F(function(){return _1wn(_1wh+1|0);});}};if(!E(_1wa)){if(E(_1vQ)==110){return new F(function(){return _1wl(_);});}else{var _1wz=new T(function(){return E(E(_1uW).a);});if(E(_1wg.d)==32){var _1wA=B(A(_mO,[_1uT,_1qh,new T(function(){return (E(E(_1wz).a)+1|0)+(E(_1uh)-E(_1tM)|0)|0;},1),new T(function(){return (E(E(_1wz).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1qA(_1vH));}),_10),_]));return _1vW;}else{var _1wB=B(A(_mO,[_1uT,_1qi,new T(function(){return (E(E(_1wz).a)+1|0)+(E(_1uh)-E(_1tM)|0)|0;},1),new T(function(){return (E(E(_1wz).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1qA(_1vH));}),_10),_]));return _1vW;}}}else{return new F(function(){return _1wl(_);});}};if(E(_1vQ)==114){if(!B(_69(_1vS,_1qj))){var _1wC=E(_1vS);if(!_1wC._){return _1vL;}else{var _1wD=_1wC.b;return new T(function(){var _1wE=E(_1vL),_1wF=E(_1wE.a),_1wG=E(_1wC.a),_1wH=E(_1wG);if(_1wH==34){var _1wI=B(_QD(_1wG,_1wD));if(!_1wI._){var _1wJ=E(_1rv);}else{var _1wK=E(_1wI.b);if(!_1wK._){var _1wL=E(_1qx);}else{var _1wM=_1wK.a,_1wN=E(_1wK.b);if(!_1wN._){var _1wO=new T2(1,new T2(1,_1wM,_10),_10);}else{var _1wP=E(_1wM),_1wQ=new T(function(){var _1wR=B(_H2(126,_1wN.a,_1wN.b));return new T2(0,_1wR.a,_1wR.b);});if(E(_1wP)==126){var _1wS=new T2(1,_10,new T2(1,new T(function(){return E(E(_1wQ).a);}),new T(function(){return E(E(_1wQ).b);})));}else{var _1wS=new T2(1,new T2(1,_1wP,new T(function(){return E(E(_1wQ).a);})),new T(function(){return E(E(_1wQ).b);}));}var _1wO=_1wS;}var _1wL=_1wO;}var _1wJ=_1wL;}var _1wT=_1wJ;}else{var _1wU=E(_1wD);if(!_1wU._){var _1wV=new T2(1,new T2(1,_1wG,_10),_10);}else{var _1wW=new T(function(){var _1wX=B(_H2(126,_1wU.a,_1wU.b));return new T2(0,_1wX.a,_1wX.b);});if(E(_1wH)==126){var _1wY=new T2(1,_10,new T2(1,new T(function(){return E(E(_1wW).a);}),new T(function(){return E(E(_1wW).b);})));}else{var _1wY=new T2(1,new T2(1,_1wG,new T(function(){return E(E(_1wW).a);})),new T(function(){return E(E(_1wW).b);}));}var _1wV=_1wY;}var _1wT=_1wV;}var _1wZ=B(_Ga(B(_sv(_XL,new T(function(){return B(_J2(_1wT));})))));if(!_1wZ._){return E(_XJ);}else{if(!E(_1wZ.b)._){var _1x0=E(_1wZ.a),_1x1=B(_6R(_19r,_1x0)),_1x2=B(_6R(_1wT,1));if(!_1x2._){var _1x3=__Z;}else{var _1x4=E(_1x2.b);if(!_1x4._){var _1x5=__Z;}else{var _1x6=E(_1x2.a),_1x7=new T(function(){var _1x8=B(_H2(44,_1x4.a,_1x4.b));return new T2(0,_1x8.a,_1x8.b);});if(E(_1x6)==44){var _1x9=B(_XB(_10,new T(function(){return E(E(_1x7).a);}),new T(function(){return E(E(_1x7).b);})));}else{var _1x9=B(_XF(new T2(1,_1x6,new T(function(){return E(E(_1x7).a);})),new T(function(){return E(E(_1x7).b);})));}var _1x5=_1x9;}var _1x3=_1x5;}var _1xa=B(_6R(_1wT,2));if(!_1xa._){var _1xb=E(_1qy);}else{var _1xc=_1xa.a,_1xd=E(_1xa.b);if(!_1xd._){var _1xe=B(_6e(_XM,new T2(1,new T2(1,_1xc,_10),_10)));}else{var _1xf=E(_1xc),_1xg=new T(function(){var _1xh=B(_H2(44,_1xd.a,_1xd.b));return new T2(0,_1xh.a,_1xh.b);});if(E(_1xf)==44){var _1xi=B(_6e(_XM,new T2(1,_10,new T2(1,new T(function(){return E(E(_1xg).a);}),new T(function(){return E(E(_1xg).b);})))));}else{var _1xi=B(_6e(_XM,new T2(1,new T2(1,_1xf,new T(function(){return E(E(_1xg).a);})),new T(function(){return E(E(_1xg).b);}))));}var _1xe=_1xi;}var _1xb=_1xe;}return {_:0,a:E({_:0,a:E(B(_6R(_19A,_1x0))),b:E(B(_16A(_1x1.a,E(_1x1.b),new T(function(){return B(_6R(_1aF,_1x0));})))),c:B(_6R(_19N,_1x0)),d:32,e:_1x0,f:E(_1wF.f),g:_1wF.g,h:E(_1wF.h),i:E(_1wF.i),j:E(_1wF.j)}),b:E(_1x1),c:E(_1wE.c),d:E(_1wE.d),e:E(_1x3),f:E(_1xb),g:E(_1wE.g),h:E(_1wE.h),i:_1wE.i,j:_1wE.j,k:_1wE.k,l:_1wE.l,m:E(_1wE.m),n:_1wE.n,o:E(_1wE.o),p:E(_1wE.p),q:E(_1wE.q)};}else{return E(_XK);}}});}}else{return new F(function(){return _1vT(_);});}}else{return new F(function(){return _1vT(_);});}};switch(E(_1vQ)){case 100:var _1xj=__app1(E(_1rt),toJSStr(E(_1qm)));return new F(function(){return _1vR(_,_1pW);});break;case 114:var _1xk=B(_XW(_6w,toJSStr(E(_1qm)),_));return new F(function(){return _1vR(_,new T(function(){var _1xl=E(_1xk);if(!_1xl._){return E(_1pX);}else{return fromJSStr(B(_1eT(_1xl.a)));}}));});break;case 115:var _1xm=new T(function(){var _1xn=new T(function(){var _1xo=new T(function(){var _1xp=B(_6e(_6B,_1tR));if(!_1xp._){return __Z;}else{return B(_1pQ(new T2(1,_1xp.a,new T(function(){return B(_1qC(_1qk,_1xp.b));}))));}}),_1xq=new T(function(){var _1xr=function(_1xs){var _1xt=E(_1xs);if(!_1xt._){return __Z;}else{var _1xu=E(_1xt.a);return new T2(1,_1xu.a,new T2(1,_1xu.b,new T(function(){return B(_1xr(_1xt.b));})));}},_1xv=B(_1xr(_1tQ));if(!_1xv._){return __Z;}else{return B(_1pQ(new T2(1,_1xv.a,new T(function(){return B(_1qC(_1qk,_1xv.b));}))));}});return B(_1qC(_1ql,new T2(1,_1xq,new T2(1,_1xo,_10))));});return B(_y(B(_1pQ(new T2(1,new T(function(){return B(_I(0,_1tG,_10));}),_1xn))),_1qw));}),_1xw=__app2(E(_1rw),toJSStr(E(_1qm)),B(_1eT(B(_1tu(B(unAppCStr("\"",_1xm)))))));return new F(function(){return _1vR(_,_1pY);});break;default:return new F(function(){return _1vR(_,_1qn);});}};if(!E(_1uu)){var _1xx=B(_1pL(_1ts,_1rW,_));return new F(function(){return _1uP(_);});}else{var _1xy=B(_1pL(_1ts,_1rV,_));return new F(function(){return _1uP(_);});}},_1xz=E(_1tS);if(!_1xz._){var _1xA=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1uN(_);});}else{var _1xB=new T(function(){var _1xC=E(_1xz.a),_1xD=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1xE){return new F(function(){return _1ry(_1xC.a,_1xE);});},new T2(1,function(_1xF){return new F(function(){return _1ry(_1xC.b,_1xF);});},_10)),new T2(1,_G,new T(function(){return B(_1rB(_1xz.b));}))));});return new T2(1,_H,_1xD);}),_1xG=B(_1pL(_1ts,new T2(1,_2C,_1xB),_));return new F(function(){return _1uN(_);});}},_1xH=E(_1tR);if(!_1xH._){var _1xI=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1uM(_);});}else{var _1xJ=new T(function(){return B(_I(0,E(_1xH.a),new T(function(){return B(_1rJ(_1xH.b));})));}),_1xK=B(_1pL(_1ts,new T2(1,_2C,_1xJ),_));return new F(function(){return _1uM(_);});}},_1xL=E(_1tQ);if(!_1xL._){var _1xM=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1uL(_);});}else{var _1xN=new T(function(){var _1xO=E(_1xL.a),_1xP=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1xQ){return new F(function(){return _1ry(_1xO.a,_1xQ);});},new T2(1,function(_1xR){return new F(function(){return _1ry(_1xO.b,_1xR);});},_10)),new T2(1,_G,new T(function(){return B(_1rN(_1xL.b));}))));});return new T2(1,_H,_1xP);}),_1xS=B(_1pL(_1ts,new T2(1,_2C,_1xN),_));return new F(function(){return _1uL(_);});}},_1xT=E(_1u1);if(!_1xT._){return new F(function(){return _1uk(_,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1ud,_1tO,_1tP,_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua);});}else{var _1xU=E(_1xT.b);if(!_1xU._){return new F(function(){return _1uk(_,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1ud,_1tO,_1tP,_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua);});}else{var _1xV=E(_1xU.b);if(!_1xV._){return new F(function(){return _1uk(_,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1ud,_1tO,_1tP,_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua);});}else{var _1xW=_1xV.a,_1xX=E(_1xV.b);if(!_1xX._){return new F(function(){return _1uk(_,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1ud,_1tO,_1tP,_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua);});}else{if(!E(_1xX.b)._){var _1xY=B(_145(B(_mt(_1xW,0)),_1tI,new T(function(){var _1xZ=B(_Ga(B(_sv(_XL,_1xT.a))));if(!_1xZ._){return E(_1rj);}else{if(!E(_1xZ.b)._){if(E(_1xZ.a)==2){return E(_1rn);}else{return E(_1rj);}}else{return E(_1rj);}}}),_)),_1y0=E(_1xY),_1y1=_1y0.a,_1y2=new T(function(){var _1y3=new T(function(){return B(_6e(function(_1y4){var _1y5=B(_si(_3M,_1y4,B(_Gm(_1qq,_1xW))));return (_1y5._==0)?E(_1qc):E(_1y5.a);},B(_6e(_1rX,B(_1sf(B(_1ro(_1y1,_1rk))))))));}),_1y6=B(_R1(B(unAppCStr("e.==.m1:",_1xX.a)),{_:0,a:E(_1tC),b:E(_1tD),c:_1tE,d:_1tF,e:_1tG,f:E(B(_y(_1tH,new T2(1,new T2(0,new T2(0,_1xU.a,_1qp),_1tG),new T2(1,new T2(0,new T2(0,_1y3,_1qp),_1tG),_10))))),g:E(_1y0.b),h:E(_1tJ),i:E(_1tK),j:E(_1tL)},_1ud,_1tO,B(_y(_1tP,new T(function(){return B(_1pB(_1y1,_1xW));},1))),_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua)),_1y7=B(_1f4(_1xW,_1y6.a,_1y6.b,_1y6.c,_1y6.d,_1y6.e,_1y6.f,_1y6.g,_1y6.h,_1y6.i,_1y6.j,_1y6.k,_1y6.l,_1y6.m,_1y6.n,_1y6.o,_1y6.p,_1y6.q));return {_:0,a:E(_1y7.a),b:E(_1y7.b),c:E(_1y7.c),d:E(_1y7.d),e:E(_1y7.e),f:E(_1y7.f),g:E(_1y7.g),h:E(_1y7.h),i:_1y7.i,j:_1y7.j,k:_1y7.k,l:_1y7.l,m:E(_1y7.m),n:_1y7.n,o:E(_1y7.o),p:E(_1y7.p),q:E(_1y7.q)};}),_1y8=function(_){var _1y9=function(_){var _1ya=function(_){var _1yb=new T(function(){var _1yc=E(E(_1y2).a);return new T5(0,_1yc,_1yc.a,_1yc.g,_1yc.h,_1yc.j);}),_1yd=B(_1pL(_1ts,new T2(1,_6D,new T(function(){return B(_8k(E(_1yb).d,_1qz));})),_)),_1ye=E(_1yb),_1yf=_1ye.b,_1yg=function(_){var _1yh=B(_1pL(_1ts,B(_I(0,_1tY,_10)),_)),_1yi=B(_12K(_1qb,_1ye.c,_)),_1yj=E(_1ty),_1yk=_1yj.a,_1yl=_1yj.b,_1ym=new T(function(){return B(_1fJ(E(_1tB)));}),_1yn=new T(function(){var _1yo=function(_1yp,_1yq){var _1yr=E(_1ye.a),_1ys=E(_1yr.a);return new F(function(){return _1lC(_1yp,_1yq,_1ys.a,_1ys.b,_1yr.b,_1yr.c,_1yr.d,_1yr.e,_1yr.f,_1yr.g,_1yr.h,_1yr.i,_1yr.j);});};switch(E(_1ym)){case 72:var _1yt=E(_1yf),_1yu=_1yt.a,_1yv=E(_1yt.b);if(0<=(_1yv-1|0)){var _1yw=B(_1yo(E(_1yu),_1yv-1|0));return {_:0,a:E(_1yw.a),b:E(_1yw.b),c:_1yw.c,d:_1yw.d,e:_1yw.e,f:E(_1yw.f),g:_1yw.g,h:E(_1yw.h),i:E(_1yw.i),j:E(_1yw.j)};}else{var _1yx=B(_1yo(E(_1yu),_1yv));return {_:0,a:E(_1yx.a),b:E(_1yx.b),c:_1yx.c,d:_1yx.d,e:_1yx.e,f:E(_1yx.f),g:_1yx.g,h:E(_1yx.h),i:E(_1yx.i),j:E(_1yx.j)};}break;case 75:var _1yy=E(_1yf),_1yz=_1yy.b,_1yA=E(_1yy.a);if(0<=(_1yA-1|0)){var _1yB=B(_1yo(_1yA-1|0,E(_1yz)));return {_:0,a:E(_1yB.a),b:E(_1yB.b),c:_1yB.c,d:_1yB.d,e:_1yB.e,f:E(_1yB.f),g:_1yB.g,h:E(_1yB.h),i:E(_1yB.i),j:E(_1yB.j)};}else{var _1yC=B(_1yo(_1yA,E(_1yz)));return {_:0,a:E(_1yC.a),b:E(_1yC.b),c:_1yC.c,d:_1yC.d,e:_1yC.e,f:E(_1yC.f),g:_1yC.g,h:E(_1yC.h),i:E(_1yC.i),j:E(_1yC.j)};}break;case 77:var _1yD=E(_1yf),_1yE=_1yD.b,_1yF=E(_1yD.a);if(E(_1tM)!=(_1yF+1|0)){var _1yG=B(_1yo(_1yF+1|0,E(_1yE)));return {_:0,a:E(_1yG.a),b:E(_1yG.b),c:_1yG.c,d:_1yG.d,e:_1yG.e,f:E(_1yG.f),g:_1yG.g,h:E(_1yG.h),i:E(_1yG.i),j:E(_1yG.j)};}else{var _1yH=B(_1yo(_1yF,E(_1yE)));return {_:0,a:E(_1yH.a),b:E(_1yH.b),c:_1yH.c,d:_1yH.d,e:_1yH.e,f:E(_1yH.f),g:_1yH.g,h:E(_1yH.h),i:E(_1yH.i),j:E(_1yH.j)};}break;case 80:var _1yI=E(_1yf),_1yJ=_1yI.a,_1yK=E(_1yI.b);if(E(_1tN)!=(_1yK+1|0)){var _1yL=B(_1yo(E(_1yJ),_1yK+1|0));return {_:0,a:E(_1yL.a),b:E(_1yL.b),c:_1yL.c,d:_1yL.d,e:_1yL.e,f:E(_1yL.f),g:_1yL.g,h:E(_1yL.h),i:E(_1yL.i),j:E(_1yL.j)};}else{var _1yM=B(_1yo(E(_1yJ),_1yK));return {_:0,a:E(_1yM.a),b:E(_1yM.b),c:_1yM.c,d:_1yM.d,e:_1yM.e,f:E(_1yM.f),g:_1yM.g,h:E(_1yM.h),i:E(_1yM.i),j:E(_1yM.j)};}break;case 104:var _1yN=E(_1yf),_1yO=_1yN.b,_1yP=E(_1yN.a);if(0<=(_1yP-1|0)){var _1yQ=B(_1yo(_1yP-1|0,E(_1yO)));return {_:0,a:E(_1yQ.a),b:E(_1yQ.b),c:_1yQ.c,d:_1yQ.d,e:_1yQ.e,f:E(_1yQ.f),g:_1yQ.g,h:E(_1yQ.h),i:E(_1yQ.i),j:E(_1yQ.j)};}else{var _1yR=B(_1yo(_1yP,E(_1yO)));return {_:0,a:E(_1yR.a),b:E(_1yR.b),c:_1yR.c,d:_1yR.d,e:_1yR.e,f:E(_1yR.f),g:_1yR.g,h:E(_1yR.h),i:E(_1yR.i),j:E(_1yR.j)};}break;case 106:var _1yS=E(_1yf),_1yT=_1yS.a,_1yU=E(_1yS.b);if(E(_1tN)!=(_1yU+1|0)){var _1yV=B(_1yo(E(_1yT),_1yU+1|0));return {_:0,a:E(_1yV.a),b:E(_1yV.b),c:_1yV.c,d:_1yV.d,e:_1yV.e,f:E(_1yV.f),g:_1yV.g,h:E(_1yV.h),i:E(_1yV.i),j:E(_1yV.j)};}else{var _1yW=B(_1yo(E(_1yT),_1yU));return {_:0,a:E(_1yW.a),b:E(_1yW.b),c:_1yW.c,d:_1yW.d,e:_1yW.e,f:E(_1yW.f),g:_1yW.g,h:E(_1yW.h),i:E(_1yW.i),j:E(_1yW.j)};}break;case 107:var _1yX=E(_1yf),_1yY=_1yX.a,_1yZ=E(_1yX.b);if(0<=(_1yZ-1|0)){var _1z0=B(_1yo(E(_1yY),_1yZ-1|0));return {_:0,a:E(_1z0.a),b:E(_1z0.b),c:_1z0.c,d:_1z0.d,e:_1z0.e,f:E(_1z0.f),g:_1z0.g,h:E(_1z0.h),i:E(_1z0.i),j:E(_1z0.j)};}else{var _1z1=B(_1yo(E(_1yY),_1yZ));return {_:0,a:E(_1z1.a),b:E(_1z1.b),c:_1z1.c,d:_1z1.d,e:_1z1.e,f:E(_1z1.f),g:_1z1.g,h:E(_1z1.h),i:E(_1z1.i),j:E(_1z1.j)};}break;case 108:var _1z2=E(_1yf),_1z3=_1z2.b,_1z4=E(_1z2.a);if(E(_1tM)!=(_1z4+1|0)){var _1z5=B(_1yo(_1z4+1|0,E(_1z3)));return {_:0,a:E(_1z5.a),b:E(_1z5.b),c:_1z5.c,d:_1z5.d,e:_1z5.e,f:E(_1z5.f),g:_1z5.g,h:E(_1z5.h),i:E(_1z5.i),j:E(_1z5.j)};}else{var _1z6=B(_1yo(_1z4,E(_1z3)));return {_:0,a:E(_1z6.a),b:E(_1z6.b),c:_1z6.c,d:_1z6.d,e:_1z6.e,f:E(_1z6.f),g:_1z6.g,h:E(_1z6.h),i:E(_1z6.i),j:E(_1z6.j)};}break;default:var _1z7=E(_1yf),_1z8=B(_1yo(E(_1z7.a),E(_1z7.b)));return {_:0,a:E(_1z8.a),b:E(_1z8.b),c:_1z8.c,d:_1z8.d,e:_1z8.e,f:E(_1z8.f),g:_1z8.g,h:E(_1z8.h),i:E(_1z8.i),j:E(_1z8.j)};}}),_1z9=new T(function(){if(E(_1ym)==32){var _1za=E(_1yn),_1zb=E(_1za.a),_1zc=B(_1oW(_1zb.a,E(_1zb.b),_1za.b,_1za.c,_1za.d,_1za.e,_1za.f,_1za.g,_1za.h,_1za.i,_1za.j));return {_:0,a:E(_1zc.a),b:E(_1zc.b),c:_1zc.c,d:_1zc.d,e:_1zc.e,f:E(_1zc.f),g:_1zc.g,h:E(_1zc.h),i:E(_1zc.i),j:E(_1zc.j)};}else{return E(_1yn);}}),_1zd=new T(function(){var _1ze=E(_1y2),_1zf=_1ze.e,_1zg=E(_1z9),_1zh=_1zg.h,_1zi=B(_1cO(_1qo,_1zh,_1zf,{_:0,a:E(_1zg.a),b:E(_1zg.b),c:_1zg.c,d:_1zg.d,e:_1zg.e,f:E(_1zg.f),g:E(E(_1yi).b),h:E(_1zh),i:E(_1zg.i),j:E(_1zg.j)},_1ze.b,_1ze.c,_1ze.d,_1zf,_1ze.f,_1ze.g,_1ze.h,_1ze.i,_1ze.j,_1ze.k,_1ze.l,_1ze.m,_1ze.n,_1ze.o,_1ze.p,_1ze.q));return {_:0,a:E(_1zi.a),b:E(_1zi.b),c:E(_1zi.c),d:E(_1zi.d),e:E(_1zi.e),f:E(_1zi.f),g:E(_1zi.g),h:E(_1zi.h),i:_1zi.i,j:_1zi.j,k:_1zi.k,l:_1zi.l,m:E(_1zi.m),n:_1zi.n,o:E(_1zi.o),p:E(_1zi.p),q:E(_1zi.q)};}),_1zj=B(_nq(_1yk,_1yl,new T(function(){return E(_1uh)-E(E(E(_1zd).b).a)|0;}),_nP,new T(function(){return E(E(E(_1zd).a).b);}),_)),_1zk=E(_1ym),_1zl=function(_,_1zm){var _1zn=function(_1zo){var _1zp=B(_1pL(_1ts,B(_8q(_1zm)),_)),_1zq=E(_1zd),_1zr=_1zq.d,_1zs=_1zq.e,_1zt=_1zq.f,_1zu=_1zq.g,_1zv=_1zq.i,_1zw=_1zq.j,_1zx=_1zq.k,_1zy=_1zq.l,_1zz=_1zq.m,_1zA=_1zq.n,_1zB=_1zq.o,_1zC=_1zq.q,_1zD=E(_1zq.p),_1zE=_1zD.a,_1zF=_1zD.d,_1zG=_1zD.e,_1zH=_1zD.f,_1zI=_1zD.g,_1zJ=_1zD.h,_1zK=E(_1zq.a),_1zL=_1zK.e,_1zM=_1zK.f,_1zN=_1zK.g,_1zO=E(_1zq.h),_1zP=function(_1zQ){var _1zR=function(_1zS){if(_1zS!=E(_1qg)){var _1zT=B(_6R(_19r,_1zS)),_1zU=_1zT.a,_1zV=E(_1zT.b),_1zW=B(_16A(_1zU,_1zV,new T(function(){return B(_6R(_1aF,_1zS));})));return new F(function(){return _1tx(_1yj,_1tz,_1tA,_1qf,B(_6R(_19A,_1zS)),_1zW,B(_6R(_19N,_1zS)),32,_1zS,_1zM,_1zN,B(_y(_1zK.h,new T2(1,_1qe,new T(function(){return B(_I(0,_1zL,_10));})))),B(_1pk(_1qd,_1zW)),_wq,_1zU,_1zV,_10,_1zr,_1zs,_1zt,_1zu,_1zO.a,_1zO.b,_1zv,_1zw,_1zx, -1,_1zz,_1zA,_1zB,_wq,_wq,_wq,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zC,_);});}else{var _1zX=__app1(E(_ni),_1yl),_1zY=B(A2(_nj,_1yk,_)),_1zZ=B(A(_mO,[_1yk,_j3,_1q4,_1qb,_1qa,_])),_1A0=B(A(_mO,[_1yk,_j3,_1q7,_1q9,_1q8,_])),_1A1=B(A(_mO,[_1yk,_j3,_1q7,_1q6,_1q5,_])),_1A2=B(A(_mO,[_1yk,_j3,_1q4,_1q3,_1q2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_19w),b:E(_1q1),c:E(_1pZ),d:32,e:0,f:E(_1zM),g:_1zN,h:E(_10),i:E(_1zK.i),j:E(_wq)}),b:E(_19o),c:E(_1zq.c),d:E(_1zr),e:E(_1zs),f:E(_1zt),g:E(_1zu),h:E(_1zO),i:_1zv,j:_1zw,k:_1zx,l:_1zy,m:E(_1zz),n:_1zA,o:E(_1zB),p:E({_:0,a:E(_1zE),b:E(_wq),c:E(_wq),d:E(_1zF),e:E(_1zG),f:E(_1zH),g:E(_1zI),h:E(_1zJ)}),q:E(_1zC)};});}};if(_1zy>=0){return new F(function(){return _1zR(_1zy);});}else{return new F(function(){return _1zR(_1zL+1|0);});}};if(!E(_1zE)){if(E(_1zk)==110){return new F(function(){return _1zP(_);});}else{var _1A3=new T(function(){return E(E(_1yn).a);});if(E(_1zK.d)==32){var _1A4=B(A(_mO,[_1yk,_1qh,new T(function(){return (E(E(_1A3).a)+1|0)+(E(_1uh)-E(_1tM)|0)|0;},1),new T(function(){return (E(E(_1A3).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1qA(_1z9));}),_10),_]));return _1zq;}else{var _1A5=B(A(_mO,[_1yk,_1qi,new T(function(){return (E(E(_1A3).a)+1|0)+(E(_1uh)-E(_1tM)|0)|0;},1),new T(function(){return (E(E(_1A3).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1qA(_1z9));}),_10),_]));return _1zq;}}}else{return new F(function(){return _1zP(_);});}};if(E(_1zk)==114){if(!B(_69(_1zm,_1qj))){var _1A6=E(_1zm);if(!_1A6._){return _1zd;}else{var _1A7=_1A6.b;return new T(function(){var _1A8=E(_1zd),_1A9=E(_1A8.a),_1Aa=E(_1A6.a),_1Ab=E(_1Aa);if(_1Ab==34){var _1Ac=B(_QD(_1Aa,_1A7));if(!_1Ac._){var _1Ad=E(_1rv);}else{var _1Ae=E(_1Ac.b);if(!_1Ae._){var _1Af=E(_1qx);}else{var _1Ag=_1Ae.a,_1Ah=E(_1Ae.b);if(!_1Ah._){var _1Ai=new T2(1,new T2(1,_1Ag,_10),_10);}else{var _1Aj=E(_1Ag),_1Ak=new T(function(){var _1Al=B(_H2(126,_1Ah.a,_1Ah.b));return new T2(0,_1Al.a,_1Al.b);});if(E(_1Aj)==126){var _1Am=new T2(1,_10,new T2(1,new T(function(){return E(E(_1Ak).a);}),new T(function(){return E(E(_1Ak).b);})));}else{var _1Am=new T2(1,new T2(1,_1Aj,new T(function(){return E(E(_1Ak).a);})),new T(function(){return E(E(_1Ak).b);}));}var _1Ai=_1Am;}var _1Af=_1Ai;}var _1Ad=_1Af;}var _1An=_1Ad;}else{var _1Ao=E(_1A7);if(!_1Ao._){var _1Ap=new T2(1,new T2(1,_1Aa,_10),_10);}else{var _1Aq=new T(function(){var _1Ar=B(_H2(126,_1Ao.a,_1Ao.b));return new T2(0,_1Ar.a,_1Ar.b);});if(E(_1Ab)==126){var _1As=new T2(1,_10,new T2(1,new T(function(){return E(E(_1Aq).a);}),new T(function(){return E(E(_1Aq).b);})));}else{var _1As=new T2(1,new T2(1,_1Aa,new T(function(){return E(E(_1Aq).a);})),new T(function(){return E(E(_1Aq).b);}));}var _1Ap=_1As;}var _1An=_1Ap;}var _1At=B(_Ga(B(_sv(_XL,new T(function(){return B(_J2(_1An));})))));if(!_1At._){return E(_XJ);}else{if(!E(_1At.b)._){var _1Au=E(_1At.a),_1Av=B(_6R(_19r,_1Au)),_1Aw=B(_6R(_1An,1));if(!_1Aw._){var _1Ax=__Z;}else{var _1Ay=E(_1Aw.b);if(!_1Ay._){var _1Az=__Z;}else{var _1AA=E(_1Aw.a),_1AB=new T(function(){var _1AC=B(_H2(44,_1Ay.a,_1Ay.b));return new T2(0,_1AC.a,_1AC.b);});if(E(_1AA)==44){var _1AD=B(_XB(_10,new T(function(){return E(E(_1AB).a);}),new T(function(){return E(E(_1AB).b);})));}else{var _1AD=B(_XF(new T2(1,_1AA,new T(function(){return E(E(_1AB).a);})),new T(function(){return E(E(_1AB).b);})));}var _1Az=_1AD;}var _1Ax=_1Az;}var _1AE=B(_6R(_1An,2));if(!_1AE._){var _1AF=E(_1qy);}else{var _1AG=_1AE.a,_1AH=E(_1AE.b);if(!_1AH._){var _1AI=B(_6e(_XM,new T2(1,new T2(1,_1AG,_10),_10)));}else{var _1AJ=E(_1AG),_1AK=new T(function(){var _1AL=B(_H2(44,_1AH.a,_1AH.b));return new T2(0,_1AL.a,_1AL.b);});if(E(_1AJ)==44){var _1AM=B(_6e(_XM,new T2(1,_10,new T2(1,new T(function(){return E(E(_1AK).a);}),new T(function(){return E(E(_1AK).b);})))));}else{var _1AM=B(_6e(_XM,new T2(1,new T2(1,_1AJ,new T(function(){return E(E(_1AK).a);})),new T(function(){return E(E(_1AK).b);}))));}var _1AI=_1AM;}var _1AF=_1AI;}return {_:0,a:E({_:0,a:E(B(_6R(_19A,_1Au))),b:E(B(_16A(_1Av.a,E(_1Av.b),new T(function(){return B(_6R(_1aF,_1Au));})))),c:B(_6R(_19N,_1Au)),d:32,e:_1Au,f:E(_1A9.f),g:_1A9.g,h:E(_1A9.h),i:E(_1A9.i),j:E(_1A9.j)}),b:E(_1Av),c:E(_1A8.c),d:E(_1A8.d),e:E(_1Ax),f:E(_1AF),g:E(_1A8.g),h:E(_1A8.h),i:_1A8.i,j:_1A8.j,k:_1A8.k,l:_1A8.l,m:E(_1A8.m),n:_1A8.n,o:E(_1A8.o),p:E(_1A8.p),q:E(_1A8.q)};}else{return E(_XK);}}});}}else{return new F(function(){return _1zn(_);});}}else{return new F(function(){return _1zn(_);});}};switch(E(_1zk)){case 100:var _1AN=__app1(E(_1rt),toJSStr(E(_1qm)));return new F(function(){return _1zl(_,_1pW);});break;case 114:var _1AO=B(_XW(_6w,toJSStr(E(_1qm)),_));return new F(function(){return _1zl(_,new T(function(){var _1AP=E(_1AO);if(!_1AP._){return E(_1pX);}else{return fromJSStr(B(_1eT(_1AP.a)));}}));});break;case 115:var _1AQ=new T(function(){var _1AR=new T(function(){var _1AS=new T(function(){var _1AT=B(_6e(_6B,_1tR));if(!_1AT._){return __Z;}else{return B(_1pQ(new T2(1,_1AT.a,new T(function(){return B(_1qC(_1qk,_1AT.b));}))));}}),_1AU=new T(function(){var _1AV=function(_1AW){var _1AX=E(_1AW);if(!_1AX._){return __Z;}else{var _1AY=E(_1AX.a);return new T2(1,_1AY.a,new T2(1,_1AY.b,new T(function(){return B(_1AV(_1AX.b));})));}},_1AZ=B(_1AV(_1tQ));if(!_1AZ._){return __Z;}else{return B(_1pQ(new T2(1,_1AZ.a,new T(function(){return B(_1qC(_1qk,_1AZ.b));}))));}});return B(_1qC(_1ql,new T2(1,_1AU,new T2(1,_1AS,_10))));});return B(_y(B(_1pQ(new T2(1,new T(function(){return B(_I(0,_1tG,_10));}),_1AR))),_1qw));}),_1B0=__app2(E(_1rw),toJSStr(E(_1qm)),B(_1eT(B(_1tu(B(unAppCStr("\"",_1AQ)))))));return new F(function(){return _1zl(_,_1pY);});break;default:return new F(function(){return _1zl(_,_1qn);});}};if(!E(_1ye.e)){var _1B1=B(_1pL(_1ts,_1rW,_));return new F(function(){return _1yg(_);});}else{var _1B2=B(_1pL(_1ts,_1rV,_));return new F(function(){return _1yg(_);});}},_1B3=E(_1tS);if(!_1B3._){var _1B4=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1ya(_);});}else{var _1B5=new T(function(){var _1B6=E(_1B3.a),_1B7=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1B8){return new F(function(){return _1ry(_1B6.a,_1B8);});},new T2(1,function(_1B9){return new F(function(){return _1ry(_1B6.b,_1B9);});},_10)),new T2(1,_G,new T(function(){return B(_1rB(_1B3.b));}))));});return new T2(1,_H,_1B7);}),_1Ba=B(_1pL(_1ts,new T2(1,_2C,_1B5),_));return new F(function(){return _1ya(_);});}},_1Bb=E(_1tR);if(!_1Bb._){var _1Bc=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1y9(_);});}else{var _1Bd=new T(function(){return B(_I(0,E(_1Bb.a),new T(function(){return B(_1rJ(_1Bb.b));})));}),_1Be=B(_1pL(_1ts,new T2(1,_2C,_1Bd),_));return new F(function(){return _1y9(_);});}},_1Bf=E(_1tQ);if(!_1Bf._){var _1Bg=B(_1pL(_1ts,_1qv,_));return new F(function(){return _1y8(_);});}else{var _1Bh=new T(function(){var _1Bi=E(_1Bf.a),_1Bj=new T(function(){return B(A3(_sa,_6x,new T2(1,function(_1Bk){return new F(function(){return _1ry(_1Bi.a,_1Bk);});},new T2(1,function(_1Bl){return new F(function(){return _1ry(_1Bi.b,_1Bl);});},_10)),new T2(1,_G,new T(function(){return B(_1rN(_1Bf.b));}))));});return new T2(1,_H,_1Bj);}),_1Bm=B(_1pL(_1ts,new T2(1,_2C,_1Bh),_));return new F(function(){return _1y8(_);});}}else{return new F(function(){return _1uk(_,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1ud,_1tO,_1tP,_1tQ,_1tR,_1tS,_1uc,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_10,_1ub,_1ua);});}}}}}}}else{if(!E(_1u8)){return {_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E({_:0,a:E(_1u2),b:E(_1u3),c:E(_1u4),d:E(_wq),e:E(_1u6),f:E(_wq),g:E(_wq),h:E(_1u9)}),q:E(_1ua)};}else{var _1Bn=B(_1pL(_1ts,_1qu,_)),_1Bo=new T(function(){var _1Bp=B(_1eX(_1tZ));return new T2(0,_1Bp.a,_1Bp.b);}),_1Bq=new T(function(){return E(E(_1Bo).a);}),_1Br=function(_1Bs,_1Bt){var _1Bu=E(_1Bs);switch(_1Bu){case  -2:return {_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E(_1ub),q:E(_1ua)};case  -1:var _1Bv=E(_1ty),_1Bw=B(_nQ(_1Bv.a,_1Bv.b,_1uh,{_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E(_1ub),q:E(_1ua)},_));return new T(function(){return {_:0,a:E(_1ue),b:E(_1ud),c:E(B(_191(_10,new T(function(){return B(_6R(E(_1Bo).b,_1u0));})))),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E({_:0,a:E(_1u2),b:E(_1u3),c:E(_wr),d:E(_wq),e:E(_1u6),f:E(_wq),g:E(_wq),h:E(_1u9)}),q:E(_1ua)};});default:var _1Bx=E(_1ty),_1By=B(_nQ(_1Bx.a,_1Bx.b,_1uh,{_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E(_1ub),q:E(_1ua)},_)),_1Bz=new T(function(){if(!E(_1u9)){return E(_1q4);}else{return 2+(E(_1tN)+3|0)|0;}}),_1BA=B(_ja(_1Bx,_1tA,0,_1Bz,new T(function(){var _1BB=E(_1tz)/28,_1BC=_1BB&4294967295;if(_1BB>=_1BC){return (_1BC-1|0)+_1tX|0;}else{return ((_1BC-1|0)-1|0)+_1tX|0;}}),_1Bz,B(_TG(_1tO,_1Bq,_1Bt)),_));return {_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1Bu,o:E(_1u1),p:E(_1ub),q:E(_1ua)};}};switch(E(B(_1fJ(E(_1tB))))){case 32:return new F(function(){return _1Br( -1,_1pU);});break;case 72:var _1BD=E(_1u0);if(!_1BD){var _1BE=B(_mt(_1Bq,0))-1|0;return new F(function(){return _1Br(_1BE,_1BE);});}else{var _1BF=_1BD-1|0;return new F(function(){return _1Br(_1BF,_1BF);});}break;case 75:if(_1u0!=(B(_mt(_1Bq,0))-1|0)){var _1BG=_1u0+1|0;return new F(function(){return _1Br(_1BG,_1BG);});}else{return new F(function(){return _1Br(0,_1pT);});}break;case 77:var _1BH=E(_1u0);if(!_1BH){var _1BI=B(_mt(_1Bq,0))-1|0;return new F(function(){return _1Br(_1BI,_1BI);});}else{var _1BJ=_1BH-1|0;return new F(function(){return _1Br(_1BJ,_1BJ);});}break;case 80:if(_1u0!=(B(_mt(_1Bq,0))-1|0)){var _1BK=_1u0+1|0;return new F(function(){return _1Br(_1BK,_1BK);});}else{return new F(function(){return _1Br(0,_1pT);});}break;case 104:if(_1u0!=(B(_mt(_1Bq,0))-1|0)){var _1BL=_1u0+1|0;return new F(function(){return _1Br(_1BL,_1BL);});}else{return new F(function(){return _1Br(0,_1pT);});}break;case 106:if(_1u0!=(B(_mt(_1Bq,0))-1|0)){var _1BM=_1u0+1|0;return new F(function(){return _1Br(_1BM,_1BM);});}else{return new F(function(){return _1Br(0,_1pT);});}break;case 107:var _1BN=E(_1u0);if(!_1BN){var _1BO=B(_mt(_1Bq,0))-1|0;return new F(function(){return _1Br(_1BO,_1BO);});}else{var _1BP=_1BN-1|0;return new F(function(){return _1Br(_1BP,_1BP);});}break;case 108:var _1BQ=E(_1u0);if(!_1BQ){var _1BR=B(_mt(_1Bq,0))-1|0;return new F(function(){return _1Br(_1BR,_1BR);});}else{var _1BS=_1BQ-1|0;return new F(function(){return _1Br(_1BS,_1BS);});}break;default:return new F(function(){return _1Br( -2,_1pV);});}}}};if(!E(_1u4)){return new F(function(){return _1uf(_);});}else{if(!E(_1u5)){return new F(function(){return _Ww(_1ty,_1tz,_1tA,_1tC,_1tD,_1tE,_1tF,_1tG,_1tH,_1tI,_1tJ,_1tK,_1tL,_1tM,_1tN,_1tO,_1tP,_1tQ,_1tR,_1tS,_1tT,_1tU,_1tV,_1tW,_1tX,_1tY,_1tZ,_1u0,_1u1,_1u2,_1u3,_wq,_1u6,_wr,_1u8,_1u9,_1ua,_);});}else{return new F(function(){return _1uf(_);});}}}else{return {_:0,a:E(_1ue),b:E(_1ud),c:E(_1tO),d:E(_1tP),e:E(_1tQ),f:E(_1tR),g:E(_1tS),h:E(_1uc),i:_1tV,j:_1tW,k:_1tX,l:_1tY,m:E(_1tZ),n:_1u0,o:E(_1u1),p:E(_1ub),q:E(_1ua)};}},_1BT=function(_1BU,_1BV,_1BW){var _1BX=E(_1BW);if(!_1BX._){return 0;}else{var _1BY=_1BX.b,_1BZ=E(_1BX.a),_1C0=_1BZ.a,_1C1=_1BZ.b;return (_1BU<=_1C0)?1+B(_1BT(_1BU,_1BV,_1BY))|0:(_1BU>=_1C0+_1BZ.c)?1+B(_1BT(_1BU,_1BV,_1BY))|0:(_1BV<=_1C1)?1+B(_1BT(_1BU,_1BV,_1BY))|0:(_1BV>=_1C1+_1BZ.d)?1+B(_1BT(_1BU,_1BV,_1BY))|0:1;}},_1C2=function(_1C3,_1C4,_1C5){var _1C6=E(_1C5);if(!_1C6._){return 0;}else{var _1C7=_1C6.b,_1C8=E(_1C6.a),_1C9=_1C8.a,_1Ca=_1C8.b;if(_1C3<=_1C9){return 1+B(_1C2(_1C3,_1C4,_1C7))|0;}else{if(_1C3>=_1C9+_1C8.c){return 1+B(_1C2(_1C3,_1C4,_1C7))|0;}else{var _1Cb=E(_1C4);return (_1Cb<=_1Ca)?1+B(_1BT(_1C3,_1Cb,_1C7))|0:(_1Cb>=_1Ca+_1C8.d)?1+B(_1BT(_1C3,_1Cb,_1C7))|0:1;}}}},_1Cc=function(_1Cd,_1Ce,_1Cf){var _1Cg=E(_1Cf);if(!_1Cg._){return 0;}else{var _1Ch=_1Cg.b,_1Ci=E(_1Cg.a),_1Cj=_1Ci.a,_1Ck=_1Ci.b,_1Cl=E(_1Cd);if(_1Cl<=_1Cj){return 1+B(_1C2(_1Cl,_1Ce,_1Ch))|0;}else{if(_1Cl>=_1Cj+_1Ci.c){return 1+B(_1C2(_1Cl,_1Ce,_1Ch))|0;}else{var _1Cm=E(_1Ce);return (_1Cm<=_1Ck)?1+B(_1BT(_1Cl,_1Cm,_1Ch))|0:(_1Cm>=_1Ck+_1Ci.d)?1+B(_1BT(_1Cl,_1Cm,_1Ch))|0:1;}}}},_1Cn=function(_1Co,_1Cp){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1Cp)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1Cp)-100,E(_1Co),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1Co),100);}),new T2(1,new T(function(){return new T4(0,E(_1Co)-100,100,100,E(_1Cp)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1Co)-200,E(_1Cp)-200);}),_10)))));},_1Cq=32,_1Cr=76,_1Cs=75,_1Ct=74,_1Cu=72,_1Cv=64,_1Cw=function(_1Cx,_1Cy,_1Cz,_1CA){var _1CB=new T(function(){var _1CC=E(_1Cy),_1CD=E(_1CC.a),_1CE=_1CD.a,_1CF=_1CD.b,_1CG=B(_1Cn(_1CE,_1CF)),_1CH=new T(function(){var _1CI=E(_1CC.b);return new T2(0,new T(function(){return B(_g8(_1CE,_1CI.a));}),new T(function(){return B(_g8(_1CF,_1CI.b));}));});switch(B(_1Cc(new T(function(){return E(_1Cz)*E(E(_1CH).a);},1),new T(function(){return E(_1CA)*E(E(_1CH).b);},1),new T2(1,_1CG.a,_1CG.b)))){case 1:return E(_1Cu);break;case 2:return E(_1Ct);break;case 3:return E(_1Cs);break;case 4:return E(_1Cr);break;case 5:return E(_1Cq);break;default:return E(_1Cv);}});return function(_1CJ,_){var _1CK=E(E(_1Cy).a),_1CL=E(_1CJ),_1CM=E(_1CL.a),_1CN=E(_1CL.b),_1CO=E(_1CL.h),_1CP=E(_1CL.p);return new F(function(){return _1tx(_1Cx,_1CK.a,_1CK.b,_1CB,_1CM.a,_1CM.b,_1CM.c,_1CM.d,_1CM.e,_1CM.f,_1CM.g,_1CM.h,_1CM.i,_1CM.j,_1CN.a,_1CN.b,_1CL.c,_1CL.d,_1CL.e,_1CL.f,_1CL.g,_1CO.a,_1CO.b,_1CL.i,_1CL.j,_1CL.k,_1CL.l,_1CL.m,_1CL.n,_1CL.o,_1CP.a,_1CP.b,_1CP.c,_1CP.d,_1CP.e,_1CP.f,_1CP.g,_1CP.h,_1CL.q,_);});};},_1CQ=0,_1CR=2,_1CS=2,_1CT=0,_1CU=new T(function(){return eval("document");}),_1CV=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1CW=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1CX=function(_1CY){return E(E(_1CY).b);},_1CZ=function(_1D0,_1D1){return new F(function(){return A2(_1CX,_1D0,function(_){var _1D2=E(_1D1),_1D3=__app1(E(_1CW),_1D2);if(!_1D3){return _0;}else{var _1D4=__app1(E(_1CV),_1D2);return new T1(1,new T2(0,_1D4,_1D2));}});});},_1D5=new T(function(){var _1D6=E(_19N);if(!_1D6._){return E(_nh);}else{return {_:0,a:E(_19w),b:E(B(_16A(_19l,5,_1ag))),c:E(_1D6.a),d:32,e:0,f:E(_10),g:0,h:E(_10),i:E(_wq),j:E(_wq)};}}),_1D7=0,_1D8=new T2(0,_1D7,_1D7),_1D9={_:0,a:E(_wq),b:E(_wq),c:E(_wr),d:E(_wq),e:E(_wq),f:E(_wq),g:E(_wq),h:E(_wq)},_1Da=new T(function(){return {_:0,a:E(_1D5),b:E(_19o),c:E(_17L),d:E(_10),e:E(_10),f:E(_10),g:E(_10),h:E(_1D8),i:0,j:0,k:0,l: -1,m:E(_10),n:0,o:E(_10),p:E(_1D9),q:E(_10)};}),_1Db=new T1(0,100),_1Dc=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-9"));}),_1Dd=new T6(0,_0,_2V,_10,_1Dc,_0,_0),_1De=new T(function(){return B(_2T(_1Dd));}),_1Df=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:14:3-8"));}),_1Dg=new T6(0,_0,_2V,_10,_1Df,_0,_0),_1Dh=new T(function(){return B(_2T(_1Dg));}),_1Di=new T1(1,50),_1Dj=function(_1Dk){return E(E(_1Dk).a);},_1Dl=function(_1Dm){return E(E(_1Dm).a);},_1Dn=function(_1Do){return E(E(_1Do).b);},_1Dp=function(_1Dq){return E(E(_1Dq).b);},_1Dr=function(_1Ds){return E(E(_1Ds).a);},_1Dt=function(_){return new F(function(){return nMV(_0);});},_1Du=new T(function(){return B(_3(_1Dt));}),_1Dv=function(_1Dw){return E(E(_1Dw).b);},_1Dx=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Dy=function(_1Dz){return E(E(_1Dz).d);},_1DA=function(_1DB,_1DC,_1DD,_1DE,_1DF,_1DG){var _1DH=B(_1Dj(_1DB)),_1DI=B(_1Dl(_1DH)),_1DJ=new T(function(){return B(_1CX(_1DH));}),_1DK=new T(function(){return B(_1Dy(_1DI));}),_1DL=new T(function(){return B(A1(_1DC,_1DE));}),_1DM=new T(function(){return B(A2(_1Dr,_1DD,_1DF));}),_1DN=function(_1DO){return new F(function(){return A1(_1DK,new T3(0,_1DM,_1DL,_1DO));});},_1DP=function(_1DQ){var _1DR=new T(function(){var _1DS=new T(function(){var _1DT=__createJSFunc(2,function(_1DU,_){var _1DV=B(A2(E(_1DQ),_1DU,_));return _7;}),_1DW=_1DT;return function(_){return new F(function(){return __app3(E(_1Dx),E(_1DL),E(_1DM),_1DW);});};});return B(A1(_1DJ,_1DS));});return new F(function(){return A3(_1Dn,_1DI,_1DR,_1DN);});},_1DX=new T(function(){var _1DY=new T(function(){return B(_1CX(_1DH));}),_1DZ=function(_1E0){var _1E1=new T(function(){return B(A1(_1DY,function(_){var _=wMV(E(_1Du),new T1(1,_1E0));return new F(function(){return A(_1Dp,[_1DD,_1DF,_1E0,_]);});}));});return new F(function(){return A3(_1Dn,_1DI,_1E1,_1DG);});};return B(A2(_1Dv,_1DB,_1DZ));});return new F(function(){return A3(_1Dn,_1DI,_1DX,_1DP);});},_1E2=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1E3=function(_){var _1E4=rMV(E(_1Du)),_1E5=E(_1E4);if(!_1E5._){var _1E6=__app1(E(_1E2),E(_7));return new F(function(){return _gF(_);});}else{var _1E7=__app1(E(_1E2),E(_1E5.a));return new F(function(){return _gF(_);});}},_1E8=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1E9=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1Ea=function(_1Eb,_1Ec,_1Ed){var _1Ee=B(_1Dj(_1Eb)),_1Ef=new T(function(){return B(_1CX(_1Ee));}),_1Eg=function(_1Eh){var _1Ei=function(_){var _1Ej=E(_1Ec);if(!_1Ej._){var _1Ek=B(A1(_1Eh,_gE)),_1El=__createJSFunc(0,function(_){var _1Em=B(A1(_1Ek,_));return _7;}),_1En=__app2(E(_1E9),_1Ej.a,_1El);return new T(function(){var _1Eo=Number(_1En),_1Ep=jsTrunc(_1Eo);return new T2(0,_1Ep,E(_1Ej));});}else{var _1Eq=B(A1(_1Eh,_gE)),_1Er=__createJSFunc(0,function(_){var _1Es=B(A1(_1Eq,_));return _7;}),_1Et=__app2(E(_1E8),_1Ej.a,_1Er);return new T(function(){var _1Eu=Number(_1Et),_1Ev=jsTrunc(_1Eu);return new T2(0,_1Ev,E(_1Ej));});}};return new F(function(){return A1(_1Ef,_1Ei);});},_1Ew=new T(function(){return B(A2(_1Dv,_1Eb,function(_1Ex){return E(_1Ed);}));});return new F(function(){return A3(_1Dn,B(_1Dl(_1Ee)),_1Ew,_1Eg);});},_1Ey=function(_,_1Ez){var _1EA=E(_1Ez);if(!_1EA._){return new F(function(){return die(_1De);});}else{var _1EB=_1EA.a,_1EC=B(A3(_1CZ,_5X,_1EB,_)),_1ED=E(_1EC);if(!_1ED._){return new F(function(){return die(_1Dh);});}else{var _1EE=E(_1ED.a),_1EF=B(_63(_1EE.b,_)),_1EG=_1EF,_1EH=nMV(_1Da),_1EI=_1EH,_1EJ=B(A(_1DA,[_5Y,_3E,_u,_1CU,_1CR,function(_1EK,_){var _1EL=B(_1E3(_)),_1EM=rMV(_1EI),_1EN=E(E(_1EG).a),_1EO=E(_1EM),_1EP=E(_1EO.a),_1EQ=E(_1EO.b),_1ER=E(_1EO.h),_1ES=E(_1EO.p),_1ET=B(_1tx(_1EE,_1EN.a,_1EN.b,E(_1EK).a,_1EP.a,_1EP.b,_1EP.c,_1EP.d,_1EP.e,_1EP.f,_1EP.g,_1EP.h,_1EP.i,_1EP.j,_1EQ.a,_1EQ.b,_1EO.c,_1EO.d,_1EO.e,_1EO.f,_1EO.g,_1ER.a,_1ER.b,_1EO.i,_1EO.j,_1EO.k,_1EO.l,_1EO.m,_1EO.n,_1EO.o,_1ES.a,_1ES.b,_1ES.c,_1ES.d,_1ES.e,_1ES.f,_1ES.g,_1ES.h,_1EO.q,_)),_=wMV(_1EI,_1ET);return _gE;},_])),_1EU=B(A(_1DA,[_5Y,_3E,_3D,_1EB,_1CQ,function(_1EV,_){var _1EW=E(E(_1EV).a),_1EX=rMV(_1EI),_1EY=B(A(_1Cw,[_1EE,_1EG,_1EW.a,_1EW.b,_1EX,_])),_=wMV(_1EI,_1EY);return _gE;},_])),_1EZ=B(A(_1DA,[_5Y,_3E,_5d,_1EB,_1CT,function(_1F0,_){var _1F1=E(_1F0),_1F2=rMV(_1EI),_1F3=E(_1F2);if(!E(E(_1F3.p).e)){var _=wMV(_1EI,_1F3);return _gE;}else{var _1F4=B(_1E3(_)),_=wMV(_1EI,_1F3);return _gE;}},_])),_1F5=function(_){var _1F6=rMV(_1EI),_=wMV(_1EI,new T(function(){var _1F7=E(_1F6),_1F8=E(_1F7.p);return {_:0,a:E(_1F7.a),b:E(_1F7.b),c:E(_1F7.c),d:E(_1F7.d),e:E(_1F7.e),f:E(_1F7.f),g:E(_1F7.g),h:E(_1F7.h),i:_1F7.i,j:_1F7.j,k:_1F7.k,l:_1F7.l,m:E(_1F7.m),n:_1F7.n,o:E(_1F7.o),p:E({_:0,a:E(_1F8.a),b:E(_1F8.b),c:E(_1F8.c),d:E(_1F8.d),e:E(_wq),f:E(_1F8.f),g:E(_1F8.g),h:E(_1F8.h)}),q:E(_1F7.q)};}));return _gE;},_1F9=function(_1Fa,_){var _1Fb=E(_1Fa),_1Fc=rMV(_1EI),_=wMV(_1EI,new T(function(){var _1Fd=E(_1Fc),_1Fe=E(_1Fd.p);return {_:0,a:E(_1Fd.a),b:E(_1Fd.b),c:E(_1Fd.c),d:E(_1Fd.d),e:E(_1Fd.e),f:E(_1Fd.f),g:E(_1Fd.g),h:E(_1Fd.h),i:_1Fd.i,j:_1Fd.j,k:_1Fd.k,l:_1Fd.l,m:E(_1Fd.m),n:_1Fd.n,o:E(_1Fd.o),p:E({_:0,a:E(_1Fe.a),b:E(_1Fe.b),c:E(_1Fe.c),d:E(_1Fe.d),e:E(_wr),f:E(_1Fe.f),g:E(_1Fe.g),h:E(_1Fe.h)}),q:E(_1Fd.q)};})),_1Ff=B(A(_1Ea,[_5Y,_1Db,_1F5,_]));return _gE;},_1Fg=B(A(_1DA,[_5Y,_3E,_5d,_1EB,_1CS,_1F9,_])),_1Fh=B(A(_1Ea,[_5Y,_1Di,function(_){var _1Fi=rMV(_1EI),_1Fj=E(E(_1EG).a),_1Fk=E(_1Fi),_1Fl=E(_1Fk.a),_1Fm=E(_1Fk.b),_1Fn=E(_1Fk.h),_1Fo=E(_1Fk.p),_1Fp=B(_Ul(_1EE,_1Fj.a,_1Fj.b,_1Fl.a,_1Fl.b,_1Fl.c,_1Fl.d,_1Fl.e,_1Fl.f,_1Fl.g,_1Fl.h,_1Fl.i,_1Fl.j,_1Fm.a,_1Fm.b,_1Fk.c,_1Fk.d,_1Fk.e,_1Fk.f,_1Fk.g,_1Fn.a,_1Fn.b,_1Fk.i,_1Fk.j,_1Fk.k,_1Fk.l,_1Fk.m,_1Fk.n,_1Fk.o,_1Fo.a,_1Fo.b,_1Fo.c,_1Fo.d,_1Fo.e,_1Fo.f,_1Fo.g,_1Fo.h,_1Fk.q,_)),_=wMV(_1EI,_1Fp);return _gE;},_]));return _gE;}}},_1Fq="src",_1Fr=new T(function(){return B(unCStr("img"));}),_1Fs=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1Ft=function(_1Fu,_1Fv){return new F(function(){return A2(_1CX,_1Fu,function(_){var _1Fw=__app1(E(_1Fs),toJSStr(E(_1Fr))),_1Fx=__app3(E(_i1),_1Fw,E(_1Fq),E(_1Fv));return _1Fw;});});},_1Fy=new T(function(){return B(unCStr(".png"));}),_1Fz=function(_1FA,_1FB){var _1FC=E(_1FA);if(_1FC==( -1)){return __Z;}else{var _1FD=new T(function(){var _1FE=new T(function(){return toJSStr(B(_y(_1FB,new T(function(){return B(_y(B(_I(0,_1FC,_10)),_1Fy));},1))));});return B(_1Ft(_5X,_1FE));});return new F(function(){return _y(B(_1Fz(_1FC-1|0,_1FB)),new T2(1,_1FD,_10));});}},_1FF=new T(function(){return B(unCStr("WstImage/wst"));}),_1FG=new T(function(){return B(_1Fz(120,_1FF));}),_1FH=function(_1FI,_){var _1FJ=E(_1FI);if(!_1FJ._){return _10;}else{var _1FK=B(A1(_1FJ.a,_)),_1FL=B(_1FH(_1FJ.b,_));return new T2(1,_1FK,_1FL);}},_1FM=new T(function(){return B(unCStr("Images/img"));}),_1FN=new T(function(){return B(_1Fz(5,_1FM));}),_1FO=function(_1FP,_){var _1FQ=E(_1FP);if(!_1FQ._){return _10;}else{var _1FR=B(A1(_1FQ.a,_)),_1FS=B(_1FO(_1FQ.b,_));return new T2(1,_1FR,_1FS);}},_1FT=function(_){var _1FU=B(_1FO(_1FN,_)),_1FV=B(_1FH(_1FG,_)),_1FW=__app1(E(_1),"canvas"),_1FX=__eq(_1FW,E(_7));if(!E(_1FX)){var _1FY=__isUndef(_1FW);if(!E(_1FY)){return new F(function(){return _1Ey(_,new T1(1,_1FW));});}else{return new F(function(){return _1Ey(_,_0);});}}else{return new F(function(){return _1Ey(_,_0);});}},_1FZ=function(_){return new F(function(){return _1FT(_);});};
var hasteMain = function() {B(A(_1FZ, [0]));};window.onload = hasteMain;