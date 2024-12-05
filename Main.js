"use strict";
var __haste_prog_id = '89af7dd4c4811e8f020a7f225bcb5974373e18fc25bba03f348ec1393cee1439';
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

var _0=__Z,_1=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2=function(_){return new F(function(){return __jsNull();});},_3=function(_4){var _5=B(A1(_4,_));return E(_5);},_6=new T(function(){return B(_3(_2));}),_7=new T(function(){return E(_6);}),_8="metaKey",_9="shiftKey",_a="altKey",_b="ctrlKey",_c="keyCode",_d=function(_e,_){var _f=__get(_e,E(_c)),_g=__get(_e,E(_b)),_h=__get(_e,E(_a)),_i=__get(_e,E(_9)),_j=__get(_e,E(_8));return new T(function(){var _k=Number(_f),_l=jsTrunc(_k);return new T5(0,_l,E(_g),E(_h),E(_i),E(_j));});},_m=function(_n,_o,_){return new F(function(){return _d(E(_o),_);});},_p="keydown",_q="keyup",_r="keypress",_s=function(_t){switch(E(_t)){case 0:return E(_r);case 1:return E(_q);default:return E(_p);}},_u=new T2(0,_s,_m),_v="deltaZ",_w="deltaY",_x="deltaX",_y=function(_z,_A){var _B=E(_z);return (_B._==0)?E(_A):new T2(1,_B.a,new T(function(){return B(_y(_B.b,_A));}));},_C=function(_D,_E){var _F=jsShowI(_D);return new F(function(){return _y(fromJSStr(_F),_E);});},_G=41,_H=40,_I=function(_J,_K,_L){if(_K>=0){return new F(function(){return _C(_K,_L);});}else{if(_J<=6){return new F(function(){return _C(_K,_L);});}else{return new T2(1,_H,new T(function(){var _M=jsShowI(_K);return B(_y(fromJSStr(_M),new T2(1,_G,_L)));}));}}},_N=new T(function(){return B(unCStr(")"));}),_O=new T(function(){return B(_I(0,2,_N));}),_P=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_O));}),_Q=function(_R){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_I(0,_R,_P));}))));});},_S=function(_T,_){return new T(function(){var _U=Number(E(_T)),_V=jsTrunc(_U);if(_V<0){return B(_Q(_V));}else{if(_V>2){return B(_Q(_V));}else{return _V;}}});},_W=0,_X=new T3(0,_W,_W,_W),_Y="button",_Z=new T(function(){return eval("jsGetMouseCoords");}),_10=__Z,_11=function(_12,_){var _13=E(_12);if(!_13._){return _10;}else{var _14=B(_11(_13.b,_));return new T2(1,new T(function(){var _15=Number(E(_13.a));return jsTrunc(_15);}),_14);}},_16=function(_17,_){var _18=__arr2lst(0,_17);return new F(function(){return _11(_18,_);});},_19=function(_1a,_){return new F(function(){return _16(E(_1a),_);});},_1b=function(_1c,_){return new T(function(){var _1d=Number(E(_1c));return jsTrunc(_1d);});},_1e=new T2(0,_1b,_19),_1f=function(_1g,_){var _1h=E(_1g);if(!_1h._){return _10;}else{var _1i=B(_1f(_1h.b,_));return new T2(1,_1h.a,_1i);}},_1j=new T(function(){return B(unCStr("base"));}),_1k=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1l=new T(function(){return B(unCStr("IOException"));}),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1j,_1k,_1l),_1n=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1m,_10,_10),_1o=function(_1p){return E(_1n);},_1q=function(_1r){return E(E(_1r).a);},_1s=function(_1t,_1u,_1v){var _1w=B(A1(_1t,_)),_1x=B(A1(_1u,_)),_1y=hs_eqWord64(_1w.a,_1x.a);if(!_1y){return __Z;}else{var _1z=hs_eqWord64(_1w.b,_1x.b);return (!_1z)?__Z:new T1(1,_1v);}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1s(B(_1q(_1C.a)),_1o,_1C.b);});},_1D=new T(function(){return B(unCStr(": "));}),_1E=new T(function(){return B(unCStr(")"));}),_1F=new T(function(){return B(unCStr(" ("));}),_1G=new T(function(){return B(unCStr("interrupted"));}),_1H=new T(function(){return B(unCStr("system error"));}),_1I=new T(function(){return B(unCStr("unsatisified constraints"));}),_1J=new T(function(){return B(unCStr("user error"));}),_1K=new T(function(){return B(unCStr("permission denied"));}),_1L=new T(function(){return B(unCStr("illegal operation"));}),_1M=new T(function(){return B(unCStr("end of file"));}),_1N=new T(function(){return B(unCStr("resource exhausted"));}),_1O=new T(function(){return B(unCStr("resource busy"));}),_1P=new T(function(){return B(unCStr("does not exist"));}),_1Q=new T(function(){return B(unCStr("already exists"));}),_1R=new T(function(){return B(unCStr("resource vanished"));}),_1S=new T(function(){return B(unCStr("timeout"));}),_1T=new T(function(){return B(unCStr("unsupported operation"));}),_1U=new T(function(){return B(unCStr("hardware fault"));}),_1V=new T(function(){return B(unCStr("inappropriate type"));}),_1W=new T(function(){return B(unCStr("invalid argument"));}),_1X=new T(function(){return B(unCStr("failed"));}),_1Y=new T(function(){return B(unCStr("protocol error"));}),_1Z=function(_20,_21){switch(E(_20)){case 0:return new F(function(){return _y(_1Q,_21);});break;case 1:return new F(function(){return _y(_1P,_21);});break;case 2:return new F(function(){return _y(_1O,_21);});break;case 3:return new F(function(){return _y(_1N,_21);});break;case 4:return new F(function(){return _y(_1M,_21);});break;case 5:return new F(function(){return _y(_1L,_21);});break;case 6:return new F(function(){return _y(_1K,_21);});break;case 7:return new F(function(){return _y(_1J,_21);});break;case 8:return new F(function(){return _y(_1I,_21);});break;case 9:return new F(function(){return _y(_1H,_21);});break;case 10:return new F(function(){return _y(_1Y,_21);});break;case 11:return new F(function(){return _y(_1X,_21);});break;case 12:return new F(function(){return _y(_1W,_21);});break;case 13:return new F(function(){return _y(_1V,_21);});break;case 14:return new F(function(){return _y(_1U,_21);});break;case 15:return new F(function(){return _y(_1T,_21);});break;case 16:return new F(function(){return _y(_1S,_21);});break;case 17:return new F(function(){return _y(_1R,_21);});break;default:return new F(function(){return _y(_1G,_21);});}},_22=new T(function(){return B(unCStr("}"));}),_23=new T(function(){return B(unCStr("{handle: "));}),_24=function(_25,_26,_27,_28,_29,_2a){var _2b=new T(function(){var _2c=new T(function(){var _2d=new T(function(){var _2e=E(_28);if(!_2e._){return E(_2a);}else{var _2f=new T(function(){return B(_y(_2e,new T(function(){return B(_y(_1E,_2a));},1)));},1);return B(_y(_1F,_2f));}},1);return B(_1Z(_26,_2d));}),_2g=E(_27);if(!_2g._){return E(_2c);}else{return B(_y(_2g,new T(function(){return B(_y(_1D,_2c));},1)));}}),_2h=E(_29);if(!_2h._){var _2i=E(_25);if(!_2i._){return E(_2b);}else{var _2j=E(_2i.a);if(!_2j._){var _2k=new T(function(){var _2l=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2l));},1);return new F(function(){return _y(_23,_2k);});}else{var _2m=new T(function(){var _2n=new T(function(){return B(_y(_22,new T(function(){return B(_y(_1D,_2b));},1)));},1);return B(_y(_2j.a,_2n));},1);return new F(function(){return _y(_23,_2m);});}}}else{return new F(function(){return _y(_2h.a,new T(function(){return B(_y(_1D,_2b));},1));});}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _24(_2q.a,_2q.b,_2q.c,_2q.d,_2q.f,_10);});},_2r=function(_2s,_2t,_2u){var _2v=E(_2t);return new F(function(){return _24(_2v.a,_2v.b,_2v.c,_2v.d,_2v.f,_2u);});},_2w=function(_2x,_2y){var _2z=E(_2x);return new F(function(){return _24(_2z.a,_2z.b,_2z.c,_2z.d,_2z.f,_2y);});},_2A=44,_2B=93,_2C=91,_2D=function(_2E,_2F,_2G){var _2H=E(_2F);if(!_2H._){return new F(function(){return unAppCStr("[]",_2G);});}else{var _2I=new T(function(){var _2J=new T(function(){var _2K=function(_2L){var _2M=E(_2L);if(!_2M._){return E(new T2(1,_2B,_2G));}else{var _2N=new T(function(){return B(A2(_2E,_2M.a,new T(function(){return B(_2K(_2M.b));})));});return new T2(1,_2A,_2N);}};return B(_2K(_2H.b));});return B(A2(_2E,_2H.a,_2J));});return new T2(1,_2C,_2I);}},_2O=function(_2P,_2Q){return new F(function(){return _2D(_2w,_2P,_2Q);});},_2R=new T3(0,_2r,_2o,_2O),_2S=new T(function(){return new T5(0,_1o,_2R,_2T,_1A,_2o);}),_2T=function(_2U){return new T2(0,_2S,_2U);},_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_0,_2V,_10,_2W,_0,_0),_2Y=new T(function(){return B(_2T(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1f(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_3d,_3e,_){if(E(_3d)==7){var _3f=__app1(E(_Z),_3e),_3g=B(_32(_1e,_1e,_3f,_)),_3h=__get(_3e,E(_x)),_3i=__get(_3e,E(_w)),_3j=__get(_3e,E(_v));return new T(function(){return new T3(0,E(_3g),E(_0),E(new T3(0,_3h,_3i,_3j)));});}else{var _3k=__app1(E(_Z),_3e),_3l=B(_32(_1e,_1e,_3k,_)),_3m=__get(_3e,E(_Y)),_3n=__eq(_3m,E(_7));if(!E(_3n)){var _3o=__isUndef(_3m);if(!E(_3o)){var _3p=B(_S(_3m,_));return new T(function(){return new T3(0,E(_3l),E(new T1(1,_3p)),E(_X));});}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}else{return new T(function(){return new T3(0,E(_3l),E(_0),E(_X));});}}},_3q=function(_3r,_3s,_){return new F(function(){return _3c(_3r,E(_3s),_);});},_3t="mouseout",_3u="mouseover",_3v="mousemove",_3w="mouseup",_3x="mousedown",_3y="dblclick",_3z="click",_3A="wheel",_3B=function(_3C){switch(E(_3C)){case 0:return E(_3z);case 1:return E(_3y);case 2:return E(_3x);case 3:return E(_3w);case 4:return E(_3v);case 5:return E(_3u);case 6:return E(_3t);default:return E(_3A);}},_3D=new T2(0,_3B,_3q),_3E=function(_3F){return E(_3F);},_3G=function(_3H,_3I){return E(_3H)==E(_3I);},_3J=function(_3K,_3L){return E(_3K)!=E(_3L);},_3M=new T2(0,_3G,_3J),_3N="screenY",_3O="screenX",_3P="clientY",_3Q="clientX",_3R="pageY",_3S="pageX",_3T="target",_3U="identifier",_3V=function(_3W,_){var _3X=__get(_3W,E(_3U)),_3Y=__get(_3W,E(_3T)),_3Z=__get(_3W,E(_3S)),_40=__get(_3W,E(_3R)),_41=__get(_3W,E(_3Q)),_42=__get(_3W,E(_3P)),_43=__get(_3W,E(_3O)),_44=__get(_3W,E(_3N));return new T(function(){var _45=Number(_3X),_46=jsTrunc(_45);return new T5(0,_46,_3Y,E(new T2(0,new T(function(){var _47=Number(_3Z);return jsTrunc(_47);}),new T(function(){var _48=Number(_40);return jsTrunc(_48);}))),E(new T2(0,new T(function(){var _49=Number(_41);return jsTrunc(_49);}),new T(function(){var _4a=Number(_42);return jsTrunc(_4a);}))),E(new T2(0,new T(function(){var _4b=Number(_43);return jsTrunc(_4b);}),new T(function(){var _4c=Number(_44);return jsTrunc(_4c);}))));});},_4d=function(_4e,_){var _4f=E(_4e);if(!_4f._){return _10;}else{var _4g=B(_3V(E(_4f.a),_)),_4h=B(_4d(_4f.b,_));return new T2(1,_4g,_4h);}},_4i="touches",_4j=function(_4k){return E(E(_4k).b);},_4l=function(_4m,_4n,_){var _4o=__arr2lst(0,_4n),_4p=new T(function(){return B(_4j(_4m));}),_4q=function(_4r,_){var _4s=E(_4r);if(!_4s._){return _10;}else{var _4t=B(A2(_4p,_4s.a,_)),_4u=B(_4q(_4s.b,_));return new T2(1,_4t,_4u);}};return new F(function(){return _4q(_4o,_);});},_4v=function(_4w,_){return new F(function(){return _4l(_1e,E(_4w),_);});},_4x=new T2(0,_19,_4v),_4y=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4z=function(_4A){return E(E(_4A).a);},_4B=function(_4C,_4D,_4E){while(1){var _4F=E(_4E);if(!_4F._){return false;}else{if(!B(A3(_4z,_4C,_4D,_4F.a))){_4E=_4F.b;continue;}else{return true;}}}},_4G=function(_4H,_4I){while(1){var _4J=B((function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=_4M.b;if(!B(A1(_4K,_4N))){var _4P=_4K;_4H=_4P;_4I=_4O;return __continue;}else{return new T2(1,_4N,new T(function(){return B(_4G(_4K,_4O));}));}}})(_4H,_4I));if(_4J!=__continue){return _4J;}}},_4Q=function(_4R,_){var _4S=__get(_4R,E(_4i)),_4T=__arr2lst(0,_4S),_4U=B(_4d(_4T,_)),_4V=__app1(E(_4y),_4R),_4W=B(_32(_4x,_4x,_4V,_)),_4X=E(_4W),_4Y=new T(function(){var _4Z=function(_50){return new F(function(){return _4B(_3M,new T(function(){return E(_50).a;}),_4X.a);});};return B(_4G(_4Z,_4U));}),_51=new T(function(){var _52=function(_53){return new F(function(){return _4B(_3M,new T(function(){return E(_53).a;}),_4X.b);});};return B(_4G(_52,_4U));});return new T3(0,_4U,_51,_4Y);},_54=function(_55,_56,_){return new F(function(){return _4Q(E(_56),_);});},_57="touchcancel",_58="touchend",_59="touchmove",_5a="touchstart",_5b=function(_5c){switch(E(_5c)){case 0:return E(_5a);case 1:return E(_59);case 2:return E(_58);default:return E(_57);}},_5d=new T2(0,_5b,_54),_5e=function(_5f,_5g,_){var _5h=B(A1(_5f,_)),_5i=B(A1(_5g,_));return _5h;},_5j=function(_5k,_5l,_){var _5m=B(A1(_5k,_)),_5n=B(A1(_5l,_));return new T(function(){return B(A1(_5m,_5n));});},_5o=function(_5p,_5q,_){var _5r=B(A1(_5q,_));return _5p;},_5s=function(_5t,_5u,_){var _5v=B(A1(_5u,_));return new T(function(){return B(A1(_5t,_5v));});},_5w=new T2(0,_5s,_5o),_5x=function(_5y,_){return _5y;},_5z=function(_5A,_5B,_){var _5C=B(A1(_5A,_));return new F(function(){return A1(_5B,_);});},_5D=new T5(0,_5w,_5x,_5j,_5z,_5e),_5E=new T(function(){return E(_2S);}),_5F=function(_5G){return E(E(_5G).c);},_5H=function(_5I){return new T6(0,_0,_2V,_10,_5I,_0,_0);},_5J=function(_5K,_){var _5L=new T(function(){return B(A2(_5F,_5E,new T(function(){return B(A1(_5H,_5K));})));});return new F(function(){return die(_5L);});},_5M=function(_5N,_){return new F(function(){return _5J(_5N,_);});},_5O=function(_5P){return new F(function(){return A1(_5M,_5P);});},_5Q=function(_5R,_5S,_){var _5T=B(A1(_5R,_));return new F(function(){return A2(_5S,_5T,_);});},_5U=new T5(0,_5D,_5Q,_5z,_5x,_5O),_5V=function(_5W){return E(_5W);},_5X=new T2(0,_5U,_5V),_5Y=new T2(0,_5X,_5x),_5Z=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_60=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_61=new T(function(){return eval("(function(cv){return cv.height})");}),_62=new T(function(){return eval("(function(cv){return cv.width})");}),_63=function(_64,_){var _65=__app1(E(_62),_64),_66=__app1(E(_61),_64),_67=__app1(E(_60),_64),_68=__app1(E(_5Z),_64);return new T2(0,new T2(0,_65,_66),new T2(0,_67,_68));},_69=function(_6a,_6b){while(1){var _6c=E(_6a);if(!_6c._){return (E(_6b)._==0)?true:false;}else{var _6d=E(_6b);if(!_6d._){return false;}else{if(E(_6c.a)!=E(_6d.a)){return false;}else{_6a=_6c.b;_6b=_6d.b;continue;}}}}},_6e=function(_6f,_6g){var _6h=E(_6g);return (_6h._==0)?__Z:new T2(1,new T(function(){return B(A1(_6f,_6h.a));}),new T(function(){return B(_6e(_6f,_6h.b));}));},_6i=function(_6j){return new T1(3,E(B(_6e(_5V,_6j))));},_6k="Tried to deserialie a non-array to a list!",_6l=new T1(0,_6k),_6m=new T1(1,_10),_6n=function(_6o){var _6p=E(_6o);if(!_6p._){return E(_6m);}else{var _6q=B(_6n(_6p.b));return (_6q._==0)?new T1(0,_6q.a):new T1(1,new T2(1,_6p.a,_6q.a));}},_6r=function(_6s){var _6t=E(_6s);if(_6t._==3){return new F(function(){return _6n(_6t.a);});}else{return E(_6l);}},_6u=function(_6v){return new T1(1,_6v);},_6w=new T4(0,_5V,_6i,_6u,_6r),_6x=function(_6y,_6z,_6A){return new F(function(){return A1(_6y,new T2(1,_2A,new T(function(){return B(A1(_6z,_6A));})));});},_6B=function(_6C){return new F(function(){return _I(0,E(_6C),_10);});},_6D=34,_6E=new T2(1,_6D,_10),_6F=new T(function(){return B(unCStr("!!: negative index"));}),_6G=new T(function(){return B(unCStr("Prelude."));}),_6H=new T(function(){return B(_y(_6G,_6F));}),_6I=new T(function(){return B(err(_6H));}),_6J=new T(function(){return B(unCStr("!!: index too large"));}),_6K=new T(function(){return B(_y(_6G,_6J));}),_6L=new T(function(){return B(err(_6K));}),_6M=function(_6N,_6O){while(1){var _6P=E(_6N);if(!_6P._){return E(_6L);}else{var _6Q=E(_6O);if(!_6Q){return E(_6P.a);}else{_6N=_6P.b;_6O=_6Q-1|0;continue;}}}},_6R=function(_6S,_6T){if(_6T>=0){return new F(function(){return _6M(_6S,_6T);});}else{return E(_6I);}},_6U=new T(function(){return B(unCStr("ACK"));}),_6V=new T(function(){return B(unCStr("BEL"));}),_6W=new T(function(){return B(unCStr("BS"));}),_6X=new T(function(){return B(unCStr("SP"));}),_6Y=new T2(1,_6X,_10),_6Z=new T(function(){return B(unCStr("US"));}),_70=new T2(1,_6Z,_6Y),_71=new T(function(){return B(unCStr("RS"));}),_72=new T2(1,_71,_70),_73=new T(function(){return B(unCStr("GS"));}),_74=new T2(1,_73,_72),_75=new T(function(){return B(unCStr("FS"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("ESC"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("SUB"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("EM"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("CAN"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("ETB"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("SYN"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("NAK"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("DC4"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("DC3"));}),_7o=new T2(1,_7n,_7m),_7p=new T(function(){return B(unCStr("DC2"));}),_7q=new T2(1,_7p,_7o),_7r=new T(function(){return B(unCStr("DC1"));}),_7s=new T2(1,_7r,_7q),_7t=new T(function(){return B(unCStr("DLE"));}),_7u=new T2(1,_7t,_7s),_7v=new T(function(){return B(unCStr("SI"));}),_7w=new T2(1,_7v,_7u),_7x=new T(function(){return B(unCStr("SO"));}),_7y=new T2(1,_7x,_7w),_7z=new T(function(){return B(unCStr("CR"));}),_7A=new T2(1,_7z,_7y),_7B=new T(function(){return B(unCStr("FF"));}),_7C=new T2(1,_7B,_7A),_7D=new T(function(){return B(unCStr("VT"));}),_7E=new T2(1,_7D,_7C),_7F=new T(function(){return B(unCStr("LF"));}),_7G=new T2(1,_7F,_7E),_7H=new T(function(){return B(unCStr("HT"));}),_7I=new T2(1,_7H,_7G),_7J=new T2(1,_6W,_7I),_7K=new T2(1,_6V,_7J),_7L=new T2(1,_6U,_7K),_7M=new T(function(){return B(unCStr("ENQ"));}),_7N=new T2(1,_7M,_7L),_7O=new T(function(){return B(unCStr("EOT"));}),_7P=new T2(1,_7O,_7N),_7Q=new T(function(){return B(unCStr("ETX"));}),_7R=new T2(1,_7Q,_7P),_7S=new T(function(){return B(unCStr("STX"));}),_7T=new T2(1,_7S,_7R),_7U=new T(function(){return B(unCStr("SOH"));}),_7V=new T2(1,_7U,_7T),_7W=new T(function(){return B(unCStr("NUL"));}),_7X=new T2(1,_7W,_7V),_7Y=92,_7Z=new T(function(){return B(unCStr("\\DEL"));}),_80=new T(function(){return B(unCStr("\\a"));}),_81=new T(function(){return B(unCStr("\\\\"));}),_82=new T(function(){return B(unCStr("\\SO"));}),_83=new T(function(){return B(unCStr("\\r"));}),_84=new T(function(){return B(unCStr("\\f"));}),_85=new T(function(){return B(unCStr("\\v"));}),_86=new T(function(){return B(unCStr("\\n"));}),_87=new T(function(){return B(unCStr("\\t"));}),_88=new T(function(){return B(unCStr("\\b"));}),_89=function(_8a,_8b){if(_8a<=127){var _8c=E(_8a);switch(_8c){case 92:return new F(function(){return _y(_81,_8b);});break;case 127:return new F(function(){return _y(_7Z,_8b);});break;default:if(_8c<32){var _8d=E(_8c);switch(_8d){case 7:return new F(function(){return _y(_80,_8b);});break;case 8:return new F(function(){return _y(_88,_8b);});break;case 9:return new F(function(){return _y(_87,_8b);});break;case 10:return new F(function(){return _y(_86,_8b);});break;case 11:return new F(function(){return _y(_85,_8b);});break;case 12:return new F(function(){return _y(_84,_8b);});break;case 13:return new F(function(){return _y(_83,_8b);});break;case 14:return new F(function(){return _y(_82,new T(function(){var _8e=E(_8b);if(!_8e._){return __Z;}else{if(E(_8e.a)==72){return B(unAppCStr("\\&",_8e));}else{return E(_8e);}}},1));});break;default:return new F(function(){return _y(new T2(1,_7Y,new T(function(){return B(_6R(_7X,_8d));})),_8b);});}}else{return new T2(1,_8c,_8b);}}}else{var _8f=new T(function(){var _8g=jsShowI(_8a);return B(_y(fromJSStr(_8g),new T(function(){var _8h=E(_8b);if(!_8h._){return __Z;}else{var _8i=E(_8h.a);if(_8i<48){return E(_8h);}else{if(_8i>57){return E(_8h);}else{return B(unAppCStr("\\&",_8h));}}}},1)));});return new T2(1,_7Y,_8f);}},_8j=new T(function(){return B(unCStr("\\\""));}),_8k=function(_8l,_8m){var _8n=E(_8l);if(!_8n._){return E(_8m);}else{var _8o=_8n.b,_8p=E(_8n.a);if(_8p==34){return new F(function(){return _y(_8j,new T(function(){return B(_8k(_8o,_8m));},1));});}else{return new F(function(){return _89(_8p,new T(function(){return B(_8k(_8o,_8m));}));});}}},_8q=function(_8r){return new T2(1,_6D,new T(function(){return B(_8k(_8r,_6E));}));},_8s=function(_8t,_8u){if(_8t<=_8u){var _8v=function(_8w){return new T2(1,_8w,new T(function(){if(_8w!=_8u){return B(_8v(_8w+1|0));}else{return __Z;}}));};return new F(function(){return _8v(_8t);});}else{return __Z;}},_8x=function(_8y){return new F(function(){return _8s(E(_8y),2147483647);});},_8z=function(_8A,_8B,_8C){if(_8C<=_8B){var _8D=new T(function(){var _8E=_8B-_8A|0,_8F=function(_8G){return (_8G>=(_8C-_8E|0))?new T2(1,_8G,new T(function(){return B(_8F(_8G+_8E|0));})):new T2(1,_8G,_10);};return B(_8F(_8B));});return new T2(1,_8A,_8D);}else{return (_8C<=_8A)?new T2(1,_8A,_10):__Z;}},_8H=function(_8I,_8J,_8K){if(_8K>=_8J){var _8L=new T(function(){var _8M=_8J-_8I|0,_8N=function(_8O){return (_8O<=(_8K-_8M|0))?new T2(1,_8O,new T(function(){return B(_8N(_8O+_8M|0));})):new T2(1,_8O,_10);};return B(_8N(_8J));});return new T2(1,_8I,_8L);}else{return (_8K>=_8I)?new T2(1,_8I,_10):__Z;}},_8P=function(_8Q,_8R){if(_8R<_8Q){return new F(function(){return _8z(_8Q,_8R, -2147483648);});}else{return new F(function(){return _8H(_8Q,_8R,2147483647);});}},_8S=function(_8T,_8U){return new F(function(){return _8P(E(_8T),E(_8U));});},_8V=function(_8W,_8X,_8Y){if(_8X<_8W){return new F(function(){return _8z(_8W,_8X,_8Y);});}else{return new F(function(){return _8H(_8W,_8X,_8Y);});}},_8Z=function(_90,_91,_92){return new F(function(){return _8V(E(_90),E(_91),E(_92));});},_93=function(_94,_95){return new F(function(){return _8s(E(_94),E(_95));});},_96=function(_97){return E(_97);},_98=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_99=new T(function(){return B(err(_98));}),_9a=function(_9b){var _9c=E(_9b);return (_9c==( -2147483648))?E(_99):_9c-1|0;},_9d=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_9e=new T(function(){return B(err(_9d));}),_9f=function(_9g){var _9h=E(_9g);return (_9h==2147483647)?E(_9e):_9h+1|0;},_9i={_:0,a:_9f,b:_9a,c:_96,d:_96,e:_8x,f:_8S,g:_93,h:_8Z},_9j=function(_9k,_9l){if(_9k<=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{if(_9l>=0){if(_9k>=0){return new F(function(){return quot(_9k,_9l);});}else{if(_9l<=0){return new F(function(){return quot(_9k,_9l);});}else{return quot(_9k+1|0,_9l)-1|0;}}}else{return quot(_9k-1|0,_9l)-1|0;}}},_9m=new T(function(){return B(unCStr("base"));}),_9n=new T(function(){return B(unCStr("GHC.Exception"));}),_9o=new T(function(){return B(unCStr("ArithException"));}),_9p=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9m,_9n,_9o),_9q=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9p,_10,_10),_9r=function(_9s){return E(_9q);},_9t=function(_9u){var _9v=E(_9u);return new F(function(){return _1s(B(_1q(_9v.a)),_9r,_9v.b);});},_9w=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_9x=new T(function(){return B(unCStr("denormal"));}),_9y=new T(function(){return B(unCStr("divide by zero"));}),_9z=new T(function(){return B(unCStr("loss of precision"));}),_9A=new T(function(){return B(unCStr("arithmetic underflow"));}),_9B=new T(function(){return B(unCStr("arithmetic overflow"));}),_9C=function(_9D,_9E){switch(E(_9D)){case 0:return new F(function(){return _y(_9B,_9E);});break;case 1:return new F(function(){return _y(_9A,_9E);});break;case 2:return new F(function(){return _y(_9z,_9E);});break;case 3:return new F(function(){return _y(_9y,_9E);});break;case 4:return new F(function(){return _y(_9x,_9E);});break;default:return new F(function(){return _y(_9w,_9E);});}},_9F=function(_9G){return new F(function(){return _9C(_9G,_10);});},_9H=function(_9I,_9J,_9K){return new F(function(){return _9C(_9J,_9K);});},_9L=function(_9M,_9N){return new F(function(){return _2D(_9C,_9M,_9N);});},_9O=new T3(0,_9H,_9F,_9L),_9P=new T(function(){return new T5(0,_9r,_9O,_9Q,_9t,_9F);}),_9Q=function(_9R){return new T2(0,_9P,_9R);},_9S=3,_9T=new T(function(){return B(_9Q(_9S));}),_9U=new T(function(){return die(_9T);}),_9V=0,_9W=new T(function(){return B(_9Q(_9V));}),_9X=new T(function(){return die(_9W);}),_9Y=function(_9Z,_a0){var _a1=E(_a0);switch(_a1){case  -1:var _a2=E(_9Z);if(_a2==( -2147483648)){return E(_9X);}else{return new F(function(){return _9j(_a2, -1);});}break;case 0:return E(_9U);default:return new F(function(){return _9j(_9Z,_a1);});}},_a3=function(_a4,_a5){return new F(function(){return _9Y(E(_a4),E(_a5));});},_a6=0,_a7=new T2(0,_9X,_a6),_a8=function(_a9,_aa){var _ab=E(_a9),_ac=E(_aa);switch(_ac){case  -1:var _ad=E(_ab);if(_ad==( -2147483648)){return E(_a7);}else{if(_ad<=0){if(_ad>=0){var _ae=quotRemI(_ad, -1);return new T2(0,_ae.a,_ae.b);}else{var _af=quotRemI(_ad, -1);return new T2(0,_af.a,_af.b);}}else{var _ag=quotRemI(_ad-1|0, -1);return new T2(0,_ag.a-1|0,(_ag.b+( -1)|0)+1|0);}}break;case 0:return E(_9U);default:if(_ab<=0){if(_ab>=0){var _ah=quotRemI(_ab,_ac);return new T2(0,_ah.a,_ah.b);}else{if(_ac<=0){var _ai=quotRemI(_ab,_ac);return new T2(0,_ai.a,_ai.b);}else{var _aj=quotRemI(_ab+1|0,_ac);return new T2(0,_aj.a-1|0,(_aj.b+_ac|0)-1|0);}}}else{if(_ac>=0){if(_ab>=0){var _ak=quotRemI(_ab,_ac);return new T2(0,_ak.a,_ak.b);}else{if(_ac<=0){var _al=quotRemI(_ab,_ac);return new T2(0,_al.a,_al.b);}else{var _am=quotRemI(_ab+1|0,_ac);return new T2(0,_am.a-1|0,(_am.b+_ac|0)-1|0);}}}else{var _an=quotRemI(_ab-1|0,_ac);return new T2(0,_an.a-1|0,(_an.b+_ac|0)+1|0);}}}},_ao=function(_ap,_aq){var _ar=_ap%_aq;if(_ap<=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _as=E(_ar);return (_as==0)?0:_as+_aq|0;}}}else{if(_aq>=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _at=E(_ar);return (_at==0)?0:_at+_aq|0;}}}else{var _au=E(_ar);return (_au==0)?0:_au+_aq|0;}}},_av=function(_aw,_ax){var _ay=E(_ax);switch(_ay){case  -1:return E(_a6);case 0:return E(_9U);default:return new F(function(){return _ao(E(_aw),_ay);});}},_az=function(_aA,_aB){var _aC=E(_aA),_aD=E(_aB);switch(_aD){case  -1:var _aE=E(_aC);if(_aE==( -2147483648)){return E(_9X);}else{return new F(function(){return quot(_aE, -1);});}break;case 0:return E(_9U);default:return new F(function(){return quot(_aC,_aD);});}},_aF=function(_aG,_aH){var _aI=E(_aG),_aJ=E(_aH);switch(_aJ){case  -1:var _aK=E(_aI);if(_aK==( -2147483648)){return E(_a7);}else{var _aL=quotRemI(_aK, -1);return new T2(0,_aL.a,_aL.b);}break;case 0:return E(_9U);default:var _aM=quotRemI(_aI,_aJ);return new T2(0,_aM.a,_aM.b);}},_aN=function(_aO,_aP){var _aQ=E(_aP);switch(_aQ){case  -1:return E(_a6);case 0:return E(_9U);default:return E(_aO)%_aQ;}},_aR=function(_aS){return new T1(0,_aS);},_aT=function(_aU){return new F(function(){return _aR(E(_aU));});},_aV=new T1(0,1),_aW=function(_aX){return new T2(0,E(B(_aR(E(_aX)))),E(_aV));},_aY=function(_aZ,_b0){return imul(E(_aZ),E(_b0))|0;},_b1=function(_b2,_b3){return E(_b2)+E(_b3)|0;},_b4=function(_b5,_b6){return E(_b5)-E(_b6)|0;},_b7=function(_b8){var _b9=E(_b8);return (_b9<0)? -_b9:E(_b9);},_ba=function(_bb){var _bc=E(_bb);if(!_bc._){return E(_bc.a);}else{return new F(function(){return I_toInt(_bc.a);});}},_bd=function(_be){return new F(function(){return _ba(_be);});},_bf=function(_bg){return  -E(_bg);},_bh= -1,_bi=0,_bj=1,_bk=function(_bl){var _bm=E(_bl);return (_bm>=0)?(E(_bm)==0)?E(_bi):E(_bj):E(_bh);},_bn={_:0,a:_b1,b:_b4,c:_aY,d:_bf,e:_b7,f:_bk,g:_bd},_bo=function(_bp,_bq){var _br=E(_bp),_bs=E(_bq);return (_br>_bs)?E(_br):E(_bs);},_bt=function(_bu,_bv){var _bw=E(_bu),_bx=E(_bv);return (_bw>_bx)?E(_bx):E(_bw);},_by=function(_bz,_bA){return (_bz>=_bA)?(_bz!=_bA)?2:1:0;},_bB=function(_bC,_bD){return new F(function(){return _by(E(_bC),E(_bD));});},_bE=function(_bF,_bG){return E(_bF)>=E(_bG);},_bH=function(_bI,_bJ){return E(_bI)>E(_bJ);},_bK=function(_bL,_bM){return E(_bL)<=E(_bM);},_bN=function(_bO,_bP){return E(_bO)<E(_bP);},_bQ={_:0,a:_3M,b:_bB,c:_bN,d:_bK,e:_bH,f:_bE,g:_bo,h:_bt},_bR=new T3(0,_bn,_bQ,_aW),_bS={_:0,a:_bR,b:_9i,c:_az,d:_aN,e:_a3,f:_av,g:_aF,h:_a8,i:_aT},_bT=function(_bU){var _bV=E(_bU);return new F(function(){return Math.log(_bV+(_bV+1)*Math.sqrt((_bV-1)/(_bV+1)));});},_bW=function(_bX){var _bY=E(_bX);return new F(function(){return Math.log(_bY+Math.sqrt(1+_bY*_bY));});},_bZ=function(_c0){var _c1=E(_c0);return 0.5*Math.log((1+_c1)/(1-_c1));},_c2=function(_c3,_c4){return Math.log(E(_c4))/Math.log(E(_c3));},_c5=3.141592653589793,_c6=new T1(0,1),_c7=function(_c8,_c9){var _ca=E(_c8);if(!_ca._){var _cb=_ca.a,_cc=E(_c9);if(!_cc._){var _cd=_cc.a;return (_cb!=_cd)?(_cb>_cd)?2:0:1;}else{var _ce=I_compareInt(_cc.a,_cb);return (_ce<=0)?(_ce>=0)?1:2:0;}}else{var _cf=_ca.a,_cg=E(_c9);if(!_cg._){var _ch=I_compareInt(_cf,_cg.a);return (_ch>=0)?(_ch<=0)?1:2:0;}else{var _ci=I_compare(_cf,_cg.a);return (_ci>=0)?(_ci<=0)?1:2:0;}}},_cj=function(_ck,_cl){var _cm=E(_ck);return (_cm._==0)?_cm.a*Math.pow(2,_cl):I_toNumber(_cm.a)*Math.pow(2,_cl);},_cn=function(_co,_cp){var _cq=E(_co);if(!_cq._){var _cr=_cq.a,_cs=E(_cp);return (_cs._==0)?_cr==_cs.a:(I_compareInt(_cs.a,_cr)==0)?true:false;}else{var _ct=_cq.a,_cu=E(_cp);return (_cu._==0)?(I_compareInt(_ct,_cu.a)==0)?true:false:(I_compare(_ct,_cu.a)==0)?true:false;}},_cv=function(_cw,_cx){while(1){var _cy=E(_cw);if(!_cy._){var _cz=_cy.a,_cA=E(_cx);if(!_cA._){var _cB=_cA.a,_cC=addC(_cz,_cB);if(!E(_cC.b)){return new T1(0,_cC.a);}else{_cw=new T1(1,I_fromInt(_cz));_cx=new T1(1,I_fromInt(_cB));continue;}}else{_cw=new T1(1,I_fromInt(_cz));_cx=_cA;continue;}}else{var _cD=E(_cx);if(!_cD._){_cw=_cy;_cx=new T1(1,I_fromInt(_cD.a));continue;}else{return new T1(1,I_add(_cy.a,_cD.a));}}}},_cE=function(_cF,_cG){while(1){var _cH=E(_cF);if(!_cH._){var _cI=E(_cH.a);if(_cI==( -2147483648)){_cF=new T1(1,I_fromInt( -2147483648));continue;}else{var _cJ=E(_cG);if(!_cJ._){var _cK=_cJ.a;return new T2(0,new T1(0,quot(_cI,_cK)),new T1(0,_cI%_cK));}else{_cF=new T1(1,I_fromInt(_cI));_cG=_cJ;continue;}}}else{var _cL=E(_cG);if(!_cL._){_cF=_cH;_cG=new T1(1,I_fromInt(_cL.a));continue;}else{var _cM=I_quotRem(_cH.a,_cL.a);return new T2(0,new T1(1,_cM.a),new T1(1,_cM.b));}}}},_cN=new T1(0,0),_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR._){_cP=new T1(1,I_fromInt(_cR.a));continue;}else{return new T1(1,I_shiftLeft(_cR.a,_cQ));}}},_cS=function(_cT,_cU,_cV){if(!B(_cn(_cV,_cN))){var _cW=B(_cE(_cU,_cV)),_cX=_cW.a;switch(B(_c7(B(_cO(_cW.b,1)),_cV))){case 0:return new F(function(){return _cj(_cX,_cT);});break;case 1:if(!(B(_ba(_cX))&1)){return new F(function(){return _cj(_cX,_cT);});}else{return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}break;default:return new F(function(){return _cj(B(_cv(_cX,_c6)),_cT);});}}else{return E(_9U);}},_cY=function(_cZ,_d0){var _d1=E(_cZ);if(!_d1._){var _d2=_d1.a,_d3=E(_d0);return (_d3._==0)?_d2>_d3.a:I_compareInt(_d3.a,_d2)<0;}else{var _d4=_d1.a,_d5=E(_d0);return (_d5._==0)?I_compareInt(_d4,_d5.a)>0:I_compare(_d4,_d5.a)>0;}},_d6=new T1(0,1),_d7=function(_d8,_d9){var _da=E(_d8);if(!_da._){var _db=_da.a,_dc=E(_d9);return (_dc._==0)?_db<_dc.a:I_compareInt(_dc.a,_db)>0;}else{var _dd=_da.a,_de=E(_d9);return (_de._==0)?I_compareInt(_dd,_de.a)<0:I_compare(_dd,_de.a)<0;}},_df=new T(function(){return B(unCStr("base"));}),_dg=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dh=new T(function(){return B(unCStr("PatternMatchFail"));}),_di=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_df,_dg,_dh),_dj=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_di,_10,_10),_dk=function(_dl){return E(_dj);},_dm=function(_dn){var _do=E(_dn);return new F(function(){return _1s(B(_1q(_do.a)),_dk,_do.b);});},_dp=function(_dq){return E(E(_dq).a);},_dr=function(_ds){return new T2(0,_dt,_ds);},_du=function(_dv,_dw){return new F(function(){return _y(E(_dv).a,_dw);});},_dx=function(_dy,_dz){return new F(function(){return _2D(_du,_dy,_dz);});},_dA=function(_dB,_dC,_dD){return new F(function(){return _y(E(_dC).a,_dD);});},_dE=new T3(0,_dA,_dp,_dx),_dt=new T(function(){return new T5(0,_dk,_dE,_dr,_dm,_dp);}),_dF=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_dG=function(_dH,_dI){return new F(function(){return die(new T(function(){return B(A2(_5F,_dI,_dH));}));});},_dJ=function(_dK,_9R){return new F(function(){return _dG(_dK,_9R);});},_dL=function(_dM,_dN){var _dO=E(_dN);if(!_dO._){return new T2(0,_10,_10);}else{var _dP=_dO.a;if(!B(A1(_dM,_dP))){return new T2(0,_10,_dO);}else{var _dQ=new T(function(){var _dR=B(_dL(_dM,_dO.b));return new T2(0,_dR.a,_dR.b);});return new T2(0,new T2(1,_dP,new T(function(){return E(E(_dQ).a);})),new T(function(){return E(E(_dQ).b);}));}}},_dS=32,_dT=new T(function(){return B(unCStr("\n"));}),_dU=function(_dV){return (E(_dV)==124)?false:true;},_dW=function(_dX,_dY){var _dZ=B(_dL(_dU,B(unCStr(_dX)))),_e0=_dZ.a,_e1=function(_e2,_e3){var _e4=new T(function(){var _e5=new T(function(){return B(_y(_dY,new T(function(){return B(_y(_e3,_dT));},1)));});return B(unAppCStr(": ",_e5));},1);return new F(function(){return _y(_e2,_e4);});},_e6=E(_dZ.b);if(!_e6._){return new F(function(){return _e1(_e0,_10);});}else{if(E(_e6.a)==124){return new F(function(){return _e1(_e0,new T2(1,_dS,_e6.b));});}else{return new F(function(){return _e1(_e0,_10);});}}},_e7=function(_e8){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_e8,_dF));})),_dt);});},_e9=function(_ea){var _eb=function(_ec,_ed){while(1){if(!B(_d7(_ec,_ea))){if(!B(_cY(_ec,_ea))){if(!B(_cn(_ec,_ea))){return new F(function(){return _e7("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ed);}}else{return _ed-1|0;}}else{var _ee=B(_cO(_ec,1)),_ef=_ed+1|0;_ec=_ee;_ed=_ef;continue;}}};return new F(function(){return _eb(_d6,0);});},_eg=function(_eh){var _ei=E(_eh);if(!_ei._){var _ej=_ei.a>>>0;if(!_ej){return  -1;}else{var _ek=function(_el,_em){while(1){if(_el>=_ej){if(_el<=_ej){if(_el!=_ej){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_em);}}else{return _em-1|0;}}else{var _en=imul(_el,2)>>>0,_eo=_em+1|0;_el=_en;_em=_eo;continue;}}};return new F(function(){return _ek(1,0);});}}else{return new F(function(){return _e9(_ei);});}},_ep=function(_eq){var _er=E(_eq);if(!_er._){var _es=_er.a>>>0;if(!_es){return new T2(0, -1,0);}else{var _et=function(_eu,_ev){while(1){if(_eu>=_es){if(_eu<=_es){if(_eu!=_es){return new F(function(){return _e7("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ev);}}else{return _ev-1|0;}}else{var _ew=imul(_eu,2)>>>0,_ex=_ev+1|0;_eu=_ew;_ev=_ex;continue;}}};return new T2(0,B(_et(1,0)),(_es&_es-1>>>0)>>>0&4294967295);}}else{var _ey=_er.a;return new T2(0,B(_eg(_er)),I_compareInt(I_and(_ey,I_sub(_ey,I_fromInt(1))),0));}},_ez=function(_eA,_eB){var _eC=E(_eA);if(!_eC._){var _eD=_eC.a,_eE=E(_eB);return (_eE._==0)?_eD<=_eE.a:I_compareInt(_eE.a,_eD)>=0;}else{var _eF=_eC.a,_eG=E(_eB);return (_eG._==0)?I_compareInt(_eF,_eG.a)<=0:I_compare(_eF,_eG.a)<=0;}},_eH=function(_eI,_eJ){while(1){var _eK=E(_eI);if(!_eK._){var _eL=_eK.a,_eM=E(_eJ);if(!_eM._){return new T1(0,(_eL>>>0&_eM.a>>>0)>>>0&4294967295);}else{_eI=new T1(1,I_fromInt(_eL));_eJ=_eM;continue;}}else{var _eN=E(_eJ);if(!_eN._){_eI=_eK;_eJ=new T1(1,I_fromInt(_eN.a));continue;}else{return new T1(1,I_and(_eK.a,_eN.a));}}}},_eO=function(_eP,_eQ){while(1){var _eR=E(_eP);if(!_eR._){var _eS=_eR.a,_eT=E(_eQ);if(!_eT._){var _eU=_eT.a,_eV=subC(_eS,_eU);if(!E(_eV.b)){return new T1(0,_eV.a);}else{_eP=new T1(1,I_fromInt(_eS));_eQ=new T1(1,I_fromInt(_eU));continue;}}else{_eP=new T1(1,I_fromInt(_eS));_eQ=_eT;continue;}}else{var _eW=E(_eQ);if(!_eW._){_eP=_eR;_eQ=new T1(1,I_fromInt(_eW.a));continue;}else{return new T1(1,I_sub(_eR.a,_eW.a));}}}},_eX=new T1(0,2),_eY=function(_eZ,_f0){var _f1=E(_eZ);if(!_f1._){var _f2=(_f1.a>>>0&(2<<_f0>>>0)-1>>>0)>>>0,_f3=1<<_f0>>>0;return (_f3<=_f2)?(_f3>=_f2)?1:2:0;}else{var _f4=B(_eH(_f1,B(_eO(B(_cO(_eX,_f0)),_d6)))),_f5=B(_cO(_d6,_f0));return (!B(_cY(_f5,_f4)))?(!B(_d7(_f5,_f4)))?1:2:0;}},_f6=function(_f7,_f8){while(1){var _f9=E(_f7);if(!_f9._){_f7=new T1(1,I_fromInt(_f9.a));continue;}else{return new T1(1,I_shiftRight(_f9.a,_f8));}}},_fa=function(_fb,_fc,_fd,_fe){var _ff=B(_ep(_fe)),_fg=_ff.a;if(!E(_ff.b)){var _fh=B(_eg(_fd));if(_fh<((_fg+_fb|0)-1|0)){var _fi=_fg+(_fb-_fc|0)|0;if(_fi>0){if(_fi>_fh){if(_fi<=(_fh+1|0)){if(!E(B(_ep(_fd)).b)){return 0;}else{return new F(function(){return _cj(_c6,_fb-_fc|0);});}}else{return 0;}}else{var _fj=B(_f6(_fd,_fi));switch(B(_eY(_fd,_fi-1|0))){case 0:return new F(function(){return _cj(_fj,_fb-_fc|0);});break;case 1:if(!(B(_ba(_fj))&1)){return new F(function(){return _cj(_fj,_fb-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}break;default:return new F(function(){return _cj(B(_cv(_fj,_c6)),_fb-_fc|0);});}}}else{return new F(function(){return _cj(_fd,(_fb-_fc|0)-_fi|0);});}}else{if(_fh>=_fc){var _fk=B(_f6(_fd,(_fh+1|0)-_fc|0));switch(B(_eY(_fd,_fh-_fc|0))){case 0:return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});break;case 2:return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});break;default:if(!(B(_ba(_fk))&1)){return new F(function(){return _cj(_fk,((_fh-_fg|0)+1|0)-_fc|0);});}else{return new F(function(){return _cj(B(_cv(_fk,_c6)),((_fh-_fg|0)+1|0)-_fc|0);});}}}else{return new F(function(){return _cj(_fd, -_fg);});}}}else{var _fl=B(_eg(_fd))-_fg|0,_fm=function(_fn){var _fo=function(_fp,_fq){if(!B(_ez(B(_cO(_fq,_fc)),_fp))){return new F(function(){return _cS(_fn-_fc|0,_fp,_fq);});}else{return new F(function(){return _cS((_fn-_fc|0)+1|0,_fp,B(_cO(_fq,1)));});}};if(_fn>=_fc){if(_fn!=_fc){return new F(function(){return _fo(_fd,new T(function(){return B(_cO(_fe,_fn-_fc|0));}));});}else{return new F(function(){return _fo(_fd,_fe);});}}else{return new F(function(){return _fo(new T(function(){return B(_cO(_fd,_fc-_fn|0));}),_fe);});}};if(_fb>_fl){return new F(function(){return _fm(_fb);});}else{return new F(function(){return _fm(_fl);});}}},_fr=new T1(0,2147483647),_fs=new T(function(){return B(_cv(_fr,_d6));}),_ft=function(_fu){var _fv=E(_fu);if(!_fv._){var _fw=E(_fv.a);return (_fw==( -2147483648))?E(_fs):new T1(0, -_fw);}else{return new T1(1,I_negate(_fv.a));}},_fx=new T(function(){return 0/0;}),_fy=new T(function(){return  -1/0;}),_fz=new T(function(){return 1/0;}),_fA=0,_fB=function(_fC,_fD){if(!B(_cn(_fD,_cN))){if(!B(_cn(_fC,_cN))){if(!B(_d7(_fC,_cN))){return new F(function(){return _fa( -1021,53,_fC,_fD);});}else{return  -B(_fa( -1021,53,B(_ft(_fC)),_fD));}}else{return E(_fA);}}else{return (!B(_cn(_fC,_cN)))?(!B(_d7(_fC,_cN)))?E(_fz):E(_fy):E(_fx);}},_fE=function(_fF){var _fG=E(_fF);return new F(function(){return _fB(_fG.a,_fG.b);});},_fH=function(_fI){return 1/E(_fI);},_fJ=function(_fK){var _fL=E(_fK);return (_fL!=0)?(_fL<=0)? -_fL:E(_fL):E(_fA);},_fM=function(_fN){var _fO=E(_fN);if(!_fO._){return _fO.a;}else{return new F(function(){return I_toNumber(_fO.a);});}},_fP=function(_fQ){return new F(function(){return _fM(_fQ);});},_fR=1,_fS= -1,_fT=function(_fU){var _fV=E(_fU);return (_fV<=0)?(_fV>=0)?E(_fV):E(_fS):E(_fR);},_fW=function(_fX,_fY){return E(_fX)-E(_fY);},_fZ=function(_g0){return  -E(_g0);},_g1=function(_g2,_g3){return E(_g2)+E(_g3);},_g4=function(_g5,_g6){return E(_g5)*E(_g6);},_g7={_:0,a:_g1,b:_fW,c:_g4,d:_fZ,e:_fJ,f:_fT,g:_fP},_g8=function(_g9,_ga){return E(_g9)/E(_ga);},_gb=new T4(0,_g7,_g8,_fH,_fE),_gc=function(_gd){return new F(function(){return Math.acos(E(_gd));});},_ge=function(_gf){return new F(function(){return Math.asin(E(_gf));});},_gg=function(_gh){return new F(function(){return Math.atan(E(_gh));});},_gi=function(_gj){return new F(function(){return Math.cos(E(_gj));});},_gk=function(_gl){return new F(function(){return cosh(E(_gl));});},_gm=function(_gn){return new F(function(){return Math.exp(E(_gn));});},_go=function(_gp){return new F(function(){return Math.log(E(_gp));});},_gq=function(_gr,_gs){return new F(function(){return Math.pow(E(_gr),E(_gs));});},_gt=function(_gu){return new F(function(){return Math.sin(E(_gu));});},_gv=function(_gw){return new F(function(){return sinh(E(_gw));});},_gx=function(_gy){return new F(function(){return Math.sqrt(E(_gy));});},_gz=function(_gA){return new F(function(){return Math.tan(E(_gA));});},_gB=function(_gC){return new F(function(){return tanh(E(_gC));});},_gD={_:0,a:_gb,b:_c5,c:_gm,d:_go,e:_gx,f:_gq,g:_c2,h:_gt,i:_gi,j:_gz,k:_ge,l:_gc,m:_gg,n:_gv,o:_gk,p:_gB,q:_bW,r:_bT,s:_bZ},_gE=0,_gF=function(_){return _gE;},_gG=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_gH=new T(function(){return eval("(function(ctx){ctx.save();})");}),_gI=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_gJ=function(_gK,_gL,_gM,_){var _gN=__app1(E(_gH),_gM),_gO=__app2(E(_gI),_gM,E(_gK)),_gP=B(A2(_gL,_gM,_)),_gQ=__app1(E(_gG),_gM);return new F(function(){return _gF(_);});},_gR=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_gS=function(_gT,_gU,_gV,_gW,_){var _gX=__app1(E(_gH),_gW),_gY=__app3(E(_gR),_gW,E(_gT),E(_gU)),_gZ=B(A2(_gV,_gW,_)),_h0=__app1(E(_gG),_gW);return new F(function(){return _gF(_);});},_h1=function(_h2,_h3){return E(_h2)!=E(_h3);},_h4=function(_h5,_h6){return E(_h5)==E(_h6);},_h7=new T2(0,_h4,_h1),_h8=function(_h9){return E(E(_h9).a);},_ha=function(_hb){return E(E(_hb).a);},_hc=function(_hd){return E(E(_hd).b);},_he=function(_hf){return E(E(_hf).g);},_hg=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_hh=0,_hi=3.3333333333333335,_hj=16.666666666666668,_hk=function(_hl){return E(E(_hl).b);},_hm=new T1(0,0),_hn=new T1(0,2),_ho=function(_hp){return E(E(_hp).i);},_hq=function(_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy){var _hz=new T(function(){var _hA=E(_hy);if(_hA<=31){return B(_4B(_h7,_hA,_hg));}else{if(_hA>=128){return B(_4B(_h7,_hA,_hg));}else{return true;}}}),_hB=new T(function(){if(E(_hu)==8){return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28+20;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20+8*(E(_hv)-1);}));}else{return new T2(0,new T(function(){return B(_fM(B(A2(_ho,_hs,_hw))))*28;}),new T(function(){return B(_fM(B(A2(_ho,_ht,_hx))))*20;}));}}),_hC=new T(function(){var _hD=B(_h8(_hr));if(!E(_hz)){return B(A2(_he,B(_ha(_hD)),_hm));}else{return B(A3(_hc,_hD,new T(function(){return B(_hk(_hr));}),new T(function(){return B(A2(_he,B(_ha(_hD)),_hn));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_hB).a);}),new T(function(){return E(E(_hB).b);})),new T2(0,new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hi);}}),new T(function(){if(!E(_hz)){return E(_hh);}else{return E(_hj);}})),_hC);},_hE=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_hF=function(_hG,_hH,_hI){var _hJ=new T(function(){return toJSStr(E(_hI));});return function(_hK,_){var _hL=__app4(E(_hE),E(_hK),E(_hJ),E(_hG),E(_hH));return new F(function(){return _gF(_);});};},_hM=0,_hN=",",_hO="rgba(",_hP=new T(function(){return toJSStr(_10);}),_hQ="rgb(",_hR=")",_hS=new T2(1,_hR,_10),_hT=function(_hU){var _hV=E(_hU);if(!_hV._){var _hW=jsCat(new T2(1,_hQ,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),_hS)))))),E(_hP));return E(_hW);}else{var _hX=jsCat(new T2(1,_hO,new T2(1,new T(function(){return String(_hV.a);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.b);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.c);}),new T2(1,_hN,new T2(1,new T(function(){return String(_hV.d);}),_hS)))))))),E(_hP));return E(_hX);}},_hY="strokeStyle",_hZ="fillStyle",_i0=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_i1=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_i2=function(_i3,_i4){var _i5=new T(function(){return B(_hT(_i3));});return function(_i6,_){var _i7=E(_i6),_i8=E(_hZ),_i9=E(_i0),_ia=__app2(_i9,_i7,_i8),_ib=E(_hY),_ic=__app2(_i9,_i7,_ib),_id=E(_i5),_ie=E(_i1),_if=__app3(_ie,_i7,_i8,_id),_ig=__app3(_ie,_i7,_ib,_id),_ih=B(A2(_i4,_i7,_)),_ii=String(_ia),_ij=__app3(_ie,_i7,_i8,_ii),_ik=String(_ic),_il=__app3(_ie,_i7,_ib,_ik);return new F(function(){return _gF(_);});};},_im="font",_in=function(_io,_ip){var _iq=new T(function(){return toJSStr(E(_io));});return function(_ir,_){var _is=E(_ir),_it=E(_im),_iu=__app2(E(_i0),_is,_it),_iv=E(_i1),_iw=__app3(_iv,_is,_it,E(_iq)),_ix=B(A2(_ip,_is,_)),_iy=String(_iu),_iz=__app3(_iv,_is,_it,_iy);return new F(function(){return _gF(_);});};},_iA=new T(function(){return B(unCStr("px IPAGothic"));}),_iB=function(_iC,_iD,_iE,_iF,_iG,_iH,_iI,_){var _iJ=new T(function(){var _iK=new T(function(){var _iL=B(_hq(_gD,_bS,_bS,_iE,_iF,_iG,_iH,_iI)),_iM=E(_iL.a),_iN=E(_iL.b);return new T5(0,_iM.a,_iM.b,_iN.a,_iN.b,_iL.c);}),_iO=new T(function(){var _iP=E(_iK);return E(_iP.a)+E(_iP.c);}),_iQ=new T(function(){var _iR=E(_iK);return E(_iR.b)-E(_iR.d);}),_iS=new T(function(){return E(E(_iK).e);}),_iT=new T(function(){return B(_hF(_hM,_hM,new T2(1,_iI,_10)));}),_iU=function(_iV,_){return new F(function(){return _gJ(_iS,_iT,E(_iV),_);});};return B(_in(new T(function(){return B(_y(B(_I(0,E(_iE),_10)),_iA));},1),function(_iW,_){return new F(function(){return _gS(_iO,_iQ,_iU,E(_iW),_);});}));});return new F(function(){return A(_i2,[_iD,_iJ,_iC,_]);});},_iX=new T3(0,153,255,255),_iY=new T2(1,_iX,_10),_iZ=new T3(0,255,153,204),_j0=new T2(1,_iZ,_iY),_j1=new T3(0,255,204,153),_j2=new T2(1,_j1,_j0),_j3=new T3(0,200,255,200),_j4=new T2(1,_j3,_j2),_j5=20,_j6=64,_j7=1,_j8=2,_j9=8,_ja=function(_jb,_jc,_jd,_je,_jf,_jg,_jh,_){while(1){var _ji=B((function(_jj,_jk,_jl,_jm,_jn,_jo,_jp,_){var _jq=E(_jp);if(!_jq._){return _gE;}else{var _jr=_jq.b,_js=E(_jq.a),_jt=E(_js);switch(_jt){case 10:var _ju=_jj,_jv=_jk,_jw=_jm,_jx=_jm;_jb=_ju;_jc=_jv;_jd=0;_je=_jw;_jf=new T(function(){return E(_jn)-1|0;});_jg=_jx;_jh=_jr;return __continue;case 123:return new F(function(){return _jy(_jj,_jk,_jl,_jm,_jn,_jo,_jr,_);});break;case 65306:var _jz=new T(function(){return B(_6R(_j4,_jl));}),_jA=function(_jB,_jC,_jD,_jE,_jF,_jG,_){while(1){var _jH=B((function(_jI,_jJ,_jK,_jL,_jM,_jN,_){var _jO=E(_jN);if(!_jO._){return _gE;}else{var _jP=_jO.b,_jQ=E(_jO.a);if(E(_jQ)==65306){var _jR=new T(function(){var _jS=E(_jM);if((_jS+1)*20<=E(_jk)-10){return new T2(0,_jL,_jS+1|0);}else{return new T2(0,new T(function(){return E(_jL)-1|0;}),_jJ);}});return new F(function(){return _ja(_jI,_jk,_jl,_jJ,new T(function(){return E(E(_jR).a);}),new T(function(){return E(E(_jR).b);}),_jP,_);});}else{var _jT=E(_jI),_jU=B(_iB(_jT.a,_jz,_j9,_jK,_jL,_jM,_jQ,_)),_jV=_jJ,_jW=_jK+1,_jX=_jL,_jY=_jM;_jB=_jT;_jC=_jV;_jD=_jW;_jE=_jX;_jF=_jY;_jG=_jP;return __continue;}}})(_jB,_jC,_jD,_jE,_jF,_jG,_));if(_jH!=__continue){return _jH;}}};return new F(function(){return _jA(_jj,_jm,0,new T(function(){if(E(_jm)!=E(_jo)){return E(_jn);}else{return E(_jn)+1|0;}}),new T(function(){var _jZ=E(_jo);if(E(_jm)!=_jZ){return _jZ-1|0;}else{var _k0=(E(_jk)-10)/20,_k1=_k0&4294967295;if(_k0>=_k1){return _k1;}else{return _k1-1|0;}}}),_jr,_);});break;default:var _k2=function(_k3,_k4){var _k5=new T(function(){switch(E(_jt)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _jl;}}),_k6=new T(function(){var _k7=E(_jo);if((_k7+1)*20<=E(_jk)-10){return new T2(0,_jn,_k7+1|0);}else{return new T2(0,new T(function(){return E(_jn)-1|0;}),_jm);}});if(E(_k3)==64){return new F(function(){return _k8(_jj,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}else{var _k9=E(_jj),_ka=B(_iB(_k9.a,new T(function(){return B(_6R(_j4,E(_k5)));},1),_j5,_hM,_jn,_jo,_k4,_));return new F(function(){return _k8(_k9,_jk,_k5,_jm,new T(function(){return E(E(_k6).a);}),new T(function(){return E(E(_k6).b);}),_jr,_);});}},_kb=E(_jt);switch(_kb){case 42:return new F(function(){return _k2(64,_j6);});break;case 12289:return new F(function(){return _k2(64,_j6);});break;case 12290:return new F(function(){return _k2(64,_j6);});break;default:return new F(function(){return _k2(_kb,_js);});}}}})(_jb,_jc,_jd,_je,_jf,_jg,_jh,_));if(_ji!=__continue){return _ji;}}},_k8=function(_kc,_kd,_ke,_kf,_kg,_kh,_ki,_){var _kj=E(_ki);if(!_kj._){return _gE;}else{var _kk=_kj.b,_kl=E(_kj.a),_km=E(_kl);switch(_km){case 10:return new F(function(){return _ja(_kc,_kd,0,_kf,new T(function(){return E(_kg)-1|0;}),_kf,_kk,_);});break;case 123:return new F(function(){return _jy(_kc,_kd,_ke,_kf,_kg,_kh,_kk,_);});break;case 65306:var _kn=new T(function(){return B(_6R(_j4,E(_ke)));}),_ko=function(_kp,_kq,_kr,_ks,_kt,_ku,_){while(1){var _kv=B((function(_kw,_kx,_ky,_kz,_kA,_kB,_){var _kC=E(_kB);if(!_kC._){return _gE;}else{var _kD=_kC.b,_kE=E(_kC.a);if(E(_kE)==65306){var _kF=new T(function(){var _kG=E(_kA);if((_kG+1)*20<=E(_kd)-10){return new T2(0,_kz,_kG+1|0);}else{return new T2(0,new T(function(){return E(_kz)-1|0;}),_kx);}});return new F(function(){return _k8(_kw,_kd,_ke,_kx,new T(function(){return E(E(_kF).a);}),new T(function(){return E(E(_kF).b);}),_kD,_);});}else{var _kH=E(_kw),_kI=B(_iB(_kH.a,_kn,_j9,_ky,_kz,_kA,_kE,_)),_kJ=_kx,_kK=_ky+1,_kL=_kz,_kM=_kA;_kp=_kH;_kq=_kJ;_kr=_kK;_ks=_kL;_kt=_kM;_ku=_kD;return __continue;}}})(_kp,_kq,_kr,_ks,_kt,_ku,_));if(_kv!=__continue){return _kv;}}};return new F(function(){return _ko(_kc,_kf,0,new T(function(){if(E(_kf)!=E(_kh)){return E(_kg);}else{return E(_kg)+1|0;}}),new T(function(){var _kN=E(_kh);if(E(_kf)!=_kN){return _kN-1|0;}else{var _kO=(E(_kd)-10)/20,_kP=_kO&4294967295;if(_kO>=_kP){return _kP;}else{return _kP-1|0;}}}),_kk,_);});break;default:var _kQ=function(_kR,_kS){var _kT=new T(function(){switch(E(_km)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return E(_ke);}}),_kU=new T(function(){var _kV=E(_kh);if((_kV+1)*20<=E(_kd)-10){return new T2(0,_kg,_kV+1|0);}else{return new T2(0,new T(function(){return E(_kg)-1|0;}),_kf);}});if(E(_kR)==64){return new F(function(){return _k8(_kc,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}else{var _kW=E(_kc),_kX=B(_iB(_kW.a,new T(function(){return B(_6R(_j4,E(_kT)));},1),_j5,_hM,_kg,_kh,_kS,_));return new F(function(){return _k8(_kW,_kd,_kT,_kf,new T(function(){return E(E(_kU).a);}),new T(function(){return E(E(_kU).b);}),_kk,_);});}},_kY=E(_km);switch(_kY){case 42:return new F(function(){return _kQ(64,_j6);});break;case 12289:return new F(function(){return _kQ(64,_j6);});break;case 12290:return new F(function(){return _kQ(64,_j6);});break;default:return new F(function(){return _kQ(_kY,_kl);});}}}},_jy=function(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_){while(1){var _l6=B((function(_l7,_l8,_l9,_la,_lb,_lc,_ld,_){var _le=E(_ld);if(!_le._){return _gE;}else{var _lf=_le.b;if(E(_le.a)==125){var _lg=new T(function(){var _lh=E(_lc);if((_lh+1)*20<=E(_l8)-10){return new T2(0,_lb,_lh+1|0);}else{return new T2(0,new T(function(){return E(_lb)-1|0;}),_la);}});return new F(function(){return _k8(_l7,_l8,_l9,_la,new T(function(){return E(E(_lg).a);}),new T(function(){return E(E(_lg).b);}),_lf,_);});}else{var _li=_l7,_lj=_l8,_lk=_l9,_ll=_la,_lm=_lb,_ln=_lc;_kZ=_li;_l0=_lj;_l1=_lk;_l2=_ll;_l3=_lm;_l4=_ln;_l5=_lf;return __continue;}}})(_kZ,_l0,_l1,_l2,_l3,_l4,_l5,_));if(_l6!=__continue){return _l6;}}},_lo=function(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_){while(1){var _lx=B((function(_ly,_lz,_lA,_lB,_lC,_lD,_lE,_lF,_){var _lG=E(_lF);if(!_lG._){return _gE;}else{var _lH=_lG.b,_lI=E(_lG.a),_lJ=E(_lI);switch(_lJ){case 10:var _lK=_ly,_lL=_lz,_lM=_lA,_lN=_lC,_lO=_lC;_lp=_lK;_lq=_lL;_lr=_lM;_ls=0;_lt=_lN;_lu=new T(function(){return E(_lD)-1|0;});_lv=_lO;_lw=_lH;return __continue;case 123:return new F(function(){return _jy(new T2(0,_ly,_lz),_lA,_lB,_lC,_lD,_lE,_lH,_);});break;case 65306:var _lP=new T(function(){return B(_6R(_j4,_lB));}),_lQ=function(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_){while(1){var _lY=B((function(_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_){var _m6=E(_m5);if(!_m6._){return _gE;}else{var _m7=_m6.b,_m8=E(_m6.a);if(E(_m8)==65306){var _m9=new T(function(){var _ma=E(_m4);if((_ma+1)*20<=E(_lA)-10){return new T2(0,_m3,_ma+1|0);}else{return new T2(0,new T(function(){return E(_m3)-1|0;}),_m1);}});return new F(function(){return _lo(_lZ,_m0,_lA,_lB,_m1,new T(function(){return E(E(_m9).a);}),new T(function(){return E(E(_m9).b);}),_m7,_);});}else{var _mb=B(_iB(_lZ,_lP,_j9,_m2,_m3,_m4,_m8,_)),_mc=_lZ,_md=_m0,_me=_m1,_mf=_m2+1,_mg=_m3,_mh=_m4;_lR=_mc;_lS=_md;_lT=_me;_lU=_mf;_lV=_mg;_lW=_mh;_lX=_m7;return __continue;}}})(_lR,_lS,_lT,_lU,_lV,_lW,_lX,_));if(_lY!=__continue){return _lY;}}};return new F(function(){return _lQ(_ly,_lz,_lC,0,new T(function(){if(E(_lC)!=E(_lE)){return E(_lD);}else{return E(_lD)+1|0;}}),new T(function(){var _mi=E(_lE);if(E(_lC)!=_mi){return _mi-1|0;}else{var _mj=(E(_lA)-10)/20,_mk=_mj&4294967295;if(_mj>=_mk){return _mk;}else{return _mk-1|0;}}}),_lH,_);});break;default:var _ml=function(_mm,_mn){var _mo=new T(function(){switch(E(_lJ)){case 42:return E(_j8);break;case 12300:return E(_j7);break;default:return _lB;}}),_mp=new T(function(){var _mq=E(_lE);if((_mq+1)*20<=E(_lA)-10){return new T2(0,_lD,_mq+1|0);}else{return new T2(0,new T(function(){return E(_lD)-1|0;}),_lC);}});if(E(_mm)==64){return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}else{var _mr=B(_iB(_ly,new T(function(){return B(_6R(_j4,E(_mo)));},1),_j5,_hM,_lD,_lE,_mn,_));return new F(function(){return _k8(new T2(0,_ly,_lz),_lA,_mo,_lC,new T(function(){return E(E(_mp).a);}),new T(function(){return E(E(_mp).b);}),_lH,_);});}},_ms=E(_lJ);switch(_ms){case 42:return new F(function(){return _ml(64,_j6);});break;case 12289:return new F(function(){return _ml(64,_j6);});break;case 12290:return new F(function(){return _ml(64,_j6);});break;default:return new F(function(){return _ml(_ms,_lI);});}}}})(_lp,_lq,_lr,_ls,_lt,_lu,_lv,_lw,_));if(_lx!=__continue){return _lx;}}},_mt=function(_mu,_mv){while(1){var _mw=E(_mu);if(!_mw._){return E(_mv);}else{var _mx=_mv+1|0;_mu=_mw.b;_mv=_mx;continue;}}},_my=function(_mz){return E(E(_mz).a);},_mA=function(_mB,_mC){var _mD=E(_mC),_mE=new T(function(){var _mF=B(_ha(_mB)),_mG=B(_mA(_mB,B(A3(_my,_mF,_mD,new T(function(){return B(A2(_he,_mF,_aV));})))));return new T2(1,_mG.a,_mG.b);});return new T2(0,_mD,_mE);},_mH=new T(function(){var _mI=B(_mA(_gb,_hM));return new T2(1,_mI.a,_mI.b);}),_mJ=new T(function(){return B(unCStr("px Courier"));}),_mK=new T(function(){return B(_I(0,20,_10));}),_mL=new T(function(){return B(_y(_mK,_mJ));}),_mM=function(_mN,_){return _gE;},_mO=function(_mP,_mQ,_mR,_mS,_mT){var _mU=new T(function(){return E(_mR)*16;}),_mV=new T(function(){return E(_mS)*20;}),_mW=function(_mX,_mY){var _mZ=E(_mX);if(!_mZ._){return E(_mM);}else{var _n0=E(_mY);if(!_n0._){return E(_mM);}else{var _n1=new T(function(){return B(_mW(_mZ.b,_n0.b));}),_n2=new T(function(){var _n3=new T(function(){var _n4=new T(function(){return B(_hF(new T(function(){return E(_mU)+16*E(_n0.a);}),_mV,new T2(1,_mZ.a,_10)));});return B(_in(_mL,_n4));});return B(_i2(_mQ,_n3));});return function(_n5,_){var _n6=B(A2(_n2,_n5,_));return new F(function(){return A2(_n1,_n5,_);});};}}};return new F(function(){return A3(_mW,_mT,_mH,_mP);});},_n7=45,_n8=new T(function(){return B(unCStr("-"));}),_n9=new T2(1,_n7,_n8),_na=function(_nb){var _nc=E(_nb);return (_nc==1)?E(_n9):new T2(1,_n7,new T(function(){return B(_na(_nc-1|0));}));},_nd=new T(function(){return B(unCStr(": empty list"));}),_ne=function(_nf){return new F(function(){return err(B(_y(_6G,new T(function(){return B(_y(_nf,_nd));},1))));});},_ng=new T(function(){return B(unCStr("head"));}),_nh=new T(function(){return B(_ne(_ng));}),_ni=new T(function(){return eval("(function(e){e.width = e.width;})");}),_nj=new T(function(){return B(_hF(_hM,_hM,_10));}),_nk=32,_nl=new T(function(){return B(unCStr("|"));}),_nm=function(_nn){var _no=E(_nn);return (_no._==0)?E(_nl):new T2(1,new T(function(){var _np=E(_no.a);switch(E(_np.b)){case 7:return E(_nk);break;case 8:return E(_nk);break;default:return E(_np.a);}}),new T(function(){return B(_nm(_no.b));}));},_nq=function(_nr,_ns,_nt,_nu,_nv,_){var _nw=__app1(E(_ni),_ns),_nx=B(A2(_nj,_nr,_)),_ny=B(unAppCStr("-",new T(function(){var _nz=E(_nv);if(!_nz._){return E(_nh);}else{var _nA=B(_mt(_nz.a,0));if(0>=_nA){return E(_n8);}else{return B(_na(_nA));}}}))),_nB=B(A(_mO,[_nr,_j3,_nt,_nu,_ny,_])),_nC=function(_nD,_nE,_nF,_){while(1){var _nG=B((function(_nH,_nI,_nJ,_){var _nK=E(_nJ);if(!_nK._){return new F(function(){return A(_mO,[_nr,_j3,_nH,_nI,_ny,_]);});}else{var _nL=B(A(_mO,[_nr,_j3,_nH,_nI,B(unAppCStr("|",new T(function(){return B(_nm(_nK.a));}))),_])),_nM=_nH;_nD=_nM;_nE=new T(function(){return E(_nI)+1|0;});_nF=_nK.b;return __continue;}})(_nD,_nE,_nF,_));if(_nG!=__continue){return _nG;}}};return new F(function(){return _nC(_nt,new T(function(){return E(_nu)+1|0;}),_nv,_);});},_nN=new T(function(){return B(_6R(_j4,1));}),_nO=new T(function(){return B(_6R(_j4,2));}),_nP=2,_nQ=function(_nR,_nS,_nT,_nU,_){var _nV=__app1(E(_ni),_nS),_nW=B(A2(_nj,_nR,_)),_nX=E(_nU),_nY=E(_nX.b).a,_nZ=E(_nX.a),_o0=_nZ.a;if(!E(E(_nX.r).h)){return _gE;}else{var _o1=B(_nq(_nR,_nS,new T(function(){return E(_nT)-E(_nY)|0;}),_nP,_nZ.b,_));return new F(function(){return A(_mO,[_nR,new T(function(){if(E(_nZ.d)==32){return E(_nN);}else{return E(_nO);}}),new T(function(){return ((E(E(_o0).a)+1|0)+E(_nT)|0)-E(_nY)|0;},1),new T(function(){return (E(E(_o0).b)+2|0)+1|0;},1),new T2(1,_nZ.c,_10),_]);});}},_o2=function(_o3){return E(E(_o3).a);},_o4=function(_o5){return E(E(_o5).a);},_o6=function(_o7,_o8){while(1){var _o9=E(_o7);if(!_o9._){return E(_o8);}else{_o7=_o9.b;_o8=_o9.a;continue;}}},_oa=function(_ob,_oc,_od){return new F(function(){return _o6(_oc,_ob);});},_oe=new T1(0,2),_of=function(_og,_oh){while(1){var _oi=E(_og);if(!_oi._){var _oj=_oi.a,_ok=E(_oh);if(!_ok._){var _ol=_ok.a;if(!(imul(_oj,_ol)|0)){return new T1(0,imul(_oj,_ol)|0);}else{_og=new T1(1,I_fromInt(_oj));_oh=new T1(1,I_fromInt(_ol));continue;}}else{_og=new T1(1,I_fromInt(_oj));_oh=_ok;continue;}}else{var _om=E(_oh);if(!_om._){_og=_oi;_oh=new T1(1,I_fromInt(_om.a));continue;}else{return new T1(1,I_mul(_oi.a,_om.a));}}}},_on=function(_oo,_op,_oq){while(1){if(!(_op%2)){var _or=B(_of(_oo,_oo)),_os=quot(_op,2);_oo=_or;_op=_os;continue;}else{var _ot=E(_op);if(_ot==1){return new F(function(){return _of(_oo,_oq);});}else{var _or=B(_of(_oo,_oo)),_ou=B(_of(_oo,_oq));_oo=_or;_op=quot(_ot-1|0,2);_oq=_ou;continue;}}}},_ov=function(_ow,_ox){while(1){if(!(_ox%2)){var _oy=B(_of(_ow,_ow)),_oz=quot(_ox,2);_ow=_oy;_ox=_oz;continue;}else{var _oA=E(_ox);if(_oA==1){return E(_ow);}else{return new F(function(){return _on(B(_of(_ow,_ow)),quot(_oA-1|0,2),_ow);});}}}},_oB=function(_oC){return E(E(_oC).c);},_oD=function(_oE){return E(E(_oE).a);},_oF=function(_oG){return E(E(_oG).b);},_oH=function(_oI){return E(E(_oI).b);},_oJ=function(_oK){return E(E(_oK).c);},_oL=new T1(0,0),_oM=new T1(0,2),_oN=function(_oO){return E(E(_oO).d);},_oP=function(_oQ,_oR){var _oS=B(_o2(_oQ)),_oT=new T(function(){return B(_o4(_oS));}),_oU=new T(function(){return B(A3(_oN,_oQ,_oR,new T(function(){return B(A2(_he,_oT,_oM));})));});return new F(function(){return A3(_4z,B(_oD(B(_oF(_oS)))),_oU,new T(function(){return B(A2(_he,_oT,_oL));}));});},_oV=new T(function(){return B(unCStr("Negative exponent"));}),_oW=new T(function(){return B(err(_oV));}),_oX=function(_oY){return E(E(_oY).c);},_oZ=function(_p0,_p1,_p2,_p3){var _p4=B(_o2(_p1)),_p5=new T(function(){return B(_o4(_p4));}),_p6=B(_oF(_p4));if(!B(A3(_oJ,_p6,_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){if(!B(A3(_4z,B(_oD(_p6)),_p3,new T(function(){return B(A2(_he,_p5,_oL));})))){var _p7=new T(function(){return B(A2(_he,_p5,_oM));}),_p8=new T(function(){return B(A2(_he,_p5,_aV));}),_p9=B(_oD(_p6)),_pa=function(_pb,_pc,_pd){while(1){var _pe=B((function(_pf,_pg,_ph){if(!B(_oP(_p1,_pg))){if(!B(A3(_4z,_p9,_pg,_p8))){var _pi=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pg,_p8));}),_p7));});_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=_pi;_pd=new T(function(){return B(A3(_oB,_p0,_pf,_ph));});return __continue;}else{return new F(function(){return A3(_oB,_p0,_pf,_ph);});}}else{var _pj=_ph;_pb=new T(function(){return B(A3(_oB,_p0,_pf,_pf));});_pc=new T(function(){return B(A3(_oX,_p1,_pg,_p7));});_pd=_pj;return __continue;}})(_pb,_pc,_pd));if(_pe!=__continue){return _pe;}}},_pk=function(_pl,_pm){while(1){var _pn=B((function(_po,_pp){if(!B(_oP(_p1,_pp))){if(!B(A3(_4z,_p9,_pp,_p8))){var _pq=new T(function(){return B(A3(_oX,_p1,new T(function(){return B(A3(_oH,_p5,_pp,_p8));}),_p7));});return new F(function(){return _pa(new T(function(){return B(A3(_oB,_p0,_po,_po));}),_pq,_po);});}else{return E(_po);}}else{_pl=new T(function(){return B(A3(_oB,_p0,_po,_po));});_pm=new T(function(){return B(A3(_oX,_p1,_pp,_p7));});return __continue;}})(_pl,_pm));if(_pn!=__continue){return _pn;}}};return new F(function(){return _pk(_p2,_p3);});}else{return new F(function(){return A2(_he,_p0,_aV);});}}else{return E(_oW);}},_pr=new T(function(){return B(err(_oV));}),_ps=function(_pt){var _pu=I_decodeDouble(_pt);return new T2(0,new T1(1,_pu.b),_pu.a);},_pv=function(_pw,_px){var _py=B(_ps(_px)),_pz=_py.a,_pA=_py.b,_pB=new T(function(){return B(_o4(new T(function(){return B(_o2(_pw));})));});if(_pA<0){var _pC= -_pA;if(_pC>=0){var _pD=E(_pC);if(!_pD){var _pE=E(_aV);}else{var _pE=B(_ov(_oe,_pD));}if(!B(_cn(_pE,_cN))){var _pF=B(_cE(_pz,_pE));return new T2(0,new T(function(){return B(A2(_he,_pB,_pF.a));}),new T(function(){return B(_cj(_pF.b,_pA));}));}else{return E(_9U);}}else{return E(_pr);}}else{var _pG=new T(function(){var _pH=new T(function(){return B(_oZ(_pB,_bS,new T(function(){return B(A2(_he,_pB,_oe));}),_pA));});return B(A3(_oB,_pB,new T(function(){return B(A2(_he,_pB,_pz));}),_pH));});return new T2(0,_pG,_fA);}},_pI=function(_pJ,_pK){while(1){var _pL=E(_pK);if(!_pL._){return __Z;}else{var _pM=_pL.b,_pN=E(_pJ);if(_pN==1){return E(_pM);}else{_pJ=_pN-1|0;_pK=_pM;continue;}}}},_pO=function(_pP,_pQ){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.a,_pT=E(_pP);return (_pT==1)?new T2(1,_pS,_10):new T2(1,_pS,new T(function(){return B(_pO(_pT-1|0,_pR.b));}));}},_pU=function(_pV,_pW,_pX,_pY){while(1){if(B(_6R(new T2(1,_pX,_pY),_pW))!=_pV){var _pZ=_pW+1|0;_pW=_pZ;continue;}else{if(0>=_pW){return __Z;}else{return new F(function(){return _pO(_pW,new T2(1,_pX,_pY));});}}}},_q0=function(_q1,_q2,_q3){var _q4=E(_q3);if(!_q4._){return __Z;}else{var _q5=E(_q1);if(B(_6R(_q4,_q2))!=_q5){return new F(function(){return _pU(_q5,_q2+1|0,_q4.a,_q4.b);});}else{if(0>=_q2){return __Z;}else{return new F(function(){return _pO(_q2,_q4);});}}}},_q6=function(_q7,_q8,_q9){var _qa=_q8+1|0;if(_qa>0){return new F(function(){return _pI(_qa,B(_q0(_q7,_qa,_q9)));});}else{return new F(function(){return _q0(_q7,_qa,_q9);});}},_qb=function(_qc,_qd){return (!B(_69(_qc,_qd)))?true:false;},_qe=new T2(0,_69,_qb),_qf=new T(function(){return B(_e7("Event.hs:(65,1)-(66,68)|function addEvent"));}),_qg=0,_qh=function(_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB){while(1){var _qC=E(_qi);if(!_qC._){return {_:0,a:_qj,b:_qk,c:_ql,d:_qm,e:_qn,f:_qo,g:_qp,h:_qq,i:_qr,j:_qs,k:_qt,l:_qu,m:_qv,n:_qw,o:_qx,p:_qy,q:_qz,r:_qA,s:_qB};}else{var _qD=E(_qC.b);if(!_qD._){return E(_qf);}else{var _qE=new T2(1,new T2(0,_qC.a,_qD.a),_qn),_qF=new T2(1,_qg,_qo);_qi=_qD.b;_qn=_qE;_qo=_qF;continue;}}}},_qG=function(_qH,_qI,_qJ){var _qK=E(_qJ);if(!_qK._){return __Z;}else{var _qL=_qK.a,_qM=_qK.b;return (!B(A2(_qH,_qI,_qL)))?new T2(1,_qL,new T(function(){return B(_qG(_qH,_qI,_qM));})):E(_qM);}},_qN=function(_qO,_qP){while(1){var _qQ=E(_qO);if(!_qQ._){return (E(_qP)._==0)?true:false;}else{var _qR=E(_qP);if(!_qR._){return false;}else{if(E(_qQ.a)!=E(_qR.a)){return false;}else{_qO=_qQ.b;_qP=_qR.b;continue;}}}}},_qS=function(_qT,_qU){while(1){var _qV=E(_qT);if(!_qV._){return (E(_qU)._==0)?true:false;}else{var _qW=E(_qU);if(!_qW._){return false;}else{if(!B(_69(_qV.a,_qW.a))){return false;}else{_qT=_qV.b;_qU=_qW.b;continue;}}}}},_qX=function(_qY,_qZ){switch(E(_qY)){case 0:return (E(_qZ)==0)?true:false;case 1:return (E(_qZ)==1)?true:false;case 2:return (E(_qZ)==2)?true:false;case 3:return (E(_qZ)==3)?true:false;case 4:return (E(_qZ)==4)?true:false;case 5:return (E(_qZ)==5)?true:false;case 6:return (E(_qZ)==6)?true:false;case 7:return (E(_qZ)==7)?true:false;default:return (E(_qZ)==8)?true:false;}},_r0=function(_r1,_r2,_r3,_r4){if(_r1!=_r3){return false;}else{return new F(function(){return _qX(_r2,_r4);});}},_r5=function(_r6,_r7){var _r8=E(_r6),_r9=E(_r7);return new F(function(){return _r0(E(_r8.a),_r8.b,E(_r9.a),_r9.b);});},_ra=function(_rb,_rc,_rd,_re){if(_rb!=_rd){return true;}else{switch(E(_rc)){case 0:return (E(_re)==0)?false:true;case 1:return (E(_re)==1)?false:true;case 2:return (E(_re)==2)?false:true;case 3:return (E(_re)==3)?false:true;case 4:return (E(_re)==4)?false:true;case 5:return (E(_re)==5)?false:true;case 6:return (E(_re)==6)?false:true;case 7:return (E(_re)==7)?false:true;default:return (E(_re)==8)?false:true;}}},_rf=function(_rg,_rh){var _ri=E(_rg),_rj=E(_rh);return new F(function(){return _ra(E(_ri.a),_ri.b,E(_rj.a),_rj.b);});},_rk=new T2(0,_r5,_rf),_rl=0,_rm=function(_rn,_ro){var _rp=E(_ro);if(!_rp._){return 0;}else{var _rq=_rp.b,_rr=E(_rn),_rs=E(_rp.a),_rt=_rs.b;if(E(_rr.a)!=E(_rs.a)){return 1+B(_rm(_rr,_rq))|0;}else{switch(E(_rr.b)){case 0:return (E(_rt)==0)?0:1+B(_rm(_rr,_rq))|0;case 1:return (E(_rt)==1)?0:1+B(_rm(_rr,_rq))|0;case 2:return (E(_rt)==2)?0:1+B(_rm(_rr,_rq))|0;case 3:return (E(_rt)==3)?0:1+B(_rm(_rr,_rq))|0;case 4:return (E(_rt)==4)?0:1+B(_rm(_rr,_rq))|0;case 5:return (E(_rt)==5)?0:1+B(_rm(_rr,_rq))|0;case 6:return (E(_rt)==6)?0:1+B(_rm(_rr,_rq))|0;case 7:return (E(_rt)==7)?0:1+B(_rm(_rr,_rq))|0;default:return (E(_rt)==8)?0:1+B(_rm(_rr,_rq))|0;}}}},_ru=function(_rv,_rw){return new F(function(){return _rm(_rv,_rw);});},_rx=function(_ry,_rz){var _rA=E(_rz);if(!_rA._){return new T2(0,_rl,_rl);}else{var _rB=_rA.a,_rC=_rA.b;return (!B(_4B(_rk,_ry,_rB)))?new T2(0,new T(function(){return E(B(_rx(_ry,_rC)).a);}),new T(function(){return 1+E(B(_rx(_ry,_rC)).b)|0;})):new T2(0,new T(function(){return B(_ru(_ry,_rB));}),_rl);}},_rD=function(_rE,_rF){while(1){var _rG=E(_rF);if(!_rG._){return __Z;}else{var _rH=_rG.b,_rI=E(_rE);if(_rI==1){return E(_rH);}else{_rE=_rI-1|0;_rF=_rH;continue;}}}},_rJ=new T(function(){return B(unCStr("getch"));}),_rK=new T(function(){return B(unCStr("=="));}),_rL=new T(function(){return B(unCStr("&&"));}),_rM=new T(function(){return B(unCStr("||"));}),_rN=new T(function(){return B(unCStr("getpos"));}),_rO=new T(function(){return B(unCStr("ch"));}),_rP=new T(function(){return B(unCStr("tp"));}),_rQ=new T2(1,_rP,_10),_rR=new T2(1,_rO,_rQ),_rS=new T2(0,_rN,_rR),_rT=new T(function(){return B(unCStr("a"));}),_rU=new T(function(){return B(unCStr("b"));}),_rV=new T2(1,_rU,_10),_rW=new T2(1,_rT,_rV),_rX=new T2(0,_rK,_rW),_rY=new T2(0,_rL,_rW),_rZ=new T2(0,_rM,_rW),_s0=new T2(1,_rZ,_10),_s1=new T2(1,_rY,_s0),_s2=new T2(1,_rX,_s1),_s3=new T2(1,_rS,_s2),_s4=new T(function(){return B(unCStr("p"));}),_s5=new T(function(){return B(unCStr("q"));}),_s6=new T2(1,_s5,_10),_s7=new T2(1,_s4,_s6),_s8=new T2(0,_rJ,_s7),_s9=new T2(1,_s8,_s3),_sa=new T(function(){return B(unCStr("foldr1"));}),_sb=new T(function(){return B(_ne(_sa));}),_sc=function(_sd,_se){var _sf=E(_se);if(!_sf._){return E(_sb);}else{var _sg=_sf.a,_sh=E(_sf.b);if(!_sh._){return E(_sg);}else{return new F(function(){return A2(_sd,_sg,new T(function(){return B(_sc(_sd,_sh));}));});}}},_si=function(_sj){return E(E(_sj).a);},_sk=function(_sl,_sm,_sn){while(1){var _so=E(_sn);if(!_so._){return __Z;}else{var _sp=E(_so.a);if(!B(A3(_4z,_sl,_sm,_sp.a))){_sn=_so.b;continue;}else{return new T1(1,_sp.b);}}}},_sq=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sr=new T(function(){return B(err(_sq));}),_ss=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_st=new T(function(){return B(err(_ss));}),_su=new T(function(){return B(unCStr("T"));}),_sv=new T(function(){return B(unCStr("F"));}),_sw=new T(function(){return B(_e7("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sx=function(_sy,_sz){while(1){var _sA=B((function(_sB,_sC){var _sD=E(_sB);switch(_sD._){case 0:var _sE=E(_sC);if(!_sE._){return __Z;}else{_sy=B(A1(_sD.a,_sE.a));_sz=_sE.b;return __continue;}break;case 1:var _sF=B(A1(_sD.a,_sC)),_sG=_sC;_sy=_sF;_sz=_sG;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sD.a,_sC),new T(function(){return B(_sx(_sD.b,_sC));}));default:return E(_sD.a);}})(_sy,_sz));if(_sA!=__continue){return _sA;}}},_sH=function(_sI,_sJ){var _sK=function(_sL){var _sM=E(_sJ);if(_sM._==3){return new T2(3,_sM.a,new T(function(){return B(_sH(_sI,_sM.b));}));}else{var _sN=E(_sI);if(_sN._==2){return E(_sM);}else{var _sO=E(_sM);if(_sO._==2){return E(_sN);}else{var _sP=function(_sQ){var _sR=E(_sO);if(_sR._==4){var _sS=function(_sT){return new T1(4,new T(function(){return B(_y(B(_sx(_sN,_sT)),_sR.a));}));};return new T1(1,_sS);}else{var _sU=E(_sN);if(_sU._==1){var _sV=_sU.a,_sW=E(_sR);if(!_sW._){return new T1(1,function(_sX){return new F(function(){return _sH(B(A1(_sV,_sX)),_sW);});});}else{var _sY=function(_sZ){return new F(function(){return _sH(B(A1(_sV,_sZ)),new T(function(){return B(A1(_sW.a,_sZ));}));});};return new T1(1,_sY);}}else{var _t0=E(_sR);if(!_t0._){return E(_sw);}else{var _t1=function(_t2){return new F(function(){return _sH(_sU,new T(function(){return B(A1(_t0.a,_t2));}));});};return new T1(1,_t1);}}}},_t3=E(_sN);switch(_t3._){case 1:var _t4=E(_sO);if(_t4._==4){var _t5=function(_t6){return new T1(4,new T(function(){return B(_y(B(_sx(B(A1(_t3.a,_t6)),_t6)),_t4.a));}));};return new T1(1,_t5);}else{return new F(function(){return _sP(_);});}break;case 4:var _t7=_t3.a,_t8=E(_sO);switch(_t8._){case 0:var _t9=function(_ta){var _tb=new T(function(){return B(_y(_t7,new T(function(){return B(_sx(_t8,_ta));},1)));});return new T1(4,_tb);};return new T1(1,_t9);case 1:var _tc=function(_td){var _te=new T(function(){return B(_y(_t7,new T(function(){return B(_sx(B(A1(_t8.a,_td)),_td));},1)));});return new T1(4,_te);};return new T1(1,_tc);default:return new T1(4,new T(function(){return B(_y(_t7,_t8.a));}));}break;default:return new F(function(){return _sP(_);});}}}}},_tf=E(_sI);switch(_tf._){case 0:var _tg=E(_sJ);if(!_tg._){var _th=function(_ti){return new F(function(){return _sH(B(A1(_tf.a,_ti)),new T(function(){return B(A1(_tg.a,_ti));}));});};return new T1(0,_th);}else{return new F(function(){return _sK(_);});}break;case 3:return new T2(3,_tf.a,new T(function(){return B(_sH(_tf.b,_sJ));}));default:return new F(function(){return _sK(_);});}},_tj=new T(function(){return B(unCStr("("));}),_tk=new T(function(){return B(unCStr(")"));}),_tl=function(_tm,_tn){var _to=E(_tm);switch(_to._){case 0:return new T1(0,function(_tp){return new F(function(){return _tl(B(A1(_to.a,_tp)),_tn);});});case 1:return new T1(1,function(_tq){return new F(function(){return _tl(B(A1(_to.a,_tq)),_tn);});});case 2:return new T0(2);case 3:return new F(function(){return _sH(B(A1(_tn,_to.a)),new T(function(){return B(_tl(_to.b,_tn));}));});break;default:var _tr=function(_ts){var _tt=E(_ts);if(!_tt._){return __Z;}else{var _tu=E(_tt.a);return new F(function(){return _y(B(_sx(B(A1(_tn,_tu.a)),_tu.b)),new T(function(){return B(_tr(_tt.b));},1));});}},_tv=B(_tr(_to.a));return (_tv._==0)?new T0(2):new T1(4,_tv);}},_tw=new T0(2),_tx=function(_ty){return new T2(3,_ty,_tw);},_tz=function(_tA,_tB){var _tC=E(_tA);if(!_tC){return new F(function(){return A1(_tB,_gE);});}else{var _tD=new T(function(){return B(_tz(_tC-1|0,_tB));});return new T1(0,function(_tE){return E(_tD);});}},_tF=function(_tG,_tH,_tI){var _tJ=new T(function(){return B(A1(_tG,_tx));}),_tK=function(_tL,_tM,_tN,_tO){while(1){var _tP=B((function(_tQ,_tR,_tS,_tT){var _tU=E(_tQ);switch(_tU._){case 0:var _tV=E(_tR);if(!_tV._){return new F(function(){return A1(_tH,_tT);});}else{var _tW=_tS+1|0,_tX=_tT;_tL=B(A1(_tU.a,_tV.a));_tM=_tV.b;_tN=_tW;_tO=_tX;return __continue;}break;case 1:var _tY=B(A1(_tU.a,_tR)),_tZ=_tR,_tW=_tS,_tX=_tT;_tL=_tY;_tM=_tZ;_tN=_tW;_tO=_tX;return __continue;case 2:return new F(function(){return A1(_tH,_tT);});break;case 3:var _u0=new T(function(){return B(_tl(_tU,_tT));});return new F(function(){return _tz(_tS,function(_u1){return E(_u0);});});break;default:return new F(function(){return _tl(_tU,_tT);});}})(_tL,_tM,_tN,_tO));if(_tP!=__continue){return _tP;}}};return function(_u2){return new F(function(){return _tK(_tJ,_u2,0,_tI);});};},_u3=function(_u4){return new F(function(){return A1(_u4,_10);});},_u5=function(_u6,_u7){var _u8=function(_u9){var _ua=E(_u9);if(!_ua._){return E(_u3);}else{var _ub=_ua.a;if(!B(A1(_u6,_ub))){return E(_u3);}else{var _uc=new T(function(){return B(_u8(_ua.b));}),_ud=function(_ue){var _uf=new T(function(){return B(A1(_uc,function(_ug){return new F(function(){return A1(_ue,new T2(1,_ub,_ug));});}));});return new T1(0,function(_uh){return E(_uf);});};return E(_ud);}}};return function(_ui){return new F(function(){return A2(_u8,_ui,_u7);});};},_uj=new T0(6),_uk=new T(function(){return B(unCStr("valDig: Bad base"));}),_ul=new T(function(){return B(err(_uk));}),_um=function(_un,_uo){var _up=function(_uq,_ur){var _us=E(_uq);if(!_us._){var _ut=new T(function(){return B(A1(_ur,_10));});return function(_uu){return new F(function(){return A1(_uu,_ut);});};}else{var _uv=E(_us.a),_uw=function(_ux){var _uy=new T(function(){return B(_up(_us.b,function(_uz){return new F(function(){return A1(_ur,new T2(1,_ux,_uz));});}));}),_uA=function(_uB){var _uC=new T(function(){return B(A1(_uy,_uB));});return new T1(0,function(_uD){return E(_uC);});};return E(_uA);};switch(E(_un)){case 8:if(48>_uv){var _uE=new T(function(){return B(A1(_ur,_10));});return function(_uF){return new F(function(){return A1(_uF,_uE);});};}else{if(_uv>55){var _uG=new T(function(){return B(A1(_ur,_10));});return function(_uH){return new F(function(){return A1(_uH,_uG);});};}else{return new F(function(){return _uw(_uv-48|0);});}}break;case 10:if(48>_uv){var _uI=new T(function(){return B(A1(_ur,_10));});return function(_uJ){return new F(function(){return A1(_uJ,_uI);});};}else{if(_uv>57){var _uK=new T(function(){return B(A1(_ur,_10));});return function(_uL){return new F(function(){return A1(_uL,_uK);});};}else{return new F(function(){return _uw(_uv-48|0);});}}break;case 16:if(48>_uv){if(97>_uv){if(65>_uv){var _uM=new T(function(){return B(A1(_ur,_10));});return function(_uN){return new F(function(){return A1(_uN,_uM);});};}else{if(_uv>70){var _uO=new T(function(){return B(A1(_ur,_10));});return function(_uP){return new F(function(){return A1(_uP,_uO);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{if(_uv>102){if(65>_uv){var _uQ=new T(function(){return B(A1(_ur,_10));});return function(_uR){return new F(function(){return A1(_uR,_uQ);});};}else{if(_uv>70){var _uS=new T(function(){return B(A1(_ur,_10));});return function(_uT){return new F(function(){return A1(_uT,_uS);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{return new F(function(){return _uw((_uv-97|0)+10|0);});}}}else{if(_uv>57){if(97>_uv){if(65>_uv){var _uU=new T(function(){return B(A1(_ur,_10));});return function(_uV){return new F(function(){return A1(_uV,_uU);});};}else{if(_uv>70){var _uW=new T(function(){return B(A1(_ur,_10));});return function(_uX){return new F(function(){return A1(_uX,_uW);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{if(_uv>102){if(65>_uv){var _uY=new T(function(){return B(A1(_ur,_10));});return function(_uZ){return new F(function(){return A1(_uZ,_uY);});};}else{if(_uv>70){var _v0=new T(function(){return B(A1(_ur,_10));});return function(_v1){return new F(function(){return A1(_v1,_v0);});};}else{return new F(function(){return _uw((_uv-65|0)+10|0);});}}}else{return new F(function(){return _uw((_uv-97|0)+10|0);});}}}else{return new F(function(){return _uw(_uv-48|0);});}}break;default:return E(_ul);}}},_v2=function(_v3){var _v4=E(_v3);if(!_v4._){return new T0(2);}else{return new F(function(){return A1(_uo,_v4);});}};return function(_v5){return new F(function(){return A3(_up,_v5,_5V,_v2);});};},_v6=16,_v7=8,_v8=function(_v9){var _va=function(_vb){return new F(function(){return A1(_v9,new T1(5,new T2(0,_v7,_vb)));});},_vc=function(_vd){return new F(function(){return A1(_v9,new T1(5,new T2(0,_v6,_vd)));});},_ve=function(_vf){switch(E(_vf)){case 79:return new T1(1,B(_um(_v7,_va)));case 88:return new T1(1,B(_um(_v6,_vc)));case 111:return new T1(1,B(_um(_v7,_va)));case 120:return new T1(1,B(_um(_v6,_vc)));default:return new T0(2);}};return function(_vg){return (E(_vg)==48)?E(new T1(0,_ve)):new T0(2);};},_vh=function(_vi){return new T1(0,B(_v8(_vi)));},_vj=function(_vk){return new F(function(){return A1(_vk,_0);});},_vl=function(_vm){return new F(function(){return A1(_vm,_0);});},_vn=10,_vo=new T1(0,10),_vp=function(_vq){return new F(function(){return _aR(E(_vq));});},_vr=new T(function(){return B(unCStr("this should not happen"));}),_vs=new T(function(){return B(err(_vr));}),_vt=function(_vu,_vv){var _vw=E(_vv);if(!_vw._){return __Z;}else{var _vx=E(_vw.b);return (_vx._==0)?E(_vs):new T2(1,B(_cv(B(_of(_vw.a,_vu)),_vx.a)),new T(function(){return B(_vt(_vu,_vx.b));}));}},_vy=new T1(0,0),_vz=function(_vA,_vB,_vC){while(1){var _vD=B((function(_vE,_vF,_vG){var _vH=E(_vG);if(!_vH._){return E(_vy);}else{if(!E(_vH.b)._){return E(_vH.a);}else{var _vI=E(_vF);if(_vI<=40){var _vJ=function(_vK,_vL){while(1){var _vM=E(_vL);if(!_vM._){return E(_vK);}else{var _vN=B(_cv(B(_of(_vK,_vE)),_vM.a));_vK=_vN;_vL=_vM.b;continue;}}};return new F(function(){return _vJ(_vy,_vH);});}else{var _vO=B(_of(_vE,_vE));if(!(_vI%2)){var _vP=B(_vt(_vE,_vH));_vA=_vO;_vB=quot(_vI+1|0,2);_vC=_vP;return __continue;}else{var _vP=B(_vt(_vE,new T2(1,_vy,_vH)));_vA=_vO;_vB=quot(_vI+1|0,2);_vC=_vP;return __continue;}}}}})(_vA,_vB,_vC));if(_vD!=__continue){return _vD;}}},_vQ=function(_vR,_vS){return new F(function(){return _vz(_vR,new T(function(){return B(_mt(_vS,0));},1),B(_6e(_vp,_vS)));});},_vT=function(_vU){var _vV=new T(function(){var _vW=new T(function(){var _vX=function(_vY){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_vQ(_vo,_vY));})));});};return new T1(1,B(_um(_vn,_vX)));}),_vZ=function(_w0){if(E(_w0)==43){var _w1=function(_w2){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_vQ(_vo,_w2));})));});};return new T1(1,B(_um(_vn,_w1)));}else{return new T0(2);}},_w3=function(_w4){if(E(_w4)==45){var _w5=function(_w6){return new F(function(){return A1(_vU,new T1(1,new T(function(){return B(_ft(B(_vQ(_vo,_w6))));})));});};return new T1(1,B(_um(_vn,_w5)));}else{return new T0(2);}};return B(_sH(B(_sH(new T1(0,_w3),new T1(0,_vZ))),_vW));});return new F(function(){return _sH(new T1(0,function(_w7){return (E(_w7)==101)?E(_vV):new T0(2);}),new T1(0,function(_w8){return (E(_w8)==69)?E(_vV):new T0(2);}));});},_w9=function(_wa){var _wb=function(_wc){return new F(function(){return A1(_wa,new T1(1,_wc));});};return function(_wd){return (E(_wd)==46)?new T1(1,B(_um(_vn,_wb))):new T0(2);};},_we=function(_wf){return new T1(0,B(_w9(_wf)));},_wg=function(_wh){var _wi=function(_wj){var _wk=function(_wl){return new T1(1,B(_tF(_vT,_vj,function(_wm){return new F(function(){return A1(_wh,new T1(5,new T3(1,_wj,_wl,_wm)));});})));};return new T1(1,B(_tF(_we,_vl,_wk)));};return new F(function(){return _um(_vn,_wi);});},_wn=function(_wo){return new T1(1,B(_wg(_wo)));},_wp=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wq=function(_wr){return new F(function(){return _4B(_h7,_wr,_wp);});},_ws=false,_wt=true,_wu=function(_wv){var _ww=new T(function(){return B(A1(_wv,_v7));}),_wx=new T(function(){return B(A1(_wv,_v6));});return function(_wy){switch(E(_wy)){case 79:return E(_ww);case 88:return E(_wx);case 111:return E(_ww);case 120:return E(_wx);default:return new T0(2);}};},_wz=function(_wA){return new T1(0,B(_wu(_wA)));},_wB=function(_wC){return new F(function(){return A1(_wC,_vn);});},_wD=function(_wE){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_I(9,_wE,_10));}))));});},_wF=function(_wG){return new T0(2);},_wH=function(_wI){var _wJ=E(_wI);if(!_wJ._){return E(_wF);}else{var _wK=_wJ.a,_wL=E(_wJ.b);if(!_wL._){return E(_wK);}else{var _wM=new T(function(){return B(_wH(_wL));}),_wN=function(_wO){return new F(function(){return _sH(B(A1(_wK,_wO)),new T(function(){return B(A1(_wM,_wO));}));});};return E(_wN);}}},_wP=function(_wQ,_wR){var _wS=function(_wT,_wU,_wV){var _wW=E(_wT);if(!_wW._){return new F(function(){return A1(_wV,_wQ);});}else{var _wX=E(_wU);if(!_wX._){return new T0(2);}else{if(E(_wW.a)!=E(_wX.a)){return new T0(2);}else{var _wY=new T(function(){return B(_wS(_wW.b,_wX.b,_wV));});return new T1(0,function(_wZ){return E(_wY);});}}}};return function(_x0){return new F(function(){return _wS(_wQ,_x0,_wR);});};},_x1=new T(function(){return B(unCStr("SO"));}),_x2=14,_x3=function(_x4){var _x5=new T(function(){return B(A1(_x4,_x2));});return new T1(1,B(_wP(_x1,function(_x6){return E(_x5);})));},_x7=new T(function(){return B(unCStr("SOH"));}),_x8=1,_x9=function(_xa){var _xb=new T(function(){return B(A1(_xa,_x8));});return new T1(1,B(_wP(_x7,function(_xc){return E(_xb);})));},_xd=function(_xe){return new T1(1,B(_tF(_x9,_x3,_xe)));},_xf=new T(function(){return B(unCStr("NUL"));}),_xg=0,_xh=function(_xi){var _xj=new T(function(){return B(A1(_xi,_xg));});return new T1(1,B(_wP(_xf,function(_xk){return E(_xj);})));},_xl=new T(function(){return B(unCStr("STX"));}),_xm=2,_xn=function(_xo){var _xp=new T(function(){return B(A1(_xo,_xm));});return new T1(1,B(_wP(_xl,function(_xq){return E(_xp);})));},_xr=new T(function(){return B(unCStr("ETX"));}),_xs=3,_xt=function(_xu){var _xv=new T(function(){return B(A1(_xu,_xs));});return new T1(1,B(_wP(_xr,function(_xw){return E(_xv);})));},_xx=new T(function(){return B(unCStr("EOT"));}),_xy=4,_xz=function(_xA){var _xB=new T(function(){return B(A1(_xA,_xy));});return new T1(1,B(_wP(_xx,function(_xC){return E(_xB);})));},_xD=new T(function(){return B(unCStr("ENQ"));}),_xE=5,_xF=function(_xG){var _xH=new T(function(){return B(A1(_xG,_xE));});return new T1(1,B(_wP(_xD,function(_xI){return E(_xH);})));},_xJ=new T(function(){return B(unCStr("ACK"));}),_xK=6,_xL=function(_xM){var _xN=new T(function(){return B(A1(_xM,_xK));});return new T1(1,B(_wP(_xJ,function(_xO){return E(_xN);})));},_xP=new T(function(){return B(unCStr("BEL"));}),_xQ=7,_xR=function(_xS){var _xT=new T(function(){return B(A1(_xS,_xQ));});return new T1(1,B(_wP(_xP,function(_xU){return E(_xT);})));},_xV=new T(function(){return B(unCStr("BS"));}),_xW=8,_xX=function(_xY){var _xZ=new T(function(){return B(A1(_xY,_xW));});return new T1(1,B(_wP(_xV,function(_y0){return E(_xZ);})));},_y1=new T(function(){return B(unCStr("HT"));}),_y2=9,_y3=function(_y4){var _y5=new T(function(){return B(A1(_y4,_y2));});return new T1(1,B(_wP(_y1,function(_y6){return E(_y5);})));},_y7=new T(function(){return B(unCStr("LF"));}),_y8=10,_y9=function(_ya){var _yb=new T(function(){return B(A1(_ya,_y8));});return new T1(1,B(_wP(_y7,function(_yc){return E(_yb);})));},_yd=new T(function(){return B(unCStr("VT"));}),_ye=11,_yf=function(_yg){var _yh=new T(function(){return B(A1(_yg,_ye));});return new T1(1,B(_wP(_yd,function(_yi){return E(_yh);})));},_yj=new T(function(){return B(unCStr("FF"));}),_yk=12,_yl=function(_ym){var _yn=new T(function(){return B(A1(_ym,_yk));});return new T1(1,B(_wP(_yj,function(_yo){return E(_yn);})));},_yp=new T(function(){return B(unCStr("CR"));}),_yq=13,_yr=function(_ys){var _yt=new T(function(){return B(A1(_ys,_yq));});return new T1(1,B(_wP(_yp,function(_yu){return E(_yt);})));},_yv=new T(function(){return B(unCStr("SI"));}),_yw=15,_yx=function(_yy){var _yz=new T(function(){return B(A1(_yy,_yw));});return new T1(1,B(_wP(_yv,function(_yA){return E(_yz);})));},_yB=new T(function(){return B(unCStr("DLE"));}),_yC=16,_yD=function(_yE){var _yF=new T(function(){return B(A1(_yE,_yC));});return new T1(1,B(_wP(_yB,function(_yG){return E(_yF);})));},_yH=new T(function(){return B(unCStr("DC1"));}),_yI=17,_yJ=function(_yK){var _yL=new T(function(){return B(A1(_yK,_yI));});return new T1(1,B(_wP(_yH,function(_yM){return E(_yL);})));},_yN=new T(function(){return B(unCStr("DC2"));}),_yO=18,_yP=function(_yQ){var _yR=new T(function(){return B(A1(_yQ,_yO));});return new T1(1,B(_wP(_yN,function(_yS){return E(_yR);})));},_yT=new T(function(){return B(unCStr("DC3"));}),_yU=19,_yV=function(_yW){var _yX=new T(function(){return B(A1(_yW,_yU));});return new T1(1,B(_wP(_yT,function(_yY){return E(_yX);})));},_yZ=new T(function(){return B(unCStr("DC4"));}),_z0=20,_z1=function(_z2){var _z3=new T(function(){return B(A1(_z2,_z0));});return new T1(1,B(_wP(_yZ,function(_z4){return E(_z3);})));},_z5=new T(function(){return B(unCStr("NAK"));}),_z6=21,_z7=function(_z8){var _z9=new T(function(){return B(A1(_z8,_z6));});return new T1(1,B(_wP(_z5,function(_za){return E(_z9);})));},_zb=new T(function(){return B(unCStr("SYN"));}),_zc=22,_zd=function(_ze){var _zf=new T(function(){return B(A1(_ze,_zc));});return new T1(1,B(_wP(_zb,function(_zg){return E(_zf);})));},_zh=new T(function(){return B(unCStr("ETB"));}),_zi=23,_zj=function(_zk){var _zl=new T(function(){return B(A1(_zk,_zi));});return new T1(1,B(_wP(_zh,function(_zm){return E(_zl);})));},_zn=new T(function(){return B(unCStr("CAN"));}),_zo=24,_zp=function(_zq){var _zr=new T(function(){return B(A1(_zq,_zo));});return new T1(1,B(_wP(_zn,function(_zs){return E(_zr);})));},_zt=new T(function(){return B(unCStr("EM"));}),_zu=25,_zv=function(_zw){var _zx=new T(function(){return B(A1(_zw,_zu));});return new T1(1,B(_wP(_zt,function(_zy){return E(_zx);})));},_zz=new T(function(){return B(unCStr("SUB"));}),_zA=26,_zB=function(_zC){var _zD=new T(function(){return B(A1(_zC,_zA));});return new T1(1,B(_wP(_zz,function(_zE){return E(_zD);})));},_zF=new T(function(){return B(unCStr("ESC"));}),_zG=27,_zH=function(_zI){var _zJ=new T(function(){return B(A1(_zI,_zG));});return new T1(1,B(_wP(_zF,function(_zK){return E(_zJ);})));},_zL=new T(function(){return B(unCStr("FS"));}),_zM=28,_zN=function(_zO){var _zP=new T(function(){return B(A1(_zO,_zM));});return new T1(1,B(_wP(_zL,function(_zQ){return E(_zP);})));},_zR=new T(function(){return B(unCStr("GS"));}),_zS=29,_zT=function(_zU){var _zV=new T(function(){return B(A1(_zU,_zS));});return new T1(1,B(_wP(_zR,function(_zW){return E(_zV);})));},_zX=new T(function(){return B(unCStr("RS"));}),_zY=30,_zZ=function(_A0){var _A1=new T(function(){return B(A1(_A0,_zY));});return new T1(1,B(_wP(_zX,function(_A2){return E(_A1);})));},_A3=new T(function(){return B(unCStr("US"));}),_A4=31,_A5=function(_A6){var _A7=new T(function(){return B(A1(_A6,_A4));});return new T1(1,B(_wP(_A3,function(_A8){return E(_A7);})));},_A9=new T(function(){return B(unCStr("SP"));}),_Aa=32,_Ab=function(_Ac){var _Ad=new T(function(){return B(A1(_Ac,_Aa));});return new T1(1,B(_wP(_A9,function(_Ae){return E(_Ad);})));},_Af=new T(function(){return B(unCStr("DEL"));}),_Ag=127,_Ah=function(_Ai){var _Aj=new T(function(){return B(A1(_Ai,_Ag));});return new T1(1,B(_wP(_Af,function(_Ak){return E(_Aj);})));},_Al=new T2(1,_Ah,_10),_Am=new T2(1,_Ab,_Al),_An=new T2(1,_A5,_Am),_Ao=new T2(1,_zZ,_An),_Ap=new T2(1,_zT,_Ao),_Aq=new T2(1,_zN,_Ap),_Ar=new T2(1,_zH,_Aq),_As=new T2(1,_zB,_Ar),_At=new T2(1,_zv,_As),_Au=new T2(1,_zp,_At),_Av=new T2(1,_zj,_Au),_Aw=new T2(1,_zd,_Av),_Ax=new T2(1,_z7,_Aw),_Ay=new T2(1,_z1,_Ax),_Az=new T2(1,_yV,_Ay),_AA=new T2(1,_yP,_Az),_AB=new T2(1,_yJ,_AA),_AC=new T2(1,_yD,_AB),_AD=new T2(1,_yx,_AC),_AE=new T2(1,_yr,_AD),_AF=new T2(1,_yl,_AE),_AG=new T2(1,_yf,_AF),_AH=new T2(1,_y9,_AG),_AI=new T2(1,_y3,_AH),_AJ=new T2(1,_xX,_AI),_AK=new T2(1,_xR,_AJ),_AL=new T2(1,_xL,_AK),_AM=new T2(1,_xF,_AL),_AN=new T2(1,_xz,_AM),_AO=new T2(1,_xt,_AN),_AP=new T2(1,_xn,_AO),_AQ=new T2(1,_xh,_AP),_AR=new T2(1,_xd,_AQ),_AS=new T(function(){return B(_wH(_AR));}),_AT=34,_AU=new T1(0,1114111),_AV=92,_AW=39,_AX=function(_AY){var _AZ=new T(function(){return B(A1(_AY,_xQ));}),_B0=new T(function(){return B(A1(_AY,_xW));}),_B1=new T(function(){return B(A1(_AY,_y2));}),_B2=new T(function(){return B(A1(_AY,_y8));}),_B3=new T(function(){return B(A1(_AY,_ye));}),_B4=new T(function(){return B(A1(_AY,_yk));}),_B5=new T(function(){return B(A1(_AY,_yq));}),_B6=new T(function(){return B(A1(_AY,_AV));}),_B7=new T(function(){return B(A1(_AY,_AW));}),_B8=new T(function(){return B(A1(_AY,_AT));}),_B9=new T(function(){var _Ba=function(_Bb){var _Bc=new T(function(){return B(_aR(E(_Bb)));}),_Bd=function(_Be){var _Bf=B(_vQ(_Bc,_Be));if(!B(_ez(_Bf,_AU))){return new T0(2);}else{return new F(function(){return A1(_AY,new T(function(){var _Bg=B(_ba(_Bf));if(_Bg>>>0>1114111){return B(_wD(_Bg));}else{return _Bg;}}));});}};return new T1(1,B(_um(_Bb,_Bd)));},_Bh=new T(function(){var _Bi=new T(function(){return B(A1(_AY,_A4));}),_Bj=new T(function(){return B(A1(_AY,_zY));}),_Bk=new T(function(){return B(A1(_AY,_zS));}),_Bl=new T(function(){return B(A1(_AY,_zM));}),_Bm=new T(function(){return B(A1(_AY,_zG));}),_Bn=new T(function(){return B(A1(_AY,_zA));}),_Bo=new T(function(){return B(A1(_AY,_zu));}),_Bp=new T(function(){return B(A1(_AY,_zo));}),_Bq=new T(function(){return B(A1(_AY,_zi));}),_Br=new T(function(){return B(A1(_AY,_zc));}),_Bs=new T(function(){return B(A1(_AY,_z6));}),_Bt=new T(function(){return B(A1(_AY,_z0));}),_Bu=new T(function(){return B(A1(_AY,_yU));}),_Bv=new T(function(){return B(A1(_AY,_yO));}),_Bw=new T(function(){return B(A1(_AY,_yI));}),_Bx=new T(function(){return B(A1(_AY,_yC));}),_By=new T(function(){return B(A1(_AY,_yw));}),_Bz=new T(function(){return B(A1(_AY,_x2));}),_BA=new T(function(){return B(A1(_AY,_xK));}),_BB=new T(function(){return B(A1(_AY,_xE));}),_BC=new T(function(){return B(A1(_AY,_xy));}),_BD=new T(function(){return B(A1(_AY,_xs));}),_BE=new T(function(){return B(A1(_AY,_xm));}),_BF=new T(function(){return B(A1(_AY,_x8));}),_BG=new T(function(){return B(A1(_AY,_xg));}),_BH=function(_BI){switch(E(_BI)){case 64:return E(_BG);case 65:return E(_BF);case 66:return E(_BE);case 67:return E(_BD);case 68:return E(_BC);case 69:return E(_BB);case 70:return E(_BA);case 71:return E(_AZ);case 72:return E(_B0);case 73:return E(_B1);case 74:return E(_B2);case 75:return E(_B3);case 76:return E(_B4);case 77:return E(_B5);case 78:return E(_Bz);case 79:return E(_By);case 80:return E(_Bx);case 81:return E(_Bw);case 82:return E(_Bv);case 83:return E(_Bu);case 84:return E(_Bt);case 85:return E(_Bs);case 86:return E(_Br);case 87:return E(_Bq);case 88:return E(_Bp);case 89:return E(_Bo);case 90:return E(_Bn);case 91:return E(_Bm);case 92:return E(_Bl);case 93:return E(_Bk);case 94:return E(_Bj);case 95:return E(_Bi);default:return new T0(2);}};return B(_sH(new T1(0,function(_BJ){return (E(_BJ)==94)?E(new T1(0,_BH)):new T0(2);}),new T(function(){return B(A1(_AS,_AY));})));});return B(_sH(new T1(1,B(_tF(_wz,_wB,_Ba))),_Bh));});return new F(function(){return _sH(new T1(0,function(_BK){switch(E(_BK)){case 34:return E(_B8);case 39:return E(_B7);case 92:return E(_B6);case 97:return E(_AZ);case 98:return E(_B0);case 102:return E(_B4);case 110:return E(_B2);case 114:return E(_B5);case 116:return E(_B1);case 118:return E(_B3);default:return new T0(2);}}),_B9);});},_BL=function(_BM){return new F(function(){return A1(_BM,_gE);});},_BN=function(_BO){var _BP=E(_BO);if(!_BP._){return E(_BL);}else{var _BQ=E(_BP.a),_BR=_BQ>>>0,_BS=new T(function(){return B(_BN(_BP.b));});if(_BR>887){var _BT=u_iswspace(_BQ);if(!E(_BT)){return E(_BL);}else{var _BU=function(_BV){var _BW=new T(function(){return B(A1(_BS,_BV));});return new T1(0,function(_BX){return E(_BW);});};return E(_BU);}}else{var _BY=E(_BR);if(_BY==32){var _BZ=function(_C0){var _C1=new T(function(){return B(A1(_BS,_C0));});return new T1(0,function(_C2){return E(_C1);});};return E(_BZ);}else{if(_BY-9>>>0>4){if(E(_BY)==160){var _C3=function(_C4){var _C5=new T(function(){return B(A1(_BS,_C4));});return new T1(0,function(_C6){return E(_C5);});};return E(_C3);}else{return E(_BL);}}else{var _C7=function(_C8){var _C9=new T(function(){return B(A1(_BS,_C8));});return new T1(0,function(_Ca){return E(_C9);});};return E(_C7);}}}}},_Cb=function(_Cc){var _Cd=new T(function(){return B(_Cb(_Cc));}),_Ce=function(_Cf){return (E(_Cf)==92)?E(_Cd):new T0(2);},_Cg=function(_Ch){return E(new T1(0,_Ce));},_Ci=new T1(1,function(_Cj){return new F(function(){return A2(_BN,_Cj,_Cg);});}),_Ck=new T(function(){return B(_AX(function(_Cl){return new F(function(){return A1(_Cc,new T2(0,_Cl,_wt));});}));}),_Cm=function(_Cn){var _Co=E(_Cn);if(_Co==38){return E(_Cd);}else{var _Cp=_Co>>>0;if(_Cp>887){var _Cq=u_iswspace(_Co);return (E(_Cq)==0)?new T0(2):E(_Ci);}else{var _Cr=E(_Cp);return (_Cr==32)?E(_Ci):(_Cr-9>>>0>4)?(E(_Cr)==160)?E(_Ci):new T0(2):E(_Ci);}}};return new F(function(){return _sH(new T1(0,function(_Cs){return (E(_Cs)==92)?E(new T1(0,_Cm)):new T0(2);}),new T1(0,function(_Ct){var _Cu=E(_Ct);if(E(_Cu)==92){return E(_Ck);}else{return new F(function(){return A1(_Cc,new T2(0,_Cu,_ws));});}}));});},_Cv=function(_Cw,_Cx){var _Cy=new T(function(){return B(A1(_Cx,new T1(1,new T(function(){return B(A1(_Cw,_10));}))));}),_Cz=function(_CA){var _CB=E(_CA),_CC=E(_CB.a);if(E(_CC)==34){if(!E(_CB.b)){return E(_Cy);}else{return new F(function(){return _Cv(function(_CD){return new F(function(){return A1(_Cw,new T2(1,_CC,_CD));});},_Cx);});}}else{return new F(function(){return _Cv(function(_CE){return new F(function(){return A1(_Cw,new T2(1,_CC,_CE));});},_Cx);});}};return new F(function(){return _Cb(_Cz);});},_CF=new T(function(){return B(unCStr("_\'"));}),_CG=function(_CH){var _CI=u_iswalnum(_CH);if(!E(_CI)){return new F(function(){return _4B(_h7,_CH,_CF);});}else{return true;}},_CJ=function(_CK){return new F(function(){return _CG(E(_CK));});},_CL=new T(function(){return B(unCStr(",;()[]{}`"));}),_CM=new T(function(){return B(unCStr("=>"));}),_CN=new T2(1,_CM,_10),_CO=new T(function(){return B(unCStr("~"));}),_CP=new T2(1,_CO,_CN),_CQ=new T(function(){return B(unCStr("@"));}),_CR=new T2(1,_CQ,_CP),_CS=new T(function(){return B(unCStr("->"));}),_CT=new T2(1,_CS,_CR),_CU=new T(function(){return B(unCStr("<-"));}),_CV=new T2(1,_CU,_CT),_CW=new T(function(){return B(unCStr("|"));}),_CX=new T2(1,_CW,_CV),_CY=new T(function(){return B(unCStr("\\"));}),_CZ=new T2(1,_CY,_CX),_D0=new T(function(){return B(unCStr("="));}),_D1=new T2(1,_D0,_CZ),_D2=new T(function(){return B(unCStr("::"));}),_D3=new T2(1,_D2,_D1),_D4=new T(function(){return B(unCStr(".."));}),_D5=new T2(1,_D4,_D3),_D6=function(_D7){var _D8=new T(function(){return B(A1(_D7,_uj));}),_D9=new T(function(){var _Da=new T(function(){var _Db=function(_Dc){var _Dd=new T(function(){return B(A1(_D7,new T1(0,_Dc)));});return new T1(0,function(_De){return (E(_De)==39)?E(_Dd):new T0(2);});};return B(_AX(_Db));}),_Df=function(_Dg){var _Dh=E(_Dg);switch(E(_Dh)){case 39:return new T0(2);case 92:return E(_Da);default:var _Di=new T(function(){return B(A1(_D7,new T1(0,_Dh)));});return new T1(0,function(_Dj){return (E(_Dj)==39)?E(_Di):new T0(2);});}},_Dk=new T(function(){var _Dl=new T(function(){return B(_Cv(_5V,_D7));}),_Dm=new T(function(){var _Dn=new T(function(){var _Do=new T(function(){var _Dp=function(_Dq){var _Dr=E(_Dq),_Ds=u_iswalpha(_Dr);return (E(_Ds)==0)?(E(_Dr)==95)?new T1(1,B(_u5(_CJ,function(_Dt){return new F(function(){return A1(_D7,new T1(3,new T2(1,_Dr,_Dt)));});}))):new T0(2):new T1(1,B(_u5(_CJ,function(_Du){return new F(function(){return A1(_D7,new T1(3,new T2(1,_Dr,_Du)));});})));};return B(_sH(new T1(0,_Dp),new T(function(){return new T1(1,B(_tF(_vh,_wn,_D7)));})));}),_Dv=function(_Dw){return (!B(_4B(_h7,_Dw,_wp)))?new T0(2):new T1(1,B(_u5(_wq,function(_Dx){var _Dy=new T2(1,_Dw,_Dx);if(!B(_4B(_qe,_Dy,_D5))){return new F(function(){return A1(_D7,new T1(4,_Dy));});}else{return new F(function(){return A1(_D7,new T1(2,_Dy));});}})));};return B(_sH(new T1(0,_Dv),_Do));});return B(_sH(new T1(0,function(_Dz){if(!B(_4B(_h7,_Dz,_CL))){return new T0(2);}else{return new F(function(){return A1(_D7,new T1(2,new T2(1,_Dz,_10)));});}}),_Dn));});return B(_sH(new T1(0,function(_DA){return (E(_DA)==34)?E(_Dl):new T0(2);}),_Dm));});return B(_sH(new T1(0,function(_DB){return (E(_DB)==39)?E(new T1(0,_Df)):new T0(2);}),_Dk));});return new F(function(){return _sH(new T1(1,function(_DC){return (E(_DC)._==0)?E(_D8):new T0(2);}),_D9);});},_DD=0,_DE=function(_DF,_DG){var _DH=new T(function(){var _DI=new T(function(){var _DJ=function(_DK){var _DL=new T(function(){var _DM=new T(function(){return B(A1(_DG,_DK));});return B(_D6(function(_DN){var _DO=E(_DN);return (_DO._==2)?(!B(_qN(_DO.a,_tk)))?new T0(2):E(_DM):new T0(2);}));}),_DP=function(_DQ){return E(_DL);};return new T1(1,function(_DR){return new F(function(){return A2(_BN,_DR,_DP);});});};return B(A2(_DF,_DD,_DJ));});return B(_D6(function(_DS){var _DT=E(_DS);return (_DT._==2)?(!B(_qN(_DT.a,_tj)))?new T0(2):E(_DI):new T0(2);}));}),_DU=function(_DV){return E(_DH);};return function(_DW){return new F(function(){return A2(_BN,_DW,_DU);});};},_DX=function(_DY,_DZ){var _E0=function(_E1){var _E2=new T(function(){return B(A1(_DY,_E1));}),_E3=function(_E4){return new F(function(){return _sH(B(A1(_E2,_E4)),new T(function(){return new T1(1,B(_DE(_E0,_E4)));}));});};return E(_E3);},_E5=new T(function(){return B(A1(_DY,_DZ));}),_E6=function(_E7){return new F(function(){return _sH(B(A1(_E5,_E7)),new T(function(){return new T1(1,B(_DE(_E0,_E7)));}));});};return E(_E6);},_E8=0,_E9=function(_Ea,_Eb){return new F(function(){return A1(_Eb,_E8);});},_Ec=new T(function(){return B(unCStr("Fr"));}),_Ed=new T2(0,_Ec,_E9),_Ee=1,_Ef=function(_Eg,_Eh){return new F(function(){return A1(_Eh,_Ee);});},_Ei=new T(function(){return B(unCStr("Bl"));}),_Ej=new T2(0,_Ei,_Ef),_Ek=2,_El=function(_Em,_En){return new F(function(){return A1(_En,_Ek);});},_Eo=new T(function(){return B(unCStr("Ex"));}),_Ep=new T2(0,_Eo,_El),_Eq=3,_Er=function(_Es,_Et){return new F(function(){return A1(_Et,_Eq);});},_Eu=new T(function(){return B(unCStr("Mv"));}),_Ev=new T2(0,_Eu,_Er),_Ew=4,_Ex=function(_Ey,_Ez){return new F(function(){return A1(_Ez,_Ew);});},_EA=new T(function(){return B(unCStr("Pn"));}),_EB=new T2(0,_EA,_Ex),_EC=8,_ED=function(_EE,_EF){return new F(function(){return A1(_EF,_EC);});},_EG=new T(function(){return B(unCStr("DF"));}),_EH=new T2(0,_EG,_ED),_EI=new T2(1,_EH,_10),_EJ=7,_EK=function(_EL,_EM){return new F(function(){return A1(_EM,_EJ);});},_EN=new T(function(){return B(unCStr("DB"));}),_EO=new T2(0,_EN,_EK),_EP=new T2(1,_EO,_EI),_EQ=6,_ER=function(_ES,_ET){return new F(function(){return A1(_ET,_EQ);});},_EU=new T(function(){return B(unCStr("Cm"));}),_EV=new T2(0,_EU,_ER),_EW=new T2(1,_EV,_EP),_EX=5,_EY=function(_EZ,_F0){return new F(function(){return A1(_F0,_EX);});},_F1=new T(function(){return B(unCStr("Wn"));}),_F2=new T2(0,_F1,_EY),_F3=new T2(1,_F2,_EW),_F4=new T2(1,_EB,_F3),_F5=new T2(1,_Ev,_F4),_F6=new T2(1,_Ep,_F5),_F7=new T2(1,_Ej,_F6),_F8=new T2(1,_Ed,_F7),_F9=function(_Fa,_Fb,_Fc){var _Fd=E(_Fa);if(!_Fd._){return new T0(2);}else{var _Fe=E(_Fd.a),_Ff=_Fe.a,_Fg=new T(function(){return B(A2(_Fe.b,_Fb,_Fc));}),_Fh=new T(function(){return B(_D6(function(_Fi){var _Fj=E(_Fi);switch(_Fj._){case 3:return (!B(_qN(_Ff,_Fj.a)))?new T0(2):E(_Fg);case 4:return (!B(_qN(_Ff,_Fj.a)))?new T0(2):E(_Fg);default:return new T0(2);}}));}),_Fk=function(_Fl){return E(_Fh);};return new F(function(){return _sH(new T1(1,function(_Fm){return new F(function(){return A2(_BN,_Fm,_Fk);});}),new T(function(){return B(_F9(_Fd.b,_Fb,_Fc));}));});}},_Fn=function(_Fo,_Fp){return new F(function(){return _F9(_F8,_Fo,_Fp);});},_Fq=function(_Fr){var _Fs=function(_Ft){return E(new T2(3,_Fr,_tw));};return new T1(1,function(_Fu){return new F(function(){return A2(_BN,_Fu,_Fs);});});},_Fv=new T(function(){return B(A3(_DX,_Fn,_DD,_Fq));}),_Fw=new T(function(){return B(unCStr("empty"));}),_Fx=new T2(1,_Fw,_10),_Fy=new T(function(){return B(err(_sq));}),_Fz=new T(function(){return B(err(_ss));}),_FA=function(_FB,_FC){var _FD=function(_FE,_FF){var _FG=function(_FH){return new F(function(){return A1(_FF,new T(function(){return  -E(_FH);}));});},_FI=new T(function(){return B(_D6(function(_FJ){return new F(function(){return A3(_FB,_FJ,_FE,_FG);});}));}),_FK=function(_FL){return E(_FI);},_FM=function(_FN){return new F(function(){return A2(_BN,_FN,_FK);});},_FO=new T(function(){return B(_D6(function(_FP){var _FQ=E(_FP);if(_FQ._==4){var _FR=E(_FQ.a);if(!_FR._){return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}else{if(E(_FR.a)==45){if(!E(_FR.b)._){return E(new T1(1,_FM));}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}}else{return new F(function(){return A3(_FB,_FQ,_FE,_FF);});}}));}),_FS=function(_FT){return E(_FO);};return new T1(1,function(_FU){return new F(function(){return A2(_BN,_FU,_FS);});});};return new F(function(){return _DX(_FD,_FC);});},_FV=function(_FW){var _FX=E(_FW);if(!_FX._){var _FY=_FX.b,_FZ=new T(function(){return B(_vz(new T(function(){return B(_aR(E(_FX.a)));}),new T(function(){return B(_mt(_FY,0));},1),B(_6e(_vp,_FY))));});return new T1(1,_FZ);}else{return (E(_FX.b)._==0)?(E(_FX.c)._==0)?new T1(1,new T(function(){return B(_vQ(_vo,_FX.a));})):__Z:__Z;}},_G0=function(_G1,_G2){return new T0(2);},_G3=function(_G4){var _G5=E(_G4);if(_G5._==5){var _G6=B(_FV(_G5.a));if(!_G6._){return E(_G0);}else{var _G7=new T(function(){return B(_ba(_G6.a));});return function(_G8,_G9){return new F(function(){return A1(_G9,_G7);});};}}else{return E(_G0);}},_Ga=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_Gb=new T2(1,_G,_10),_Gc=function(_Gd){while(1){var _Ge=B((function(_Gf){var _Gg=E(_Gf);if(!_Gg._){return __Z;}else{var _Gh=_Gg.b,_Gi=E(_Gg.a);if(!E(_Gi.b)._){return new T2(1,_Gi.a,new T(function(){return B(_Gc(_Gh));}));}else{_Gd=_Gh;return __continue;}}})(_Gd));if(_Ge!=__continue){return _Ge;}}},_Gj=function(_Gk,_Gl){while(1){var _Gm=E(_Gk);if(!_Gm._){return E(_Gl);}else{var _Gn=new T2(1,_Gm.a,_Gl);_Gk=_Gm.b;_Gl=_Gn;continue;}}},_Go=function(_Gp,_Gq){var _Gr=E(_Gp);if(!_Gr._){return __Z;}else{var _Gs=E(_Gq);return (_Gs._==0)?__Z:new T2(1,new T2(0,_Gr.a,_Gs.a),new T(function(){return B(_Go(_Gr.b,_Gs.b));}));}},_Gt=function(_Gu,_Gv,_Gw){while(1){var _Gx=B((function(_Gy,_Gz,_GA){var _GB=E(_GA);if(!_GB._){return E(_Gz);}else{var _GC=_GB.a,_GD=_GB.b,_GE=B(_sk(_qe,_GC,_s9));if(!_GE._){var _GF=E(_Fx);}else{var _GF=E(_GE.a);}if(!B(_qS(_GF,_Fx))){var _GG=B(_Gj(B(_Go(B(_Gj(_Gz,_10)),new T(function(){return B(_Gj(_GF,_10));},1))),_10)),_GH=B(_mt(_GG,0)),_GI=new T(function(){var _GJ=B(_6e(_si,_GG));if(!_GJ._){return __Z;}else{var _GK=_GJ.a,_GL=E(_GJ.b);if(!_GL._){return __Z;}else{var _GM=_GL.a;if(!E(_GL.b)._){if(!B(_qN(_GC,_rL))){if(!B(_qN(_GC,_rK))){if(!B(_qN(_GC,_rJ))){if(!B(_qN(_GC,_rN))){if(!B(_qN(_GC,_rM))){return __Z;}else{if(!B(_qN(_GK,_su))){if(!B(_qN(_GM,_su))){return E(_sv);}else{return E(_su);}}else{return E(_su);}}}else{var _GN=B(_rx(new T2(0,new T(function(){var _GO=E(_GK);if(!_GO._){return E(_nh);}else{return E(_GO.a);}}),new T(function(){var _GP=B(_Gc(B(_sx(_Fv,_GM))));if(!_GP._){return E(_sr);}else{if(!E(_GP.b)._){return E(_GP.a);}else{return E(_st);}}})),E(E(_Gy).a).b)),_GQ=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_GR){return new F(function(){return _I(0,E(_GN.a),_GR);});},new T2(1,function(_GS){return new F(function(){return _I(0,E(_GN.b),_GS);});},_10)),_Gb));});return new T2(1,_H,_GQ);}}else{return new T2(1,new T(function(){var _GT=B(_Gc(B(_sx(_Ga,_GK))));if(!_GT._){return E(_Fy);}else{if(!E(_GT.b)._){var _GU=B(_Gc(B(_sx(_Ga,_GM))));if(!_GU._){return E(_Fy);}else{if(!E(_GU.b)._){return E(B(_6R(B(_6R(E(E(_Gy).a).b,E(_GU.a))),E(_GT.a))).a);}else{return E(_Fz);}}}else{return E(_Fz);}}}),_10);}}else{if(!B(_qN(_GK,_GM))){return E(_sv);}else{return E(_su);}}}else{if(!B(_qN(_GK,_su))){return E(_sv);}else{if(!B(_qN(_GM,_su))){return E(_sv);}else{return E(_su);}}}}else{return __Z;}}}});if(_GH>0){var _GV=_Gy,_GW=B(_y(B(_Gj(B(_rD(_GH,B(_Gj(_Gz,_10)))),_10)),new T2(1,_GI,_10)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}else{var _GV=_Gy,_GW=B(_y(B(_Gj(B(_Gj(_Gz,_10)),_10)),new T2(1,_GI,_10)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}}else{var _GV=_Gy,_GW=B(_y(_Gz,new T2(1,_GC,_10)));_Gu=_GV;_Gv=_GW;_Gw=_GD;return __continue;}}})(_Gu,_Gv,_Gw));if(_Gx!=__continue){return _Gx;}}},_GX=new T(function(){return B(_e7("Event.hs:(86,1)-(90,73)|function addMemory"));}),_GY=function(_GZ,_H0){var _H1=E(_GZ),_H2=E(_H0);if(!B(_qN(_H1.a,_H2.a))){return false;}else{return new F(function(){return _qN(_H1.b,_H2.b);});}},_H3=new T2(1,_10,_10),_H4=function(_H5,_H6,_H7){var _H8=E(_H7);if(!_H8._){return new T2(0,new T2(1,_H6,_10),_10);}else{var _H9=E(_H6),_Ha=new T(function(){var _Hb=B(_H4(_H5,_H8.a,_H8.b));return new T2(0,_Hb.a,_Hb.b);});return (_H5!=_H9)?new T2(0,new T2(1,_H9,new T(function(){return E(E(_Ha).a);})),new T(function(){return E(E(_Ha).b);})):new T2(0,_10,new T2(1,new T(function(){return E(E(_Ha).a);}),new T(function(){return E(E(_Ha).b);})));}},_Hc=32,_Hd=function(_He){var _Hf=E(_He);if(!_Hf._){return __Z;}else{var _Hg=new T(function(){return B(_y(_Hf.a,new T(function(){return B(_Hd(_Hf.b));},1)));});return new T2(1,_Hc,_Hg);}},_Hh=function(_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB){while(1){var _HC=B((function(_HD,_HE,_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM,_HN,_HO,_HP,_HQ,_HR,_HS,_HT,_HU,_HV,_HW){var _HX=E(_HD);if(!_HX._){return {_:0,a:_HE,b:_HF,c:_HG,d:_HH,e:_HI,f:_HJ,g:_HK,h:_HL,i:_HM,j:_HN,k:_HO,l:_HP,m:_HQ,n:_HR,o:_HS,p:_HT,q:_HU,r:_HV,s:_HW};}else{var _HY=_HX.a,_HZ=E(_HX.b);if(!_HZ._){return E(_GX);}else{var _I0=new T(function(){var _I1=E(_HZ.a);if(!_I1._){var _I2=B(_Gt({_:0,a:E(_HE),b:E(_HF),c:E(_HG),d:E(_HH),e:E(_HI),f:E(_HJ),g:E(_HK),h:E(_HL),i:_HM,j:_HN,k:_HO,l:_HP,m:E(_HQ),n:_HR,o:E(_HS),p:E(_HT),q:_HU,r:E(_HV),s:E(_HW)},_10,_H3));if(!_I2._){return __Z;}else{return B(_y(_I2.a,new T(function(){return B(_Hd(_I2.b));},1)));}}else{var _I3=_I1.a,_I4=E(_I1.b);if(!_I4._){var _I5=B(_Gt({_:0,a:E(_HE),b:E(_HF),c:E(_HG),d:E(_HH),e:E(_HI),f:E(_HJ),g:E(_HK),h:E(_HL),i:_HM,j:_HN,k:_HO,l:_HP,m:E(_HQ),n:_HR,o:E(_HS),p:E(_HT),q:_HU,r:E(_HV),s:E(_HW)},_10,new T2(1,new T2(1,_I3,_10),_10)));if(!_I5._){return __Z;}else{return B(_y(_I5.a,new T(function(){return B(_Hd(_I5.b));},1)));}}else{var _I6=E(_I3),_I7=new T(function(){var _I8=B(_H4(95,_I4.a,_I4.b));return new T2(0,_I8.a,_I8.b);});if(E(_I6)==95){var _I9=B(_Gt({_:0,a:E(_HE),b:E(_HF),c:E(_HG),d:E(_HH),e:E(_HI),f:E(_HJ),g:E(_HK),h:E(_HL),i:_HM,j:_HN,k:_HO,l:_HP,m:E(_HQ),n:_HR,o:E(_HS),p:E(_HT),q:_HU,r:E(_HV),s:E(_HW)},_10,new T2(1,_10,new T2(1,new T(function(){return E(E(_I7).a);}),new T(function(){return E(E(_I7).b);})))));if(!_I9._){return __Z;}else{return B(_y(_I9.a,new T(function(){return B(_Hd(_I9.b));},1)));}}else{var _Ia=B(_Gt({_:0,a:E(_HE),b:E(_HF),c:E(_HG),d:E(_HH),e:E(_HI),f:E(_HJ),g:E(_HK),h:E(_HL),i:_HM,j:_HN,k:_HO,l:_HP,m:E(_HQ),n:_HR,o:E(_HS),p:E(_HT),q:_HU,r:E(_HV),s:E(_HW)},_10,new T2(1,new T2(1,_I6,new T(function(){return E(E(_I7).a);})),new T(function(){return E(E(_I7).b);}))));if(!_Ia._){return __Z;}else{return B(_y(_Ia.a,new T(function(){return B(_Hd(_Ia.b));},1)));}}}}}),_Ib=_HE,_Ic=_HF,_Id=_HG,_Ie=_HH,_If=_HI,_Ig=_HJ,_Ih=_HL,_Ii=_HM,_Ij=_HN,_Ik=_HO,_Il=_HP,_Im=_HQ,_In=_HR,_Io=_HS,_Ip=_HT,_Iq=_HU,_Ir=_HV,_Is=_HW;_Hi=_HZ.b;_Hj=_Ib;_Hk=_Ic;_Hl=_Id;_Hm=_Ie;_Hn=_If;_Ho=_Ig;_Hp=new T2(1,new T2(0,_HY,_I0),new T(function(){var _It=B(_sk(_qe,_HY,_HK));if(!_It._){var _Iu=__Z;}else{var _Iu=E(_It.a);}if(!B(_qN(_Iu,_10))){return B(_qG(_GY,new T2(0,_HY,_Iu),_HK));}else{return E(_HK);}}));_Hq=_Ih;_Hr=_Ii;_Hs=_Ij;_Ht=_Ik;_Hu=_Il;_Hv=_Im;_Hw=_In;_Hx=_Io;_Hy=_Ip;_Hz=_Iq;_HA=_Ir;_HB=_Is;return __continue;}}})(_Hi,_Hj,_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs,_Ht,_Hu,_Hv,_Hw,_Hx,_Hy,_Hz,_HA,_HB));if(_HC!=__continue){return _HC;}}},_Iv=function(_Iw){var _Ix=E(_Iw);if(!_Ix._){return new T2(0,_10,_10);}else{var _Iy=E(_Ix.a),_Iz=new T(function(){var _IA=B(_Iv(_Ix.b));return new T2(0,_IA.a,_IA.b);});return new T2(0,new T2(1,_Iy.a,new T(function(){return E(E(_Iz).a);})),new T2(1,_Iy.b,new T(function(){return E(E(_Iz).b);})));}},_IB=function(_IC,_ID,_IE){while(1){var _IF=B((function(_IG,_IH,_II){var _IJ=E(_II);if(!_IJ._){return __Z;}else{var _IK=_IJ.b;if(_IH!=E(_IJ.a)){var _IL=_IG+1|0,_IM=_IH;_IC=_IL;_ID=_IM;_IE=_IK;return __continue;}else{return new T2(1,_IG,new T(function(){return B(_IB(_IG+1|0,_IH,_IK));}));}}})(_IC,_ID,_IE));if(_IF!=__continue){return _IF;}}},_IN=function(_IO,_IP,_IQ){var _IR=E(_IQ);if(!_IR._){return __Z;}else{var _IS=_IR.b,_IT=E(_IP);if(_IT!=E(_IR.a)){return new F(function(){return _IB(_IO+1|0,_IT,_IS);});}else{return new T2(1,_IO,new T(function(){return B(_IB(_IO+1|0,_IT,_IS));}));}}},_IU=function(_IV,_IW,_IX,_IY){var _IZ=E(_IY);if(!_IZ._){return __Z;}else{var _J0=_IZ.b;return (!B(_4B(_3M,_IV,_IX)))?new T2(1,_IZ.a,new T(function(){return B(_IU(_IV+1|0,_IW,_IX,_J0));})):new T2(1,_IW,new T(function(){return B(_IU(_IV+1|0,_IW,_IX,_J0));}));}},_J1=function(_J2,_J3,_J4){var _J5=E(_J4);if(!_J5._){return __Z;}else{var _J6=new T(function(){var _J7=B(_Iv(_J5.a)),_J8=_J7.a,_J9=new T(function(){return B(_IU(0,_J3,new T(function(){return B(_IN(0,_J2,_J8));}),_J7.b));},1);return B(_Go(_J8,_J9));});return new T2(1,_J6,new T(function(){return B(_J1(_J2,_J3,_J5.b));}));}},_Ja=function(_Jb){var _Jc=E(_Jb);return (_Jc._==0)?E(_nh):E(_Jc.a);},_Jd=new T(function(){return B(_e7("Event.hs:(59,1)-(62,93)|function changeType"));}),_Je=new T(function(){return B(_e7("Event.hs:56:16-116|case"));}),_Jf=new T(function(){return B(unCStr("Wn"));}),_Jg=new T(function(){return B(unCStr("Pn"));}),_Jh=new T(function(){return B(unCStr("Mv"));}),_Ji=new T(function(){return B(unCStr("Fr"));}),_Jj=new T(function(){return B(unCStr("Ex"));}),_Jk=new T(function(){return B(unCStr("DF"));}),_Jl=new T(function(){return B(unCStr("DB"));}),_Jm=new T(function(){return B(unCStr("Cm"));}),_Jn=new T(function(){return B(unCStr("Bl"));}),_Jo=function(_Jp){return (!B(_qN(_Jp,_Jn)))?(!B(_qN(_Jp,_Jm)))?(!B(_qN(_Jp,_Jl)))?(!B(_qN(_Jp,_Jk)))?(!B(_qN(_Jp,_Jj)))?(!B(_qN(_Jp,_Ji)))?(!B(_qN(_Jp,_Jh)))?(!B(_qN(_Jp,_Jg)))?(!B(_qN(_Jp,_Jf)))?E(_Je):5:4:3:0:2:8:7:6:1;},_Jq=function(_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK){while(1){var _JL=B((function(_JM,_JN,_JO,_JP,_JQ,_JR,_JS,_JT,_JU,_JV,_JW,_JX,_JY,_JZ,_K0,_K1,_K2,_K3,_K4,_K5){var _K6=E(_JM);if(!_K6._){return {_:0,a:_JN,b:_JO,c:_JP,d:_JQ,e:_JR,f:_JS,g:_JT,h:_JU,i:_JV,j:_JW,k:_JX,l:_JY,m:_JZ,n:_K0,o:_K1,p:_K2,q:_K3,r:_K4,s:_K5};}else{var _K7=E(_K6.b);if(!_K7._){return E(_Jd);}else{var _K8=E(_JN),_K9=_JO,_Ka=_JP,_Kb=_JQ,_Kc=_JR,_Kd=_JS,_Ke=_JT,_Kf=_JU,_Kg=_JV,_Kh=_JW,_Ki=_JX,_Kj=_JY,_Kk=_JZ,_Kl=_K0,_Km=_K1,_Kn=_K2,_Ko=_K3,_Kp=_K4,_Kq=_K5;_Jr=_K7.b;_Js={_:0,a:E(_K8.a),b:E(B(_J1(new T(function(){return B(_Ja(_K6.a));}),new T(function(){return B(_Jo(_K7.a));}),_K8.b))),c:_K8.c,d:_K8.d,e:_K8.e,f:E(_K8.f),g:_K8.g,h:E(_K8.h),i:E(_K8.i),j:E(_K8.j)};_Jt=_K9;_Ju=_Ka;_Jv=_Kb;_Jw=_Kc;_Jx=_Kd;_Jy=_Ke;_Jz=_Kf;_JA=_Kg;_JB=_Kh;_JC=_Ki;_JD=_Kj;_JE=_Kk;_JF=_Kl;_JG=_Km;_JH=_Kn;_JI=_Ko;_JJ=_Kp;_JK=_Kq;return __continue;}}})(_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH,_JI,_JJ,_JK));if(_JL!=__continue){return _JL;}}},_Kr=function(_Ks,_Kt){while(1){var _Ku=E(_Kt);if(!_Ku._){return __Z;}else{var _Kv=_Ku.b,_Kw=E(_Ks);if(_Kw==1){return E(_Kv);}else{_Ks=_Kw-1|0;_Kt=_Kv;continue;}}}},_Kx=function(_Ky,_Kz){while(1){var _KA=E(_Kz);if(!_KA._){return __Z;}else{var _KB=_KA.b,_KC=E(_Ky);if(_KC==1){return E(_KB);}else{_Ky=_KC-1|0;_Kz=_KB;continue;}}}},_KD=function(_KE,_KF,_KG,_KH,_KI){var _KJ=new T(function(){var _KK=E(_KE),_KL=new T(function(){return B(_6R(_KI,_KF));}),_KM=new T2(1,new T2(0,_KG,_KH),new T(function(){var _KN=_KK+1|0;if(_KN>0){return B(_Kx(_KN,_KL));}else{return E(_KL);}}));if(0>=_KK){return E(_KM);}else{var _KO=function(_KP,_KQ){var _KR=E(_KP);if(!_KR._){return E(_KM);}else{var _KS=_KR.a,_KT=E(_KQ);return (_KT==1)?new T2(1,_KS,_KM):new T2(1,_KS,new T(function(){return B(_KO(_KR.b,_KT-1|0));}));}};return B(_KO(_KL,_KK));}}),_KU=new T2(1,_KJ,new T(function(){var _KV=_KF+1|0;if(_KV>0){return B(_Kr(_KV,_KI));}else{return E(_KI);}}));if(0>=_KF){return E(_KU);}else{var _KW=function(_KX,_KY){var _KZ=E(_KX);if(!_KZ._){return E(_KU);}else{var _L0=_KZ.a,_L1=E(_KY);return (_L1==1)?new T2(1,_L0,_KU):new T2(1,_L0,new T(function(){return B(_KW(_KZ.b,_L1-1|0));}));}};return new F(function(){return _KW(_KI,_KF);});}},_L2=32,_L3=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_L4=function(_L5){return new F(function(){return _dJ(new T1(0,new T(function(){return B(_dW(_L5,_L3));})),_dt);});},_L6=function(_L7){return new F(function(){return _L4("Event.hs:42:27-53|(x\' : y\' : _)");});},_L8=new T(function(){return B(_L6(_));}),_L9=function(_La,_Lb,_Lc,_Ld,_Le,_Lf,_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt){while(1){var _Lu=B((function(_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM,_LN,_LO){var _LP=E(_Lv);if(!_LP._){return {_:0,a:_Lw,b:_Lx,c:_Ly,d:_Lz,e:_LA,f:_LB,g:_LC,h:_LD,i:_LE,j:_LF,k:_LG,l:_LH,m:_LI,n:_LJ,o:_LK,p:_LL,q:_LM,r:_LN,s:_LO};}else{var _LQ=E(_Lw),_LR=new T(function(){var _LS=E(_LP.a);if(!_LS._){return E(_L8);}else{var _LT=E(_LS.b);if(!_LT._){return E(_L8);}else{var _LU=_LT.a,_LV=_LT.b,_LW=E(_LS.a);if(E(_LW)==44){return new T2(0,_10,new T(function(){return E(B(_H4(44,_LU,_LV)).a);}));}else{var _LX=B(_H4(44,_LU,_LV)),_LY=E(_LX.b);if(!_LY._){return E(_L8);}else{return new T2(0,new T2(1,_LW,_LX.a),_LY.a);}}}}}),_LZ=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_LR).b);})))));if(!_LZ._){return E(_Fy);}else{if(!E(_LZ.b)._){var _M0=new T(function(){var _M1=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_LR).a);})))));if(!_M1._){return E(_Fy);}else{if(!E(_M1.b)._){return E(_M1.a);}else{return E(_Fz);}}},1),_M2=_Lx,_M3=_Ly,_M4=_Lz,_M5=_LA,_M6=_LB,_M7=_LC,_M8=_LD,_M9=_LE,_Ma=_LF,_Mb=_LG,_Mc=_LH,_Md=_LI,_Me=_LJ,_Mf=_LK,_Mg=_LL,_Mh=_LM,_Mi=_LN,_Mj=_LO;_La=_LP.b;_Lb={_:0,a:E(_LQ.a),b:E(B(_KD(_M0,E(_LZ.a),_L2,_E8,_LQ.b))),c:_LQ.c,d:_LQ.d,e:_LQ.e,f:E(_LQ.f),g:_LQ.g,h:E(_LQ.h),i:E(_LQ.i),j:E(_LQ.j)};_Lc=_M2;_Ld=_M3;_Le=_M4;_Lf=_M5;_Lg=_M6;_Lh=_M7;_Li=_M8;_Lj=_M9;_Lk=_Ma;_Ll=_Mb;_Lm=_Mc;_Ln=_Md;_Lo=_Me;_Lp=_Mf;_Lq=_Mg;_Lr=_Mh;_Ls=_Mi;_Lt=_Mj;return __continue;}else{return E(_Fz);}}}})(_La,_Lb,_Lc,_Ld,_Le,_Lf,_Lg,_Lh,_Li,_Lj,_Lk,_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt));if(_Lu!=__continue){return _Lu;}}},_Mk=function(_Ml,_Mm,_Mn){var _Mo=E(_Mn);return (_Mo._==0)?0:(!B(A3(_4z,_Ml,_Mm,_Mo.a)))?1+B(_Mk(_Ml,_Mm,_Mo.b))|0:0;},_Mp=function(_Mq,_Mr){while(1){var _Ms=E(_Mr);if(!_Ms._){return __Z;}else{var _Mt=_Ms.b,_Mu=E(_Mq);if(_Mu==1){return E(_Mt);}else{_Mq=_Mu-1|0;_Mr=_Mt;continue;}}}},_Mv=function(_Mw,_Mx){var _My=new T(function(){var _Mz=_Mw+1|0;if(_Mz>0){return B(_Mp(_Mz,_Mx));}else{return E(_Mx);}});if(0>=_Mw){return E(_My);}else{var _MA=function(_MB,_MC){var _MD=E(_MB);if(!_MD._){return E(_My);}else{var _ME=_MD.a,_MF=E(_MC);return (_MF==1)?new T2(1,_ME,_My):new T2(1,_ME,new T(function(){return B(_MA(_MD.b,_MF-1|0));}));}};return new F(function(){return _MA(_Mx,_Mw);});}},_MG=function(_MH,_MI){return new F(function(){return _Mv(E(_MH),_MI);});},_MJ= -1,_MK=function(_ML,_MM,_MN,_MO,_MP,_MQ,_MR,_MS,_MT,_MU,_MV,_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4){while(1){var _N5=B((function(_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj,_Nk,_Nl,_Nm,_Nn,_No,_Np){var _Nq=E(_N6);if(!_Nq._){return {_:0,a:_N7,b:_N8,c:_N9,d:_Na,e:_Nb,f:_Nc,g:_Nd,h:_Ne,i:_Nf,j:_Ng,k:_Nh,l:_Ni,m:_Nj,n:_Nk,o:_Nl,p:_Nm,q:_Nn,r:_No,s:_Np};}else{var _Nr=_Nq.a,_Ns=B(_6e(_si,_Nb)),_Nt=B(_4B(_qe,_Nr,_Ns)),_Nu=new T(function(){if(!E(_Nt)){return E(_MJ);}else{return B(_Mk(_qe,_Nr,_Ns));}});if(!E(_Nt)){var _Nv=E(_Nb);}else{var _Nv=B(_MG(_Nu,_Nb));}if(!E(_Nt)){var _Nw=E(_Nc);}else{var _Nw=B(_MG(_Nu,_Nc));}var _Nx=_N7,_Ny=_N8,_Nz=_N9,_NA=_Na,_NB=_Nd,_NC=_Ne,_ND=_Nf,_NE=_Ng,_NF=_Nh,_NG=_Ni,_NH=_Nj,_NI=_Nk,_NJ=_Nl,_NK=_Nm,_NL=_Nn,_NM=_No,_NN=_Np;_ML=_Nq.b;_MM=_Nx;_MN=_Ny;_MO=_Nz;_MP=_NA;_MQ=_Nv;_MR=_Nw;_MS=_NB;_MT=_NC;_MU=_ND;_MV=_NE;_MW=_NF;_MX=_NG;_MY=_NH;_MZ=_NI;_N0=_NJ;_N1=_NK;_N2=_NL;_N3=_NM;_N4=_NN;return __continue;}})(_ML,_MM,_MN,_MO,_MP,_MQ,_MR,_MS,_MT,_MU,_MV,_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4));if(_N5!=__continue){return _N5;}}},_NO=function(_NP){var _NQ=E(_NP);if(!_NQ._){return new T2(0,_10,_10);}else{var _NR=E(_NQ.a),_NS=new T(function(){var _NT=B(_NO(_NQ.b));return new T2(0,_NT.a,_NT.b);});return new T2(0,new T2(1,_NR.a,new T(function(){return E(E(_NS).a);})),new T2(1,_NR.b,new T(function(){return E(E(_NS).b);})));}},_NU=function(_NV){return new F(function(){return _L4("Event.hs:103:28-52|(c : d : _)");});},_NW=new T(function(){return B(_NU(_));}),_NX=function(_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo){while(1){var _Op=B((function(_Oq,_Or,_Os,_Ot,_Ou,_Ov,_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ){var _OR=E(_Oq);if(!_OR._){return {_:0,a:E(_Or),b:E(_Os),c:E(_Ot),d:E(_Ou),e:E(_Ov),f:E(_Ow),g:E(_Ox),h:E(_Oy),i:_Oz,j:_OA,k:_OB,l:_OC,m:E(_OD),n:_OE,o:E(_OF),p:E(_OG),q:_OH,r:E({_:0,a:E(_OI),b:E(_OJ),c:E(_OK),d:E(_wt),e:E(_OM),f:E(_ON),g:E(_wt),h:E(_OP)}),s:E(_OQ)};}else{var _OS=new T(function(){var _OT=E(_OR.a);if(!_OT._){return E(_NW);}else{var _OU=E(_OT.b);if(!_OU._){return E(_NW);}else{var _OV=_OU.a,_OW=_OU.b,_OX=E(_OT.a);if(E(_OX)==44){return new T2(0,_10,new T(function(){return E(B(_H4(44,_OV,_OW)).a);}));}else{var _OY=B(_H4(44,_OV,_OW)),_OZ=E(_OY.b);if(!_OZ._){return E(_NW);}else{return new T2(0,new T2(1,_OX,_OY.a),_OZ.a);}}}}}),_P0=_Or,_P1=_Os,_P2=_Ot,_P3=_Ou,_P4=_Ov,_P5=_Ow,_P6=_Ox,_P7=_Oy,_P8=_Oz,_P9=_OA,_Pa=_OB,_Pb=_OC,_Pc=B(_y(_OD,new T2(1,new T2(0,new T(function(){return E(E(_OS).a);}),new T(function(){return E(E(_OS).b);})),_10))),_Pd=_OE,_Pe=_OF,_Pf=_OG,_Pg=_OH,_Ph=_OI,_Pi=_OJ,_Pj=_OK,_Pk=_OL,_Pl=_OM,_Pm=_ON,_Pn=_OO,_Po=_OP,_Pp=_OQ;_NY=_OR.b;_NZ=_P0;_O0=_P1;_O1=_P2;_O2=_P3;_O3=_P4;_O4=_P5;_O5=_P6;_O6=_P7;_O7=_P8;_O8=_P9;_O9=_Pa;_Oa=_Pb;_Ob=_Pc;_Oc=_Pd;_Od=_Pe;_Oe=_Pf;_Of=_Pg;_Og=_Ph;_Oh=_Pi;_Oi=_Pj;_Oj=_Pk;_Ok=_Pl;_Ol=_Pm;_Om=_Pn;_On=_Po;_Oo=_Pp;return __continue;}})(_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo));if(_Op!=__continue){return _Op;}}},_Pq=function(_Pr){return new F(function(){return _L4("Event.hs:49:27-53|(x\' : y\' : _)");});},_Ps=new T(function(){return B(_Pq(_));}),_Pt=function(_Pu){return new F(function(){return _L4("Event.hs:50:27-55|(chs : tps : _)");});},_Pv=new T(function(){return B(_Pt(_));}),_Pw=new T(function(){return B(_e7("Event.hs:(47,1)-(53,83)|function putCell"));}),_Px=function(_Py,_Pz,_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI,_PJ,_PK,_PL,_PM,_PN,_PO,_PP,_PQ,_PR){while(1){var _PS=B((function(_PT,_PU,_PV,_PW,_PX,_PY,_PZ,_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc){var _Qd=E(_PT);if(!_Qd._){return {_:0,a:_PU,b:_PV,c:_PW,d:_PX,e:_PY,f:_PZ,g:_Q0,h:_Q1,i:_Q2,j:_Q3,k:_Q4,l:_Q5,m:_Q6,n:_Q7,o:_Q8,p:_Q9,q:_Qa,r:_Qb,s:_Qc};}else{var _Qe=E(_Qd.b);if(!_Qe._){return E(_Pw);}else{var _Qf=E(_PU),_Qg=new T(function(){var _Qh=E(_Qd.a);if(!_Qh._){return E(_Ps);}else{var _Qi=E(_Qh.b);if(!_Qi._){return E(_Ps);}else{var _Qj=_Qi.a,_Qk=_Qi.b,_Ql=E(_Qh.a);if(E(_Ql)==44){return new T2(0,_10,new T(function(){return E(B(_H4(44,_Qj,_Qk)).a);}));}else{var _Qm=B(_H4(44,_Qj,_Qk)),_Qn=E(_Qm.b);if(!_Qn._){return E(_Ps);}else{return new T2(0,new T2(1,_Ql,_Qm.a),_Qn.a);}}}}}),_Qo=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_Qg).b);})))));if(!_Qo._){return E(_Fy);}else{if(!E(_Qo.b)._){var _Qp=new T(function(){var _Qq=E(_Qe.a);if(!_Qq._){return E(_Pv);}else{var _Qr=E(_Qq.b);if(!_Qr._){return E(_Pv);}else{var _Qs=_Qr.a,_Qt=_Qr.b,_Qu=E(_Qq.a);if(E(_Qu)==44){return new T2(0,_10,new T(function(){return E(B(_H4(44,_Qs,_Qt)).a);}));}else{var _Qv=B(_H4(44,_Qs,_Qt)),_Qw=E(_Qv.b);if(!_Qw._){return E(_Pv);}else{return new T2(0,new T2(1,_Qu,_Qv.a),_Qw.a);}}}}}),_Qx=new T(function(){var _Qy=B(_Gc(B(_sx(_Ga,new T(function(){return E(E(_Qg).a);})))));if(!_Qy._){return E(_Fy);}else{if(!E(_Qy.b)._){return E(_Qy.a);}else{return E(_Fz);}}},1),_Qz=_PV,_QA=_PW,_QB=_PX,_QC=_PY,_QD=_PZ,_QE=_Q0,_QF=_Q1,_QG=_Q2,_QH=_Q3,_QI=_Q4,_QJ=_Q5,_QK=_Q6,_QL=_Q7,_QM=_Q8,_QN=_Q9,_QO=_Qa,_QP=_Qb,_QQ=_Qc;_Py=_Qe.b;_Pz={_:0,a:E(_Qf.a),b:E(B(_KD(_Qx,E(_Qo.a),new T(function(){return B(_Ja(E(_Qp).a));}),new T(function(){return B(_Jo(E(_Qp).b));}),_Qf.b))),c:_Qf.c,d:_Qf.d,e:_Qf.e,f:E(_Qf.f),g:_Qf.g,h:E(_Qf.h),i:E(_Qf.i),j:E(_Qf.j)};_PA=_Qz;_PB=_QA;_PC=_QB;_PD=_QC;_PE=_QD;_PF=_QE;_PG=_QF;_PH=_QG;_PI=_QH;_PJ=_QI;_PK=_QJ;_PL=_QK;_PM=_QL;_PN=_QM;_PO=_QN;_PP=_QO;_PQ=_QP;_PR=_QQ;return __continue;}else{return E(_Fz);}}}}})(_Py,_Pz,_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI,_PJ,_PK,_PL,_PM,_PN,_PO,_PP,_PQ,_PR));if(_PS!=__continue){return _PS;}}},_QR=function(_QS){var _QT=E(_QS);if(!_QT._){return new T2(0,_10,_10);}else{var _QU=E(_QT.a),_QV=new T(function(){var _QW=B(_QR(_QT.b));return new T2(0,_QW.a,_QW.b);});return new T2(0,new T2(1,_QU.a,new T(function(){return E(E(_QV).a);})),new T2(1,_QU.b,new T(function(){return E(E(_QV).b);})));}},_QX=32,_QY=function(_QZ,_R0,_R1,_R2){var _R3=E(_R2);if(!_R3._){return __Z;}else{var _R4=_R3.b;if(!B(_4B(_3M,_QZ,_R1))){var _R5=new T(function(){return B(_QY(new T(function(){return E(_QZ)+1|0;}),_R0,_R1,_R4));});return new T2(1,_R3.a,_R5);}else{var _R6=new T(function(){return B(_QY(new T(function(){return E(_QZ)+1|0;}),_R0,_R1,_R4));});return new T2(1,_R0,_R6);}}},_R7=function(_R8,_R9){var _Ra=E(_R9);if(!_Ra._){return __Z;}else{var _Rb=new T(function(){var _Rc=B(_QR(_Ra.a)),_Rd=_Rc.a,_Re=new T(function(){return B(_IN(0,_R8,_Rd));});return B(_Go(B(_QY(_rl,_QX,_Re,_Rd)),new T(function(){return B(_IU(0,_E8,_Re,_Rc.b));},1)));});return new T2(1,_Rb,new T(function(){return B(_R7(_R8,_Ra.b));}));}},_Rf=function(_Rg,_Rh){var _Ri=E(_Rh);return (_Ri._==0)?__Z:new T2(1,_Rg,new T(function(){return B(_Rf(_Ri.a,_Ri.b));}));},_Rj=new T(function(){return B(unCStr("init"));}),_Rk=new T(function(){return B(_ne(_Rj));}),_Rl=function(_Rm,_Rn){var _Ro=function(_Rp){var _Rq=E(_Rp);if(!_Rq._){return __Z;}else{var _Rr=new T(function(){return B(_y(new T2(1,_Rm,_10),new T(function(){return B(_Ro(_Rq.b));},1)));},1);return new F(function(){return _y(_Rq.a,_Rr);});}},_Rs=B(_Ro(_Rn));if(!_Rs._){return E(_Rk);}else{return new F(function(){return _Rf(_Rs.a,_Rs.b);});}},_Rt=61,_Ru=46,_Rv=new T(function(){return B(_e7("Event.hs:(93,1)-(99,61)|function makeDecision"));}),_Rw=new T(function(){return B(unCStr("sm"));}),_Rx=new T(function(){return B(unCStr("rk"));}),_Ry=new T(function(){return B(unCStr("if"));}),_Rz=new T(function(){return B(unCStr("hm"));}),_RA=new T(function(){return B(unCStr("cleq"));}),_RB=new T(function(){return B(unCStr("da"));}),_RC=new T(function(){return B(unCStr("ct"));}),_RD=function(_RE,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX){var _RY=function(_RZ,_S0){var _S1=function(_S2){if(!B(_qN(_RZ,_RC))){if(!B(_qN(_RZ,_RB))){var _S3=function(_S4){if(!B(_qN(_RZ,_RA))){var _S5=function(_S6){if(!B(_qN(_RZ,_rO))){if(!B(_qN(_RZ,_Rz))){if(!B(_qN(_RZ,_Ry))){if(!B(_qN(_RZ,_Rx))){if(!B(_qN(_RZ,_Rw))){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{var _S7=E(_RW);return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E({_:0,a:E(_S7.a),b:E(_S7.b),c:E(_S7.c),d:E(_S7.d),e:E(_S7.e),f:E(_S7.f),g:E(_S7.g),h:E(_wt)}),s:E(_RX)};}}else{return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_S0),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}}else{var _S8=E(_S0);if(!_S8._){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{var _S9=_S8.a,_Sa=E(_S8.b);if(!_Sa._){return E(_Rv);}else{var _Sb=_Sa.a,_Sc=B(_NO(_RL)),_Sd=_Sc.a,_Se=_Sc.b,_Sf=function(_Sg){if(!B(_4B(_qe,_S9,_Sd))){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{if(!B(_qN(_Sb,B(_6R(_Se,B(_Mk(_qe,_S9,_Sd))))))){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{return new F(function(){return _RD(_Sg,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}}},_Sh=B(_Rl(_Ru,_Sa.b));if(!_Sh._){return new F(function(){return _Sf(_10);});}else{var _Si=_Sh.a,_Sj=E(_Sh.b);if(!_Sj._){return new F(function(){return _Sf(new T2(1,_Si,_10));});}else{var _Sk=_Sj.a,_Sl=_Sj.b,_Sm=E(_Si);if(E(_Sm)==47){if(!B(_4B(_qe,_S9,_Sd))){return new F(function(){return _RD(B(_H4(47,_Sk,_Sl)).a,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}else{if(!B(_qN(_Sb,B(_6R(_Se,B(_Mk(_qe,_S9,_Sd))))))){return new F(function(){return _RD(B(_H4(47,_Sk,_Sl)).a,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}else{return new F(function(){return _RD(_10,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}}}else{if(!B(_4B(_qe,_S9,_Sd))){var _Sn=E(B(_H4(47,_Sk,_Sl)).b);if(!_Sn._){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{return new F(function(){return _RD(_Sn.a,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}}else{if(!B(_qN(_Sb,B(_6R(_Se,B(_Mk(_qe,_S9,_Sd))))))){var _So=E(B(_H4(47,_Sk,_Sl)).b);if(!_So._){return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}else{return new F(function(){return _RD(_So.a,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}}else{return new F(function(){return _RD(new T2(1,_Sm,new T(function(){return E(B(_H4(47,_Sk,_Sl)).a);})),_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX);});}}}}}}}}}else{var _Sp=E(_RW);return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E({_:0,a:E(_Sp.a),b:E(_Sp.b),c:E(_Sp.c),d:E(_Sp.d),e:E(_Sp.e),f:E(_Sp.f),g:E(_Sp.g),h:E(_ws)}),s:E(_RX)};}}else{var _Sq=E(_RW);return new F(function(){return _NX(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_10,_RS,_RT,_RU,_RV,_Sq.a,_Sq.b,_Sq.c,_Sq.d,_Sq.e,_Sq.f,_Sq.g,_Sq.h,_RX);});}},_Sr=E(_RZ);if(!_Sr._){return new F(function(){return _S5(_);});}else{if(E(_Sr.a)==109){if(!E(_Sr.b)._){var _Ss=B(_Hh(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_Ss.a),b:E(_Ss.b),c:E(_Ss.c),d:E(_Ss.d),e:E(_Ss.e),f:E(_Ss.f),g:E(_Ss.g),h:E(_Ss.h),i:_Ss.i,j:_Ss.j,k:_Ss.k,l:_Ss.l,m:E(_Ss.m),n:_Ss.n,o:E(_Ss.o),p:E(_Ss.p),q:_Ss.q,r:E(_Ss.r),s:E(_Ss.s)};}else{return new F(function(){return _S5(_);});}}else{return new F(function(){return _S5(_);});}}}else{var _St=E(_RF);return {_:0,a:E({_:0,a:E(_St.a),b:E(B(_R7(_Rt,_St.b))),c:_St.c,d:_St.d,e:_St.e,f:E(_St.f),g:_St.g,h:E(_St.h),i:E(_St.i),j:E(_St.j)}),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_RJ),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}},_Su=E(_RZ);if(!_Su._){return new F(function(){return _S3(_);});}else{var _Sv=_Su.b;switch(E(_Su.a)){case 99:if(!E(_Sv)._){var _Sw=B(_L9(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_Sw.a),b:E(_Sw.b),c:E(_Sw.c),d:E(_Sw.d),e:E(_Sw.e),f:E(_Sw.f),g:E(_Sw.g),h:E(_Sw.h),i:_Sw.i,j:_Sw.j,k:_Sw.k,l:_Sw.l,m:E(_Sw.m),n:_Sw.n,o:E(_Sw.o),p:E(_Sw.p),q:_Sw.q,r:E(_Sw.r),s:E(_Sw.s)};}else{return new F(function(){return _S3(_);});}break;case 112:if(!E(_Sv)._){var _Sx=B(_Px(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_Sx.a),b:E(_Sx.b),c:E(_Sx.c),d:E(_Sx.d),e:E(_Sx.e),f:E(_Sx.f),g:E(_Sx.g),h:E(_Sx.h),i:_Sx.i,j:_Sx.j,k:_Sx.k,l:_Sx.l,m:E(_Sx.m),n:_Sx.n,o:E(_Sx.o),p:E(_Sx.p),q:_Sx.q,r:E(_Sx.r),s:E(_Sx.s)};}else{return new F(function(){return _S3(_);});}break;default:return new F(function(){return _S3(_);});}}}else{return {_:0,a:E(_RF),b:E(_RG),c:E(_RH),d:E(_RI),e:E(_10),f:E(_RK),g:E(_RL),h:E(_RM),i:_RN,j:_RO,k:_RP,l:_RQ,m:E(_RR),n:_RS,o:E(_RT),p:E(_RU),q:_RV,r:E(_RW),s:E(_RX)};}}else{var _Sy=B(_Jq(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_Sy.a),b:E(_Sy.b),c:E(_Sy.c),d:E(_Sy.d),e:E(_Sy.e),f:E(_Sy.f),g:E(_Sy.g),h:E(_Sy.h),i:_Sy.i,j:_Sy.j,k:_Sy.k,l:_Sy.l,m:E(_Sy.m),n:_Sy.n,o:E(_Sy.o),p:E(_Sy.p),q:_Sy.q,r:E(_Sy.r),s:E(_Sy.s)};}},_Sz=E(_RZ);if(!_Sz._){return new F(function(){return _S1(_);});}else{var _SA=_Sz.b;switch(E(_Sz.a)){case 100:if(!E(_SA)._){var _SB=B(_MK(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_SB.a),b:E(_SB.b),c:E(_SB.c),d:E(_SB.d),e:E(_SB.e),f:E(_SB.f),g:E(_SB.g),h:E(_SB.h),i:_SB.i,j:_SB.j,k:_SB.k,l:_SB.l,m:E(_SB.m),n:_SB.n,o:E(_SB.o),p:E(_SB.p),q:_SB.q,r:E(_SB.r),s:E(_SB.s)};}else{return new F(function(){return _S1(_);});}break;case 101:if(!E(_SA)._){var _SC=B(_qh(_S0,_RF,_RG,_RH,_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX));return {_:0,a:E(_SC.a),b:E(_SC.b),c:E(_SC.c),d:E(_SC.d),e:E(_SC.e),f:E(_SC.f),g:E(_SC.g),h:E(_SC.h),i:_SC.i,j:_SC.j,k:_SC.k,l:_SC.l,m:E(_SC.m),n:_SC.n,o:E(_SC.o),p:E(_SC.p),q:_SC.q,r:E(_SC.r),s:E(_SC.s)};}else{return new F(function(){return _S1(_);});}break;default:return new F(function(){return _S1(_);});}}},_SD=E(_RE);if(!_SD._){return new F(function(){return _RY(_10,_10);});}else{var _SE=_SD.a,_SF=E(_SD.b);if(!_SF._){return new F(function(){return _RY(new T2(1,_SE,_10),_10);});}else{var _SG=E(_SE),_SH=new T(function(){var _SI=B(_H4(46,_SF.a,_SF.b));return new T2(0,_SI.a,_SI.b);});if(E(_SG)==46){return new F(function(){return _RY(_10,new T2(1,new T(function(){return E(E(_SH).a);}),new T(function(){return E(E(_SH).b);})));});}else{return new F(function(){return _RY(new T2(1,_SG,new T(function(){return E(E(_SH).a);})),new T(function(){return E(E(_SH).b);}));});}}}},_SJ=new T(function(){return B(unCStr("last"));}),_SK=new T(function(){return B(_ne(_SJ));}),_SL=32,_SM=0,_SN=65306,_SO=125,_SP=new T1(0,1),_SQ=function(_SR,_SS,_ST,_SU,_SV){var _SW=new T(function(){return E(_SV).i;}),_SX=new T(function(){return E(E(_SV).c);}),_SY=new T(function(){var _SZ=E(_SW)+1|0;if(0>=_SZ){return E(_SL);}else{var _T0=B(_pO(_SZ,_SX));if(!_T0._){return E(_SL);}else{return B(_oa(_T0.a,_T0.b,_SK));}}}),_T1=new T(function(){var _T2=E(_SY);switch(E(_T2)){case 125:return E(_SL);break;case 12289:return E(_SL);break;case 12290:return E(_SL);break;default:return E(_T2);}}),_T3=new T(function(){if(E(_T1)==10){return true;}else{return false;}}),_T4=new T(function(){if(!E(_T3)){if(E(_T1)==12300){return E(_j7);}else{return E(_SV).j;}}else{return E(_SM);}}),_T5=new T(function(){var _T6=E(_SS)/28,_T7=_T6&4294967295;if(_T6>=_T7){return _T7-1|0;}else{return (_T7-1|0)-1|0;}}),_T8=new T(function(){if(!E(E(_SU).h)){return E(_j8);}else{return 2+(E(E(E(_SV).b).b)+3|0)|0;}}),_T9=new T(function(){if(!E(_SW)){return new T2(0,_T5,_T8);}else{return E(E(_SV).h);}}),_Ta=new T(function(){return E(E(_T9).b);}),_Tb=new T(function(){return E(E(_T9).a);}),_Tc=new T(function(){if(E(_T1)==65306){return true;}else{return false;}}),_Td=new T(function(){if(!E(_Tc)){if(!E(_T3)){var _Te=E(_Ta);if((_Te+1)*20<=E(_ST)-10){return new T2(0,_Tb,_Te+1|0);}else{return new T2(0,new T(function(){return E(_Tb)-1|0;}),_T8);}}else{return new T2(0,new T(function(){return E(_Tb)-1|0;}),_T8);}}else{return new T2(0,_Tb,_Ta);}}),_Tf=new T(function(){if(E(E(_Td).a)==1){if(E(_Tb)==1){return false;}else{return true;}}else{return false;}}),_Tg=new T(function(){if(!E(_Tc)){return __Z;}else{return B(_q6(_SN,E(_SW),_SX));}}),_Th=new T(function(){if(E(_T1)==123){return true;}else{return false;}}),_Ti=new T(function(){if(!E(_Th)){return __Z;}else{return B(_q6(_SO,E(_SW),_SX));}}),_Tj=new T(function(){if(!E(_Th)){var _Tk=E(_SV),_Tl=E(_SU);if(E(_SY)==12290){var _Tm=true;}else{var _Tm=false;}return {_:0,a:E(_Tk.a),b:E(_Tk.b),c:E(_Tk.c),d:E(_Tk.d),e:E(_Tk.e),f:E(_Tk.f),g:E(_Tk.g),h:E(_Tk.h),i:_Tk.i,j:_Tk.j,k:_Tk.k,l:_Tk.l,m:E(_Tk.m),n:_Tk.n,o:E(_Tk.o),p:E(_Tk.p),q:_Tk.q,r:E({_:0,a:E(_Tl.a),b:E(_Tl.b),c:E(_Tl.c),d:E(_Tm),e:E(_Tl.e),f:E(_Tl.f),g:E(_Tl.g),h:E(_Tl.h)}),s:E(_Tk.s)};}else{var _Tn=E(_SV),_To=E(_SU);if(E(_SY)==12290){var _Tp=true;}else{var _Tp=false;}return B(_RD(_Ti,_Tn.a,_Tn.b,_Tn.c,_Tn.d,_Tn.e,_Tn.f,_Tn.g,_Tn.h,_Tn.i,_Tn.j,_Tn.k,_Tn.l,_Tn.m,_Tn.n,_Tn.o,_Tn.p,_Tn.q,{_:0,a:E(_To.a),b:E(_To.b),c:E(_To.c),d:E(_Tp),e:E(_To.e),f:E(_To.f),g:E(_To.g),h:E(_To.h)},_Tn.s));}}),_Tq=new T(function(){return E(E(_Tj).r);}),_Tr=new T(function(){if(!E(_SW)){return E(_SM);}else{return E(_Tj).k;}}),_Ts=new T(function(){var _Tt=E(_Tj),_Tu=_Tt.a,_Tv=_Tt.b,_Tw=_Tt.c,_Tx=_Tt.d,_Ty=_Tt.e,_Tz=_Tt.f,_TA=_Tt.g,_TB=_Tt.l,_TC=_Tt.m,_TD=_Tt.n,_TE=_Tt.o,_TF=_Tt.p,_TG=_Tt.q,_TH=_Tt.s;if(!E(_Tf)){var _TI=E(_Td);}else{var _TI=new T2(0,_Tb,_T8);}var _TJ=E(_SW),_TK=function(_TL){var _TM=B(_mt(_SX,0))-1|0,_TN=function(_TO){var _TP=E(_T4);if(!E(_Tf)){var _TQ=E(_Tq);return {_:0,a:E(_Tu),b:E(_Tv),c:E(_Tw),d:E(_Tx),e:E(_Ty),f:E(_Tz),g:E(_TA),h:E(_TI),i:_TO,j:_TP,k:E(_Tr),l:_TB,m:E(_TC),n:_TD,o:E(_TE),p:E(_TF),q:_TG,r:E({_:0,a:E(_TQ.a),b:E(_TQ.b),c:(_TJ+_TL|0)<=_TM,d:E(_TQ.d),e:E(_TQ.e),f:E(_TQ.f),g:E(_TQ.g),h:E(_TQ.h)}),s:E(_TH)};}else{var _TR=E(_Tq);return {_:0,a:E(_Tu),b:E(_Tv),c:E(_Tw),d:E(_Tx),e:E(_Ty),f:E(_Tz),g:E(_TA),h:E(_TI),i:_TO,j:_TP,k:E(_Tr)+1|0,l:_TB,m:E(_TC),n:_TD,o:E(_TE),p:E(_TF),q:_TG,r:E({_:0,a:E(_TR.a),b:E(_TR.b),c:(_TJ+_TL|0)<=_TM,d:E(_TR.d),e:E(_TR.e),f:E(_TR.f),g:E(_TR.g),h:E(_TR.h)}),s:E(_TH)};}};if((_TJ+_TL|0)<=_TM){return new F(function(){return _TN(_TJ+_TL|0);});}else{return new F(function(){return _TN(0);});}};if(!E(_Tc)){if(!E(_Th)){return B(_TK(1));}else{return B(_TK(B(_mt(_Ti,0))+2|0));}}else{return B(_TK(B(_mt(_Tg,0))+2|0));}}),_TS=new T(function(){var _TT=B(_o4(B(_o2(_SR)))),_TU=new T(function(){var _TV=B(_pv(_SR,E(_SS)/16)),_TW=_TV.a;if(E(_TV.b)>=0){return E(_TW);}else{return B(A3(_oH,_TT,_TW,new T(function(){return B(A2(_he,_TT,_SP));})));}});return B(A3(_oH,_TT,_TU,new T(function(){return B(A2(_he,_TT,_hn));})));});return {_:0,a:_T1,b:_Tb,c:_Ta,d:new T(function(){if(E(_T8)!=E(_Ta)){return E(_Tb);}else{return E(_Tb)+1|0;}}),e:new T(function(){var _TX=E(_Ta);if(E(_T8)!=_TX){return _TX-1|0;}else{var _TY=(E(_ST)-10)/20,_TZ=_TY&4294967295;if(_TY>=_TZ){return _TZ;}else{return _TZ-1|0;}}}),f:_T8,g:_SW,h:_SX,i:new T(function(){return B(_6R(_j4,E(_T4)));}),j:_Tg,k:_T5,l:_TS,m:_Tr,n:_j9,o:_Tc,p:_Th,q:_Tf,r:_Tq,s:_Tj,t:_Ts};},_U0=function(_U1){var _U2=E(_U1);if(!_U2._){return new T2(0,_10,_10);}else{var _U3=E(_U2.a),_U4=new T(function(){var _U5=B(_U0(_U2.b));return new T2(0,_U5.a,_U5.b);});return new T2(0,new T2(1,_U3.a,new T(function(){return E(E(_U4).a);})),new T2(1,_U3.b,new T(function(){return E(E(_U4).b);})));}},_U6=42,_U7=32,_U8=function(_U9,_Ua,_Ub){var _Uc=E(_U9);if(!_Uc._){return __Z;}else{var _Ud=_Uc.a,_Ue=_Uc.b;if(_Ua!=_Ub){var _Uf=E(_Ud);return (_Uf._==0)?E(_nh):(E(_Uf.a)==42)?new T2(1,new T2(1,_U7,_Uf.b),new T(function(){return B(_U8(_Ue,_Ua,_Ub+1|0));})):new T2(1,new T2(1,_U7,_Uf),new T(function(){return B(_U8(_Ue,_Ua,_Ub+1|0));}));}else{var _Ug=E(_Ud);return (_Ug._==0)?E(_nh):(E(_Ug.a)==42)?new T2(1,new T2(1,_U7,_Ug),new T(function(){return B(_U8(_Ue,_Ua,_Ub+1|0));})):new T2(1,new T2(1,_U6,_Ug),new T(function(){return B(_U8(_Ue,_Ua,_Ub+1|0));}));}}},_Uh=new T(function(){return B(unCStr("\n\n"));}),_Ui=function(_Uj){var _Uk=E(_Uj);if(!_Uk._){return __Z;}else{var _Ul=new T(function(){return B(_y(_Uh,new T(function(){return B(_Ui(_Uk.b));},1)));},1);return new F(function(){return _y(_Uk.a,_Ul);});}},_Um=function(_Un,_Uo,_Up){var _Uq=new T(function(){var _Ur=new T(function(){var _Us=E(_Uo);if(!_Us._){return B(_Ui(_10));}else{var _Ut=_Us.a,_Uu=_Us.b,_Uv=E(_Up);if(!_Uv){var _Uw=E(_Ut);if(!_Uw._){return E(_nh);}else{if(E(_Uw.a)==42){return B(_Ui(new T2(1,new T2(1,_U7,_Uw),new T(function(){return B(_U8(_Uu,0,1));}))));}else{return B(_Ui(new T2(1,new T2(1,_U6,_Uw),new T(function(){return B(_U8(_Uu,0,1));}))));}}}else{var _Ux=E(_Ut);if(!_Ux._){return E(_nh);}else{if(E(_Ux.a)==42){return B(_Ui(new T2(1,new T2(1,_U7,_Ux.b),new T(function(){return B(_U8(_Uu,_Uv,1));}))));}else{return B(_Ui(new T2(1,new T2(1,_U7,_Ux),new T(function(){return B(_U8(_Uu,_Uv,1));}))));}}}}});return B(unAppCStr("\n\n",_Ur));},1);return new F(function(){return _y(_Un,_Uq);});},_Uy=function(_Uz){return E(E(_Uz).c);},_UA=function(_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ){var _UK=new T(function(){if(!E(_UC)){return E(_UD);}else{return false;}}),_UL=new T(function(){if(!E(_UC)){return false;}else{return E(E(_UI).g);}}),_UM=new T(function(){if(!E(_UL)){if(!E(_UK)){return B(A2(_he,_UB,_hm));}else{return B(A3(_my,_UB,new T(function(){return B(A3(_my,_UB,_UG,_UH));}),new T(function(){return B(A2(_he,_UB,_SP));})));}}else{return B(A3(_my,_UB,_UG,_UH));}}),_UN=new T(function(){if(!E(_UL)){if(!E(_UK)){return __Z;}else{var _UO=E(_UE)+1|0;if(0>=_UO){return __Z;}else{return B(_pO(_UO,_UF));}}}else{return B(_Um(B(_Uy(_UJ)),new T(function(){return E(B(_U0(E(_UJ).m)).a);},1),new T(function(){return E(_UJ).n;},1)));}});return new T4(0,_UL,_UK,_UN,_UM);},_UP=function(_UQ,_UR,_US){var _UT=E(_UR),_UU=E(_US),_UV=new T(function(){var _UW=B(_ha(_UQ)),_UX=B(_UP(_UQ,_UU,B(A3(_oH,_UW,new T(function(){return B(A3(_my,_UW,_UU,_UU));}),_UT))));return new T2(1,_UX.a,_UX.b);});return new T2(0,_UT,_UV);},_UY=1,_UZ=new T(function(){var _V0=B(_UP(_gb,_hM,_UY));return new T2(1,_V0.a,_V0.b);}),_V1=function(_V2,_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw,_Vx,_Vy,_Vz,_VA,_VB,_VC,_VD,_VE,_VF,_){var _VG={_:0,a:E(_Vx),b:E(_Vy),c:E(_Vz),d:E(_VA),e:E(_VB),f:E(_VC),g:E(_VD),h:E(_VE)};if(!E(_Vz)){return {_:0,a:E({_:0,a:E(_V5),b:E(_V6),c:_V7,d:_V8,e:_V9,f:E(_Va),g:_Vb,h:E(_Vc),i:E(_Vd),j:E(_Ve)}),b:E(new T2(0,_Vf,_Vg)),c:E(_Vh),d:E(_Vi),e:E(_Vj),f:E(_Vk),g:E(_Vl),h:E(new T2(0,_Vm,_Vn)),i:_Vo,j:_Vp,k:_Vq,l:_Vr,m:E(_Vs),n:_Vt,o:E(_Vu),p:E(_Vv),q:_Vw,r:E(_VG),s:E(_VF)};}else{if(!E(_VA)){var _VH=B(_SQ(_bS,_V3,_V4,_VG,{_:0,a:E({_:0,a:E(_V5),b:E(_V6),c:_V7,d:_V8,e:_V9,f:E(_Va),g:_Vb,h:E(_Vc),i:E(_Vd),j:E(_Ve)}),b:E(new T2(0,_Vf,_Vg)),c:E(_Vh),d:E(_Vi),e:E(_Vj),f:E(_Vk),g:E(_Vl),h:E(new T2(0,_Vm,_Vn)),i:_Vo,j:_Vp,k:_Vq,l:_Vr,m:E(_Vs),n:_Vt,o:E(_Vu),p:E(_Vv),q:_Vw,r:E(_VG),s:E(_VF)})),_VI=_VH.d,_VJ=_VH.e,_VK=_VH.f,_VL=_VH.i,_VM=_VH.n,_VN=_VH.p,_VO=_VH.q,_VP=_VH.s,_VQ=_VH.t;if(!E(_VH.o)){var _VR=B(_UA(_bn,_VN,_VO,_VH.g,_VH.h,_VH.k,_VH.m,_VH.r,_VP)),_VS=function(_){if(!E(_VN)){if(!E(_VO)){var _VT=B(_iB(E(_V2).a,_VL,_j5,_hM,_VH.b,_VH.c,_VH.a,_));return _VQ;}else{return _VQ;}}else{return _VQ;}},_VU=function(_VV){var _VW=E(_V2),_VX=_VW.a,_VY=_VW.b,_VZ=B(_nQ(_VX,_VY,_VH.l,_VP,_)),_W0=B(_lo(_VX,_VY,_V4,0,_VK,_VR.d,_VK,_VR.c,_));return new F(function(){return _VS(_);});};if(!E(_VR.a)){if(!E(_VR.b)){return new F(function(){return _VS(_);});}else{return new F(function(){return _VU(_);});}}else{return new F(function(){return _VU(_);});}}else{var _W1=E(_VH.j);if(!_W1._){return _VQ;}else{var _W2=E(_UZ);if(!_W2._){return _VQ;}else{var _W3=E(_V2).a,_W4=B(_iB(_W3,_VL,_VM,_W2.a,_VI,_VJ,_W1.a,_)),_W5=function(_W6,_W7,_){while(1){var _W8=E(_W6);if(!_W8._){return _gE;}else{var _W9=E(_W7);if(!_W9._){return _gE;}else{var _Wa=B(_iB(_W3,_VL,_VM,_W9.a,_VI,_VJ,_W8.a,_));_W6=_W8.b;_W7=_W9.b;continue;}}}},_Wb=B(_W5(_W1.b,_W2.b,_));return _VQ;}}}}else{return {_:0,a:E({_:0,a:E(_V5),b:E(_V6),c:_V7,d:_V8,e:_V9,f:E(_Va),g:_Vb,h:E(_Vc),i:E(_Vd),j:E(_Ve)}),b:E(new T2(0,_Vf,_Vg)),c:E(_Vh),d:E(_Vi),e:E(_Vj),f:E(_Vk),g:E(_Vl),h:E(new T2(0,_Vm,_Vn)),i:_Vo,j:_Vp,k:_Vq,l:_Vr,m:E(_Vs),n:_Vt,o:E(_Vu),p:E(_Vv),q:_Vw,r:E(_VG),s:E(_VF)};}}},_Wc=function(_Wd,_We,_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_){while(1){var _WR=B(_V1(_Wd,_We,_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_)),_WS=E(_WR),_WT=_WS.c,_WU=_WS.d,_WV=_WS.e,_WW=_WS.f,_WX=_WS.g,_WY=_WS.i,_WZ=_WS.j,_X0=_WS.k,_X1=_WS.l,_X2=_WS.m,_X3=_WS.n,_X4=_WS.o,_X5=_WS.p,_X6=_WS.q,_X7=_WS.s,_X8=E(_WS.r),_X9=_X8.a,_Xa=_X8.b,_Xb=_X8.c,_Xc=_X8.e,_Xd=_X8.g,_Xe=_X8.h,_Xf=E(_WS.a),_Xg=E(_WS.b),_Xh=E(_WS.h);if(!E(_X8.d)){if(!E(_WK)){return {_:0,a:E(_Xf),b:E(_Xg),c:E(_WT),d:E(_WU),e:E(_WV),f:E(_WW),g:E(_WX),h:E(_Xh),i:_WY,j:_WZ,k:_X0,l:_X1,m:E(_X2),n:_X3,o:E(_X4),p:E(_X5),q:_X6,r:E({_:0,a:E(_X9),b:E(_Xa),c:E(_Xb),d:E(_ws),e:E(_Xc),f:E(_ws),g:E(_Xd),h:E(_Xe)}),s:E(_X7)};}else{_Wg=_Xf.a;_Wh=_Xf.b;_Wi=_Xf.c;_Wj=_Xf.d;_Wk=_Xf.e;_Wl=_Xf.f;_Wm=_Xf.g;_Wn=_Xf.h;_Wo=_Xf.i;_Wp=_Xf.j;_Wq=_Xg.a;_Wr=_Xg.b;_Ws=_WT;_Wt=_WU;_Wu=_WV;_Wv=_WW;_Ww=_WX;_Wx=_Xh.a;_Wy=_Xh.b;_Wz=_WY;_WA=_WZ;_WB=_X0;_WC=_X1;_WD=_X2;_WE=_X3;_WF=_X4;_WG=_X5;_WH=_X6;_WI=_X9;_WJ=_Xa;_WK=_Xb;_WL=_ws;_WM=_Xc;_WN=_X8.f;_WO=_Xd;_WP=_Xe;_WQ=_X7;continue;}}else{return {_:0,a:E(_Xf),b:E(_Xg),c:E(_WT),d:E(_WU),e:E(_WV),f:E(_WW),g:E(_WX),h:E(_Xh),i:_WY,j:_WZ,k:_X0,l:_X1,m:E(_X2),n:_X3,o:E(_X4),p:E(_X5),q:_X6,r:E({_:0,a:E(_X9),b:E(_Xa),c:E(_Xb),d:E(_wt),e:E(_Xc),f:E(_ws),g:E(_Xd),h:E(_Xe)}),s:E(_X7)};}}},_Xi=function(_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_XC,_XD,_XE,_XF,_XG,_XH,_XI,_XJ,_XK,_XL,_XM,_XN,_XO,_XP,_XQ,_XR,_XS,_XT,_XU,_XV,_){var _XW=B(_V1(_Xj,_Xk,_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs,_Xt,_Xu,_Xv,_Xw,_Xx,_Xy,_Xz,_XA,_XB,_XC,_XD,_XE,_XF,_XG,_XH,_XI,_XJ,_XK,_XL,_XM,_XN,_XO,_XP,_wt,_XQ,_XR,_XS,_XT,_XU,_XV,_)),_XX=E(_XW),_XY=_XX.c,_XZ=_XX.d,_Y0=_XX.e,_Y1=_XX.f,_Y2=_XX.g,_Y3=_XX.i,_Y4=_XX.j,_Y5=_XX.k,_Y6=_XX.l,_Y7=_XX.m,_Y8=_XX.n,_Y9=_XX.o,_Ya=_XX.p,_Yb=_XX.q,_Yc=_XX.s,_Yd=E(_XX.r),_Ye=_Yd.a,_Yf=_Yd.b,_Yg=_Yd.c,_Yh=_Yd.e,_Yi=_Yd.g,_Yj=_Yd.h,_Yk=E(_XX.a),_Yl=E(_XX.b),_Ym=E(_XX.h);if(!E(_Yd.d)){return new F(function(){return _Wc(_Xj,_Xk,_Xl,_Yk.a,_Yk.b,_Yk.c,_Yk.d,_Yk.e,_Yk.f,_Yk.g,_Yk.h,_Yk.i,_Yk.j,_Yl.a,_Yl.b,_XY,_XZ,_Y0,_Y1,_Y2,_Ym.a,_Ym.b,_Y3,_Y4,_Y5,_Y6,_Y7,_Y8,_Y9,_Ya,_Yb,_Ye,_Yf,_Yg,_ws,_Yh,_Yd.f,_Yi,_Yj,_Yc,_);});}else{return {_:0,a:E(_Yk),b:E(_Yl),c:E(_XY),d:E(_XZ),e:E(_Y0),f:E(_Y1),g:E(_Y2),h:E(_Ym),i:_Y3,j:_Y4,k:_Y5,l:_Y6,m:E(_Y7),n:_Y8,o:E(_Y9),p:E(_Ya),q:_Yb,r:E({_:0,a:E(_Ye),b:E(_Yf),c:E(_Yg),d:E(_wt),e:E(_Yh),f:E(_ws),g:E(_Yi),h:E(_Yj)}),s:E(_Yc)};}},_Yn=function(_Yo){var _Yp=E(_Yo);if(!_Yp._){return __Z;}else{var _Yq=E(_Yp.b);return (_Yq._==0)?__Z:new T2(1,new T2(0,_Yp.a,_Yq.a),new T(function(){return B(_Yn(_Yq.b));}));}},_Yr=function(_Ys,_Yt,_Yu){return new T2(1,new T2(0,_Ys,_Yt),new T(function(){return B(_Yn(_Yu));}));},_Yv=function(_Yw,_Yx){var _Yy=E(_Yx);return (_Yy._==0)?__Z:new T2(1,new T2(0,_Yw,_Yy.a),new T(function(){return B(_Yn(_Yy.b));}));},_Yz=new T(function(){return B(err(_sq));}),_YA=new T(function(){return B(err(_ss));}),_YB=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_YC=function(_YD){var _YE=B(_Gc(B(_sx(_YB,_YD))));return (_YE._==0)?E(_Yz):(E(_YE.b)._==0)?E(_YE.a):E(_YA);},_YF="Invalid JSON!",_YG=new T1(0,_YF),_YH="No such value",_YI=new T1(0,_YH),_YJ=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_YK=function(_YL){return E(E(_YL).c);},_YM=function(_YN,_YO,_){var _YP=__app1(E(_YJ),_YO),_YQ=__eq(_YP,E(_7));if(!E(_YQ)){var _YR=__isUndef(_YP);return (E(_YR)==0)?new T(function(){var _YS=String(_YP),_YT=jsParseJSON(_YS);if(!_YT._){return E(_YG);}else{return B(A2(_YK,_YN,_YT.a));}}):_YI;}else{return _YI;}},_YU=new T1(0,0),_YV=function(_YW,_YX){while(1){var _YY=E(_YW);if(!_YY._){var _YZ=_YY.a,_Z0=E(_YX);if(!_Z0._){return new T1(0,(_YZ>>>0|_Z0.a>>>0)>>>0&4294967295);}else{_YW=new T1(1,I_fromInt(_YZ));_YX=_Z0;continue;}}else{var _Z1=E(_YX);if(!_Z1._){_YW=_YY;_YX=new T1(1,I_fromInt(_Z1.a));continue;}else{return new T1(1,I_or(_YY.a,_Z1.a));}}}},_Z2=function(_Z3){var _Z4=E(_Z3);if(!_Z4._){return E(_YU);}else{return new F(function(){return _YV(new T1(0,E(_Z4.a)),B(_cO(B(_Z2(_Z4.b)),31)));});}},_Z5=function(_Z6,_Z7){if(!E(_Z6)){return new F(function(){return _ft(B(_Z2(_Z7)));});}else{return new F(function(){return _Z2(_Z7);});}},_Z8=1420103680,_Z9=465,_Za=new T2(1,_Z9,_10),_Zb=new T2(1,_Z8,_Za),_Zc=new T(function(){return B(_Z5(_wt,_Zb));}),_Zd=function(_Ze){return E(_Zc);},_Zf=new T(function(){return B(unCStr("s"));}),_Zg=function(_Zh,_Zi){while(1){var _Zj=E(_Zh);if(!_Zj._){return E(_Zi);}else{_Zh=_Zj.b;_Zi=_Zj.a;continue;}}},_Zk=function(_Zl,_Zm,_Zn){return new F(function(){return _Zg(_Zm,_Zl);});},_Zo=new T1(0,1),_Zp=function(_Zq,_Zr){var _Zs=E(_Zq);return new T2(0,_Zs,new T(function(){var _Zt=B(_Zp(B(_cv(_Zs,_Zr)),_Zr));return new T2(1,_Zt.a,_Zt.b);}));},_Zu=function(_Zv){var _Zw=B(_Zp(_Zv,_Zo));return new T2(1,_Zw.a,_Zw.b);},_Zx=function(_Zy,_Zz){var _ZA=B(_Zp(_Zy,new T(function(){return B(_eO(_Zz,_Zy));})));return new T2(1,_ZA.a,_ZA.b);},_ZB=new T1(0,0),_ZC=function(_ZD,_ZE){var _ZF=E(_ZD);if(!_ZF._){var _ZG=_ZF.a,_ZH=E(_ZE);return (_ZH._==0)?_ZG>=_ZH.a:I_compareInt(_ZH.a,_ZG)<=0;}else{var _ZI=_ZF.a,_ZJ=E(_ZE);return (_ZJ._==0)?I_compareInt(_ZI,_ZJ.a)>=0:I_compare(_ZI,_ZJ.a)>=0;}},_ZK=function(_ZL,_ZM,_ZN){if(!B(_ZC(_ZM,_ZB))){var _ZO=function(_ZP){return (!B(_d7(_ZP,_ZN)))?new T2(1,_ZP,new T(function(){return B(_ZO(B(_cv(_ZP,_ZM))));})):__Z;};return new F(function(){return _ZO(_ZL);});}else{var _ZQ=function(_ZR){return (!B(_cY(_ZR,_ZN)))?new T2(1,_ZR,new T(function(){return B(_ZQ(B(_cv(_ZR,_ZM))));})):__Z;};return new F(function(){return _ZQ(_ZL);});}},_ZS=function(_ZT,_ZU,_ZV){return new F(function(){return _ZK(_ZT,B(_eO(_ZU,_ZT)),_ZV);});},_ZW=function(_ZX,_ZY){return new F(function(){return _ZK(_ZX,_Zo,_ZY);});},_ZZ=function(_100){return new F(function(){return _ba(_100);});},_101=function(_102){return new F(function(){return _eO(_102,_Zo);});},_103=function(_104){return new F(function(){return _cv(_104,_Zo);});},_105=function(_106){return new F(function(){return _aR(E(_106));});},_107={_:0,a:_103,b:_101,c:_105,d:_ZZ,e:_Zu,f:_Zx,g:_ZW,h:_ZS},_108=function(_109,_10a){while(1){var _10b=E(_109);if(!_10b._){var _10c=E(_10b.a);if(_10c==( -2147483648)){_109=new T1(1,I_fromInt( -2147483648));continue;}else{var _10d=E(_10a);if(!_10d._){return new T1(0,B(_9j(_10c,_10d.a)));}else{_109=new T1(1,I_fromInt(_10c));_10a=_10d;continue;}}}else{var _10e=_10b.a,_10f=E(_10a);return (_10f._==0)?new T1(1,I_div(_10e,I_fromInt(_10f.a))):new T1(1,I_div(_10e,_10f.a));}}},_10g=function(_10h,_10i){if(!B(_cn(_10i,_oL))){return new F(function(){return _108(_10h,_10i);});}else{return E(_9U);}},_10j=function(_10k,_10l){while(1){var _10m=E(_10k);if(!_10m._){var _10n=E(_10m.a);if(_10n==( -2147483648)){_10k=new T1(1,I_fromInt( -2147483648));continue;}else{var _10o=E(_10l);if(!_10o._){var _10p=_10o.a;return new T2(0,new T1(0,B(_9j(_10n,_10p))),new T1(0,B(_ao(_10n,_10p))));}else{_10k=new T1(1,I_fromInt(_10n));_10l=_10o;continue;}}}else{var _10q=E(_10l);if(!_10q._){_10k=_10m;_10l=new T1(1,I_fromInt(_10q.a));continue;}else{var _10r=I_divMod(_10m.a,_10q.a);return new T2(0,new T1(1,_10r.a),new T1(1,_10r.b));}}}},_10s=function(_10t,_10u){if(!B(_cn(_10u,_oL))){var _10v=B(_10j(_10t,_10u));return new T2(0,_10v.a,_10v.b);}else{return E(_9U);}},_10w=function(_10x,_10y){while(1){var _10z=E(_10x);if(!_10z._){var _10A=E(_10z.a);if(_10A==( -2147483648)){_10x=new T1(1,I_fromInt( -2147483648));continue;}else{var _10B=E(_10y);if(!_10B._){return new T1(0,B(_ao(_10A,_10B.a)));}else{_10x=new T1(1,I_fromInt(_10A));_10y=_10B;continue;}}}else{var _10C=_10z.a,_10D=E(_10y);return (_10D._==0)?new T1(1,I_mod(_10C,I_fromInt(_10D.a))):new T1(1,I_mod(_10C,_10D.a));}}},_10E=function(_10F,_10G){if(!B(_cn(_10G,_oL))){return new F(function(){return _10w(_10F,_10G);});}else{return E(_9U);}},_10H=function(_10I,_10J){while(1){var _10K=E(_10I);if(!_10K._){var _10L=E(_10K.a);if(_10L==( -2147483648)){_10I=new T1(1,I_fromInt( -2147483648));continue;}else{var _10M=E(_10J);if(!_10M._){return new T1(0,quot(_10L,_10M.a));}else{_10I=new T1(1,I_fromInt(_10L));_10J=_10M;continue;}}}else{var _10N=_10K.a,_10O=E(_10J);return (_10O._==0)?new T1(0,I_toInt(I_quot(_10N,I_fromInt(_10O.a)))):new T1(1,I_quot(_10N,_10O.a));}}},_10P=function(_10Q,_10R){if(!B(_cn(_10R,_oL))){return new F(function(){return _10H(_10Q,_10R);});}else{return E(_9U);}},_10S=function(_10T,_10U){if(!B(_cn(_10U,_oL))){var _10V=B(_cE(_10T,_10U));return new T2(0,_10V.a,_10V.b);}else{return E(_9U);}},_10W=function(_10X,_10Y){while(1){var _10Z=E(_10X);if(!_10Z._){var _110=E(_10Z.a);if(_110==( -2147483648)){_10X=new T1(1,I_fromInt( -2147483648));continue;}else{var _111=E(_10Y);if(!_111._){return new T1(0,_110%_111.a);}else{_10X=new T1(1,I_fromInt(_110));_10Y=_111;continue;}}}else{var _112=_10Z.a,_113=E(_10Y);return (_113._==0)?new T1(1,I_rem(_112,I_fromInt(_113.a))):new T1(1,I_rem(_112,_113.a));}}},_114=function(_115,_116){if(!B(_cn(_116,_oL))){return new F(function(){return _10W(_115,_116);});}else{return E(_9U);}},_117=function(_118){return E(_118);},_119=function(_11a){return E(_11a);},_11b=function(_11c){var _11d=E(_11c);if(!_11d._){var _11e=E(_11d.a);return (_11e==( -2147483648))?E(_fs):(_11e<0)?new T1(0, -_11e):E(_11d);}else{var _11f=_11d.a;return (I_compareInt(_11f,0)>=0)?E(_11d):new T1(1,I_negate(_11f));}},_11g=new T1(0, -1),_11h=function(_11i){var _11j=E(_11i);if(!_11j._){var _11k=_11j.a;return (_11k>=0)?(E(_11k)==0)?E(_YU):E(_d6):E(_11g);}else{var _11l=I_compareInt(_11j.a,0);return (_11l<=0)?(E(_11l)==0)?E(_YU):E(_11g):E(_d6);}},_11m={_:0,a:_cv,b:_eO,c:_of,d:_ft,e:_11b,f:_11h,g:_119},_11n=function(_11o,_11p){var _11q=E(_11o);if(!_11q._){var _11r=_11q.a,_11s=E(_11p);return (_11s._==0)?_11r!=_11s.a:(I_compareInt(_11s.a,_11r)==0)?false:true;}else{var _11t=_11q.a,_11u=E(_11p);return (_11u._==0)?(I_compareInt(_11t,_11u.a)==0)?false:true:(I_compare(_11t,_11u.a)==0)?false:true;}},_11v=new T2(0,_cn,_11n),_11w=function(_11x,_11y){return (!B(_ez(_11x,_11y)))?E(_11x):E(_11y);},_11z=function(_11A,_11B){return (!B(_ez(_11A,_11B)))?E(_11B):E(_11A);},_11C={_:0,a:_11v,b:_c7,c:_d7,d:_ez,e:_cY,f:_ZC,g:_11w,h:_11z},_11D=function(_11E){return new T2(0,E(_11E),E(_aV));},_11F=new T3(0,_11m,_11C,_11D),_11G={_:0,a:_11F,b:_107,c:_10P,d:_114,e:_10g,f:_10E,g:_10S,h:_10s,i:_117},_11H=new T1(0,0),_11I=function(_11J,_11K,_11L){var _11M=B(A1(_11J,_11K));if(!B(_cn(_11M,_11H))){return new F(function(){return _108(B(_of(_11K,_11L)),_11M);});}else{return E(_9U);}},_11N=function(_11O,_11P){while(1){if(!B(_cn(_11P,_oL))){var _11Q=_11P,_11R=B(_114(_11O,_11P));_11O=_11Q;_11P=_11R;continue;}else{return E(_11O);}}},_11S=5,_11T=new T(function(){return B(_9Q(_11S));}),_11U=new T(function(){return die(_11T);}),_11V=function(_11W,_11X){if(!B(_cn(_11X,_oL))){var _11Y=B(_11N(B(_11b(_11W)),B(_11b(_11X))));return (!B(_cn(_11Y,_oL)))?new T2(0,B(_10H(_11W,_11Y)),B(_10H(_11X,_11Y))):E(_9U);}else{return E(_11U);}},_11Z=function(_120,_121,_122,_123){var _124=B(_of(_121,_122));return new F(function(){return _11V(B(_of(B(_of(_120,_123)),B(_11h(_124)))),B(_11b(_124)));});},_125=function(_126,_127,_128){var _129=new T(function(){if(!B(_cn(_128,_oL))){var _12a=B(_cE(_127,_128));return new T2(0,_12a.a,_12a.b);}else{return E(_9U);}}),_12b=new T(function(){return B(A2(_he,B(_o4(B(_o2(_126)))),new T(function(){return E(E(_129).a);})));});return new T2(0,_12b,new T(function(){return new T2(0,E(E(_129).b),E(_128));}));},_12c=function(_12d,_12e,_12f){var _12g=B(_125(_12d,_12e,_12f)),_12h=_12g.a,_12i=E(_12g.b);if(!B(_d7(B(_of(_12i.a,_aV)),B(_of(_oL,_12i.b))))){return E(_12h);}else{var _12j=B(_o4(B(_o2(_12d))));return new F(function(){return A3(_oH,_12j,_12h,new T(function(){return B(A2(_he,_12j,_aV));}));});}},_12k=479723520,_12l=40233135,_12m=new T2(1,_12l,_10),_12n=new T2(1,_12k,_12m),_12o=new T(function(){return B(_Z5(_wt,_12n));}),_12p=new T1(0,40587),_12q=function(_12r){var _12s=new T(function(){var _12t=B(_11Z(_12r,_aV,_Zc,_aV)),_12u=B(_11Z(_12o,_aV,_Zc,_aV)),_12v=B(_11Z(_12t.a,_12t.b,_12u.a,_12u.b));return B(_12c(_11G,_12v.a,_12v.b));});return new T2(0,new T(function(){return B(_cv(_12p,_12s));}),new T(function(){return B(_eO(_12r,B(_11I(_Zd,B(_of(_12s,_Zc)),_12o))));}));},_12w=function(_12x,_){var _12y=__get(_12x,0),_12z=__get(_12x,1),_12A=Number(_12y),_12B=jsTrunc(_12A),_12C=Number(_12z),_12D=jsTrunc(_12C);return new T2(0,_12B,_12D);},_12E=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_12F=660865024,_12G=465661287,_12H=new T2(1,_12G,_10),_12I=new T2(1,_12F,_12H),_12J=new T(function(){return B(_Z5(_wt,_12I));}),_12K=function(_){var _12L=__app0(E(_12E)),_12M=B(_12w(_12L,_));return new T(function(){var _12N=E(_12M);if(!B(_cn(_12J,_11H))){return B(_cv(B(_of(B(_aR(E(_12N.a))),_Zc)),B(_108(B(_of(B(_of(B(_aR(E(_12N.b))),_Zc)),_Zc)),_12J))));}else{return E(_9U);}});},_12O=new T(function(){return B(err(_ss));}),_12P=new T(function(){return B(err(_sq));}),_12Q=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_12R=new T1(0,1),_12S=new T1(0,10),_12T=function(_12U){while(1){var _12V=E(_12U);if(!_12V._){_12U=new T1(1,I_fromInt(_12V.a));continue;}else{return new F(function(){return I_toString(_12V.a);});}}},_12W=function(_12X,_12Y){return new F(function(){return _y(fromJSStr(B(_12T(_12X))),_12Y);});},_12Z=new T1(0,0),_130=function(_131,_132,_133){if(_131<=6){return new F(function(){return _12W(_132,_133);});}else{if(!B(_d7(_132,_12Z))){return new F(function(){return _12W(_132,_133);});}else{return new T2(1,_H,new T(function(){return B(_y(fromJSStr(B(_12T(_132))),new T2(1,_G,_133)));}));}}},_134=function(_135){return new F(function(){return _130(0,_135,_10);});},_136=new T(function(){return B(_cn(_12S,_11H));}),_137=function(_138){while(1){if(!B(_cn(_138,_11H))){if(!E(_136)){if(!B(_cn(B(_10w(_138,_12S)),_11H))){return new F(function(){return _134(_138);});}else{var _139=B(_108(_138,_12S));_138=_139;continue;}}else{return E(_9U);}}else{return __Z;}}},_13a=46,_13b=48,_13c=function(_13d,_13e,_13f){if(!B(_d7(_13f,_11H))){var _13g=B(A1(_13d,_13f));if(!B(_cn(_13g,_11H))){var _13h=B(_10j(_13f,_13g)),_13i=_13h.b,_13j=new T(function(){var _13k=Math.log(B(_fM(_13g)))/Math.log(10),_13l=_13k&4294967295,_13m=function(_13n){if(_13n>=0){var _13o=E(_13n);if(!_13o){var _13p=B(_108(B(_eO(B(_cv(B(_of(_13i,_aV)),_13g)),_12R)),_13g));}else{var _13p=B(_108(B(_eO(B(_cv(B(_of(_13i,B(_ov(_12S,_13o)))),_13g)),_12R)),_13g));}var _13q=function(_13r){var _13s=B(_130(0,_13p,_10)),_13t=_13n-B(_mt(_13s,0))|0;if(0>=_13t){if(!E(_13e)){return E(_13s);}else{return new F(function(){return _137(_13p);});}}else{var _13u=new T(function(){if(!E(_13e)){return E(_13s);}else{return B(_137(_13p));}}),_13v=function(_13w){var _13x=E(_13w);return (_13x==1)?E(new T2(1,_13b,_13u)):new T2(1,_13b,new T(function(){return B(_13v(_13x-1|0));}));};return new F(function(){return _13v(_13t);});}};if(!E(_13e)){var _13y=B(_13q(_));return (_13y._==0)?__Z:new T2(1,_13a,_13y);}else{if(!B(_cn(_13p,_11H))){var _13z=B(_13q(_));return (_13z._==0)?__Z:new T2(1,_13a,_13z);}else{return __Z;}}}else{return E(_pr);}};if(_13l>=_13k){return B(_13m(_13l));}else{return B(_13m(_13l+1|0));}},1);return new F(function(){return _y(B(_130(0,_13h.a,_10)),_13j);});}else{return E(_9U);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_13c(_13d,_13e,B(_ft(_13f))));}));});}},_13A=function(_13B,_13C,_){var _13D=B(_12K(_)),_13E=new T(function(){var _13F=new T(function(){var _13G=new T(function(){var _13H=B(_y(B(_13c(_Zd,_wt,B(_12q(_13D)).b)),_Zf));if(!_13H._){return E(_Rk);}else{var _13I=B(_Rf(_13H.a,_13H.b));if(!_13I._){return B(_Zk(_10,_10,_SK));}else{var _13J=_13I.a,_13K=E(_13I.b);if(!_13K._){return B(_Zk(new T2(1,_13J,_10),_10,_SK));}else{var _13L=E(_13J),_13M=new T(function(){var _13N=B(_H4(46,_13K.a,_13K.b));return new T2(0,_13N.a,_13N.b);});if(E(_13L)==46){return B(_Zk(_10,new T2(1,new T(function(){return E(E(_13M).a);}),new T(function(){return E(E(_13M).b);})),_SK));}else{return B(_Zk(new T2(1,_13L,new T(function(){return E(E(_13M).a);})),new T(function(){return E(E(_13M).b);}),_SK));}}}}}),_13O=B(_Gc(B(_sx(_12Q,_13G))));if(!_13O._){return E(_12P);}else{if(!E(_13O.b)._){return B(_pO(3,B(_I(0,E(_13O.a)+(imul(E(_13C),E(_13B)-1|0)|0)|0,_10))));}else{return E(_12O);}}}),_13P=B(_Gc(B(_sx(_12Q,_13F))));if(!_13P._){return E(_12P);}else{if(!E(_13P.b)._){return E(_13P.a);}else{return E(_12O);}}});return new T2(0,new T(function(){return B(_av(_13E,_13B));}),_13E);},_13Q=function(_13R,_13S){while(1){var _13T=E(_13S);if(!_13T._){return __Z;}else{var _13U=_13T.b,_13V=E(_13R);if(_13V==1){return E(_13U);}else{_13R=_13V-1|0;_13S=_13U;continue;}}}},_13W=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_13X=new T(function(){return B(err(_13W));}),_13Y=0,_13Z=function(_140,_141,_142){return new F(function(){return _I(E(_140),E(_141),_142);});},_143=function(_144,_145){return new F(function(){return _I(0,E(_144),_145);});},_146=function(_147,_148){return new F(function(){return _2D(_143,_147,_148);});},_149=new T3(0,_13Z,_6B,_146),_14a=0,_14b=new T(function(){return B(unCStr(" out of range "));}),_14c=new T(function(){return B(unCStr("}.index: Index "));}),_14d=new T(function(){return B(unCStr("Ix{"));}),_14e=new T2(1,_G,_10),_14f=new T2(1,_G,_14e),_14g=0,_14h=function(_14i){return E(E(_14i).a);},_14j=function(_14k,_14l,_14m,_14n,_14o){var _14p=new T(function(){var _14q=new T(function(){var _14r=new T(function(){var _14s=new T(function(){var _14t=new T(function(){return B(A3(_sc,_6x,new T2(1,new T(function(){return B(A3(_14h,_14m,_14g,_14n));}),new T2(1,new T(function(){return B(A3(_14h,_14m,_14g,_14o));}),_10)),_14f));});return B(_y(_14b,new T2(1,_H,new T2(1,_H,_14t))));});return B(A(_14h,[_14m,_14a,_14l,new T2(1,_G,_14s)]));});return B(_y(_14c,new T2(1,_H,_14r)));},1);return B(_y(_14k,_14q));},1);return new F(function(){return err(B(_y(_14d,_14p)));});},_14u=function(_14v,_14w,_14x,_14y,_14z){return new F(function(){return _14j(_14v,_14w,_14z,_14x,_14y);});},_14A=function(_14B,_14C,_14D,_14E){var _14F=E(_14D);return new F(function(){return _14u(_14B,_14C,_14F.a,_14F.b,_14E);});},_14G=function(_14H,_14I,_14J,_14K){return new F(function(){return _14A(_14K,_14J,_14I,_14H);});},_14L=new T(function(){return B(unCStr("Int"));}),_14M=function(_14N,_14O,_14P){return new F(function(){return _14G(_149,new T2(0,_14O,_14P),_14N,_14L);});},_14Q=new T(function(){return B(unCStr("Negative range size"));}),_14R=new T(function(){return B(err(_14Q));}),_14S=function(_14T){var _14U=B(A1(_14T,_));return E(_14U);},_14V=function(_14W,_14X,_14Y,_){var _14Z=E(_14W);if(!_14Z){return new T2(0,_10,_14X);}else{var _150=new T(function(){return B(_mt(_14Y,0))-1|0;}),_151=B(_13A(new T(function(){return E(_150)+1|0;}),_14X,_)),_152=E(_151),_153=_152.a,_154=_152.b,_155=new T(function(){var _156=E(_153);if(B(_mt(_14Y,0))>=(_156+1|0)){var _157=new T(function(){var _158=_156+1|0;if(_158>0){return B(_13Q(_158,_14Y));}else{return E(_14Y);}});if(0>=_156){return E(_157);}else{var _159=function(_15a,_15b){var _15c=E(_15a);if(!_15c._){return E(_157);}else{var _15d=_15c.a,_15e=E(_15b);return (_15e==1)?new T2(1,_15d,_157):new T2(1,_15d,new T(function(){return B(_159(_15c.b,_15e-1|0));}));}};return B(_159(_14Y,_156));}}else{return E(_14Y);}}),_15f=B(_14V(_14Z-1|0,_154,_155,_)),_15g=new T(function(){var _15h=function(_){var _15i=E(_150),_15j=function(_15k){if(_15k>=0){var _15l=newArr(_15k,_13X),_15m=_15l,_15n=E(_15k);if(!_15n){return new T4(0,E(_13Y),E(_15i),0,_15m);}else{var _15o=function(_15p,_15q,_){while(1){var _15r=E(_15p);if(!_15r._){return E(_);}else{var _=_15m[_15q]=_15r.a;if(_15q!=(_15n-1|0)){var _15s=_15q+1|0;_15p=_15r.b;_15q=_15s;continue;}else{return E(_);}}}},_=B(_15o(_14Y,0,_));return new T4(0,E(_13Y),E(_15i),_15n,_15m);}}else{return E(_14R);}};if(0>_15i){return new F(function(){return _15j(0);});}else{return new F(function(){return _15j(_15i+1|0);});}},_15t=B(_14S(_15h)),_15u=E(_15t.a),_15v=E(_15t.b),_15w=E(_153);if(_15u>_15w){return B(_14M(_15w,_15u,_15v));}else{if(_15w>_15v){return B(_14M(_15w,_15u,_15v));}else{return E(_15t.d[_15w-_15u|0]);}}});return new T2(0,new T2(1,_15g,new T(function(){return B(_si(_15f));})),_154);}},_15x=function(_15y,_15z){while(1){var _15A=E(_15y);if(!_15A._){return E(_15z);}else{_15y=_15A.b;_15z=_15A.a;continue;}}},_15B=function(_15C,_15D,_15E){return new F(function(){return _15x(_15D,_15C);});},_15F=function(_15G,_15H){while(1){var _15I=E(_15G);if(!_15I._){return E(_15H);}else{_15G=_15I.b;_15H=_15I.a;continue;}}},_15J=function(_15K,_15L,_15M){return new F(function(){return _15F(_15L,_15K);});},_15N=function(_15O,_15P){while(1){var _15Q=E(_15P);if(!_15Q._){return __Z;}else{var _15R=_15Q.b,_15S=E(_15O);if(_15S==1){return E(_15R);}else{_15O=_15S-1|0;_15P=_15R;continue;}}}},_15T=function(_15U,_15V){var _15W=new T(function(){var _15X=_15U+1|0;if(_15X>0){return B(_15N(_15X,_15V));}else{return E(_15V);}});if(0>=_15U){return E(_15W);}else{var _15Y=function(_15Z,_160){var _161=E(_15Z);if(!_161._){return E(_15W);}else{var _162=_161.a,_163=E(_160);return (_163==1)?new T2(1,_162,_15W):new T2(1,_162,new T(function(){return B(_15Y(_161.b,_163-1|0));}));}};return new F(function(){return _15Y(_15V,_15U);});}},_164=new T(function(){return B(unCStr(":"));}),_165=function(_166){var _167=E(_166);if(!_167._){return __Z;}else{var _168=new T(function(){return B(_y(_164,new T(function(){return B(_165(_167.b));},1)));},1);return new F(function(){return _y(_167.a,_168);});}},_169=function(_16a,_16b){var _16c=new T(function(){return B(_y(_164,new T(function(){return B(_165(_16b));},1)));},1);return new F(function(){return _y(_16a,_16c);});},_16d=function(_16e){return new F(function(){return _L4("Check.hs:173:7-35|(co : na : xs)");});},_16f=new T(function(){return B(_16d(_));}),_16g=new T(function(){return B(err(_sq));}),_16h=new T(function(){return B(err(_ss));}),_16i=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_16j=0,_16k=new T(function(){return B(unCStr("!"));}),_16l=function(_16m,_16n){var _16o=E(_16n);if(!_16o._){return E(_16f);}else{var _16p=E(_16o.b);if(!_16p._){return E(_16f);}else{var _16q=E(_16o.a),_16r=new T(function(){var _16s=B(_H4(58,_16p.a,_16p.b));return new T2(0,_16s.a,_16s.b);}),_16t=function(_16u,_16v,_16w){var _16x=function(_16y){if((_16m+1|0)!=_16y){return new T3(0,_16m+1|0,_16v,_16o);}else{var _16z=E(_16w);return (_16z._==0)?new T3(0,_16j,_16v,_10):new T3(0,_16j,_16v,new T(function(){var _16A=B(_169(_16z.a,_16z.b));if(!_16A._){return E(_Rk);}else{return B(_Rf(_16A.a,_16A.b));}}));}};if(!B(_qN(_16u,_16k))){var _16B=B(_Gc(B(_sx(_16i,_16u))));if(!_16B._){return E(_16g);}else{if(!E(_16B.b)._){return new F(function(){return _16x(E(_16B.a));});}else{return E(_16h);}}}else{return new F(function(){return _16x( -1);});}};if(E(_16q)==58){return new F(function(){return _16t(_10,new T(function(){return E(E(_16r).a);}),new T(function(){return E(E(_16r).b);}));});}else{var _16C=E(_16r),_16D=E(_16C.b);if(!_16D._){return E(_16f);}else{return new F(function(){return _16t(new T2(1,_16q,_16C.a),_16D.a,_16D.b);});}}}}},_16E=function(_16F,_16G){while(1){var _16H=E(_16G);if(!_16H._){return __Z;}else{var _16I=_16H.b,_16J=E(_16F);if(_16J==1){return E(_16I);}else{_16F=_16J-1|0;_16G=_16I;continue;}}}},_16K=function(_16L,_16M,_16N){var _16O=new T2(1,_16M,new T(function(){var _16P=_16L+1|0;if(_16P>0){return B(_16E(_16P,_16N));}else{return E(_16N);}}));if(0>=_16L){return E(_16O);}else{var _16Q=function(_16R,_16S){var _16T=E(_16R);if(!_16T._){return E(_16O);}else{var _16U=_16T.a,_16V=E(_16S);return (_16V==1)?new T2(1,_16U,_16O):new T2(1,_16U,new T(function(){return B(_16Q(_16T.b,_16V-1|0));}));}};return new F(function(){return _16Q(_16N,_16L);});}},_16W=new T2(0,_QX,_E8),_16X=function(_16Y,_16Z,_170){while(1){var _171=E(_170);if(!_171._){return E(_16W);}else{var _172=_171.b,_173=E(_171.a),_174=E(_173.a);if(_16Y!=E(_174.a)){_170=_172;continue;}else{if(_16Z!=E(_174.b)){_170=_172;continue;}else{return E(_173.b);}}}}},_175=function(_176,_177){while(1){var _178=E(_177);if(!_178._){return __Z;}else{var _179=_178.b,_17a=E(_176);if(_17a==1){return E(_179);}else{_176=_17a-1|0;_177=_179;continue;}}}},_17b=function(_17c,_17d,_17e){var _17f=E(_17c);if(_17f==1){return E(_17e);}else{return new F(function(){return _175(_17f-1|0,_17e);});}},_17g=function(_17h,_17i,_17j){return new T2(1,new T(function(){if(0>=_17h){return __Z;}else{return B(_pO(_17h,new T2(1,_17i,_17j)));}}),new T(function(){if(_17h>0){return B(_17k(_17h,B(_17b(_17h,_17i,_17j))));}else{return B(_17g(_17h,_17i,_17j));}}));},_17k=function(_17l,_17m){var _17n=E(_17m);if(!_17n._){return __Z;}else{var _17o=_17n.a,_17p=_17n.b;return new T2(1,new T(function(){if(0>=_17l){return __Z;}else{return B(_pO(_17l,_17n));}}),new T(function(){if(_17l>0){return B(_17k(_17l,B(_17b(_17l,_17o,_17p))));}else{return B(_17g(_17l,_17o,_17p));}}));}},_17q=function(_17r,_17s,_17t){var _17u=_17s-1|0;if(0<=_17u){var _17v=E(_17r),_17w=function(_17x){var _17y=new T(function(){if(_17x!=_17u){return B(_17w(_17x+1|0));}else{return __Z;}}),_17z=function(_17A){var _17B=E(_17A);return (_17B._==0)?E(_17y):new T2(1,new T(function(){var _17C=E(_17t);if(!_17C._){return E(_16W);}else{var _17D=_17C.b,_17E=E(_17C.a),_17F=E(_17E.a),_17G=E(_17B.a);if(_17G!=E(_17F.a)){return B(_16X(_17G,_17x,_17D));}else{if(_17x!=E(_17F.b)){return B(_16X(_17G,_17x,_17D));}else{return E(_17E.b);}}}}),new T(function(){return B(_17z(_17B.b));}));};return new F(function(){return _17z(B(_8s(0,_17v-1|0)));});};return new F(function(){return _17k(_17v,B(_17w(0)));});}else{return __Z;}},_17H=function(_17I){return new F(function(){return _L4("Check.hs:72:21-47|(l : r : _)");});},_17J=new T(function(){return B(_17H(_));}),_17K=61,_17L=function(_17M,_17N){while(1){var _17O=E(_17M);if(!_17O._){return E(_17N);}else{_17M=_17O.b;_17N=_17O.a;continue;}}},_17P=function(_17Q,_17R,_17S){return new F(function(){return _17L(_17R,_17Q);});},_17T=function(_17U,_17V){var _17W=E(_17V);if(!_17W._){return new T2(0,_10,_10);}else{var _17X=_17W.a;if(!B(A1(_17U,_17X))){var _17Y=new T(function(){var _17Z=B(_17T(_17U,_17W.b));return new T2(0,_17Z.a,_17Z.b);});return new T2(0,new T2(1,_17X,new T(function(){return E(E(_17Y).a);})),new T(function(){return E(E(_17Y).b);}));}else{return new T2(0,_10,_17W);}}},_180=function(_181,_182){while(1){var _183=E(_182);if(!_183._){return __Z;}else{if(!B(A1(_181,_183.a))){return E(_183);}else{_182=_183.b;continue;}}}},_184=function(_185){var _186=_185>>>0;if(_186>887){var _187=u_iswspace(_185);return (E(_187)==0)?false:true;}else{var _188=E(_186);return (_188==32)?true:(_188-9>>>0>4)?(E(_188)==160)?true:false:true;}},_189=function(_18a){return new F(function(){return _184(E(_18a));});},_18b=function(_18c){var _18d=B(_180(_189,_18c));if(!_18d._){return __Z;}else{var _18e=new T(function(){var _18f=B(_17T(_189,_18d));return new T2(0,_18f.a,_18f.b);});return new T2(1,new T(function(){return E(E(_18e).a);}),new T(function(){return B(_18b(E(_18e).b));}));}},_18g=function(_18h){if(!B(_4B(_h7,_17K,_18h))){return new T2(0,_18h,_10);}else{var _18i=new T(function(){var _18j=E(_18h);if(!_18j._){return E(_17J);}else{var _18k=E(_18j.b);if(!_18k._){return E(_17J);}else{var _18l=_18k.a,_18m=_18k.b,_18n=E(_18j.a);if(E(_18n)==61){return new T2(0,_10,new T(function(){return E(B(_H4(61,_18l,_18m)).a);}));}else{var _18o=B(_H4(61,_18l,_18m)),_18p=E(_18o.b);if(!_18p._){return E(_17J);}else{return new T2(0,new T2(1,_18n,_18o.a),_18p.a);}}}}});return new T2(0,new T(function(){var _18q=B(_18b(E(_18i).a));if(!_18q._){return __Z;}else{return B(_17P(_18q.a,_18q.b,_SK));}}),new T(function(){var _18r=B(_18b(E(_18i).b));if(!_18r._){return __Z;}else{return E(_18r.a);}}));}},_18s=function(_18t,_18u){return new F(function(){return _15T(E(_18t),_18u);});},_18v=function(_18w){var _18x=E(_18w);if(!_18x._){return new T2(0,_10,_10);}else{var _18y=E(_18x.a),_18z=new T(function(){var _18A=B(_18v(_18x.b));return new T2(0,_18A.a,_18A.b);});return new T2(0,new T2(1,_18y.a,new T(function(){return E(E(_18z).a);})),new T2(1,_18y.b,new T(function(){return E(E(_18z).b);})));}},_18B=new T(function(){return B(unCStr("\u306d\u3048 \u8d77\u304d\u3066\u3088\u30fb\u30fb\u30fb\u3002 {ch.\u8d77\u304d\u308b,s0.\u8d77\u304d\u306a\u3044,initMsg}"));}),_18C=new T(function(){return B(unCStr("nubatama"));}),_18D=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_18E=new T2(0,_18C,_18D),_18F=new T(function(){return B(unCStr("s1"));}),_18G=new T(function(){return B(unCStr("\n\u3082\u306e\u3092 \u304b\u305e\u3078\u308b\u306e\u304c \u6578\uff1a\u304b\u305a\uff1a\u3067\u3059\u3002\n\u3082\u3057 \u79c1\u305f\u3061\u304c \u3053\u306e\u4e16\u754c\u3092 \u5206\uff1a\u308f\uff1a\u3051\u3066\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u306a\u3044\u306a\u3089 \u6578\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3084\u3046\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u5206\u3051\u3089\u308c\u3066\u3090\u308b\u304b\u3089 \u6578\u3078\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059 {da}{e.b0.m0:s100}"));}),_18H=new T2(0,_18F,_18G),_18I=new T(function(){return B(unCStr("s100"));}),_18J=new T(function(){return B(unCStr("\n\u3053\u308c\u306f \u5206\u3051\u3089\u308c\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_0.\u3044\u3044\u3048,s1_1}"));}),_18K=new T2(0,_18I,_18J),_18L=new T(function(){return B(unCStr("s1_0"));}),_18M=new T(function(){return B(unCStr("\n\u3067\u306f \u5206\u3051\u3066\u304f\u3060\u3055\u3044 {ct.0.Fr}{d.b0}{e.e0.m0:s101}"));}),_18N=new T2(0,_18L,_18M),_18O=new T(function(){return B(unCStr("s4"));}),_18P=new T(function(){return B(unCStr("\n4\u3064\u306e\u6578\u3067 \u6771\uff1a\u304d\uff1a\u897f\uff1a\u3064\uff1a \u5357\uff1a\u3055\uff1a\u5317\uff1a\u306d\uff1a\u306e 4\u65b9\u5411\u304c\u6578\u3078\u3089\u308c\u307e\u3059\u3002\n\u305d\u308c\u306b \u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u52a0\uff1a\u304f\u306f\uff1a\u3078\u308b\u3068 5\u3064\u306b\u306a\u308a\u307e\u3059\u3002\n5 \u306f \u3042\u3044\u3046\u3048\u304a\u3002\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u9054\uff1a\u305f\u3061\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306b\u4f4f\uff1a\u3059\uff1a\u3080\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e \u6bcd\uff1a\u306f\u306f\uff1a\u306a\u308b\u97f3\uff1a\u304a\u3068\uff1a\u3067\u3059"));}),_18Q=new T2(0,_18O,_18P),_18R=new T2(1,_18Q,_10),_18S=new T(function(){return B(unCStr("s3"));}),_18T=new T(function(){return B(unCStr("\n\u3053\u306e\u4e16\u754c\u306b\u907a\uff1a\u306e\u3053\uff1a\u3055\u308c\u305f\u8a00\uff1a\u3053\u3068\uff1a\u8449\uff1a\u3070\uff1a \u305d\u308c\u304c \u53f2\uff1a\u3075\u307f\uff1a \u3067\u3059\u3002\n\u79c1\u305f\u3061\u306f \u305d\u308c\u306b\u3088\u3063\u3066 \u4eba\uff1a\u3058\u3093\uff1a\u751f\uff1a\u305b\u3044\uff1a\u306e\u9577\u3055\u3092\u306f\u308b\u304b\u306b\u8d8a\uff1a\u3053\uff1a\u3048\u305f \u8a18\uff1a\u304d\uff1a\u61b6\uff1a\u304a\u304f\uff1a\u3092\u8fbf\uff1a\u305f\u3069\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_18U=new T2(0,_18S,_18T),_18V=new T2(1,_18U,_18R),_18W=new T(function(){return B(unCStr("s2"));}),_18X=new T(function(){return B(unCStr("\n\u3082\u306e\u3054\u3068\u306e\u7b4b\uff1a\u3059\u3058\uff1a\u9053\uff1a\u307f\u3061\uff1a\u304c \u7406\uff1a\u3053\u3068\u306f\u308a\uff1a\u3067\u3059\u3002\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306e\u3053\u3068 \u5618\uff1a\u3046\u305d\uff1a\u306e\u3053\u3068\u3002\n\u6b63\uff1a\u305f\u3060\uff1a\u3057\u3044\u3053\u3068 \u9593\uff1a\u307e\uff1a\u9055\uff1a\u3061\u304c\uff1a\u3063\u3066\u3090\u308b\u3053\u3068\u3002\n\u305d\u308c\u3092 \u306f\u3063\u304d\u308a\u3055\u305b\u308b\u306e\u304c \u7406 \u3067\u3059"));}),_18Y=new T2(0,_18W,_18X),_18Z=new T2(1,_18Y,_18V),_190=new T(function(){return B(unCStr("s1c"));}),_191=new T(function(){return B(unCStr("\n\u6249\u304c\u958b\u304b\u308c\u305f\u3084\u3046\u3067\u3059 {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"));}),_192=new T2(0,_190,_191),_193=new T2(1,_192,_18Z),_194=new T(function(){return B(unCStr("s104"));}),_195=new T(function(){return B(unCStr("\n\u706b\uff1a\u3072\uff1a(\uff11)\u3068\u6c34\uff1a\u307f\u3065\uff1a(\uff12)\u3092\u5408\u306f\u305b\u308b\u3068 \u3072\u307f\u3064(\uff13) \u306b\u306a\u308a\u307e\u3059\u3002\n\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306e\u6249\uff1a\u3068\u3073\u3089\uff1a\u306f \u307e\u3046\u958b\uff1a\u3072\u3089\uff1a\u304b\u308c\u308b\u3067\u305b\u3046\u3002\n\u9375\uff1a\u304b\u304e\uff1a\u3092\u624b\u306b\u5165\u308c\u305f\u306e\u3067\u3059\u304b\u3089 {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"));}),_196=new T2(0,_194,_195),_197=new T2(1,_196,_193),_198=new T(function(){return B(unCStr("s103"));}),_199=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u304c\u5b58\u5728\u3059\u308b\u9650\uff1a\u304b\u304e\uff1a\u308a \u6578\u306f\u7121\uff1a\u3080\uff1a\u9650\uff1a\u3052\u3093\uff1a\u306b\u3064\u304f\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u3053\u308c\u3089\u304c\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u306b\u7f6e\uff1a\u304a\uff1a\u304b\u308c\u3066\u3090\u305f\u4f4d\uff1a\u3044\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u5165\uff1a\u3044\uff1a\u308c\u66ff\uff1a\u304b\uff1a\u3078\u305f\u3089 \u4f55\uff1a\u306a\u306b\uff1a\u304b\u8d77\uff1a\u304a\uff1a\u3053\u308a\u3055\u3046\u3067\u3059 {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"));}),_19a=new T2(0,_198,_199),_19b=new T2(1,_19a,_197),_19c=new T(function(){return B(unCStr("s102"));}),_19d=new T(function(){return B(unCStr("\n\uff1c\u5728\u308b\uff1e\u3068\u3044\u3075\u5b58\u5728\u3068 \uff1c\u7121\u3044\uff1e\u3068\u3044\u3075\u5b58\u5728\u304c\u3067\u304d\u307e\u3057\u305f\u3002\n\uff1c\u5b58\u5728\uff1e\u3092 1 \u3068\u3059\u308b\u306a\u3089 \u3053\u308c\u3089\u3092\u5408\u306f\u305b\u305f\u540d\u524d\u3092\u3064\u304f\u308a\u307e\u305b\u3046 {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"));}),_19e=new T2(0,_19c,_19d),_19f=new T2(1,_19e,_19b),_19g=new T(function(){return B(unCStr("s1_3"));}),_19h=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u5206\u3051\u305f\u3068\u601d\uff1a\u304a\u3082\uff1a\u306f\u306a\u3044\u306e\u3067\u3042\u308c\u3070\u3002\n\u305d\u308c\u306f \u5206\u304b\u308c\u3066\u3090\u307e\u305b\u3093"));}),_19i=new T2(0,_19g,_19h),_19j=new T2(1,_19i,_19f),_19k=new T(function(){return B(unCStr("s1_2"));}),_19l=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u4e16\u754c\u3092 \u5206\u3051\u3066\n\u300c\u5728\uff1a\u3042\uff1a\u308b\u3002\n\u300c\u7121\uff1a\u306a\uff1a\u3044\u3002\n\u3092\u3064\u304f\u308a\u307e\u3057\u305f\u3002\n\u305d\u308c\u3067\u306f \u3053\u306e \uff1c\u5728\u308b\uff1e\u3092 1 \u3068\u547c\uff1a\u3088\uff1a\u3073\u307e\u305b\u3046 {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"));}),_19m=new T2(0,_19k,_19l),_19n=new T2(1,_19m,_19j),_19o=new T(function(){return B(unCStr("s101"));}),_19p=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u304c \u3053\u308c\u3092\u53d6\uff1a\u3068\uff1a\u3063\u305f\u306e\u3067 \u305d\u308c\u306f \u307e\u3046\u3053\u3053\u306b\u3042\u308a\u307e\u305b\u3093\u3002\n\u3053\u308c\u306f \u5206\u3051\u305f\u3053\u3068\u306b\u306a\u308a\u307e\u3059\u304b\uff1f {ch.\u306f\u3044,s1_2.\u3044\u3044\u3048,s1_3}"));}),_19q=new T2(0,_19o,_19p),_19r=new T2(1,_19q,_19n),_19s=new T(function(){return B(unCStr("s1_1"));}),_19t=new T(function(){return B(unCStr("\n\u672c\uff1a\u307b\u3093\uff1a\u7576\uff1a\u305f\u3046\uff1a\u306b\u5206\u3051\u3089\u308c\u306a\u3044\u306e\u3067\u305b\u3046\u304b"));}),_19u=new T2(0,_19s,_19t),_19v=new T2(1,_19u,_19r),_19w=new T2(1,_18N,_19v),_19x=new T2(1,_18K,_19w),_19y=new T2(1,_18H,_19x),_19z=new T2(1,_18E,_19y),_19A=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_19B=new T(function(){return B(unCStr("msgW"));}),_19C=new T2(0,_19B,_19A),_19D=new T2(1,_19C,_19z),_19E=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u307e\u305b\u3046"));}),_19F=new T(function(){return B(unCStr("msgR"));}),_19G=new T2(0,_19F,_19E),_19H=new T2(1,_19G,_19D),_19I=new T(function(){return B(unCStr("sc0"));}),_19J=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002"));}),_19K=new T2(0,_19I,_19J),_19L=new T2(1,_19K,_19H),_19M=new T(function(){return B(unCStr("s0"));}),_19N=new T(function(){return B(unCStr("\n{sm}\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066 {rk.1.z.abc.sc0}"));}),_19O=new T2(0,_19M,_19N),_19P=new T2(1,_19O,_19L),_19Q=new T(function(){return B(unCStr("initMsg"));}),_19R=function(_19S,_19T){var _19U=new T(function(){var _19V=B(_18v(_19S));return new T2(0,_19V.a,_19V.b);}),_19W=function(_19X){var _19Y=E(_19X);if(!_19Y._){return E(_19U);}else{var _19Z=E(_19Y.a),_1a0=new T(function(){return B(_19W(_19Y.b));});return new T2(0,new T2(1,_19Z.a,new T(function(){return E(E(_1a0).a);})),new T2(1,_19Z.b,new T(function(){return E(E(_1a0).b);})));}},_1a1=function(_1a2,_1a3,_1a4){var _1a5=new T(function(){return B(_19W(_1a4));});return new T2(0,new T2(1,_1a2,new T(function(){return E(E(_1a5).a);})),new T2(1,_1a3,new T(function(){return E(E(_1a5).b);})));},_1a6=B(_1a1(_19Q,_18B,_19P)),_1a7=_1a6.a;if(!B(_4B(_qe,_19T,_1a7))){return __Z;}else{return new F(function(){return _6R(_1a6.b,B(_Mk(_qe,_19T,_1a7)));});}},_1a8=7,_1a9=new T2(0,_1a8,_1a8),_1aa=new T2(1,_1a9,_10),_1ab=5,_1ac=new T2(0,_1ab,_1a8),_1ad=new T2(1,_1ac,_1aa),_1ae=new T2(0,_1ab,_1ab),_1af=new T2(1,_1ae,_1ad),_1ag=new T2(1,_1ae,_1af),_1ah=new T2(1,_1ae,_1ag),_1ai=2,_1aj=4,_1ak=new T2(0,_1aj,_1ai),_1al=new T2(1,_1ak,_10),_1am=new T2(0,_1ai,_1ai),_1an=new T2(1,_1am,_1al),_1ao=new T2(1,_1am,_1an),_1ap=new T2(1,_1am,_1ao),_1aq=new T2(1,_1am,_1ap),_1ar=new T(function(){return B(unCStr("Int"));}),_1as=function(_1at,_1au,_1av){return new F(function(){return _14G(_149,new T2(0,_1au,_1av),_1at,_1ar);});},_1aw=new T(function(){return B(unCStr("msgR"));}),_1ax=new T(function(){return B(_19R(_10,_1aw));}),_1ay=new T(function(){return B(unCStr("msgW"));}),_1az=new T(function(){return B(_19R(_10,_1ay));}),_1aA=function(_1aB){var _1aC=E(_1aB);return 0;},_1aD=new T(function(){return B(unCStr("@@@@@"));}),_1aE=new T(function(){var _1aF=E(_1aD);if(!_1aF._){return E(_nh);}else{return E(_1aF.a);}}),_1aG=122,_1aH=new T2(0,_1aG,_Ee),_1aI=0,_1aJ=new T2(0,_1aI,_1aI),_1aK=new T2(0,_1aJ,_1aH),_1aL=61,_1aM=new T2(0,_1aL,_Ee),_1aN=1,_1aO=new T2(0,_1aN,_1aI),_1aP=new T2(0,_1aO,_1aM),_1aQ=99,_1aR=new T2(0,_1aQ,_E8),_1aS=new T2(0,_1aj,_1aj),_1aT=new T2(0,_1aS,_1aR),_1aU=new T2(1,_1aT,_10),_1aV=98,_1aW=new T2(0,_1aV,_E8),_1aX=new T2(0,_1ai,_1aj),_1aY=new T2(0,_1aX,_1aW),_1aZ=new T2(1,_1aY,_1aU),_1b0=97,_1b1=new T2(0,_1b0,_E8),_1b2=new T2(0,_1aI,_1aj),_1b3=new T2(0,_1b2,_1b1),_1b4=new T2(1,_1b3,_1aZ),_1b5=new T2(1,_1aP,_1b4),_1b6=new T2(1,_1aK,_1b5),_1b7=new T(function(){return B(_17q(_1ab,5,_1b6));}),_1b8=new T(function(){return B(_L4("Check.hs:142:22-33|(ch : po)"));}),_1b9=new T(function(){return B(_e7("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1ba=48,_1bb=new T2(0,_1ba,_Ee),_1bc=new T2(0,_1ai,_1aI),_1bd=new T2(0,_1bc,_1bb),_1be=new T2(1,_1bd,_10),_1bf=6,_1bg=new T2(0,_1aI,_1bf),_1bh=new T2(0,_1bg,_1b1),_1bi=new T2(0,_1ai,_1bf),_1bj=new T2(0,_1bi,_1aW),_1bk=new T2(0,_1aj,_1bf),_1bl=new T2(0,_1bk,_1aR),_1bm=new T2(1,_1bl,_10),_1bn=new T2(1,_1bj,_1bm),_1bo=new T2(1,_1bh,_1bn),_1bp=new T2(1,_1aP,_1bo),_1bq=new T2(1,_1aK,_1bp),_1br=new T2(1,_10,_10),_1bs=new T2(1,_1bq,_1br),_1bt=new T2(1,_10,_1bs),_1bu=new T2(1,_1be,_1bt),_1bv=new T2(1,_1b6,_1bu),_1bw=function(_1bx){var _1by=E(_1bx);if(!_1by._){return __Z;}else{var _1bz=_1by.b,_1bA=E(_1by.a),_1bB=_1bA.b,_1bC=E(_1bA.a),_1bD=function(_1bE){if(E(_1bC)==32){return new T2(1,_1bA,new T(function(){return B(_1bw(_1bz));}));}else{switch(E(_1bB)){case 0:return new T2(1,new T2(0,_1bC,_E8),new T(function(){return B(_1bw(_1bz));}));case 1:return new T2(1,new T2(0,_1bC,_EJ),new T(function(){return B(_1bw(_1bz));}));case 2:return new T2(1,new T2(0,_1bC,_Ek),new T(function(){return B(_1bw(_1bz));}));case 3:return new T2(1,new T2(0,_1bC,_Eq),new T(function(){return B(_1bw(_1bz));}));case 4:return new T2(1,new T2(0,_1bC,_Ew),new T(function(){return B(_1bw(_1bz));}));case 5:return new T2(1,new T2(0,_1bC,_EX),new T(function(){return B(_1bw(_1bz));}));case 6:return new T2(1,new T2(0,_1bC,_EQ),new T(function(){return B(_1bw(_1bz));}));case 7:return new T2(1,new T2(0,_1bC,_EJ),new T(function(){return B(_1bw(_1bz));}));default:return new T2(1,new T2(0,_1bC,_EC),new T(function(){return B(_1bw(_1bz));}));}}};if(E(_1bC)==32){return new F(function(){return _1bD(_);});}else{switch(E(_1bB)){case 0:return new T2(1,new T2(0,_1bC,_EC),new T(function(){return B(_1bw(_1bz));}));case 1:return new F(function(){return _1bD(_);});break;case 2:return new F(function(){return _1bD(_);});break;case 3:return new F(function(){return _1bD(_);});break;case 4:return new F(function(){return _1bD(_);});break;case 5:return new F(function(){return _1bD(_);});break;case 6:return new F(function(){return _1bD(_);});break;case 7:return new F(function(){return _1bD(_);});break;default:return new F(function(){return _1bD(_);});}}}},_1bF=function(_1bG){var _1bH=E(_1bG);return (_1bH._==0)?__Z:new T2(1,new T(function(){return B(_1bw(_1bH.a));}),new T(function(){return B(_1bF(_1bH.b));}));},_1bI=function(_1bJ){var _1bK=E(_1bJ);if(!_1bK._){return __Z;}else{var _1bL=_1bK.b,_1bM=E(_1bK.a),_1bN=_1bM.b,_1bO=E(_1bM.a),_1bP=function(_1bQ){if(E(_1bO)==32){return new T2(1,_1bM,new T(function(){return B(_1bI(_1bL));}));}else{switch(E(_1bN)){case 0:return new T2(1,new T2(0,_1bO,_E8),new T(function(){return B(_1bI(_1bL));}));case 1:return new T2(1,new T2(0,_1bO,_Ee),new T(function(){return B(_1bI(_1bL));}));case 2:return new T2(1,new T2(0,_1bO,_Ek),new T(function(){return B(_1bI(_1bL));}));case 3:return new T2(1,new T2(0,_1bO,_Eq),new T(function(){return B(_1bI(_1bL));}));case 4:return new T2(1,new T2(0,_1bO,_Ew),new T(function(){return B(_1bI(_1bL));}));case 5:return new T2(1,new T2(0,_1bO,_EX),new T(function(){return B(_1bI(_1bL));}));case 6:return new T2(1,new T2(0,_1bO,_EQ),new T(function(){return B(_1bI(_1bL));}));case 7:return new T2(1,new T2(0,_1bO,_Ee),new T(function(){return B(_1bI(_1bL));}));default:return new T2(1,new T2(0,_1bO,_EC),new T(function(){return B(_1bI(_1bL));}));}}};if(E(_1bO)==32){return new F(function(){return _1bP(_);});}else{if(E(_1bN)==8){return new T2(1,new T2(0,_1bO,_E8),new T(function(){return B(_1bI(_1bL));}));}else{return new F(function(){return _1bP(_);});}}}},_1bR=function(_1bS){var _1bT=E(_1bS);return (_1bT._==0)?__Z:new T2(1,new T(function(){return B(_1bI(_1bT.a));}),new T(function(){return B(_1bR(_1bT.b));}));},_1bU=function(_1bV,_1bW,_1bX,_1bY,_1bZ,_1c0,_1c1,_1c2,_1c3,_1c4,_1c5,_1c6,_1c7,_1c8,_1c9,_1ca,_1cb,_1cc,_1cd,_1ce,_1cf,_1cg,_1ch,_1ci,_1cj,_1ck,_1cl,_1cm,_1cn,_1co,_1cp,_1cq,_1cr,_1cs,_1ct,_1cu,_1cv){var _1cw=E(_1bW);if(!_1cw._){return E(_1b9);}else{var _1cx=_1cw.b,_1cy=E(_1cw.a),_1cz=new T(function(){var _1cA=function(_){var _1cB=B(_mt(_1cb,0))-1|0,_1cC=function(_1cD){if(_1cD>=0){var _1cE=newArr(_1cD,_13X),_1cF=_1cE,_1cG=E(_1cD);if(!_1cG){return new T4(0,E(_16j),E(_1cB),0,_1cF);}else{var _1cH=function(_1cI,_1cJ,_){while(1){var _1cK=E(_1cI);if(!_1cK._){return E(_);}else{var _=_1cF[_1cJ]=_1cK.a;if(_1cJ!=(_1cG-1|0)){var _1cL=_1cJ+1|0;_1cI=_1cK.b;_1cJ=_1cL;continue;}else{return E(_);}}}},_=B(_1cH(_1cb,0,_));return new T4(0,E(_16j),E(_1cB),_1cG,_1cF);}}else{return E(_14R);}};if(0>_1cB){return new F(function(){return _1cC(0);});}else{return new F(function(){return _1cC(_1cB+1|0);});}},_1cM=B(_14S(_1cA)),_1cN=E(_1cM.a),_1cO=E(_1cM.b),_1cP=E(_1bV);if(_1cN>_1cP){return B(_1as(_1cP,_1cN,_1cO));}else{if(_1cP>_1cO){return B(_1as(_1cP,_1cN,_1cO));}else{return E(_1cM.d[_1cP-_1cN|0]);}}});switch(E(_1cy)){case 97:var _1cQ=new T(function(){var _1cR=E(_1cx);if(!_1cR._){return E(_1b8);}else{return new T2(0,_1cR.a,_1cR.b);}}),_1cS=new T(function(){var _1cT=B(_18g(E(_1cQ).b));return new T2(0,_1cT.a,_1cT.b);}),_1cU=B(_Gc(B(_sx(_16i,new T(function(){return E(E(_1cS).b);})))));if(!_1cU._){return E(_16g);}else{if(!E(_1cU.b)._){var _1cV=new T(function(){var _1cW=B(_Gc(B(_sx(_16i,new T(function(){return E(E(_1cS).a);})))));if(!_1cW._){return E(_16g);}else{if(!E(_1cW.b)._){return E(_1cW.a);}else{return E(_16h);}}},1);return {_:0,a:E({_:0,a:E(_1bX),b:E(B(_KD(_1cV,E(_1cU.a),new T(function(){return E(E(_1cQ).a);}),_E8,_1bY))),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};}else{return E(_16h);}}break;case 104:return {_:0,a:E({_:0,a:E(_1bX),b:E(B(_1bF(_1bY))),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};case 106:var _1cX=E(_1cx);if(!_1cX._){return {_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l: -1,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};}else{if(E(_1cX.a)==108){var _1cY=E(_1bV),_1cZ=B(_Gc(B(_sx(_16i,_1cX.b))));return (_1cZ._==0)?E(_16g):(E(_1cZ.b)._==0)?{_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(B(_15T(_1cY,_1ca))),f:E(B(_15T(_1cY,_1cb))),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:E(_1cZ.a),m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_wt),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)}:E(_16h);}else{var _1d0=B(_Gc(B(_sx(_16i,_1cX))));return (_1d0._==0)?E(_16g):(E(_1d0.b)._==0)?{_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:E(_1d0.a),m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)}:E(_16h);}}break;case 108:var _1d1=E(_1bV);return {_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(B(_15T(_1d1,_1ca))),f:E(B(_15T(_1d1,_1cb))),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_wt),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};case 109:var _1d2=B(_16l(E(_1cz),_1cx)),_1d3=_1d2.c,_1d4=B(_qN(_1d3,_10));if(!E(_1d4)){var _1d5=E(_1bV),_1d6=new T(function(){var _1d7=function(_){var _1d8=B(_mt(_1ca,0))-1|0,_1d9=function(_1da){if(_1da>=0){var _1db=newArr(_1da,_13X),_1dc=_1db,_1dd=E(_1da);if(!_1dd){return new T4(0,E(_16j),E(_1d8),0,_1dc);}else{var _1de=function(_1df,_1dg,_){while(1){var _1dh=E(_1df);if(!_1dh._){return E(_);}else{var _=_1dc[_1dg]=_1dh.a;if(_1dg!=(_1dd-1|0)){var _1di=_1dg+1|0;_1df=_1dh.b;_1dg=_1di;continue;}else{return E(_);}}}},_=B(_1de(_1ca,0,_));return new T4(0,E(_16j),E(_1d8),_1dd,_1dc);}}else{return E(_14R);}};if(0>_1d8){return new F(function(){return _1d9(0);});}else{return new F(function(){return _1d9(_1d8+1|0);});}},_1dj=B(_14S(_1d7)),_1dk=E(_1dj.a),_1dl=E(_1dj.b);if(_1dk>_1d5){return B(_1as(_1d5,_1dk,_1dl));}else{if(_1d5>_1dl){return B(_1as(_1d5,_1dk,_1dl));}else{return E(E(_1dj.d[_1d5-_1dk|0]).a);}}}),_1dm=B(_16K(_1d5,new T2(0,_1d6,new T2(1,_1cy,_1d3)),_1ca));}else{var _1dm=B(_18s(_1bV,_1ca));}if(!E(_1d4)){var _1dn=B(_16K(E(_1bV),_1d2.a,_1cb));}else{var _1dn=B(_18s(_1bV,_1cb));}return {_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(B(_19R(_1c9,_1d2.b))),d:E(_1c9),e:E(_1dm),f:E(_1dn),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_wt),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};case 114:var _1do=B(_6R(_1ah,_1c1));return {_:0,a:E({_:0,a:E(B(_6R(_1aq,_1c1))),b:E(B(_17q(_1do.a,E(_1do.b),new T(function(){return B(_6R(_1bv,_1c1));})))),c:B(_6R(_1aD,_1c1)),d:32,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1do),c:E(_1ax),d:E(_1c9),e:E(_1ca),f:E(B(_6e(_1aA,_1cb))),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_wt),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};case 115:return {_:0,a:E({_:0,a:E(_1bX),b:E(B(_1bR(_1bY))),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};case 116:var _1dp=E(_1cz),_1dq=B(_16l(_1dp,_1cx)),_1dr=E(_1dq.a);if(!E(_1dr)){var _1ds=true;}else{var _1ds=false;}if(!E(_1ds)){var _1dt=B(_16K(E(_1bV),_1dr,_1cb));}else{var _1dt=B(_16K(E(_1bV),_1dp+1|0,_1cb));}if(!E(_1ds)){var _1du=__Z;}else{var _1du=E(_1dq.b);}if(!B(_qN(_1du,_10))){var _1dv=B(_1bU(_1bV,_1du,_1bX,_1bY,_1bZ,_1c0,_1c1,_1c2,_1c3,_1c4,_1c5,_1c6,_1c7,_1c8,_1c9,_1ca,_1dt,_1cc,_1cd,_1ce,_1cf,_1cg,_1ch,_1ci,_1cj,_1ck,_1cl,_1cm,_1cn,_1co,_1cp,_1cq,_1cr,_1cs,_1ct,_1cu,_1cv)),_1dw=E(_1dv.a);return {_:0,a:E({_:0,a:E(_1dw.a),b:E(_1dw.b),c:_1dw.c,d:_1dw.d,e:_1dw.e,f:E(_1dw.f),g:_1dw.g,h:E(B(_y(_1c4,_1cw))),i:E(_1dw.i),j:E(_1dw.j)}),b:E(_1dv.b),c:E(_1dv.c),d:E(_1dv.d),e:E(_1dv.e),f:E(_1dv.f),g:E(_1dv.g),h:E(_1dv.h),i:_1dv.i,j:_1dv.j,k:_1dv.k,l:_1dv.l,m:E(_1dv.m),n:_1dv.n,o:E(_1dv.o),p:E(_1dv.p),q:_1dv.q,r:E(_1dv.r),s:E(_1dv.s)};}else{return {_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1dt),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};}break;case 119:return {_:0,a:E({_:0,a:E(_1am),b:E(_1b7),c:E(_1aE),d:32,e:0,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1ae),c:E(_1az),d:E(_1c9),e:E(_1ca),f:E(B(_6e(_1aA,_1cb))),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_wt),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};default:return {_:0,a:E({_:0,a:E(_1bX),b:E(_1bY),c:_1bZ,d:_1c0,e:_1c1,f:E(_1c2),g:_1c3,h:E(B(_y(_1c4,_1cw))),i:E(_1c5),j:E(_1c6)}),b:E(_1c7),c:E(_1c8),d:E(_1c9),e:E(_1ca),f:E(_1cb),g:E(_1cc),h:E(_1cd),i:_1ce,j:_1cf,k:_1cg,l:_1ch,m:E(_1ci),n:_1cj,o:E(_1ck),p:E(_1cl),q:_1cm,r:E({_:0,a:E(_1cn),b:E(_1co),c:E(_1cp),d:E(_1cq),e:E(_1cr),f:E(_1cs),g:E(_1ct),h:E(_1cu)}),s:E(_1cv)};}}},_1dx=function(_1dy,_1dz){while(1){var _1dA=E(_1dz);if(!_1dA._){return __Z;}else{var _1dB=_1dA.b,_1dC=E(_1dy);if(_1dC==1){return E(_1dB);}else{_1dy=_1dC-1|0;_1dz=_1dB;continue;}}}},_1dD=new T(function(){return B(unCStr("X"));}),_1dE=new T(function(){return B(_e7("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1dF=38,_1dG=function(_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_1dN,_1dO,_1dP,_1dQ,_1dR,_1dS,_1dT,_1dU,_1dV,_1dW,_1dX,_1dY,_1dZ,_1e0,_1e1,_1e2){var _1e3=E(_1dJ);if(!_1e3._){return {_:0,a:_1dK,b:_1dL,c:_1dM,d:_1dN,e:_1dO,f:_1dP,g:_1dQ,h:_1dR,i:_1dS,j:_1dT,k:_1dU,l:_1dV,m:_1dW,n:_1dX,o:_1dY,p:_1dZ,q:_1e0,r:_1e1,s:_1e2};}else{var _1e4=_1e3.b,_1e5=E(_1e3.a),_1e6=_1e5.a,_1e7=_1e5.b,_1e8=function(_1e9,_1ea,_1eb){var _1ec=function(_1ed,_1ee){if(!B(_qN(_1ed,_10))){var _1ef=E(_1dK),_1eg=E(_1e1),_1eh=B(_1bU(_1ee,_1ed,_1ef.a,_1ef.b,_1ef.c,_1ef.d,_1ef.e,_1ef.f,_1ef.g,_1ef.h,_1ef.i,_1ef.j,_1dL,_1dM,_1dN,_1dO,_1dP,_1dQ,_1dR,_1dS,_1dT,_1dU,_1dV,_1dW,_1dX,_1dY,_1dZ,_1e0,_1eg.a,_1eg.b,_1eg.c,_1eg.d,_1eg.e,_1eg.f,_1eg.g,_1eg.h,_1e2)),_1ei=_1eh.a,_1ej=_1eh.b,_1ek=_1eh.c,_1el=_1eh.d,_1em=_1eh.e,_1en=_1eh.f,_1eo=_1eh.g,_1ep=_1eh.h,_1eq=_1eh.i,_1er=_1eh.j,_1es=_1eh.k,_1et=_1eh.l,_1eu=_1eh.m,_1ev=_1eh.n,_1ew=_1eh.o,_1ex=_1eh.p,_1ey=_1eh.q,_1ez=_1eh.r,_1eA=_1eh.s;if(B(_mt(_1en,0))!=B(_mt(_1dP,0))){return {_:0,a:_1ei,b:_1ej,c:_1ek,d:_1el,e:_1em,f:_1en,g:_1eo,h:_1ep,i:_1eq,j:_1er,k:_1es,l:_1et,m:_1eu,n:_1ev,o:_1ew,p:_1ex,q:_1ey,r:_1ez,s:_1eA};}else{return new F(function(){return _1dG(new T(function(){return E(_1dH)+1|0;}),_1dI,_1e4,_1ei,_1ej,_1ek,_1el,_1em,_1en,_1eo,_1ep,_1eq,_1er,_1es,_1et,_1eu,_1ev,_1ew,_1ex,_1ey,_1ez,_1eA);});}}else{return new F(function(){return _1dG(new T(function(){return E(_1dH)+1|0;}),_1dI,_1e4,_1dK,_1dL,_1dM,_1dN,_1dO,_1dP,_1dQ,_1dR,_1dS,_1dT,_1dU,_1dV,_1dW,_1dX,_1dY,_1dZ,_1e0,_1e1,_1e2);});}},_1eB=B(_mt(_1dI,0))-B(_mt(new T2(1,_1e9,_1ea),0))|0;if(_1eB>0){var _1eC=B(_1dx(_1eB,_1dI));}else{var _1eC=E(_1dI);}if(E(B(_15B(_1e9,_1ea,_SK)))==63){var _1eD=B(_Rf(_1e9,_1ea));}else{var _1eD=new T2(1,_1e9,_1ea);}var _1eE=function(_1eF){if(!B(_4B(_h7,_1dF,_1e6))){return new T2(0,_1e7,_1dH);}else{var _1eG=function(_1eH){while(1){var _1eI=B((function(_1eJ){var _1eK=E(_1eJ);if(!_1eK._){return true;}else{var _1eL=_1eK.b,_1eM=E(_1eK.a);if(!_1eM._){return E(_1dE);}else{switch(E(_1eM.a)){case 99:var _1eN=E(_1dK);if(!E(_1eN.j)){return false;}else{var _1eO=function(_1eP){while(1){var _1eQ=E(_1eP);if(!_1eQ._){return true;}else{var _1eR=_1eQ.b,_1eS=E(_1eQ.a);if(!_1eS._){return E(_1dE);}else{if(E(_1eS.a)==115){var _1eT=B(_Gc(B(_sx(_16i,_1eS.b))));if(!_1eT._){return E(_16g);}else{if(!E(_1eT.b)._){if(_1eN.e!=E(_1eT.a)){return false;}else{_1eP=_1eR;continue;}}else{return E(_16h);}}}else{_1eP=_1eR;continue;}}}}};return new F(function(){return _1eO(_1eL);});}break;case 115:var _1eU=E(_1dK),_1eV=_1eU.e,_1eW=B(_Gc(B(_sx(_16i,_1eM.b))));if(!_1eW._){return E(_16g);}else{if(!E(_1eW.b)._){if(_1eV!=E(_1eW.a)){return false;}else{var _1eX=function(_1eY){while(1){var _1eZ=E(_1eY);if(!_1eZ._){return true;}else{var _1f0=_1eZ.b,_1f1=E(_1eZ.a);if(!_1f1._){return E(_1dE);}else{switch(E(_1f1.a)){case 99:if(!E(_1eU.j)){return false;}else{_1eY=_1f0;continue;}break;case 115:var _1f2=B(_Gc(B(_sx(_16i,_1f1.b))));if(!_1f2._){return E(_16g);}else{if(!E(_1f2.b)._){if(_1eV!=E(_1f2.a)){return false;}else{_1eY=_1f0;continue;}}else{return E(_16h);}}break;default:_1eY=_1f0;continue;}}}}};return new F(function(){return _1eX(_1eL);});}}else{return E(_16h);}}break;default:_1eH=_1eL;return __continue;}}}})(_1eH));if(_1eI!=__continue){return _1eI;}}};return (!B(_1eG(_1eb)))?(!B(_qN(_1eD,_1dD)))?new T2(0,_10,_1dH):new T2(0,_1e7,_1dH):new T2(0,_1e7,_1dH);}};if(E(B(_15J(_1e9,_1ea,_SK)))==63){if(!B(_69(_1eC,_10))){var _1f3=E(_1eC);if(!_1f3._){return E(_Rk);}else{if(!B(_qN(_1eD,B(_Rf(_1f3.a,_1f3.b))))){if(!B(_qN(_1eD,_1dD))){return new F(function(){return _1ec(_10,_1dH);});}else{return new F(function(){return _1ec(_1e7,_1dH);});}}else{var _1f4=B(_1eE(_));return new F(function(){return _1ec(_1f4.a,_1f4.b);});}}}else{if(!B(_qN(_1eD,_1eC))){if(!B(_qN(_1eD,_1dD))){return new F(function(){return _1ec(_10,_1dH);});}else{return new F(function(){return _1ec(_1e7,_1dH);});}}else{var _1f5=B(_1eE(_));return new F(function(){return _1ec(_1f5.a,_1f5.b);});}}}else{if(!B(_qN(_1eD,_1eC))){if(!B(_qN(_1eD,_1dD))){return new F(function(){return _1ec(_10,_1dH);});}else{return new F(function(){return _1ec(_1e7,_1dH);});}}else{var _1f6=B(_1eE(_));return new F(function(){return _1ec(_1f6.a,_1f6.b);});}}},_1f7=E(_1e6);if(!_1f7._){return E(_SK);}else{var _1f8=_1f7.a,_1f9=E(_1f7.b);if(!_1f9._){return new F(function(){return _1e8(_1f8,_10,_10);});}else{var _1fa=E(_1f8),_1fb=new T(function(){var _1fc=B(_H4(38,_1f9.a,_1f9.b));return new T2(0,_1fc.a,_1fc.b);});if(E(_1fa)==38){return E(_SK);}else{return new F(function(){return _1e8(_1fa,new T(function(){return E(E(_1fb).a);}),new T(function(){return E(E(_1fb).b);}));});}}}}},_1fd="]",_1fe="}",_1ff=":",_1fg=",",_1fh=new T(function(){return eval("JSON.stringify");}),_1fi="false",_1fj="null",_1fk="[",_1fl="{",_1fm="\"",_1fn="true",_1fo=function(_1fp,_1fq){var _1fr=E(_1fq);switch(_1fr._){case 0:return new T2(0,new T(function(){return jsShow(_1fr.a);}),_1fp);case 1:return new T2(0,new T(function(){var _1fs=__app1(E(_1fh),_1fr.a);return String(_1fs);}),_1fp);case 2:return (!E(_1fr.a))?new T2(0,_1fi,_1fp):new T2(0,_1fn,_1fp);case 3:var _1ft=E(_1fr.a);if(!_1ft._){return new T2(0,_1fk,new T2(1,_1fd,_1fp));}else{var _1fu=new T(function(){var _1fv=new T(function(){var _1fw=function(_1fx){var _1fy=E(_1fx);if(!_1fy._){return E(new T2(1,_1fd,_1fp));}else{var _1fz=new T(function(){var _1fA=B(_1fo(new T(function(){return B(_1fw(_1fy.b));}),_1fy.a));return new T2(1,_1fA.a,_1fA.b);});return new T2(1,_1fg,_1fz);}};return B(_1fw(_1ft.b));}),_1fB=B(_1fo(_1fv,_1ft.a));return new T2(1,_1fB.a,_1fB.b);});return new T2(0,_1fk,_1fu);}break;case 4:var _1fC=E(_1fr.a);if(!_1fC._){return new T2(0,_1fl,new T2(1,_1fe,_1fp));}else{var _1fD=E(_1fC.a),_1fE=new T(function(){var _1fF=new T(function(){var _1fG=function(_1fH){var _1fI=E(_1fH);if(!_1fI._){return E(new T2(1,_1fe,_1fp));}else{var _1fJ=E(_1fI.a),_1fK=new T(function(){var _1fL=B(_1fo(new T(function(){return B(_1fG(_1fI.b));}),_1fJ.b));return new T2(1,_1fL.a,_1fL.b);});return new T2(1,_1fg,new T2(1,_1fm,new T2(1,_1fJ.a,new T2(1,_1fm,new T2(1,_1ff,_1fK)))));}};return B(_1fG(_1fC.b));}),_1fM=B(_1fo(_1fF,_1fD.b));return new T2(1,_1fM.a,_1fM.b);});return new T2(0,_1fl,new T2(1,new T(function(){var _1fN=__app1(E(_1fh),E(_1fD.a));return String(_1fN);}),new T2(1,_1ff,_1fE)));}break;default:return new T2(0,_1fj,_1fp);}},_1fO=new T(function(){return toJSStr(_10);}),_1fP=function(_1fQ){var _1fR=B(_1fo(_10,_1fQ)),_1fS=jsCat(new T2(1,_1fR.a,_1fR.b),E(_1fO));return E(_1fS);},_1fT=function(_1fU){var _1fV=E(_1fU);if(!_1fV._){return new T2(0,_10,_10);}else{var _1fW=E(_1fV.a),_1fX=new T(function(){var _1fY=B(_1fT(_1fV.b));return new T2(0,_1fY.a,_1fY.b);});return new T2(0,new T2(1,_1fW.a,new T(function(){return E(E(_1fX).a);})),new T2(1,_1fW.b,new T(function(){return E(E(_1fX).b);})));}},_1fZ=new T(function(){return B(unCStr("Rk"));}),_1g0=function(_1g1,_1g2,_1g3,_1g4,_1g5,_1g6,_1g7,_1g8,_1g9,_1ga,_1gb,_1gc,_1gd,_1ge,_1gf,_1gg,_1gh,_1gi,_1gj,_1gk){while(1){var _1gl=B((function(_1gm,_1gn,_1go,_1gp,_1gq,_1gr,_1gs,_1gt,_1gu,_1gv,_1gw,_1gx,_1gy,_1gz,_1gA,_1gB,_1gC,_1gD,_1gE,_1gF){var _1gG=E(_1gm);if(!_1gG._){return {_:0,a:_1gn,b:_1go,c:_1gp,d:_1gq,e:_1gr,f:_1gs,g:_1gt,h:_1gu,i:_1gv,j:_1gw,k:_1gx,l:_1gy,m:_1gz,n:_1gA,o:_1gB,p:_1gC,q:_1gD,r:_1gE,s:_1gF};}else{var _1gH=_1gG.a,_1gI=B(_RD(B(unAppCStr("e.e",new T2(1,_1gH,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1gH,_1fZ)));})))),_1gn,_1go,_1gp,_1gq,_1gr,_1gs,_1gt,_1gu,_1gv,_1gw,_1gx,_1gy,_1gz,_1gA,_1gB,_1gC,_1gD,_1gE,_1gF));_1g1=_1gG.b;_1g2=_1gI.a;_1g3=_1gI.b;_1g4=_1gI.c;_1g5=_1gI.d;_1g6=_1gI.e;_1g7=_1gI.f;_1g8=_1gI.g;_1g9=_1gI.h;_1ga=_1gI.i;_1gb=_1gI.j;_1gc=_1gI.k;_1gd=_1gI.l;_1ge=_1gI.m;_1gf=_1gI.n;_1gg=_1gI.o;_1gh=_1gI.p;_1gi=_1gI.q;_1gj=_1gI.r;_1gk=_1gI.s;return __continue;}})(_1g1,_1g2,_1g3,_1g4,_1g5,_1g6,_1g7,_1g8,_1g9,_1ga,_1gb,_1gc,_1gd,_1ge,_1gf,_1gg,_1gh,_1gi,_1gj,_1gk));if(_1gl!=__continue){return _1gl;}}},_1gJ=function(_1gK){var _1gL=E(_1gK);switch(_1gL){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1gL>>>0>1114111){return new F(function(){return _wD(_1gL);});}else{return _1gL;}}},_1gM=function(_1gN,_1gO,_1gP){while(1){var _1gQ=E(_1gO);if(!_1gQ._){return (E(_1gP)._==0)?true:false;}else{var _1gR=E(_1gP);if(!_1gR._){return false;}else{if(!B(A3(_4z,_1gN,_1gQ.a,_1gR.a))){return false;}else{_1gO=_1gQ.b;_1gP=_1gR.b;continue;}}}}},_1gS=function(_1gT,_1gU){return (!B(_1gM(_rk,_1gT,_1gU)))?true:false;},_1gV=function(_1gW,_1gX){return new F(function(){return _1gM(_rk,_1gW,_1gX);});},_1gY=new T2(0,_1gV,_1gS),_1gZ=function(_1h0){var _1h1=E(_1h0);if(!_1h1._){return new T2(0,_10,_10);}else{var _1h2=E(_1h1.a),_1h3=new T(function(){var _1h4=B(_1gZ(_1h1.b));return new T2(0,_1h4.a,_1h4.b);});return new T2(0,new T2(1,_1h2.a,new T(function(){return E(E(_1h3).a);})),new T2(1,_1h2.b,new T(function(){return E(E(_1h3).b);})));}},_1h5=function(_1h6,_1h7){while(1){var _1h8=E(_1h7);if(!_1h8._){return __Z;}else{var _1h9=_1h8.b,_1ha=E(_1h6);if(_1ha==1){return E(_1h9);}else{_1h6=_1ha-1|0;_1h7=_1h9;continue;}}}},_1hb=function(_1hc,_1hd){while(1){var _1he=E(_1hd);if(!_1he._){return __Z;}else{var _1hf=_1he.b,_1hg=E(_1hc);if(_1hg==1){return E(_1hf);}else{_1hc=_1hg-1|0;_1hd=_1hf;continue;}}}},_1hh=function(_1hi){return new F(function(){return _Gj(_1hi,_10);});},_1hj=function(_1hk,_1hl,_1hm,_1hn){var _1ho=new T(function(){return B(_Mk(_h7,_1hl,_1hm));}),_1hp=new T(function(){var _1hq=E(_1ho),_1hr=new T(function(){var _1hs=_1hq+1|0;if(_1hs>0){return B(_1hb(_1hs,_1hm));}else{return E(_1hm);}});if(0>=_1hq){return E(_1hr);}else{var _1ht=function(_1hu,_1hv){var _1hw=E(_1hu);if(!_1hw._){return E(_1hr);}else{var _1hx=_1hw.a,_1hy=E(_1hv);return (_1hy==1)?new T2(1,_1hx,_1hr):new T2(1,_1hx,new T(function(){return B(_1ht(_1hw.b,_1hy-1|0));}));}};return B(_1ht(_1hm,_1hq));}}),_1hz=new T(function(){var _1hA=E(_1ho),_1hB=new T(function(){if(E(_1hl)==94){return B(A2(_1hk,new T(function(){return B(_6R(_1hn,_1hA+1|0));}),new T(function(){return B(_6R(_1hn,_1hA));})));}else{return B(A2(_1hk,new T(function(){return B(_6R(_1hn,_1hA));}),new T(function(){return B(_6R(_1hn,_1hA+1|0));})));}}),_1hC=new T2(1,_1hB,new T(function(){var _1hD=_1hA+2|0;if(_1hD>0){return B(_1h5(_1hD,_1hn));}else{return E(_1hn);}}));if(0>=_1hA){return E(_1hC);}else{var _1hE=function(_1hF,_1hG){var _1hH=E(_1hF);if(!_1hH._){return E(_1hC);}else{var _1hI=_1hH.a,_1hJ=E(_1hG);return (_1hJ==1)?new T2(1,_1hI,_1hC):new T2(1,_1hI,new T(function(){return B(_1hE(_1hH.b,_1hJ-1|0));}));}};return B(_1hE(_1hn,_1hA));}});return (E(_1hl)==94)?new T2(0,new T(function(){return B(_1hh(_1hp));}),new T(function(){return B(_1hh(_1hz));})):new T2(0,_1hp,_1hz);},_1hK=new T(function(){return B(_cn(_oM,_oL));}),_1hL=function(_1hM,_1hN,_1hO){while(1){if(!E(_1hK)){if(!B(_cn(B(_10W(_1hN,_oM)),_oL))){if(!B(_cn(_1hN,_aV))){var _1hP=B(_of(_1hM,_1hM)),_1hQ=B(_10H(B(_eO(_1hN,_aV)),_oM)),_1hR=B(_of(_1hM,_1hO));_1hM=_1hP;_1hN=_1hQ;_1hO=_1hR;continue;}else{return new F(function(){return _of(_1hM,_1hO);});}}else{var _1hP=B(_of(_1hM,_1hM)),_1hQ=B(_10H(_1hN,_oM));_1hM=_1hP;_1hN=_1hQ;continue;}}else{return E(_9U);}}},_1hS=function(_1hT,_1hU){while(1){if(!E(_1hK)){if(!B(_cn(B(_10W(_1hU,_oM)),_oL))){if(!B(_cn(_1hU,_aV))){return new F(function(){return _1hL(B(_of(_1hT,_1hT)),B(_10H(B(_eO(_1hU,_aV)),_oM)),_1hT);});}else{return E(_1hT);}}else{var _1hV=B(_of(_1hT,_1hT)),_1hW=B(_10H(_1hU,_oM));_1hT=_1hV;_1hU=_1hW;continue;}}else{return E(_9U);}}},_1hX=function(_1hY,_1hZ){if(!B(_d7(_1hZ,_oL))){if(!B(_cn(_1hZ,_oL))){return new F(function(){return _1hS(_1hY,_1hZ);});}else{return E(_aV);}}else{return E(_pr);}},_1i0=94,_1i1=45,_1i2=43,_1i3=42,_1i4=function(_1i5,_1i6){while(1){var _1i7=B((function(_1i8,_1i9){var _1ia=E(_1i9);if(!_1ia._){return __Z;}else{if((B(_mt(_1i8,0))+1|0)==B(_mt(_1ia,0))){if(!B(_4B(_h7,_1i0,_1i8))){if(!B(_4B(_h7,_1i3,_1i8))){if(!B(_4B(_h7,_1i2,_1i8))){if(!B(_4B(_h7,_1i1,_1i8))){return E(_1ia);}else{var _1ib=B(_1hj(_eO,45,_1i8,_1ia));_1i5=_1ib.a;_1i6=_1ib.b;return __continue;}}else{var _1ic=B(_1hj(_cv,43,_1i8,_1ia));_1i5=_1ic.a;_1i6=_1ic.b;return __continue;}}else{var _1id=B(_1hj(_of,42,_1i8,_1ia));_1i5=_1id.a;_1i6=_1id.b;return __continue;}}else{var _1ie=B(_1hj(_1hX,94,new T(function(){return B(_1hh(_1i8));}),new T(function(){return B(_Gj(_1ia,_10));})));_1i5=_1ie.a;_1i6=_1ie.b;return __continue;}}else{return __Z;}}})(_1i5,_1i6));if(_1i7!=__continue){return _1i7;}}},_1if=function(_1ig){var _1ih=E(_1ig);if(!_1ih._){return new T2(0,_10,_10);}else{var _1ii=E(_1ih.a),_1ij=new T(function(){var _1ik=B(_1if(_1ih.b));return new T2(0,_1ik.a,_1ik.b);});return new T2(0,new T2(1,_1ii.a,new T(function(){return E(E(_1ij).a);})),new T2(1,_1ii.b,new T(function(){return E(E(_1ij).b);})));}},_1il=new T(function(){return B(unCStr("0123456789+-"));}),_1im=function(_1in){while(1){var _1io=E(_1in);if(!_1io._){return true;}else{if(!B(_4B(_h7,_1io.a,_1il))){return false;}else{_1in=_1io.b;continue;}}}},_1ip=new T(function(){return B(err(_sq));}),_1iq=new T(function(){return B(err(_ss));}),_1ir=function(_1is,_1it){var _1iu=function(_1iv,_1iw){var _1ix=function(_1iy){return new F(function(){return A1(_1iw,new T(function(){return B(_ft(_1iy));}));});},_1iz=new T(function(){return B(_D6(function(_1iA){return new F(function(){return A3(_1is,_1iA,_1iv,_1ix);});}));}),_1iB=function(_1iC){return E(_1iz);},_1iD=function(_1iE){return new F(function(){return A2(_BN,_1iE,_1iB);});},_1iF=new T(function(){return B(_D6(function(_1iG){var _1iH=E(_1iG);if(_1iH._==4){var _1iI=E(_1iH.a);if(!_1iI._){return new F(function(){return A3(_1is,_1iH,_1iv,_1iw);});}else{if(E(_1iI.a)==45){if(!E(_1iI.b)._){return E(new T1(1,_1iD));}else{return new F(function(){return A3(_1is,_1iH,_1iv,_1iw);});}}else{return new F(function(){return A3(_1is,_1iH,_1iv,_1iw);});}}}else{return new F(function(){return A3(_1is,_1iH,_1iv,_1iw);});}}));}),_1iJ=function(_1iK){return E(_1iF);};return new T1(1,function(_1iL){return new F(function(){return A2(_BN,_1iL,_1iJ);});});};return new F(function(){return _DX(_1iu,_1it);});},_1iM=function(_1iN){var _1iO=E(_1iN);if(_1iO._==5){var _1iP=B(_FV(_1iO.a));return (_1iP._==0)?E(_G0):function(_1iQ,_1iR){return new F(function(){return A1(_1iR,_1iP.a);});};}else{return E(_G0);}},_1iS=new T(function(){return B(A3(_1ir,_1iM,_DD,_Fq));}),_1iT=function(_1iU,_1iV){var _1iW=E(_1iV);if(!_1iW._){return __Z;}else{var _1iX=_1iW.a,_1iY=_1iW.b,_1iZ=function(_1j0){var _1j1=B(_1if(_1iU)),_1j2=_1j1.a;return (!B(_4B(_qe,_1iX,_1j2)))?__Z:new T2(1,new T(function(){return B(_6R(_1j1.b,B(_Mk(_qe,_1iX,_1j2))));}),new T(function(){return B(_1iT(_1iU,_1iY));}));};if(!B(_69(_1iX,_10))){if(!B(_1im(_1iX))){return new F(function(){return _1iZ(_);});}else{return new T2(1,new T(function(){var _1j3=B(_Gc(B(_sx(_1iS,_1iX))));if(!_1j3._){return E(_1ip);}else{if(!E(_1j3.b)._){return E(_1j3.a);}else{return E(_1iq);}}}),new T(function(){return B(_1iT(_1iU,_1iY));}));}}else{return new F(function(){return _1iZ(_);});}}},_1j4=new T(function(){return B(unCStr("+-*^"));}),_1j5=new T(function(){return B(unCStr("0123456789"));}),_1j6=new T(function(){return B(_L4("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1j7=new T2(1,_10,_10),_1j8=function(_1j9){var _1ja=E(_1j9);if(!_1ja._){return new T2(0,_1j7,_10);}else{var _1jb=_1ja.a,_1jc=new T(function(){var _1jd=B(_1j8(_1ja.b)),_1je=E(_1jd.a);if(!_1je._){return E(_1j6);}else{return new T3(0,_1je.a,_1je.b,_1jd.b);}});return (!B(_4B(_h7,_1jb,_1j5)))?(!B(_4B(_h7,_1jb,_1j4)))?new T2(0,new T2(1,new T2(1,_1jb,new T(function(){return E(E(_1jc).a);})),new T(function(){return E(E(_1jc).b);})),new T(function(){return E(E(_1jc).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1jc).a);}),new T(function(){return E(E(_1jc).b);}))),new T2(1,_1jb,new T(function(){return E(E(_1jc).c);}))):new T2(0,new T2(1,new T2(1,_1jb,new T(function(){return E(E(_1jc).a);})),new T(function(){return E(E(_1jc).b);})),new T(function(){return E(E(_1jc).c);}));}},_1jf=function(_1jg,_1jh){var _1ji=new T(function(){var _1jj=B(_1j8(_1jh)),_1jk=E(_1jj.a);if(!_1jk._){return E(_1j6);}else{return new T3(0,_1jk.a,_1jk.b,_1jj.b);}});return (!B(_4B(_h7,_1jg,_1j5)))?(!B(_4B(_h7,_1jg,_1j4)))?new T2(0,new T2(1,new T2(1,_1jg,new T(function(){return E(E(_1ji).a);})),new T(function(){return E(E(_1ji).b);})),new T(function(){return E(E(_1ji).c);})):new T2(0,new T2(1,_10,new T2(1,new T(function(){return E(E(_1ji).a);}),new T(function(){return E(E(_1ji).b);}))),new T2(1,_1jg,new T(function(){return E(E(_1ji).c);}))):new T2(0,new T2(1,new T2(1,_1jg,new T(function(){return E(E(_1ji).a);})),new T(function(){return E(E(_1ji).b);})),new T(function(){return E(E(_1ji).c);}));},_1jl=function(_1jm,_1jn){while(1){var _1jo=E(_1jm);if(!_1jo._){return E(_1jn);}else{_1jm=_1jo.b;_1jn=_1jo.a;continue;}}},_1jp=function(_1jq,_1jr,_1js){return new F(function(){return _1jl(_1jr,_1jq);});},_1jt=function(_1ju,_1jv){var _1jw=E(_1jv);if(!_1jw._){return __Z;}else{var _1jx=B(_1jf(_1jw.a,_1jw.b)),_1jy=B(_1i4(_1jx.b,B(_1iT(_1ju,_1jx.a))));if(!_1jy._){return E(_1jw);}else{return new F(function(){return _130(0,B(_1jp(_1jy.a,_1jy.b,_SK)),_10);});}}},_1jz=function(_1jA,_1jB){var _1jC=function(_1jD,_1jE){while(1){var _1jF=B((function(_1jG,_1jH){var _1jI=E(_1jH);if(!_1jI._){return (!B(_qN(_1jG,_10)))?new T2(0,_wt,_1jG):new T2(0,_ws,_10);}else{var _1jJ=_1jI.b,_1jK=B(_1gZ(_1jI.a)).a;if(!B(_4B(_h7,_17K,_1jK))){var _1jL=_1jG;_1jD=_1jL;_1jE=_1jJ;return __continue;}else{var _1jM=B(_18g(_1jK)),_1jN=_1jM.a,_1jO=_1jM.b;if(!B(_69(_1jO,_10))){if(!B(_qN(B(_1jt(_1jA,_1jN)),B(_1jt(_1jA,_1jO))))){return new T2(0,_ws,_10);}else{var _1jP=new T(function(){if(!B(_qN(_1jG,_10))){return B(_y(_1jG,new T(function(){return B(unAppCStr(" ",_1jN));},1)));}else{return E(_1jN);}});_1jD=_1jP;_1jE=_1jJ;return __continue;}}else{return new T2(0,_ws,_10);}}}})(_1jD,_1jE));if(_1jF!=__continue){return _1jF;}}};return new F(function(){return _1jC(_10,_1jB);});},_1jQ=function(_1jR,_1jS){var _1jT=new T(function(){var _1jU=B(_Gc(B(_sx(_12Q,new T(function(){return B(_pO(3,B(_I(0,imul(E(_1jS),E(_1jR)-1|0)|0,_10))));})))));if(!_1jU._){return E(_12P);}else{if(!E(_1jU.b)._){return E(_1jU.a);}else{return E(_12O);}}});return new T2(0,new T(function(){return B(_av(_1jT,_1jR));}),_1jT);},_1jV=function(_1jW,_1jX){while(1){var _1jY=E(_1jX);if(!_1jY._){return __Z;}else{var _1jZ=_1jY.b,_1k0=E(_1jW);if(_1k0==1){return E(_1jZ);}else{_1jW=_1k0-1|0;_1jX=_1jZ;continue;}}}},_1k1=function(_1k2,_1k3){while(1){var _1k4=E(_1k3);if(!_1k4._){return __Z;}else{var _1k5=_1k4.b,_1k6=E(_1k2);if(_1k6==1){return E(_1k5);}else{_1k2=_1k6-1|0;_1k3=_1k5;continue;}}}},_1k7=64,_1k8=new T2(1,_1k7,_10),_1k9=function(_1ka,_1kb,_1kc,_1kd){return (!B(_qN(_1ka,_1kc)))?true:(!B(_cn(_1kb,_1kd)))?true:false;},_1ke=function(_1kf,_1kg){var _1kh=E(_1kf),_1ki=E(_1kg);return new F(function(){return _1k9(_1kh.a,_1kh.b,_1ki.a,_1ki.b);});},_1kj=function(_1kk,_1kl,_1km,_1kn){if(!B(_qN(_1kk,_1km))){return false;}else{return new F(function(){return _cn(_1kl,_1kn);});}},_1ko=function(_1kp,_1kq){var _1kr=E(_1kp),_1ks=E(_1kq);return new F(function(){return _1kj(_1kr.a,_1kr.b,_1ks.a,_1ks.b);});},_1kt=new T2(0,_1ko,_1ke),_1ku=function(_1kv){var _1kw=E(_1kv);if(!_1kw._){return new T2(0,_10,_10);}else{var _1kx=E(_1kw.a),_1ky=new T(function(){var _1kz=B(_1ku(_1kw.b));return new T2(0,_1kz.a,_1kz.b);});return new T2(0,new T2(1,_1kx.a,new T(function(){return E(E(_1ky).a);})),new T2(1,_1kx.b,new T(function(){return E(E(_1ky).b);})));}},_1kA=function(_1kB){var _1kC=E(_1kB);if(!_1kC._){return new T2(0,_10,_10);}else{var _1kD=E(_1kC.a),_1kE=new T(function(){var _1kF=B(_1kA(_1kC.b));return new T2(0,_1kF.a,_1kF.b);});return new T2(0,new T2(1,_1kD.a,new T(function(){return E(E(_1kE).a);})),new T2(1,_1kD.b,new T(function(){return E(E(_1kE).b);})));}},_1kG=function(_1kH){var _1kI=E(_1kH);if(!_1kI._){return new T2(0,_10,_10);}else{var _1kJ=E(_1kI.a),_1kK=new T(function(){var _1kL=B(_1kG(_1kI.b));return new T2(0,_1kL.a,_1kL.b);});return new T2(0,new T2(1,_1kJ.a,new T(function(){return E(E(_1kK).a);})),new T2(1,_1kJ.b,new T(function(){return E(E(_1kK).b);})));}},_1kM=function(_1kN,_1kO){return (_1kN<=_1kO)?new T2(1,_1kN,new T(function(){return B(_1kM(_1kN+1|0,_1kO));})):__Z;},_1kP=new T(function(){return B(_1kM(65,90));}),_1kQ=function(_1kR){return (_1kR<=122)?new T2(1,_1kR,new T(function(){return B(_1kQ(_1kR+1|0));})):E(_1kP);},_1kS=new T(function(){return B(_1kQ(97));}),_1kT=function(_1kU){while(1){var _1kV=E(_1kU);if(!_1kV._){return true;}else{if(!B(_4B(_h7,_1kV.a,_1kS))){return false;}else{_1kU=_1kV.b;continue;}}}},_1kW=new T2(0,_10,_10),_1kX=new T(function(){return B(err(_sq));}),_1kY=new T(function(){return B(err(_ss));}),_1kZ=new T(function(){return B(A3(_1ir,_1iM,_DD,_Fq));}),_1l0=function(_1l1,_1l2,_1l3){while(1){var _1l4=B((function(_1l5,_1l6,_1l7){var _1l8=E(_1l7);if(!_1l8._){return __Z;}else{var _1l9=_1l8.b,_1la=B(_1kA(_1l6)),_1lb=_1la.a,_1lc=B(_1ku(_1lb)),_1ld=_1lc.a,_1le=new T(function(){return E(B(_1kG(_1l8.a)).a);}),_1lf=new T(function(){return B(_4B(_h7,_17K,_1le));}),_1lg=new T(function(){if(!E(_1lf)){return E(_1kW);}else{var _1lh=B(_18g(_1le));return new T2(0,_1lh.a,_1lh.b);}}),_1li=new T(function(){return E(E(_1lg).a);}),_1lj=new T(function(){return B(_Mk(_qe,_1li,_1ld));}),_1lk=new T(function(){var _1ll=function(_){var _1lm=B(_mt(_1l6,0))-1|0,_1ln=function(_1lo){if(_1lo>=0){var _1lp=newArr(_1lo,_13X),_1lq=_1lp,_1lr=E(_1lo);if(!_1lr){return new T4(0,E(_16j),E(_1lm),0,_1lq);}else{var _1ls=function(_1lt,_1lu,_){while(1){var _1lv=E(_1lt);if(!_1lv._){return E(_);}else{var _=_1lq[_1lu]=_1lv.a;if(_1lu!=(_1lr-1|0)){var _1lw=_1lu+1|0;_1lt=_1lv.b;_1lu=_1lw;continue;}else{return E(_);}}}},_=B(_1ls(_1la.b,0,_));return new T4(0,E(_16j),E(_1lm),_1lr,_1lq);}}else{return E(_14R);}};if(0>_1lm){return new F(function(){return _1ln(0);});}else{return new F(function(){return _1ln(_1lm+1|0);});}};return B(_14S(_1ll));});if(!B(_4B(_qe,_1li,_1ld))){var _1lx=false;}else{var _1ly=E(_1lk),_1lz=E(_1ly.a),_1lA=E(_1ly.b),_1lB=E(_1lj);if(_1lz>_1lB){var _1lC=B(_1as(_1lB,_1lz,_1lA));}else{if(_1lB>_1lA){var _1lD=B(_1as(_1lB,_1lz,_1lA));}else{var _1lD=E(_1ly.d[_1lB-_1lz|0])==E(_1l5);}var _1lC=_1lD;}var _1lx=_1lC;}var _1lE=new T(function(){return E(E(_1lg).b);}),_1lF=new T(function(){return B(_Mk(_qe,_1lE,_1ld));}),_1lG=new T(function(){if(!B(_4B(_qe,_1lE,_1ld))){return false;}else{var _1lH=E(_1lk),_1lI=E(_1lH.a),_1lJ=E(_1lH.b),_1lK=E(_1lF);if(_1lI>_1lK){return B(_1as(_1lK,_1lI,_1lJ));}else{if(_1lK>_1lJ){return B(_1as(_1lK,_1lI,_1lJ));}else{return E(_1lH.d[_1lK-_1lI|0])==E(_1l5);}}}}),_1lL=new T(function(){var _1lM=function(_){var _1lN=B(_mt(_1lb,0))-1|0,_1lO=function(_1lP){if(_1lP>=0){var _1lQ=newArr(_1lP,_13X),_1lR=_1lQ,_1lS=E(_1lP);if(!_1lS){return new T4(0,E(_16j),E(_1lN),0,_1lR);}else{var _1lT=function(_1lU,_1lV,_){while(1){var _1lW=E(_1lU);if(!_1lW._){return E(_);}else{var _=_1lR[_1lV]=_1lW.a;if(_1lV!=(_1lS-1|0)){var _1lX=_1lV+1|0;_1lU=_1lW.b;_1lV=_1lX;continue;}else{return E(_);}}}},_=B(_1lT(_1lc.b,0,_));return new T4(0,E(_16j),E(_1lN),_1lS,_1lR);}}else{return E(_14R);}};if(0>_1lN){return new F(function(){return _1lO(0);});}else{return new F(function(){return _1lO(_1lN+1|0);});}};return B(_14S(_1lM));}),_1lY=function(_1lZ){var _1m0=function(_1m1){return (!E(_1lx))?__Z:(!E(_1lG))?__Z:new T2(1,new T2(0,_1li,new T(function(){var _1m2=E(_1lL),_1m3=E(_1m2.a),_1m4=E(_1m2.b),_1m5=E(_1lj);if(_1m3>_1m5){return B(_1as(_1m5,_1m3,_1m4));}else{if(_1m5>_1m4){return B(_1as(_1m5,_1m3,_1m4));}else{return E(_1m2.d[_1m5-_1m3|0]);}}})),new T2(1,new T2(0,_1lE,new T(function(){var _1m6=E(_1lL),_1m7=E(_1m6.a),_1m8=E(_1m6.b),_1m9=E(_1lF);if(_1m7>_1m9){return B(_1as(_1m9,_1m7,_1m8));}else{if(_1m9>_1m8){return B(_1as(_1m9,_1m7,_1m8));}else{return E(_1m6.d[_1m9-_1m7|0]);}}})),_10));};if(!E(_1lx)){if(!E(_1lG)){return new F(function(){return _1m0(_);});}else{return new T2(1,new T2(0,_1lE,new T(function(){var _1ma=E(_1lL),_1mb=E(_1ma.a),_1mc=E(_1ma.b),_1md=E(_1lF);if(_1mb>_1md){return B(_1as(_1md,_1mb,_1mc));}else{if(_1md>_1mc){return B(_1as(_1md,_1mb,_1mc));}else{return E(_1ma.d[_1md-_1mb|0]);}}})),_10);}}else{return new F(function(){return _1m0(_);});}};if(!E(_1lx)){var _1me=B(_1lY(_));}else{if(!E(_1lG)){var _1mf=new T2(1,new T2(0,_1li,new T(function(){var _1mg=E(_1lL),_1mh=E(_1mg.a),_1mi=E(_1mg.b),_1mj=E(_1lj);if(_1mh>_1mj){return B(_1as(_1mj,_1mh,_1mi));}else{if(_1mj>_1mi){return B(_1as(_1mj,_1mh,_1mi));}else{return E(_1mg.d[_1mj-_1mh|0]);}}})),_10);}else{var _1mf=B(_1lY(_));}var _1me=_1mf;}if(!B(_1gM(_1kt,_1me,_10))){return new F(function(){return _y(_1me,new T(function(){return B(_1l0(_1l5,_1l6,_1l9));},1));});}else{if(!E(_1lf)){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{if(!B(_1kT(_1li))){if(!B(_1kT(_1lE))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{if(!E(_1lx)){if(!E(_1lG)){if(!B(_69(_1li,_10))){if(!B(_1im(_1li))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{return new T2(1,new T2(0,_1lE,new T(function(){var _1mm=B(_Gc(B(_sx(_1kZ,_1li))));if(!_1mm._){return E(_1kX);}else{if(!E(_1mm.b)._){return E(_1mm.a);}else{return E(_1kY);}}})),new T(function(){return B(_1l0(_1l5,_1l6,_1l9));}));}}else{var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}else{var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}else{var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}}else{if(!E(_1lx)){if(!E(_1lG)){if(!B(_69(_1lE,_10))){if(!B(_1im(_1lE))){if(!B(_1kT(_1lE))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{if(!B(_69(_1li,_10))){if(!B(_1im(_1li))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{return new T2(1,new T2(0,_1lE,new T(function(){var _1mn=B(_Gc(B(_sx(_1kZ,_1li))));if(!_1mn._){return E(_1kX);}else{if(!E(_1mn.b)._){return E(_1mn.a);}else{return E(_1kY);}}})),new T(function(){return B(_1l0(_1l5,_1l6,_1l9));}));}}else{var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}}else{return new T2(1,new T2(0,_1li,new T(function(){var _1mo=B(_Gc(B(_sx(_1kZ,_1lE))));if(!_1mo._){return E(_1kX);}else{if(!E(_1mo.b)._){return E(_1mo.a);}else{return E(_1kY);}}})),new T(function(){return B(_1l0(_1l5,_1l6,_1l9));}));}}else{if(!B(_1kT(_1lE))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{if(!B(_69(_1li,_10))){if(!B(_1im(_1li))){var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}else{return new T2(1,new T2(0,_1lE,new T(function(){var _1mp=B(_Gc(B(_sx(_1kZ,_1li))));if(!_1mp._){return E(_1kX);}else{if(!E(_1mp.b)._){return E(_1mp.a);}else{return E(_1kY);}}})),new T(function(){return B(_1l0(_1l5,_1l6,_1l9));}));}}else{var _1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}}}else{var _1mq=B(_1kT(_1lE)),_1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}else{var _1mr=B(_1kT(_1lE)),_1mk=_1l5,_1ml=_1l6;_1l1=_1mk;_1l2=_1ml;_1l3=_1l9;return __continue;}}}}}})(_1l1,_1l2,_1l3));if(_1l4!=__continue){return _1l4;}}},_1ms=102,_1mt=101,_1mu=new T(function(){return B(unCStr("=="));}),_1mv=new T(function(){return B(_e7("Action.hs:(103,17)-(107,70)|case"));}),_1mw=new T(function(){return B(_e7("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1mx=5,_1my=117,_1mz=98,_1mA=110,_1mB=118,_1mC=function(_1mD,_1mE,_1mF,_1mG,_1mH,_1mI,_1mJ,_1mK,_1mL,_1mM,_1mN,_1mO,_1mP){var _1mQ=B(_6R(B(_6R(_1mH,_1mE)),_1mD)),_1mR=_1mQ.a,_1mS=_1mQ.b;if(E(_1mJ)==32){if(!B(_4B(_h7,_1mR,_1k8))){var _1mT=false;}else{switch(E(_1mS)){case 0:var _1mU=true;break;case 1:var _1mU=false;break;case 2:var _1mU=false;break;case 3:var _1mU=false;break;case 4:var _1mU=false;break;case 5:var _1mU=false;break;case 6:var _1mU=false;break;case 7:var _1mU=false;break;default:var _1mU=false;}var _1mT=_1mU;}var _1mV=_1mT;}else{var _1mV=false;}if(E(_1mJ)==32){if(E(_1mR)==32){var _1mW=false;}else{switch(E(_1mS)){case 0:if(!E(_1mV)){var _1mX=true;}else{var _1mX=false;}var _1mY=_1mX;break;case 1:var _1mY=false;break;case 2:var _1mY=false;break;case 3:var _1mY=false;break;case 4:var _1mY=false;break;case 5:var _1mY=false;break;case 6:var _1mY=false;break;case 7:var _1mY=false;break;default:if(!E(_1mV)){var _1mZ=true;}else{var _1mZ=false;}var _1mY=_1mZ;}var _1mW=_1mY;}var _1n0=_1mW;}else{var _1n0=false;}var _1n1=new T(function(){return B(_KD(_1mD,_1mE,new T(function(){if(!E(_1n0)){if(!E(_1mV)){return E(_1mR);}else{return _1mI;}}else{return E(_U7);}}),_1mS,_1mH));});switch(E(_1mS)){case 3:var _1n2=true;break;case 4:if(E(_1mJ)==32){var _1n3=true;}else{var _1n3=false;}var _1n2=_1n3;break;default:var _1n2=false;}if(!E(_1n2)){var _1n4=E(_1n1);}else{var _1n5=E(_1mF),_1n6=new T(function(){return B(_6R(_1n1,_1mE));}),_1n7=function(_1n8,_1n9){var _1na=E(_1n8);if(_1na==( -1)){return E(_1n1);}else{var _1nb=new T(function(){return B(_KD(_1mD,_1mE,_U7,_E8,_1n1));}),_1nc=E(_1n9);if(_1nc==( -1)){var _1nd=__Z;}else{var _1nd=B(_6R(_1nb,_1nc));}if(E(B(_6R(_1nd,_1na)).a)==32){var _1ne=new T(function(){var _1nf=new T(function(){return B(_6R(_1n6,_1mD));}),_1ng=new T2(1,new T2(0,new T(function(){return E(E(_1nf).a);}),new T(function(){return E(E(_1nf).b);})),new T(function(){var _1nh=_1na+1|0;if(_1nh>0){return B(_1k1(_1nh,_1nd));}else{return E(_1nd);}}));if(0>=_1na){return E(_1ng);}else{var _1ni=function(_1nj,_1nk){var _1nl=E(_1nj);if(!_1nl._){return E(_1ng);}else{var _1nm=_1nl.a,_1nn=E(_1nk);return (_1nn==1)?new T2(1,_1nm,_1ng):new T2(1,_1nm,new T(function(){return B(_1ni(_1nl.b,_1nn-1|0));}));}};return B(_1ni(_1nd,_1na));}}),_1no=new T2(1,_1ne,new T(function(){var _1np=_1n9+1|0;if(_1np>0){return B(_1jV(_1np,_1nb));}else{return E(_1nb);}}));if(0>=_1n9){return E(_1no);}else{var _1nq=function(_1nr,_1ns){var _1nt=E(_1nr);if(!_1nt._){return E(_1no);}else{var _1nu=_1nt.a,_1nv=E(_1ns);return (_1nv==1)?new T2(1,_1nu,_1no):new T2(1,_1nu,new T(function(){return B(_1nq(_1nt.b,_1nv-1|0));}));}};return new F(function(){return _1nq(_1nb,_1n9);});}}else{return E(_1n1);}}};if(_1mD<=_1n5){if(_1n5<=_1mD){var _1nw=E(_1mG);if(_1mE<=_1nw){if(_1nw<=_1mE){var _1nx=E(_1mv);}else{var _1ny=E(_1mE);if(!_1ny){var _1nz=B(_1n7( -1, -1));}else{var _1nz=B(_1n7(_1mD,_1ny-1|0));}var _1nx=_1nz;}var _1nA=_1nx;}else{if(_1mE!=(B(_mt(_1n1,0))-1|0)){var _1nB=B(_1n7(_1mD,_1mE+1|0));}else{var _1nB=B(_1n7( -1, -1));}var _1nA=_1nB;}var _1nC=_1nA;}else{var _1nD=E(_1mD);if(!_1nD){var _1nE=B(_1n7( -1, -1));}else{var _1nE=B(_1n7(_1nD-1|0,_1mE));}var _1nC=_1nE;}var _1nF=_1nC;}else{if(_1mD!=(B(_mt(_1n6,0))-1|0)){var _1nG=B(_1n7(_1mD+1|0,_1mE));}else{var _1nG=B(_1n7( -1, -1));}var _1nF=_1nG;}var _1n4=_1nF;}if(!E(_1mO)){var _1nH=E(_1n4);}else{var _1nI=new T(function(){var _1nJ=E(_1n4);if(!_1nJ._){return E(_nh);}else{return B(_mt(_1nJ.a,0));}}),_1nK=new T(function(){return B(_mt(_1n4,0));}),_1nL=function(_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS){while(1){var _1nT=B((function(_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ,_1o0){var _1o1=E(_1o0);if(!_1o1._){return E(_1nX);}else{var _1o2=_1o1.b,_1o3=E(_1o1.a);if(!_1o3._){return E(_1mw);}else{var _1o4=_1o3.b,_1o5=E(_1o3.a);if(E(_1o5.b)==5){var _1o6=new T(function(){var _1o7=B(_1jQ(_1mx,_1nU));return new T2(0,_1o7.a,_1o7.b);}),_1o8=new T(function(){var _1o9=function(_1oa,_1ob){var _1oc=function(_1od){return new F(function(){return _KD(_1nV,_1nW,_U7,_E8,new T(function(){return B(_KD(_1oa,_1ob,_1o5.a,_EX,_1nX));}));});};if(_1oa!=_1nV){return new F(function(){return _1oc(_);});}else{if(_1ob!=_1nW){return new F(function(){return _1oc(_);});}else{return E(_1nX);}}};switch(E(E(_1o6).a)){case 1:var _1oe=_1nV-1|0;if(_1oe<0){return B(_1o9(_1nV,_1nW));}else{if(_1oe>=E(_1nI)){return B(_1o9(_1nV,_1nW));}else{if(_1nW<0){return B(_1o9(_1nV,_1nW));}else{if(_1nW>=E(_1nK)){return B(_1o9(_1nV,_1nW));}else{if(_1oe!=_1nY){if(E(B(_6R(B(_6R(_1nX,_1nW)),_1oe)).a)==32){return B(_1o9(_1oe,_1nW));}else{return B(_1o9(_1nV,_1nW));}}else{if(_1nW!=_1nZ){if(E(B(_6R(B(_6R(_1nX,_1nW)),_1oe)).a)==32){return B(_1o9(_1oe,_1nW));}else{return B(_1o9(_1nV,_1nW));}}else{return B(_1o9(_1nV,_1nW));}}}}}}break;case 2:if(_1nV<0){return B(_1o9(_1nV,_1nW));}else{if(_1nV>=E(_1nI)){return B(_1o9(_1nV,_1nW));}else{var _1of=_1nW-1|0;if(_1of<0){return B(_1o9(_1nV,_1nW));}else{if(_1of>=E(_1nK)){return B(_1o9(_1nV,_1nW));}else{if(_1nV!=_1nY){if(E(B(_6R(B(_6R(_1nX,_1of)),_1nV)).a)==32){return B(_1o9(_1nV,_1of));}else{return B(_1o9(_1nV,_1nW));}}else{if(_1of!=_1nZ){if(E(B(_6R(B(_6R(_1nX,_1of)),_1nV)).a)==32){return B(_1o9(_1nV,_1of));}else{return B(_1o9(_1nV,_1nW));}}else{return B(_1o9(_1nV,_1nW));}}}}}}break;case 3:var _1og=_1nV+1|0;if(_1og<0){return B(_1o9(_1nV,_1nW));}else{if(_1og>=E(_1nI)){return B(_1o9(_1nV,_1nW));}else{if(_1nW<0){return B(_1o9(_1nV,_1nW));}else{if(_1nW>=E(_1nK)){return B(_1o9(_1nV,_1nW));}else{if(_1og!=_1nY){if(E(B(_6R(B(_6R(_1nX,_1nW)),_1og)).a)==32){return B(_1o9(_1og,_1nW));}else{return B(_1o9(_1nV,_1nW));}}else{if(_1nW!=_1nZ){if(E(B(_6R(B(_6R(_1nX,_1nW)),_1og)).a)==32){return B(_1o9(_1og,_1nW));}else{return B(_1o9(_1nV,_1nW));}}else{return B(_1o9(_1nV,_1nW));}}}}}}break;case 4:if(_1nV<0){return B(_1o9(_1nV,_1nW));}else{if(_1nV>=E(_1nI)){return B(_1o9(_1nV,_1nW));}else{var _1oh=_1nW+1|0;if(_1oh<0){return B(_1o9(_1nV,_1nW));}else{if(_1oh>=E(_1nK)){return B(_1o9(_1nV,_1nW));}else{if(_1nV!=_1nY){if(E(B(_6R(B(_6R(_1nX,_1oh)),_1nV)).a)==32){return B(_1o9(_1nV,_1oh));}else{return B(_1o9(_1nV,_1nW));}}else{if(_1oh!=_1nZ){if(E(B(_6R(B(_6R(_1nX,_1oh)),_1nV)).a)==32){return B(_1o9(_1nV,_1oh));}else{return B(_1o9(_1nV,_1nW));}}else{return B(_1o9(_1nV,_1nW));}}}}}}break;default:if(_1nV<0){return B(_1o9(_1nV,_1nW));}else{if(_1nV>=E(_1nI)){return B(_1o9(_1nV,_1nW));}else{if(_1nW<0){return B(_1o9(_1nV,_1nW));}else{if(_1nW>=E(_1nK)){return B(_1o9(_1nV,_1nW));}else{if(_1nV!=_1nY){var _1oi=E(B(_6R(B(_6R(_1nX,_1nW)),_1nV)).a);return B(_1o9(_1nV,_1nW));}else{if(_1nW!=_1nZ){var _1oj=E(B(_6R(B(_6R(_1nX,_1nW)),_1nV)).a);return B(_1o9(_1nV,_1nW));}else{return B(_1o9(_1nV,_1nW));}}}}}}}}),_1ok=E(_1o4);if(!_1ok._){var _1ol=_1nW+1|0,_1om=_1nY,_1on=_1nZ;_1nM=new T(function(){return E(E(_1o6).b);},1);_1nN=0;_1nO=_1ol;_1nP=_1o8;_1nQ=_1om;_1nR=_1on;_1nS=_1o2;return __continue;}else{return new F(function(){return _1oo(new T(function(){return E(E(_1o6).b);},1),_1nV+1|0,_1nW,_1o8,_1nY,_1nZ,_1ok.a,_1ok.b,_1o2);});}}else{var _1op=E(_1o4);if(!_1op._){var _1oq=_1nU,_1ol=_1nW+1|0,_1or=_1nX,_1om=_1nY,_1on=_1nZ;_1nM=_1oq;_1nN=0;_1nO=_1ol;_1nP=_1or;_1nQ=_1om;_1nR=_1on;_1nS=_1o2;return __continue;}else{return new F(function(){return _1oo(_1nU,_1nV+1|0,_1nW,_1nX,_1nY,_1nZ,_1op.a,_1op.b,_1o2);});}}}}})(_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR,_1nS));if(_1nT!=__continue){return _1nT;}}},_1oo=function(_1os,_1ot,_1ou,_1ov,_1ow,_1ox,_1oy,_1oz,_1oA){while(1){var _1oB=B((function(_1oC,_1oD,_1oE,_1oF,_1oG,_1oH,_1oI,_1oJ,_1oK){var _1oL=E(_1oI);if(E(_1oL.b)==5){var _1oM=new T(function(){var _1oN=B(_1jQ(_1mx,_1oC));return new T2(0,_1oN.a,_1oN.b);}),_1oO=new T(function(){var _1oP=function(_1oQ,_1oR){var _1oS=function(_1oT){return new F(function(){return _KD(_1oD,_1oE,_U7,_E8,new T(function(){return B(_KD(_1oQ,_1oR,_1oL.a,_EX,_1oF));}));});};if(_1oQ!=_1oD){return new F(function(){return _1oS(_);});}else{if(_1oR!=_1oE){return new F(function(){return _1oS(_);});}else{return E(_1oF);}}};switch(E(E(_1oM).a)){case 1:var _1oU=_1oD-1|0;if(_1oU<0){return B(_1oP(_1oD,_1oE));}else{if(_1oU>=E(_1nI)){return B(_1oP(_1oD,_1oE));}else{if(_1oE<0){return B(_1oP(_1oD,_1oE));}else{if(_1oE>=E(_1nK)){return B(_1oP(_1oD,_1oE));}else{if(_1oU!=_1oG){if(E(B(_6R(B(_6R(_1oF,_1oE)),_1oU)).a)==32){return B(_1oP(_1oU,_1oE));}else{return B(_1oP(_1oD,_1oE));}}else{if(_1oE!=_1oH){if(E(B(_6R(B(_6R(_1oF,_1oE)),_1oU)).a)==32){return B(_1oP(_1oU,_1oE));}else{return B(_1oP(_1oD,_1oE));}}else{return B(_1oP(_1oD,_1oE));}}}}}}break;case 2:if(_1oD<0){return B(_1oP(_1oD,_1oE));}else{if(_1oD>=E(_1nI)){return B(_1oP(_1oD,_1oE));}else{var _1oV=_1oE-1|0;if(_1oV<0){return B(_1oP(_1oD,_1oE));}else{if(_1oV>=E(_1nK)){return B(_1oP(_1oD,_1oE));}else{if(_1oD!=_1oG){if(E(B(_6R(B(_6R(_1oF,_1oV)),_1oD)).a)==32){return B(_1oP(_1oD,_1oV));}else{return B(_1oP(_1oD,_1oE));}}else{if(_1oV!=_1oH){if(E(B(_6R(B(_6R(_1oF,_1oV)),_1oD)).a)==32){return B(_1oP(_1oD,_1oV));}else{return B(_1oP(_1oD,_1oE));}}else{return B(_1oP(_1oD,_1oE));}}}}}}break;case 3:var _1oW=_1oD+1|0;if(_1oW<0){return B(_1oP(_1oD,_1oE));}else{if(_1oW>=E(_1nI)){return B(_1oP(_1oD,_1oE));}else{if(_1oE<0){return B(_1oP(_1oD,_1oE));}else{if(_1oE>=E(_1nK)){return B(_1oP(_1oD,_1oE));}else{if(_1oW!=_1oG){if(E(B(_6R(B(_6R(_1oF,_1oE)),_1oW)).a)==32){return B(_1oP(_1oW,_1oE));}else{return B(_1oP(_1oD,_1oE));}}else{if(_1oE!=_1oH){if(E(B(_6R(B(_6R(_1oF,_1oE)),_1oW)).a)==32){return B(_1oP(_1oW,_1oE));}else{return B(_1oP(_1oD,_1oE));}}else{return B(_1oP(_1oD,_1oE));}}}}}}break;case 4:if(_1oD<0){return B(_1oP(_1oD,_1oE));}else{if(_1oD>=E(_1nI)){return B(_1oP(_1oD,_1oE));}else{var _1oX=_1oE+1|0;if(_1oX<0){return B(_1oP(_1oD,_1oE));}else{if(_1oX>=E(_1nK)){return B(_1oP(_1oD,_1oE));}else{if(_1oD!=_1oG){if(E(B(_6R(B(_6R(_1oF,_1oX)),_1oD)).a)==32){return B(_1oP(_1oD,_1oX));}else{return B(_1oP(_1oD,_1oE));}}else{if(_1oX!=_1oH){if(E(B(_6R(B(_6R(_1oF,_1oX)),_1oD)).a)==32){return B(_1oP(_1oD,_1oX));}else{return B(_1oP(_1oD,_1oE));}}else{return B(_1oP(_1oD,_1oE));}}}}}}break;default:if(_1oD<0){return B(_1oP(_1oD,_1oE));}else{if(_1oD>=E(_1nI)){return B(_1oP(_1oD,_1oE));}else{if(_1oE<0){return B(_1oP(_1oD,_1oE));}else{if(_1oE>=E(_1nK)){return B(_1oP(_1oD,_1oE));}else{if(_1oD!=_1oG){var _1oY=E(B(_6R(B(_6R(_1oF,_1oE)),_1oD)).a);return B(_1oP(_1oD,_1oE));}else{if(_1oE!=_1oH){var _1oZ=E(B(_6R(B(_6R(_1oF,_1oE)),_1oD)).a);return B(_1oP(_1oD,_1oE));}else{return B(_1oP(_1oD,_1oE));}}}}}}}}),_1p0=E(_1oJ);if(!_1p0._){return new F(function(){return _1nL(new T(function(){return E(E(_1oM).b);},1),0,_1oE+1|0,_1oO,_1oG,_1oH,_1oK);});}else{var _1p1=_1oD+1|0,_1p2=_1oE,_1p3=_1oG,_1p4=_1oH,_1p5=_1oK;_1os=new T(function(){return E(E(_1oM).b);},1);_1ot=_1p1;_1ou=_1p2;_1ov=_1oO;_1ow=_1p3;_1ox=_1p4;_1oy=_1p0.a;_1oz=_1p0.b;_1oA=_1p5;return __continue;}}else{var _1p6=E(_1oJ);if(!_1p6._){return new F(function(){return _1nL(_1oC,0,_1oE+1|0,_1oF,_1oG,_1oH,_1oK);});}else{var _1p7=_1oC,_1p1=_1oD+1|0,_1p2=_1oE,_1p8=_1oF,_1p3=_1oG,_1p4=_1oH,_1p5=_1oK;_1os=_1p7;_1ot=_1p1;_1ou=_1p2;_1ov=_1p8;_1ow=_1p3;_1ox=_1p4;_1oy=_1p6.a;_1oz=_1p6.b;_1oA=_1p5;return __continue;}}})(_1os,_1ot,_1ou,_1ov,_1ow,_1ox,_1oy,_1oz,_1oA));if(_1oB!=__continue){return _1oB;}}},_1nH=B(_1nL(_1mM,0,0,_1n4,_1mD,_1mE,_1n4));}var _1p9=function(_1pa){var _1pb=function(_1pc){var _1pd=new T(function(){switch(E(_1mS)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1pe=new T(function(){if(!E(_1n2)){if(!E(_1pd)){return new T2(0,_1mD,_1mE);}else{return new T2(0,_1mF,_1mG);}}else{if(!B(_1gM(_1gY,_1nH,_1n1))){if(!E(_1pd)){return new T2(0,_1mD,_1mE);}else{return new T2(0,_1mF,_1mG);}}else{return new T2(0,_1mF,_1mG);}}}),_1pf=new T(function(){return E(E(_1pe).b);}),_1pg=new T(function(){return E(E(_1pe).a);});if(!E(_1n2)){var _1ph=E(_1mP);}else{var _1ph=E(B(_1jz(new T(function(){return B(_1l0(_1mK,_1mL,_1nH));}),_1nH)).a);}var _1pi=new T(function(){if(!E(_1n0)){if(!E(_1mV)){var _1pj=function(_1pk){var _1pl=function(_1pm){var _1pn=E(_1mS);if(_1pn==4){return new T2(1,_1mA,new T2(1,_1mR,_10));}else{if(!E(_1pd)){return (E(_1pn)==2)?new T2(1,_1my,new T2(1,_1mR,_10)):__Z;}else{var _1po=E(_1mR);return (E(_1po)==61)?new T2(1,_1mz,new T2(1,_1po,new T(function(){return B(_I(0,_1mE,_10));}))):new T2(1,_1mz,new T2(1,_1po,_10));}}};if(!E(_1n2)){return new F(function(){return _1pl(_);});}else{if(E(_1mF)!=E(_1pg)){return new T2(1,_1mB,new T2(1,_1mR,_10));}else{if(E(_1mG)!=E(_1pf)){return new T2(1,_1mB,new T2(1,_1mR,_10));}else{return new F(function(){return _1pl(_);});}}}};if(!E(_1n2)){return B(_1pj(_));}else{if(!E(_1ph)){return B(_1pj(_));}else{return E(_1mu);}}}else{return new T2(1,_1ms,new T2(1,_1mR,_10));}}else{return new T2(1,_1mt,new T2(1,_1mR,_10));}},1);return {_:0,a:new T2(0,_1pg,_1pf),b:_1nH,c:_1pa,d:_1pc,e:_1mK,f:_1mL,g:_1mM,h:B(_y(_1mN,_1pi)),i:_1mO,j:E(_1ph)};};if(!E(_1n0)){return new F(function(){return _1pb(_1mJ);});}else{return new F(function(){return _1pb(E(_1mR));});}};if(!E(_1mV)){return new F(function(){return _1p9(_1mI);});}else{return new F(function(){return _1p9(E(_1mR));});}},_1pp=new T2(1,_5V,_10),_1pq=5,_1pr=new T2(1,_1pq,_10),_1ps=function(_1pt,_1pu){while(1){var _1pv=E(_1pt);if(!_1pv._){return E(_1pu);}else{_1pt=_1pv.b;_1pu=_1pv.a;continue;}}},_1pw=57,_1px=48,_1py=new T2(1,_1k7,_10),_1pz=new T(function(){return B(err(_ss));}),_1pA=new T(function(){return B(err(_sq));}),_1pB=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_1pC=function(_1pD,_1pE){if((_1pE-48|0)>>>0>9){var _1pF=_1pE+_1pD|0,_1pG=function(_1pH){if(!B(_4B(_h7,_1pH,_1py))){return E(_1pH);}else{return new F(function(){return _1pC(_1pD,_1pH);});}};if(_1pF<=122){if(_1pF>=97){if(_1pF>>>0>1114111){return new F(function(){return _wD(_1pF);});}else{return new F(function(){return _1pG(_1pF);});}}else{if(_1pF<=90){if(_1pF>>>0>1114111){return new F(function(){return _wD(_1pF);});}else{return new F(function(){return _1pG(_1pF);});}}else{var _1pI=65+(_1pF-90|0)|0;if(_1pI>>>0>1114111){return new F(function(){return _wD(_1pI);});}else{return new F(function(){return _1pG(_1pI);});}}}}else{var _1pJ=97+(_1pF-122|0)|0;if(_1pJ>>>0>1114111){return new F(function(){return _wD(_1pJ);});}else{return new F(function(){return _1pG(_1pJ);});}}}else{var _1pK=B(_Gc(B(_sx(_1pB,new T2(1,_1pE,_10)))));if(!_1pK._){return E(_1pA);}else{if(!E(_1pK.b)._){var _1pL=E(_1pK.a)+_1pD|0;switch(_1pL){case  -1:return E(_1px);case 10:return E(_1pw);default:return new F(function(){return _1ps(B(_I(0,_1pL,_10)),_SK);});}}else{return E(_1pz);}}}},_1pM=function(_1pN,_1pO){if((_1pN-48|0)>>>0>9){return _1pO;}else{var _1pP=B(_Gc(B(_sx(_1pB,new T2(1,_1pN,_10)))));if(!_1pP._){return E(_1pA);}else{if(!E(_1pP.b)._){return new F(function(){return _1pC(E(_1pP.a),_1pO);});}else{return E(_1pz);}}}},_1pQ=function(_1pR,_1pS){return new F(function(){return _1pM(E(_1pR),E(_1pS));});},_1pT=new T2(1,_1pQ,_10),_1pU=112,_1pV=111,_1pW=function(_1pX,_1pY,_1pZ,_1q0,_1q1,_1q2,_1q3,_1q4,_1q5,_1q6,_1q7){var _1q8=new T(function(){return B(_6R(B(_6R(_1pZ,_1pY)),E(_1pX)));}),_1q9=new T(function(){return E(E(_1q8).b);}),_1qa=new T(function(){if(E(_1q9)==4){return true;}else{return false;}}),_1qb=new T(function(){return E(E(_1q8).a);});if(E(_1q1)==32){var _1qc=false;}else{if(E(_1qb)==32){var _1qd=true;}else{var _1qd=false;}var _1qc=_1qd;}var _1qe=new T(function(){var _1qf=new T(function(){return B(A3(_6R,_1pp,B(_Mk(_h7,_1q0,_1k8)),_1q1));});if(!E(_1qc)){if(!E(_1qa)){return E(_1qb);}else{if(!B(_4B(_3M,_1q2,_1pr))){return E(_1qb);}else{return B(A(_6R,[_1pT,B(_Mk(_3M,_1q2,_1pr)),_1qf,_1qb]));}}}else{return E(_1qf);}}),_1qg=B(_KD(_1pX,_1pY,_1qe,_1q9,_1pZ));if(!E(_1qc)){var _1qh=B(_1jz(new T(function(){return B(_1l0(_1q2,_1q3,_1qg));}),_1qg)).a;return {_:0,a:new T2(0,_1pX,_1pY),b:_1qg,c:_1q0,d:_1q1,e:_1q2,f:_1q3,g:_1q4,h:B(_y(_1q5,new T(function(){if(!E(_1qh)){if(!E(_1qa)){return __Z;}else{return new T2(1,_1pU,new T2(1,_1qe,_10));}}else{return E(_1mu);}},1))),i:_1q6,j:E(_1qh)};}else{var _1qi=B(_1jz(new T(function(){return B(_1l0(_1q2,_1q3,_1qg));}),_1qg)).a;return {_:0,a:new T2(0,_1pX,_1pY),b:_1qg,c:_1q0,d:32,e:_1q2,f:_1q3,g:_1q4,h:B(_y(_1q5,new T(function(){if(!E(_1qi)){return new T2(1,_1pV,new T2(1,_1qe,_10));}else{return E(_1mu);}},1))),i:_1q6,j:E(_1qi)};}},_1qj=new T(function(){return B(_e7("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1qk=function(_1ql,_1qm){while(1){var _1qn=E(_1qm);if(!_1qn._){return false;}else{var _1qo=_1qn.b,_1qp=E(_1ql),_1qq=_1qp.a,_1qr=_1qp.b,_1qs=E(_1qn.a);if(!_1qs._){return E(_1qj);}else{var _1qt=E(_1qs.a),_1qu=_1qt.a,_1qv=_1qt.b,_1qw=E(_1qs.b);if(!_1qw._){var _1qx=E(_1qq),_1qy=E(_1qx);if(_1qy==32){switch(E(_1qr)){case 0:if(!E(_1qv)){return true;}else{_1ql=new T2(0,_1qx,_E8);_1qm=_1qo;continue;}break;case 1:if(E(_1qv)==1){return true;}else{_1ql=new T2(0,_1qx,_Ee);_1qm=_1qo;continue;}break;case 2:if(E(_1qv)==2){return true;}else{_1ql=new T2(0,_1qx,_Ek);_1qm=_1qo;continue;}break;case 3:if(E(_1qv)==3){return true;}else{_1ql=new T2(0,_1qx,_Eq);_1qm=_1qo;continue;}break;case 4:if(E(_1qv)==4){return true;}else{_1ql=new T2(0,_1qx,_Ew);_1qm=_1qo;continue;}break;case 5:if(E(_1qv)==5){return true;}else{_1ql=new T2(0,_1qx,_EX);_1qm=_1qo;continue;}break;case 6:if(E(_1qv)==6){return true;}else{_1ql=new T2(0,_1qx,_EQ);_1qm=_1qo;continue;}break;case 7:if(E(_1qv)==7){return true;}else{_1ql=new T2(0,_1qx,_EJ);_1qm=_1qo;continue;}break;default:if(E(_1qv)==8){return true;}else{_1ql=new T2(0,_1qx,_EC);_1qm=_1qo;continue;}}}else{if(_1qy!=E(_1qu)){_1ql=_1qp;_1qm=_1qo;continue;}else{switch(E(_1qr)){case 0:if(!E(_1qv)){return true;}else{_1ql=new T2(0,_1qx,_E8);_1qm=_1qo;continue;}break;case 1:if(E(_1qv)==1){return true;}else{_1ql=new T2(0,_1qx,_Ee);_1qm=_1qo;continue;}break;case 2:if(E(_1qv)==2){return true;}else{_1ql=new T2(0,_1qx,_Ek);_1qm=_1qo;continue;}break;case 3:if(E(_1qv)==3){return true;}else{_1ql=new T2(0,_1qx,_Eq);_1qm=_1qo;continue;}break;case 4:if(E(_1qv)==4){return true;}else{_1ql=new T2(0,_1qx,_Ew);_1qm=_1qo;continue;}break;case 5:if(E(_1qv)==5){return true;}else{_1ql=new T2(0,_1qx,_EX);_1qm=_1qo;continue;}break;case 6:if(E(_1qv)==6){return true;}else{_1ql=new T2(0,_1qx,_EQ);_1qm=_1qo;continue;}break;case 7:if(E(_1qv)==7){return true;}else{_1ql=new T2(0,_1qx,_EJ);_1qm=_1qo;continue;}break;default:if(E(_1qv)==8){return true;}else{_1ql=new T2(0,_1qx,_EC);_1qm=_1qo;continue;}}}}}else{var _1qz=E(_1qq),_1qA=E(_1qz);if(_1qA==32){switch(E(_1qr)){case 0:if(!E(_1qv)){return true;}else{_1ql=new T2(0,_1qz,_E8);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 1:if(E(_1qv)==1){return true;}else{_1ql=new T2(0,_1qz,_Ee);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 2:if(E(_1qv)==2){return true;}else{_1ql=new T2(0,_1qz,_Ek);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 3:if(E(_1qv)==3){return true;}else{_1ql=new T2(0,_1qz,_Eq);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 4:if(E(_1qv)==4){return true;}else{_1ql=new T2(0,_1qz,_Ew);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 5:if(E(_1qv)==5){return true;}else{_1ql=new T2(0,_1qz,_EX);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 6:if(E(_1qv)==6){return true;}else{_1ql=new T2(0,_1qz,_EQ);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 7:if(E(_1qv)==7){return true;}else{_1ql=new T2(0,_1qz,_EJ);_1qm=new T2(1,_1qw,_1qo);continue;}break;default:if(E(_1qv)==8){return true;}else{_1ql=new T2(0,_1qz,_EC);_1qm=new T2(1,_1qw,_1qo);continue;}}}else{if(_1qA!=E(_1qu)){_1ql=_1qp;_1qm=new T2(1,_1qw,_1qo);continue;}else{switch(E(_1qr)){case 0:if(!E(_1qv)){return true;}else{_1ql=new T2(0,_1qz,_E8);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 1:if(E(_1qv)==1){return true;}else{_1ql=new T2(0,_1qz,_Ee);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 2:if(E(_1qv)==2){return true;}else{_1ql=new T2(0,_1qz,_Ek);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 3:if(E(_1qv)==3){return true;}else{_1ql=new T2(0,_1qz,_Eq);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 4:if(E(_1qv)==4){return true;}else{_1ql=new T2(0,_1qz,_Ew);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 5:if(E(_1qv)==5){return true;}else{_1ql=new T2(0,_1qz,_EX);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 6:if(E(_1qv)==6){return true;}else{_1ql=new T2(0,_1qz,_EQ);_1qm=new T2(1,_1qw,_1qo);continue;}break;case 7:if(E(_1qv)==7){return true;}else{_1ql=new T2(0,_1qz,_EJ);_1qm=new T2(1,_1qw,_1qo);continue;}break;default:if(E(_1qv)==8){return true;}else{_1ql=new T2(0,_1qz,_EC);_1qm=new T2(1,_1qw,_1qo);continue;}}}}}}}}},_1qB=function(_1qC,_1qD){var _1qE=E(_1qC);if(!_1qE._){return __Z;}else{var _1qF=E(_1qD);return (_1qF._==0)?__Z:new T2(1,new T(function(){return new T2(0,new T2(1,_1qF.a,_1fZ),E(_1qE.a).b);}),new T(function(){return B(_1qB(_1qE.b,_1qF.b));}));}},_1qG=new T(function(){return B(unCStr("\n"));}),_1qH=function(_1qI,_1qJ,_){var _1qK=jsWriteHandle(E(_1qI),toJSStr(E(_1qJ)));return _gE;},_1qL=function(_1qM,_1qN,_){var _1qO=E(_1qM),_1qP=jsWriteHandle(_1qO,toJSStr(E(_1qN)));return new F(function(){return _1qH(_1qO,_1qG,_);});},_1qQ=function(_1qR){var _1qS=E(_1qR);if(!_1qS._){return __Z;}else{return new F(function(){return _y(_1qS.a,new T(function(){return B(_1qQ(_1qS.b));},1));});}},_1qT=0,_1qU= -1,_1qV= -2,_1qW=new T(function(){return B(unCStr("removed"));}),_1qX=new T(function(){return B(unCStr("loadError"));}),_1qY=new T(function(){return B(unCStr("saved"));}),_1qZ=new T(function(){var _1r0=E(_1aD);if(!_1r0._){return E(_nh);}else{return E(_1r0.a);}}),_1r1=new T(function(){return B(_17q(_1ab,5,_1b6));}),_1r2=new T(function(){return B(unCStr("Thank you for playing!"));}),_1r3=17,_1r4=2,_1r5=new T(function(){return B(unCStr("Test Play : takaPon"));}),_1r6=10,_1r7=3,_1r8=new T(function(){return B(unCStr("Coding : yokoP"));}),_1r9=8,_1ra=new T(function(){return B(unCStr("Congratulations!"));}),_1rb=5,_1rc=32,_1rd=new T2(0,_1rc,_EX),_1re=99,_1rf=64,_1rg=new T(function(){return B(_mt(_1bv,0));}),_1rh=new T(function(){return B(_6R(_j4,1));}),_1ri=new T(function(){return B(_6R(_j4,2));}),_1rj=new T(function(){return B(unCStr("loadError"));}),_1rk=new T(function(){return B(unCStr(","));}),_1rl=new T(function(){return B(unCStr("~"));}),_1rm=new T(function(){return B(unCStr("savedata"));}),_1rn=new T(function(){return B(unCStr("---"));}),_1ro=0,_1rp=new T1(0,333),_1rq=new T(function(){return B(_8s(1,2147483647));}),_1rr=new T(function(){return B(unCStr("choice"));}),_1rs=new T2(1,_6D,_10),_1rt=new T(function(){return B(_8k(_1rr,_1rs));}),_1ru=new T2(1,_6D,_1rt),_1rv=new T(function(){return B(unAppCStr("[]",_10));}),_1rw=new T(function(){return B(unCStr("\""));}),_1rx=new T2(1,_10,_10),_1ry=new T(function(){return B(_6e(_YC,_1rx));}),_1rz=new T2(1,_6D,_10),_1rA=function(_1rB){return E(_1rB).c;},_1rC=function(_1rD,_1rE){var _1rF=E(_1rE);return (_1rF._==0)?__Z:new T2(1,_1rD,new T2(1,_1rF.a,new T(function(){return B(_1rC(_1rD,_1rF.b));})));},_1rG=new T(function(){return B(unCStr("noContent"));}),_1rH=new T(function(){return B(unCStr("noHint"));}),_1rI=new T(function(){return B(err(_ss));}),_1rJ=new T(function(){return B(err(_sq));}),_1rK=new T(function(){return B(A3(_FA,_G3,_DD,_Fq));}),_1rL=function(_1rM,_1rN){var _1rO=E(_1rN);if(!_1rO._){var _1rP=B(_Gc(B(_sx(_1rK,_1rM))));return (_1rP._==0)?E(_1rJ):(E(_1rP.b)._==0)?new T4(0,E(_1rP.a),_10,_10,_10):E(_1rI);}else{var _1rQ=_1rO.a,_1rR=E(_1rO.b);if(!_1rR._){var _1rS=B(_Gc(B(_sx(_1rK,_1rM))));return (_1rS._==0)?E(_1rJ):(E(_1rS.b)._==0)?new T4(0,E(_1rS.a),E(_1rQ),E(_1rH),E(_1rG)):E(_1rI);}else{var _1rT=_1rR.a,_1rU=E(_1rR.b);if(!_1rU._){var _1rV=B(_Gc(B(_sx(_1rK,_1rM))));return (_1rV._==0)?E(_1rJ):(E(_1rV.b)._==0)?new T4(0,E(_1rV.a),E(_1rQ),E(_1rT),E(_1rG)):E(_1rI);}else{if(!E(_1rU.b)._){var _1rW=B(_Gc(B(_sx(_1rK,_1rM))));return (_1rW._==0)?E(_1rJ):(E(_1rW.b)._==0)?new T4(0,E(_1rW.a),E(_1rQ),E(_1rT),E(_1rU.a)):E(_1rI);}else{return new T4(0,0,_10,_10,_10);}}}}},_1rX=function(_1rY){var _1rZ=E(_1rY);if(!_1rZ._){return new F(function(){return _1rL(_10,_10);});}else{var _1s0=_1rZ.a,_1s1=E(_1rZ.b);if(!_1s1._){return new F(function(){return _1rL(new T2(1,_1s0,_10),_10);});}else{var _1s2=E(_1s0),_1s3=new T(function(){var _1s4=B(_H4(44,_1s1.a,_1s1.b));return new T2(0,_1s4.a,_1s4.b);});if(E(_1s2)==44){return new F(function(){return _1rL(_10,new T2(1,new T(function(){return E(E(_1s3).a);}),new T(function(){return E(E(_1s3).b);})));});}else{var _1s5=E(_1s3);return new F(function(){return _1rL(new T2(1,_1s2,_1s5.a),_1s5.b);});}}}},_1s6=function(_1s7){var _1s8=B(_1rX(_1s7));return new T4(0,_1s8.a,E(_1s8.b),E(_1s8.c),E(_1s8.d));},_1s9=function(_1sa){return (E(_1sa)==10)?true:false;},_1sb=function(_1sc){var _1sd=E(_1sc);if(!_1sd._){return __Z;}else{var _1se=new T(function(){var _1sf=B(_17T(_1s9,_1sd));return new T2(0,_1sf.a,new T(function(){var _1sg=E(_1sf.b);if(!_1sg._){return __Z;}else{return B(_1sb(_1sg.b));}}));});return new T2(1,new T(function(){return E(E(_1se).a);}),new T(function(){return E(E(_1se).b);}));}},_1sh=new T(function(){return B(unCStr("57,\u5974\u56fd\u738b\u304c\u5f8c\u6f22\u304b\u3089\u91d1\u5370,\u300c\u5f8c\u6f22\u66f8\u300d\u306b\u8a18\u8f09\u304c\u3042\u308a \u6c5f\u6238\u671f\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\u5ca1\u770c\u5fd7\u8cc0\u5cf6\u306b\u3066\u300c\u6f22\u59d4\u5974\u570b\u738b\u300d\u3068\u523b\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\u898b\u3055\u308c\u308b**\u5927\u548c\u671d\u5ef7\u3068\u306e\u95dc\u4fc2\u306f\u4e0d\u660e\n239,\u300c\u5351\u5f25\u547c\u300d\u304c\u9b4f\u306b\u9063\u4f7f,\u652f\u90a3\u306e\u6b74\u53f2\u66f8\u300c\u9b4f\u5fd7\u300d\u306b\u8a18\u8f09\u3055\u308c\u3066\u3090\u308b\u5deb\u5973,\u300c\u9b4f\u5fd7\u300d\u502d\u4eba\u4f1d\u306b\u8a18\u3055\u308c\u3066\u3090\u308b\u300c\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)\u300d\u3082\u300c\u5351\u5f25\u547c\u300d\u3082\u65e5\u672c\u306b\u6b98\u308b\u8cc7\u6599\u3067\u306f\u4e00\u5207\u78ba\u8a8d\u3067\u304d\u306a\u3044\n316,\u4ec1\u5fb3\u5929\u7687 \u7a0e\u3092\u514d\u9664,\u300c\u53e4\u4e8b\u8a18\u300d\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u8a18\u8f09\u304c\u3042\u308b,16\u4ee3\u4ec1\u5fb3\u5929\u7687\u304c\u300c\u6c11\u306e\u304b\u307e\u3069\u3088\u308a\u7159\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\u3057\u304f\u3066\u708a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b\u300d\u3068\u3057\u3066 \u5bae\u4e2d\u306e\u4fee\u7e55\u3092\u5f8c\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\u304b\u306b\u3059\u308b\u8a71\u304c\u300c\u65e5\u672c\u66f8\u7d00\u300d\u306b\u3042\u308b\n478,\u300c\u502d\u300d\u306e\u6b66\u738b \u5357\u671d\u306e\u5b8b\u3078\u9063\u4f7f,\u96c4\u7565\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\u8aac,\u300c\u5b8b\u66f8\u300d\u502d\u570b\u50b3\u306b\u8a18\u8f09\u304c\u3042\u308b**\u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\u6559\u516c\u4f1d,\u6b3d\u660e\u5929\u7687\u5fa1\u4ee3\u306b\u767e\u6e08\u306e\u8056\u660e\u738b\u304b\u3089\u4f1d\u6765\u3057\u305f\u3068\u306e\u6587\u732e\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\u8aac\u3042\u308b\n604,\u5341\u4e03\u6761\u61b2\u6cd5\u5236\u5b9a,\u8056\u5fb3\u592a\u5b50\u304c\u5236\u5b9a\u3057\u305f\u3068\u3055\u308c\u308b,\u300c\u548c\u3092\u4ee5\u3066\u8cb4\u3057\u3068\u70ba\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\u304d\u3092\u5b97\u3068\u305b\u3088\u300d\n607,\u6cd5\u9686\u5bfa\u304c\u5275\u5efa\u3055\u308c\u308b,\u8056\u5fb3\u592a\u5b50\u3086\u304b\u308a\u306e\u5bfa\u9662,\u897f\u9662\u4f3d\u85cd\u306f\u73fe\u5b58\u3059\u308b\u4e16\u754c\u6700\u53e4\u306e\u6728\u9020\u5efa\u7bc9\u7269\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\u5df3\u306e\u5909,\u3053\u306e\u5f8c\u3059\u3050\u5927\u5316\u306e\u6539\u65b0\u306a\u308b,\u4e2d\u5927\u5144\u7687\u5b50(\u5f8c\u306e38\u4ee3\u5929\u667a\u5929\u7687)\u304c\u8607\u6211\u6c0f\u3092\u4ea1\u307c\u3059\n663,\u767d\u6751\u6c5f\u306e\u6226,\u5510\u3068\u65b0\u7f85\u306b\u6ec5\u307c\u3055\u308c\u305f\u767e\u6e08\u3092\u518d\u8208\u3059\u308b\u76ee\u7684,\u5510\u30fb\u65b0\u7f85\u9023\u5408\u8ecd\u306b\u6557\u308c\u308b\n672,\u58ec\u7533\u306e\u4e71,\u5929\u667a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\u7d99\u8005\u4e89\u3072,\u5f8c\u7d99\u8005\u3067\u3042\u3063\u305f\u5927\u53cb\u7687\u5b50\u306b\u53d4\u7236\u306e\u5927\u6d77\u4eba\u7687\u5b50\u304c\u53cd\u65d7\u3092\u7ffb\u3057 \u5927\u53cb\u7687\u5b50\u3092\u5012\u3057\u3066\u5929\u6b66\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\u57ce\u4eac\u9077\u90fd,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f\u300c\u306a\u3089\u300d\u3068\u3082\u8b80\u3080,\u548c\u92853\u5e74 \u7b2c43\u4ee3\u5143\u660e\u5929\u7687\u306b\u3088\u308b \u5148\u4ee3\u306e\u6587\u6b66\u5929\u7687\u304c\u75ab\u75c5\u3067\u5d29\u5fa1\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\u5b89\u4eac\u9077\u90fd,\u5ef6\u66a613\u5e74 \u7b2c50\u4ee3\u6853\u6b66\u5929\u7687 \u9577\u5ca1\u4eac\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\u6e05\u76db\u306b\u3088\u308b\u798f\u539f\u4eac\u9077\u90fd\u3084\u5357\u5317\u671d\u6642\u4ee3\u306e\u5409\u91ce\u306a\u3069\u306e\u4f8b\u5916\u306f\u3042\u308b\u3082\u306e\u306e \u660e\u6cbb\u7dad\u65b0\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\u304f\n806,\u6700\u6f84\u304c\u5929\u53f0\u5b97 \u7a7a\u6d77\u304c\u771f\u8a00\u5b97,\u5e73\u5b89\u6642\u4ee3\u521d\u671f \u3069\u3061\u3089\u3082\u5510\u3067\u4fee\u884c\u3057\u5e30\u570b\u5f8c \u4ecf\u6559\u3092\u50b3\u3078\u308b,\u6700\u6f84\u306f\u5929\u53f0\u5b97\u3092\u958b\u304d \u6bd4\u53e1\u5c71\u306b\u5ef6\u66a6\u5bfa\u3092 \u7a7a\u6d77\u306f\u771f\u8a00\u5b97\u3092\u958b\u304d \u9ad8\u91ce\u5c71\u306b\u91d1\u525b\u5cf0\u5bfa\u3092\u5efa\u7acb\n857,\u85e4\u539f\u826f\u623f\u304c\u592a\u653f\u5927\u81e3\u306b,56\u4ee3\u6e05\u548c\u5929\u7687\u306e\u6442\u653f,\u81e3\u4e0b\u306e\u8eab\u5206\u3067\u521d\u3081\u3066\u6442\u653f\u306b\u306a\u3063\u305f\n894,\u9063\u5510\u4f7f\u304c\u5ec3\u6b62\u3055\u308c\u308b,\u83c5\u539f\u9053\u771f\u306e\u5efa\u8b70\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\u306f\u6ec5\u3073\u5c0f\u56fd\u304c\u5206\u7acb\u3057\u305f\u5f8c \u5b8b(\u5317\u5b8b)\u304c\u652f\u90a3\u5927\u9678\u3092\u7d71\u4e00\u3059\u308b\n935,\u627f\u5e73\u5929\u6176\u306e\u4e71,\u5e73\u5c06\u9580\u3084\u85e4\u539f\u7d14\u53cb\u3068\u3044\u3064\u305f\u6b66\u58eb\u306e\u53cd\u4e71,\u6442\u95a2\u653f\u6cbb\u3078\u306e\u4e0d\u6e80\u304c\u6839\u5e95\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\u539f\u9053\u9577\u304c\u6442\u653f\u306b,\u85e4\u539f\u6c0f\u5168\u76db\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\u9577\u306f\u9577\u5973\u3092\u4e00\u6761\u5929\u7687(66\u4ee3)\u306e\u540e\u306b \u6b21\u5973\u3092\u4e09\u6761\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\u5973\u3092\u5f8c\u4e00\u6761\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\u653f\u958b\u59cb,\u6442\u653f\u3084\u95a2\u767d\u306e\u529b\u3092\u6291\u3078\u308b,72\u4ee3\u767d\u6cb3\u5929\u7687\u304c\u8b72\u4f4d\u5f8c \u4e0a\u7687\u3068\u306a\u308a \u653f\u6cbb\u306e\u5b9f\u6a29\u3092\u63e1\u308b\n1167,\u5e73\u6e05\u76db\u304c\u592a\u653f\u5927\u81e3\u306b,\u5a18\u3092\u5929\u7687\u306e\u540e\u306b\u3057 81\u4ee3\u5b89\u5fb3\u5929\u7687\u304c\u8a95\u751f,\u6b66\u58eb\u3068\u3057\u3066\u521d\u3081\u3066\u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c\u308b\n1185,\u5e73\u5bb6\u6ec5\u4ea1,\u58c7\u30ce\u6d66\u306e\u6230\u3072,\u6e90\u983c\u671d\u306e\u547d\u3092\u53d7\u3051\u305f \u5f1f\u306e\u7fa9\u7d4c\u3089\u306e\u6d3b\u8e8d\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\u5fb3\u5929\u7687\u306f\u6578\u3078\u5e74\u4e03\u6b73\u3067\u5165\u6c34\u3057\u5d29\u5fa1\u3055\u308c\u308b\n1192,\u6e90\u983c\u671d\u304c\u5f81\u5937\u5927\u5c06\u8ecd\u306b,\u6b66\u5bb6\u653f\u6a29\u304c\u672c\u683c\u7684\u306b\u59cb\u307e\u308b,\u938c\u5009\u5e55\u5e9c\u6210\u7acb\n1221,\u627f\u4e45\u306e\u5909,\u5168\u56fd\u306e\u6b66\u58eb\u306b \u57f7\u6a29\u5317\u6761\u7fa9\u6642\u306e\u8a0e\u4f10\u3092\u547d\u305a\u308b\u5f8c\u9ce5\u7fbd\u4e0a\u7687\u306e\u9662\u5ba3\u304c\u767c\u305b\u3089\u308c\u308b,\u4eac\u90fd\u306f\u5e55\u5e9c\u8ecd\u306b\u5360\u9818\u3055\u308c \u5931\u6557\n1274,\u6587\u6c38\u306e\u5f79,1281\u5e74\u306e\u5f18\u5b89\u306e\u5f79\u3068\u5408\u306f\u305b\u3066 \u5143\u5bc7\u3068\u547c\u3076,\u7d04\u4e09\u4e07\u306e\u5143\u8ecd\u304c\u7d04900\u96bb\u306e\u8ecd\u8239\u3067\u5317\u4e5d\u5dde\u3078\u9032\u653b\u3059\u308b\u3082\u65e5\u672c\u8ecd\u306b\u6483\u9000\u3055\u308c\u308b\n1334,\u5efa\u6b66\u306e\u65b0\u653f,\u5f8c\u918d\u9190\u5929\u7687\u304c\u938c\u5009\u5e55\u5e9c\u3092\u5012\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\u6cbb\u3092\u5fd7\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\u53cd\u3057 \u5f8c\u918d\u9190\u5929\u7687\u306f\u5409\u91ce\u306b\u9003\u308c \u5357\u671d\u3092\u958b\u304d \u8db3\u5229\u5c0a\u6c0f\u306f\u5149\u660e\u5929\u7687\u3092\u64c1\u3057\u305f\u5317\u671d\u3092\u958b\u304f\n1338,\u5ba4\u753a\u5e55\u5e9c\u6210\u7acb,\u8db3\u5229\u5c0a\u6c0f\u304c\u5317\u671d\u306e\u5149\u660e\u5929\u7687\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\u7acb,\u8db3\u5229\u7fa9\u6e80(3\u4ee3)\u304c\u4eac\u90fd\u306e\u5ba4\u753a\u306b\u300c\u82b1\u306e\u5fa1\u6240\u300d\u3092\u69cb\u3078\u653f\u6cbb\u3092\u884c\u3063\u305f\u3053\u3068\u304b\u3089\u300c\u5ba4\u753a\u5e55\u5e9c\u300d\u3068\u79f0\u3055\u308c\u308b\n1429,\u7409\u7403\u7d71\u4e00,\u4e09\u3064\u306e\u52e2\u529b\u304c\u5341\u4e94\u4e16\u7d00\u306b\u7d71\u4e00\u3055\u308c\u308b,\u660e\u306e\u518a\u5c01\u3092\u53d7\u3051 \u671d\u8ca2\u8cbf\u6613\u3092\u884c\u3075\n1467,\u5fdc\u4ec1\u306e\u4e71,\u6226\u56fd\u6642\u4ee3\u306e\u5e55\u958b\u3051,\u5c06\u8ecd\u5bb6\u3068\u7ba1\u9818\u5bb6\u306e\u8de1\u7d99\u304e\u4e89\u3072\u304c11\u5e74\u7e8c\u304d\u4eac\u90fd\u306e\u753a\u306f\u7126\u571f\u3068\u5316\u3059\n1495,\u5317\u6761\u65e9\u96f2\u304c\u5c0f\u7530\u539f\u5165\u57ce,\u5317\u6761\u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5148\u99c6\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\u7a0b\u306f \u5bb6\u81e3\u304c\u4e3b\u541b\u304b\u3089\u6a29\u529b\u3092\u596a\u3063\u3066\u306e\u3057\u4e0a\u308b\u3068\u3044\u3075\u300c\u4e0b\u524b\u4e0a\u300d\u3067\u3042\u308a \u65e9\u96f2\u306f\u6226\u56fd\u5927\u540d\u306e\u5686\u77e2\u3068\u3044\u3078\u308b\n1542,\u658e\u85e4\u9053\u4e09\u304c\u7f8e\u6fc3\u3092\u596a\u3046,\u6226\u56fd\u6b66\u5c06\u306e\u4e00,\u4ed6\u306b\u3082\u95a2\u6771\u4e00\u5186\u3092\u652f\u914d\u3057\u305f\u5317\u6761\u6c0f\u5eb7 \u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384 \u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1 \u51fa\u7fbd\u3068\u9678\u5965\u306e\u4f0a\u9054\u6b63\u5b97 \u5b89\u82b8\u306e\u6bdb\u5229\u5143\u5c31 \u571f\u4f50\u306e\u9577\u5b97\u6211\u90e8\u5143\u89aa \u85a9\u6469\u306e\u5cf6\u6d25\u8cb4\u4e45\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\u4e2d\u5cf6\u306e\u6226\u3044,\u7532\u6590\u306e\u6b66\u7530\u4fe1\u7384\u3068\u8d8a\u5f8c\u306e\u4e0a\u6749\u8b19\u4fe1,\u6226\u56fd\u6642\u4ee3\u306e\u975e\u5e38\u306b\u6709\u540d\u306a\u6230\u3072\u3067\u52dd\u6557\u306f\u8af8\u8aac\u3042\u308b\u3082\u5b9a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\u72ed\u9593\u306e\u6226\u3044,\u5c3e\u5f35\u306e\u7e54\u7530\u4fe1\u9577\u304c\u99ff\u6cb3\u306e\u4eca\u5ddd\u7fa9\u5143\u3092\u7834\u308b,\u4fe1\u9577\u306f\u5c3e\u5f35\u3068\u7f8e\u6fc3\u3092\u652f\u914d\u4e0b\u306b\u304a\u304d \u300c\u5929\u4e0b\u5e03\u6b66\u300d\u3092\u304b\u304b\u3052 \u5f8c\u306b\u8db3\u5229\u7fa9\u662d\u3092\u4eac\u90fd\u304b\u3089\u8ffd\u653e\u3057\u3066\u5ba4\u753a\u5e55\u5e9c\u3092\u6ec5\u4ea1\u3055\u305b\u308b\n1590,\u8c4a\u81e3\u79c0\u5409\u306e\u5929\u4e0b\u7d71\u4e00,106\u4ee3\u6b63\u89aa\u753a\u5929\u7687\u304b\u3089\u95a2\u767d\u306e\u4f4d\u3092\u6388\u3051\u3089\u308c \u5929\u4e0b\u7d71\u4e00\u3078\u306e\u5f8c\u62bc\u3057\u3092\u3082\u3089\u3075,\u60e3\u7121\u4e8b\u4ee4\u3092\u51fa\u3057\u3066\u5927\u540d\u9593\u306e\u79c1\u95d8\u3092\u7981\u3058 \u5929\u7687\u3088\u308a\u8c4a\u81e3\u306e\u59d3\u3092\u8cdc\u306f\u308a \u592a\u653f\u5927\u81e3\u306b\u4efb\u547d\u3055\u308c \u5cf6\u6d25\u7fa9\u4e45 \u5317\u6761\u6c0f\u653f \u4f0a\u9054\u653f\u5b97\u3089\u8af8\u5927\u540d\u3092\u5e73\u5b9a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\u7984\u306e\u5f79,\u79c0\u5409\u306e\u671d\u9bae\u51fa\u5175,\u4e8c\u5ea6\u76ee\u306e\u6176\u9577\u306e\u5f79\u3067\u79c0\u5409\u304c\u6ca1\u3057 \u65e5\u672c\u8ecd\u306f\u671d\u9bae\u304b\u3089\u64a4\u9000\n1600,\u95a2\u30f6\u539f\u306e\u6226\u3044,\u3053\u306e\u6230\u3072\u306b\u52dd\u5229\u3057\u305f\u5fb3\u5ddd\u5bb6\u5eb7\u304c \u5f8c\u967d\u6210\u5929\u7687\u306b\u3088\u308a\u5f81\u5937\u5927\u5c06\u8ecd\u306b\u4efb\u547d\u3055\u308c \u6c5f\u6238\u5e55\u5e9c\u304c\u6210\u7acb\n1637,\u5cf6\u539f\u306e\u4e71,\u3044\u306f\u3086\u308b\u300c\u9396\u56fd\u300d\u653f\u7b56\u306e\u5f15\u304d\u91d1\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u3089\u304c\u5bfa\u793e\u306b\u653e\u706b\u3057\u50e7\u4fb6\u3092\u6bba\u5bb3\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\u5e9c\u306f\u5927\u8ecd\u3092\u9001\u308a\u93ae\u5727\u3059\u308b\n1685,\u751f\u985e\u6190\u307f\u306e\u4ee4,\u4e94\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u7db1\u5409,\u75c5\u4eba\u907a\u68c4\u3084\u6368\u3066\u5b50\u3092\u7981\u6b62 \u4eba\u9593\u4ee5\u5916\u306e\u3042\u3089\u3086\u308b\u751f\u7269\u3078\u306e\u8650\u5f85\u3084\u6bba\u751f\u3092\u3082\u7f70\u3059\u308b\u3053\u3068\u3067 \u9053\u5fb3\u5fc3\u3092\u559a\u8d77\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\u4fdd\u306e\u6539\u9769,\u516b\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5409\u5b97,\u8cea\u7d20\u5039\u7d04 \u7c73\u306e\u5897\u53ce \u516c\u4e8b\u65b9\u5fa1\u5b9a\u66f8 \u5b9f\u5b66\u306e\u5968\u52b1 \u76ee\u5b89\u7bb1\u306a\u3069\n1767,\u7530\u6cbc\u610f\u6b21\u306e\u653f\u6cbb,\u4ee3\u5341\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6cbb\u306e\u6642\u4ee3,\u682a\u4ef2\u9593\u3092\u516c\u8a8d \u7a0e\u5236\u6539\u9769 \u7d4c\u6e08\u3092\u6d3b\u6027\u5316\u3055\u305b\u308b\n1787,\u5bdb\u653f\u306e\u6539\u9769,\u5341\u4e00\u4ee3\u5c06\u8ecd \u5fb3\u5ddd\u5bb6\u6589\u304c \u767d\u6cb3\u85e9\u4e3b \u677e\u5e73\u5b9a\u4fe1\u3092\u767b\u7528,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\u91d1\u306e\u5e33\u6d88\u3057 \u8fb2\u6c11\u306e\u5e30\u90f7\u3092\u4fc3\u3059 \u6e6f\u5cf6\u306b\u660c\u5e73\u5742\u5b66\u554f\u6240\u3092\u3064\u304f\u308a\u5b78\u554f\u30fb\u6b66\u8853\u3092\u5968\u52b1 \u53b3\u3057\u3044\u7dca\u7e2e\u8ca1\u653f\u3067\u7d4c\u6e08\u306f\u505c\u6ede\n1837,\u5927\u5869\u5e73\u516b\u90ce\u306e\u4e71,\u5929\u4fdd\u306e\u98e2\u9949\u304c\u6839\u672c\u539f\u56e0\u306e\u3072\u3068\u3064,\u5e55\u5e9c\u306e\u5143\u5f79\u4eba\u306e\u53cd\u4e71\u306f\u5e55\u5e9c\u306b\u885d\u6483\u3092\u4e0e\u3078\u308b\n1854,\u65e5\u7c73\u548c\u89aa\u6761\u7d04,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\u8cc0\u306b\u8ecd\u8266\u56db\u96bb\u3067\u6765\u822a,\u4e0b\u7530(\u9759\u5ca1\u770c)\u30fb\u7bb1\u9928(\u5317\u6d77\u9053)\u306e\u4e8c\u6e2f\u3092\u958b\u304f\n1860,\u685c\u7530\u9580\u5916\u306e\u5909,121\u4ee3\u5b5d\u660e\u5929\u7687\u306e\u52c5\u8a31\u3092\u5f97\u305a \u65e5\u7c73\u4fee\u4ea4\u901a\u5546\u6761\u7d04\u3092\u7d50\u3093\u3060 \u3068\u3044\u3075\u6279\u5224\u306b \u4e95\u4f0a\u76f4\u5f3c\u304c \u5b89\u653f\u306e\u5927\u7344\u3067\u591a\u304f\u306e\u5fd7\u58eb\u3092\u51e6\u5211\u3057\u305f\u3053\u3068\u304c\u539f\u56e0\u3068\u3055\u308c\u308b,\u4e95\u4f0a\u76f4\u5f3c\u304c\u6c34\u6238\u85e9\u306e\u6d6a\u58eb\u3089\u306b\u6697\u6bba\u3055\u308c\u308b\n1868,\u660e\u6cbb\u7dad\u65b0,\u524d\u5e74\u306e\u5927\u653f\u5949\u9084\u3092\u53d7\u3051 \u671d\u5ef7\u304c\u300c\u738b\u653f\u5fa9\u53e4\u306e\u5927\u53f7\u4ee4\u300d\u3092\u51fa\u3059,\u660e\u6cbb\u5929\u7687\u304c \u4e94\u7b87\u6761\u306e\u5fa1\u8a93\u6587\u3092\u767a\u5e03\u3055\u308c\u308b\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1931,\u6e80\u6d32\u4e8b\u5909\n1937,\u652f\u90a3\u4e8b\u5909\n1941,\u5927\u6771\u4e9c\u6226\u4e89\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\u8a00\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\u548c\u6761\u7d04"));}),_1si=new T(function(){return B(_1sb(_1sh));}),_1sj=new T(function(){return B(_6e(_1s6,_1si));}),_1sk=new T(function(){return B(_8P(1,2));}),_1sl=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b\u300c\u4e0d\u5e73\u7b49\u300d\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,\u300c\u6276\u6e05\u6ec5\u6d0b\u300d\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***\u300c\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287\u300d\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b\u300c\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42\u300d,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059\u300d\u30fc\u30fc\u5f8c\u6bb5\u306f\u300c\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059\u300d"));}),_1sm=new T(function(){return B(_1sb(_1sl));}),_1sn=new T(function(){return B(_6e(_1s6,_1sm));}),_1so=function(_1sp,_1sq){var _1sr=E(_1sp);if(!_1sr._){return __Z;}else{var _1ss=E(_1sq);return (_1ss._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1sr.a).a;}),_1ss.a),new T(function(){return B(_1so(_1sr.b,_1ss.b));}));}},_1st=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1su=new T(function(){return B(unCStr("tail"));}),_1sv=new T(function(){return B(_ne(_1su));}),_1sw=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1sx=new T2(1,_2B,_10),_1sy=function(_1sz,_1sA){return new T2(1,_6D,new T(function(){return B(_8k(_1sz,new T2(1,_6D,_1sA)));}));},_1sB=function(_1sC){var _1sD=E(_1sC);if(!_1sD._){return E(_1sx);}else{var _1sE=new T(function(){var _1sF=E(_1sD.a),_1sG=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1sH){return new F(function(){return _1sy(_1sF.a,_1sH);});},new T2(1,function(_1sI){return new F(function(){return _1sy(_1sF.b,_1sI);});},_10)),new T2(1,_G,new T(function(){return B(_1sB(_1sD.b));}))));});return new T2(1,_H,_1sG);});return new T2(1,_2A,_1sE);}},_1sJ=function(_1sK){var _1sL=E(_1sK);if(!_1sL._){return E(_1sx);}else{var _1sM=new T(function(){return B(_I(0,E(_1sL.a),new T(function(){return B(_1sJ(_1sL.b));})));});return new T2(1,_2A,_1sM);}},_1sN=function(_1sO){var _1sP=E(_1sO);if(!_1sP._){return E(_1sx);}else{var _1sQ=new T(function(){var _1sR=E(_1sP.a),_1sS=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1sT){return new F(function(){return _1sy(_1sR.a,_1sT);});},new T2(1,function(_1sU){return new F(function(){return _1sy(_1sR.b,_1sU);});},_10)),new T2(1,_G,new T(function(){return B(_1sN(_1sP.b));}))));});return new T2(1,_H,_1sS);});return new T2(1,_2A,_1sQ);}},_1sV=new T(function(){return B(unCStr("True"));}),_1sW=new T(function(){return B(unCStr("False"));}),_1sX=function(_1sY){return E(E(_1sY).b);},_1sZ=function(_1t0,_1t1,_1t2){var _1t3=new T(function(){var _1t4=E(_1t2);if(!_1t4._){return __Z;}else{var _1t5=_1t4.b,_1t6=E(_1t4.a),_1t7=E(_1t6.a);if(_1t7<_1t0){var _1t8=function(_1t9){while(1){var _1ta=B((function(_1tb){var _1tc=E(_1tb);if(!_1tc._){return __Z;}else{var _1td=_1tc.b,_1te=E(_1tc.a);if(E(_1te.a)<_1t0){_1t9=_1td;return __continue;}else{return new T2(1,_1te,new T(function(){return B(_1t8(_1td));}));}}})(_1t9));if(_1ta!=__continue){return _1ta;}}};return B(_1tf(B(_1t8(_1t5))));}else{var _1tg=new T(function(){var _1th=function(_1ti){while(1){var _1tj=B((function(_1tk){var _1tl=E(_1tk);if(!_1tl._){return __Z;}else{var _1tm=_1tl.b,_1tn=E(_1tl.a);if(E(_1tn.a)<_1t0){_1ti=_1tm;return __continue;}else{return new T2(1,_1tn,new T(function(){return B(_1th(_1tm));}));}}})(_1ti));if(_1tj!=__continue){return _1tj;}}};return B(_1th(_1t5));});return B(_1sZ(_1t7,_1t6.b,_1tg));}}}),_1to=E(_1t2);if(!_1to._){return new F(function(){return _y(_10,new T2(1,new T2(0,_1t0,_1t1),_1t3));});}else{var _1tp=_1to.b,_1tq=E(_1to.a),_1tr=E(_1tq.a);if(_1tr>=_1t0){var _1ts=function(_1tt){while(1){var _1tu=B((function(_1tv){var _1tw=E(_1tv);if(!_1tw._){return __Z;}else{var _1tx=_1tw.b,_1ty=E(_1tw.a);if(E(_1ty.a)>=_1t0){_1tt=_1tx;return __continue;}else{return new T2(1,_1ty,new T(function(){return B(_1ts(_1tx));}));}}})(_1tt));if(_1tu!=__continue){return _1tu;}}};return new F(function(){return _y(B(_1tf(B(_1ts(_1tp)))),new T2(1,new T2(0,_1t0,_1t1),_1t3));});}else{var _1tz=new T(function(){var _1tA=function(_1tB){while(1){var _1tC=B((function(_1tD){var _1tE=E(_1tD);if(!_1tE._){return __Z;}else{var _1tF=_1tE.b,_1tG=E(_1tE.a);if(E(_1tG.a)>=_1t0){_1tB=_1tF;return __continue;}else{return new T2(1,_1tG,new T(function(){return B(_1tA(_1tF));}));}}})(_1tB));if(_1tC!=__continue){return _1tC;}}};return B(_1tA(_1tp));});return new F(function(){return _y(B(_1sZ(_1tr,_1tq.b,_1tz)),new T2(1,new T2(0,_1t0,_1t1),_1t3));});}}},_1tf=function(_1tH){var _1tI=E(_1tH);if(!_1tI._){return __Z;}else{var _1tJ=_1tI.b,_1tK=E(_1tI.a),_1tL=_1tK.a,_1tM=new T(function(){var _1tN=E(_1tJ);if(!_1tN._){return __Z;}else{var _1tO=_1tN.b,_1tP=E(_1tN.a),_1tQ=E(_1tP.a),_1tR=E(_1tL);if(_1tQ<_1tR){var _1tS=function(_1tT){while(1){var _1tU=B((function(_1tV){var _1tW=E(_1tV);if(!_1tW._){return __Z;}else{var _1tX=_1tW.b,_1tY=E(_1tW.a);if(E(_1tY.a)<_1tR){_1tT=_1tX;return __continue;}else{return new T2(1,_1tY,new T(function(){return B(_1tS(_1tX));}));}}})(_1tT));if(_1tU!=__continue){return _1tU;}}};return B(_1tf(B(_1tS(_1tO))));}else{var _1tZ=new T(function(){var _1u0=function(_1u1){while(1){var _1u2=B((function(_1u3){var _1u4=E(_1u3);if(!_1u4._){return __Z;}else{var _1u5=_1u4.b,_1u6=E(_1u4.a);if(E(_1u6.a)<_1tR){_1u1=_1u5;return __continue;}else{return new T2(1,_1u6,new T(function(){return B(_1u0(_1u5));}));}}})(_1u1));if(_1u2!=__continue){return _1u2;}}};return B(_1u0(_1tO));});return B(_1sZ(_1tQ,_1tP.b,_1tZ));}}}),_1u7=E(_1tJ);if(!_1u7._){return new F(function(){return _y(_10,new T2(1,_1tK,_1tM));});}else{var _1u8=_1u7.b,_1u9=E(_1u7.a),_1ua=E(_1u9.a),_1ub=E(_1tL);if(_1ua>=_1ub){var _1uc=function(_1ud){while(1){var _1ue=B((function(_1uf){var _1ug=E(_1uf);if(!_1ug._){return __Z;}else{var _1uh=_1ug.b,_1ui=E(_1ug.a);if(E(_1ui.a)>=_1ub){_1ud=_1uh;return __continue;}else{return new T2(1,_1ui,new T(function(){return B(_1uc(_1uh));}));}}})(_1ud));if(_1ue!=__continue){return _1ue;}}};return new F(function(){return _y(B(_1tf(B(_1uc(_1u8)))),new T2(1,_1tK,_1tM));});}else{var _1uj=new T(function(){var _1uk=function(_1ul){while(1){var _1um=B((function(_1un){var _1uo=E(_1un);if(!_1uo._){return __Z;}else{var _1up=_1uo.b,_1uq=E(_1uo.a);if(E(_1uq.a)>=_1ub){_1ul=_1up;return __continue;}else{return new T2(1,_1uq,new T(function(){return B(_1uk(_1up));}));}}})(_1ul));if(_1um!=__continue){return _1um;}}};return B(_1uk(_1u8));});return new F(function(){return _y(B(_1sZ(_1ua,_1u9.b,_1uj)),new T2(1,_1tK,_1tM));});}}}},_1ur=function(_){return new F(function(){return jsMkStdout();});},_1us=new T(function(){return B(_3(_1ur));}),_1ut=new T(function(){return B(_L4("Browser.hs:82:24-56|(Right j)"));}),_1uu=function(_1uv){var _1uw=jsParseJSON(toJSStr(E(_1uv)));return (_1uw._==0)?E(_1ut):E(_1uw.a);},_1ux=function(_1uy,_1uz,_1uA,_1uB,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1uM,_1uN,_1uO,_1uP,_1uQ,_1uR,_1uS,_1uT,_1uU,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_1v1,_1v2,_1v3,_1v4,_1v5,_1v6,_1v7,_1v8,_1v9,_1va,_1vb,_1vc,_){var _1vd={_:0,a:E(_1v4),b:E(_1v5),c:E(_1v6),d:E(_1v7),e:E(_1v8),f:E(_1v9),g:E(_1va),h:E(_1vb)},_1ve=new T2(0,_1uT,_1uU),_1vf=new T2(0,_1uM,_1uN),_1vg={_:0,a:E(_1uC),b:E(_1uD),c:_1uE,d:_1uF,e:_1uG,f:E(_1uH),g:_1uI,h:E(_1uJ),i:E(_1uK),j:E(_1uL)};if(!E(_1v9)){var _1vh=function(_1vi){var _1vj=new T(function(){var _1vk=E(_1uz)/16,_1vl=_1vk&4294967295;if(_1vk>=_1vl){return _1vl-2|0;}else{return (_1vl-1|0)-2|0;}});if(!E(_1v7)){if(!E(_1vb)){return {_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)};}else{var _1vm=function(_,_1vn,_1vo,_1vp,_1vq,_1vr,_1vs,_1vt,_1vu,_1vv,_1vw,_1vx,_1vy,_1vz,_1vA,_1vB,_1vC,_1vD,_1vE,_1vF,_1vG,_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM,_1vN,_1vO){var _1vP=function(_){var _1vQ=function(_){var _1vR=function(_){var _1vS=B(_1qL(_1us,new T2(1,_6D,new T(function(){return B(_8k(_1vu,_1rz));})),_)),_1vT=function(_){var _1vU=B(_1qL(_1us,B(_I(0,_1uY,_10)),_)),_1vV=B(_13A(_1rb,_1vt,_)),_1vW=E(_1uy),_1vX=_1vW.a,_1vY=_1vW.b,_1vZ=new T(function(){return B(_1gJ(E(_1uB)));}),_1w0=new T(function(){var _1w1=function(_1w2,_1w3){var _1w4=E(_1vn);return new F(function(){return _1mC(_1w2,_1w3,_1w4.a,_1w4.b,_1vo,_1vp,_1vq,_1vr,_1vs,_1vt,_1vu,_1vv,_1vw);});};switch(E(_1vZ)){case 72:var _1w5=E(_1vn),_1w6=_1w5.a,_1w7=E(_1w5.b);if(0<=(_1w7-1|0)){var _1w8=B(_1w1(E(_1w6),_1w7-1|0));return {_:0,a:E(_1w8.a),b:E(_1w8.b),c:_1w8.c,d:_1w8.d,e:_1w8.e,f:E(_1w8.f),g:_1w8.g,h:E(_1w8.h),i:E(_1w8.i),j:E(_1w8.j)};}else{var _1w9=B(_1w1(E(_1w6),_1w7));return {_:0,a:E(_1w9.a),b:E(_1w9.b),c:_1w9.c,d:_1w9.d,e:_1w9.e,f:E(_1w9.f),g:_1w9.g,h:E(_1w9.h),i:E(_1w9.i),j:E(_1w9.j)};}break;case 75:var _1wa=E(_1vn),_1wb=_1wa.b,_1wc=E(_1wa.a);if(0<=(_1wc-1|0)){var _1wd=B(_1w1(_1wc-1|0,E(_1wb)));return {_:0,a:E(_1wd.a),b:E(_1wd.b),c:_1wd.c,d:_1wd.d,e:_1wd.e,f:E(_1wd.f),g:_1wd.g,h:E(_1wd.h),i:E(_1wd.i),j:E(_1wd.j)};}else{var _1we=B(_1w1(_1wc,E(_1wb)));return {_:0,a:E(_1we.a),b:E(_1we.b),c:_1we.c,d:_1we.d,e:_1we.e,f:E(_1we.f),g:_1we.g,h:E(_1we.h),i:E(_1we.i),j:E(_1we.j)};}break;case 77:var _1wf=E(_1vn),_1wg=_1wf.b,_1wh=E(_1wf.a);if(E(_1uM)!=(_1wh+1|0)){var _1wi=B(_1w1(_1wh+1|0,E(_1wg)));return {_:0,a:E(_1wi.a),b:E(_1wi.b),c:_1wi.c,d:_1wi.d,e:_1wi.e,f:E(_1wi.f),g:_1wi.g,h:E(_1wi.h),i:E(_1wi.i),j:E(_1wi.j)};}else{var _1wj=B(_1w1(_1wh,E(_1wg)));return {_:0,a:E(_1wj.a),b:E(_1wj.b),c:_1wj.c,d:_1wj.d,e:_1wj.e,f:E(_1wj.f),g:_1wj.g,h:E(_1wj.h),i:E(_1wj.i),j:E(_1wj.j)};}break;case 80:var _1wk=E(_1vn),_1wl=_1wk.a,_1wm=E(_1wk.b);if(E(_1uN)!=(_1wm+1|0)){var _1wn=B(_1w1(E(_1wl),_1wm+1|0));return {_:0,a:E(_1wn.a),b:E(_1wn.b),c:_1wn.c,d:_1wn.d,e:_1wn.e,f:E(_1wn.f),g:_1wn.g,h:E(_1wn.h),i:E(_1wn.i),j:E(_1wn.j)};}else{var _1wo=B(_1w1(E(_1wl),_1wm));return {_:0,a:E(_1wo.a),b:E(_1wo.b),c:_1wo.c,d:_1wo.d,e:_1wo.e,f:E(_1wo.f),g:_1wo.g,h:E(_1wo.h),i:E(_1wo.i),j:E(_1wo.j)};}break;case 104:var _1wp=E(_1vn),_1wq=_1wp.b,_1wr=E(_1wp.a);if(0<=(_1wr-1|0)){var _1ws=B(_1w1(_1wr-1|0,E(_1wq)));return {_:0,a:E(_1ws.a),b:E(_1ws.b),c:_1ws.c,d:_1ws.d,e:_1ws.e,f:E(_1ws.f),g:_1ws.g,h:E(_1ws.h),i:E(_1ws.i),j:E(_1ws.j)};}else{var _1wt=B(_1w1(_1wr,E(_1wq)));return {_:0,a:E(_1wt.a),b:E(_1wt.b),c:_1wt.c,d:_1wt.d,e:_1wt.e,f:E(_1wt.f),g:_1wt.g,h:E(_1wt.h),i:E(_1wt.i),j:E(_1wt.j)};}break;case 106:var _1wu=E(_1vn),_1wv=_1wu.a,_1ww=E(_1wu.b);if(E(_1uN)!=(_1ww+1|0)){var _1wx=B(_1w1(E(_1wv),_1ww+1|0));return {_:0,a:E(_1wx.a),b:E(_1wx.b),c:_1wx.c,d:_1wx.d,e:_1wx.e,f:E(_1wx.f),g:_1wx.g,h:E(_1wx.h),i:E(_1wx.i),j:E(_1wx.j)};}else{var _1wy=B(_1w1(E(_1wv),_1ww));return {_:0,a:E(_1wy.a),b:E(_1wy.b),c:_1wy.c,d:_1wy.d,e:_1wy.e,f:E(_1wy.f),g:_1wy.g,h:E(_1wy.h),i:E(_1wy.i),j:E(_1wy.j)};}break;case 107:var _1wz=E(_1vn),_1wA=_1wz.a,_1wB=E(_1wz.b);if(0<=(_1wB-1|0)){var _1wC=B(_1w1(E(_1wA),_1wB-1|0));return {_:0,a:E(_1wC.a),b:E(_1wC.b),c:_1wC.c,d:_1wC.d,e:_1wC.e,f:E(_1wC.f),g:_1wC.g,h:E(_1wC.h),i:E(_1wC.i),j:E(_1wC.j)};}else{var _1wD=B(_1w1(E(_1wA),_1wB));return {_:0,a:E(_1wD.a),b:E(_1wD.b),c:_1wD.c,d:_1wD.d,e:_1wD.e,f:E(_1wD.f),g:_1wD.g,h:E(_1wD.h),i:E(_1wD.i),j:E(_1wD.j)};}break;case 108:var _1wE=E(_1vn),_1wF=_1wE.b,_1wG=E(_1wE.a);if(E(_1uM)!=(_1wG+1|0)){var _1wH=B(_1w1(_1wG+1|0,E(_1wF)));return {_:0,a:E(_1wH.a),b:E(_1wH.b),c:_1wH.c,d:_1wH.d,e:_1wH.e,f:E(_1wH.f),g:_1wH.g,h:E(_1wH.h),i:E(_1wH.i),j:E(_1wH.j)};}else{var _1wI=B(_1w1(_1wG,E(_1wF)));return {_:0,a:E(_1wI.a),b:E(_1wI.b),c:_1wI.c,d:_1wI.d,e:_1wI.e,f:E(_1wI.f),g:_1wI.g,h:E(_1wI.h),i:E(_1wI.i),j:E(_1wI.j)};}break;default:var _1wJ=E(_1vn),_1wK=B(_1w1(E(_1wJ.a),E(_1wJ.b)));return {_:0,a:E(_1wK.a),b:E(_1wK.b),c:_1wK.c,d:_1wK.d,e:_1wK.e,f:E(_1wK.f),g:_1wK.g,h:E(_1wK.h),i:E(_1wK.i),j:E(_1wK.j)};}}),_1wL=new T(function(){if(E(_1vZ)==32){var _1wM=E(_1w0),_1wN=E(_1wM.a),_1wO=B(_1pW(_1wN.a,E(_1wN.b),_1wM.b,_1wM.c,_1wM.d,_1wM.e,_1wM.f,_1wM.g,_1wM.h,_1wM.i,_1wM.j));return {_:0,a:E(_1wO.a),b:E(_1wO.b),c:_1wO.c,d:_1wO.d,e:_1wO.e,f:E(_1wO.f),g:_1wO.g,h:E(_1wO.h),i:E(_1wO.i),j:E(_1wO.j)};}else{return E(_1w0);}}),_1wP=new T(function(){var _1wQ=E(_1wL),_1wR=_1wQ.h,_1wS=B(_1dG(_1ro,_1wR,_1vA,{_:0,a:E(_1wQ.a),b:E(_1wQ.b),c:_1wQ.c,d:_1wQ.d,e:_1wQ.e,f:E(_1wQ.f),g:E(E(_1vV).b),h:E(_1wR),i:E(_1wQ.i),j:E(_1wQ.j)},_1vx,_1vy,_1vz,_1vA,_1vB,_1vC,_1vD,_1vE,_1vF,_1vG,_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM,_1vN,_1vO));return {_:0,a:E(_1wS.a),b:E(_1wS.b),c:E(_1wS.c),d:E(_1wS.d),e:E(_1wS.e),f:E(_1wS.f),g:E(_1wS.g),h:E(_1wS.h),i:_1wS.i,j:_1wS.j,k:_1wS.k,l:_1wS.l,m:E(_1wS.m),n:_1wS.n,o:E(_1wS.o),p:E(_1wS.p),q:_1wS.q,r:E(_1wS.r),s:E(_1wS.s)};}),_1wT=B(_nq(_1vX,_1vY,new T(function(){return E(_1vj)-E(E(E(_1wP).b).a)|0;}),_nP,new T(function(){return E(E(E(_1wP).a).b);}),_)),_1wU=E(_1vZ),_1wV=function(_,_1wW){var _1wX=function(_1wY){var _1wZ=B(_1qL(_1us,B(_8q(_1wW)),_)),_1x0=E(_1wP),_1x1=_1x0.d,_1x2=_1x0.e,_1x3=_1x0.f,_1x4=_1x0.g,_1x5=_1x0.i,_1x6=_1x0.j,_1x7=_1x0.k,_1x8=_1x0.l,_1x9=_1x0.m,_1xa=_1x0.n,_1xb=_1x0.o,_1xc=_1x0.p,_1xd=_1x0.q,_1xe=_1x0.s,_1xf=E(_1x0.r),_1xg=_1xf.a,_1xh=_1xf.d,_1xi=_1xf.e,_1xj=_1xf.f,_1xk=_1xf.g,_1xl=_1xf.h,_1xm=E(_1x0.a),_1xn=_1xm.e,_1xo=_1xm.f,_1xp=_1xm.g,_1xq=E(_1x0.h),_1xr=function(_1xs){var _1xt=function(_1xu){if(_1xu!=E(_1rg)){var _1xv=B(_6R(_1ah,_1xu)),_1xw=_1xv.a,_1xx=E(_1xv.b),_1xy=B(_17q(_1xw,_1xx,new T(function(){return B(_6R(_1bv,_1xu));})));return new F(function(){return _1ux(_1vW,_1uz,_1uA,_1rf,B(_6R(_1aq,_1xu)),_1xy,B(_6R(_1aD,_1xu)),32,_1xu,_1xo,_1xp,B(_y(_1xm.h,new T2(1,_1re,new T(function(){return B(_I(0,_1xn,_10));})))),B(_1qk(_1rd,_1xy)),_ws,_1xw,_1xx,_10,_1x1,_1x2,_1x3,_1x4,_1xq.a,_1xq.b,_1x5,_1x6,_1x7, -1,_1x9,_1xa,_1xb,_1xc,_1xd,_ws,_ws,_ws,_1xh,_1xi,_1xj,_1xk,_1xl,_1xe,_);});}else{var _1xz=__app1(E(_ni),_1vY),_1xA=B(A2(_nj,_1vX,_)),_1xB=B(A(_mO,[_1vX,_j3,_1r4,_1rb,_1ra,_])),_1xC=B(A(_mO,[_1vX,_j3,_1r7,_1r9,_1r8,_])),_1xD=B(A(_mO,[_1vX,_j3,_1r7,_1r6,_1r5,_])),_1xE=B(A(_mO,[_1vX,_j3,_1r4,_1r3,_1r2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1am),b:E(_1r1),c:E(_1qZ),d:32,e:0,f:E(_1xo),g:_1xp,h:E(_10),i:E(_1xm.i),j:E(_ws)}),b:E(_1ae),c:E(_1x0.c),d:E(_1x1),e:E(_1x2),f:E(_1x3),g:E(_1x4),h:E(_1xq),i:_1x5,j:_1x6,k:_1x7,l:_1x8,m:E(_1x9),n:_1xa,o:E(_1xb),p:E(_1xc),q:_1xd,r:E({_:0,a:E(_1xg),b:E(_ws),c:E(_ws),d:E(_1xh),e:E(_1xi),f:E(_1xj),g:E(_1xk),h:E(_1xl)}),s:E(_1xe)};});}};if(_1x8>=0){return new F(function(){return _1xt(_1x8);});}else{return new F(function(){return _1xt(_1xn+1|0);});}};if(!E(_1xg)){if(E(_1wU)==110){return new F(function(){return _1xr(_);});}else{var _1xF=new T(function(){return E(E(_1w0).a);});if(E(_1xm.d)==32){var _1xG=B(A(_mO,[_1vX,_1rh,new T(function(){return (E(E(_1xF).a)+1|0)+(E(_1vj)-E(_1uM)|0)|0;},1),new T(function(){return (E(E(_1xF).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1rA(_1wL));}),_10),_]));return _1x0;}else{var _1xH=B(A(_mO,[_1vX,_1ri,new T(function(){return (E(E(_1xF).a)+1|0)+(E(_1vj)-E(_1uM)|0)|0;},1),new T(function(){return (E(E(_1xF).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1rA(_1wL));}),_10),_]));return _1x0;}}}else{return new F(function(){return _1xr(_);});}};if(E(_1wU)==114){if(!B(_69(_1wW,_1rj))){var _1xI=E(_1wW);if(!_1xI._){return _1wP;}else{var _1xJ=_1xI.b;return new T(function(){var _1xK=E(_1wP),_1xL=E(_1xK.a),_1xM=E(_1xI.a),_1xN=E(_1xM);if(_1xN==34){var _1xO=B(_Rf(_1xM,_1xJ));if(!_1xO._){var _1xP=E(_1sv);}else{var _1xQ=E(_1xO.b);if(!_1xQ._){var _1xR=E(_1rx);}else{var _1xS=_1xQ.a,_1xT=E(_1xQ.b);if(!_1xT._){var _1xU=new T2(1,new T2(1,_1xS,_10),_10);}else{var _1xV=E(_1xS),_1xW=new T(function(){var _1xX=B(_H4(126,_1xT.a,_1xT.b));return new T2(0,_1xX.a,_1xX.b);});if(E(_1xV)==126){var _1xY=new T2(1,_10,new T2(1,new T(function(){return E(E(_1xW).a);}),new T(function(){return E(E(_1xW).b);})));}else{var _1xY=new T2(1,new T2(1,_1xV,new T(function(){return E(E(_1xW).a);})),new T(function(){return E(E(_1xW).b);}));}var _1xU=_1xY;}var _1xR=_1xU;}var _1xP=_1xR;}var _1xZ=_1xP;}else{var _1y0=E(_1xJ);if(!_1y0._){var _1y1=new T2(1,new T2(1,_1xM,_10),_10);}else{var _1y2=new T(function(){var _1y3=B(_H4(126,_1y0.a,_1y0.b));return new T2(0,_1y3.a,_1y3.b);});if(E(_1xN)==126){var _1y4=new T2(1,_10,new T2(1,new T(function(){return E(E(_1y2).a);}),new T(function(){return E(E(_1y2).b);})));}else{var _1y4=new T2(1,new T2(1,_1xM,new T(function(){return E(E(_1y2).a);})),new T(function(){return E(E(_1y2).b);}));}var _1y1=_1y4;}var _1xZ=_1y1;}var _1y5=B(_Gc(B(_sx(_YB,new T(function(){return B(_Ja(_1xZ));})))));if(!_1y5._){return E(_Yz);}else{if(!E(_1y5.b)._){var _1y6=E(_1y5.a),_1y7=B(_6R(_1ah,_1y6)),_1y8=B(_6R(_1xZ,1));if(!_1y8._){var _1y9=__Z;}else{var _1ya=E(_1y8.b);if(!_1ya._){var _1yb=__Z;}else{var _1yc=E(_1y8.a),_1yd=new T(function(){var _1ye=B(_H4(44,_1ya.a,_1ya.b));return new T2(0,_1ye.a,_1ye.b);});if(E(_1yc)==44){var _1yf=B(_Yr(_10,new T(function(){return E(E(_1yd).a);}),new T(function(){return E(E(_1yd).b);})));}else{var _1yf=B(_Yv(new T2(1,_1yc,new T(function(){return E(E(_1yd).a);})),new T(function(){return E(E(_1yd).b);})));}var _1yb=_1yf;}var _1y9=_1yb;}var _1yg=B(_6R(_1xZ,2));if(!_1yg._){var _1yh=E(_1ry);}else{var _1yi=_1yg.a,_1yj=E(_1yg.b);if(!_1yj._){var _1yk=B(_6e(_YC,new T2(1,new T2(1,_1yi,_10),_10)));}else{var _1yl=E(_1yi),_1ym=new T(function(){var _1yn=B(_H4(44,_1yj.a,_1yj.b));return new T2(0,_1yn.a,_1yn.b);});if(E(_1yl)==44){var _1yo=B(_6e(_YC,new T2(1,_10,new T2(1,new T(function(){return E(E(_1ym).a);}),new T(function(){return E(E(_1ym).b);})))));}else{var _1yo=B(_6e(_YC,new T2(1,new T2(1,_1yl,new T(function(){return E(E(_1ym).a);})),new T(function(){return E(E(_1ym).b);}))));}var _1yk=_1yo;}var _1yh=_1yk;}return {_:0,a:E({_:0,a:E(B(_6R(_1aq,_1y6))),b:E(B(_17q(_1y7.a,E(_1y7.b),new T(function(){return B(_6R(_1bv,_1y6));})))),c:B(_6R(_1aD,_1y6)),d:32,e:_1y6,f:E(_1xL.f),g:_1xL.g,h:E(_1xL.h),i:E(_1xL.i),j:E(_1xL.j)}),b:E(_1y7),c:E(_1xK.c),d:E(_1xK.d),e:E(_1y9),f:E(_1yh),g:E(_1xK.g),h:E(_1xK.h),i:_1xK.i,j:_1xK.j,k:_1xK.k,l:_1xK.l,m:E(_1xK.m),n:_1xK.n,o:E(_1xK.o),p:E(_1xK.p),q:_1xK.q,r:E(_1xK.r),s:E(_1xK.s)};}else{return E(_YA);}}});}}else{return new F(function(){return _1wX(_);});}}else{return new F(function(){return _1wX(_);});}};switch(E(_1wU)){case 100:var _1yp=__app1(E(_1st),toJSStr(E(_1rm)));return new F(function(){return _1wV(_,_1qW);});break;case 114:var _1yq=B(_YM(_6w,toJSStr(E(_1rm)),_));return new F(function(){return _1wV(_,new T(function(){var _1yr=E(_1yq);if(!_1yr._){return E(_1qX);}else{return fromJSStr(B(_1fP(_1yr.a)));}}));});break;case 115:var _1ys=new T(function(){var _1yt=new T(function(){var _1yu=new T(function(){var _1yv=B(_6e(_6B,_1uR));if(!_1yv._){return __Z;}else{return B(_1qQ(new T2(1,_1yv.a,new T(function(){return B(_1rC(_1rk,_1yv.b));}))));}}),_1yw=new T(function(){var _1yx=function(_1yy){var _1yz=E(_1yy);if(!_1yz._){return __Z;}else{var _1yA=E(_1yz.a);return new T2(1,_1yA.a,new T2(1,_1yA.b,new T(function(){return B(_1yx(_1yz.b));})));}},_1yB=B(_1yx(_1uQ));if(!_1yB._){return __Z;}else{return B(_1qQ(new T2(1,_1yB.a,new T(function(){return B(_1rC(_1rk,_1yB.b));}))));}});return B(_1rC(_1rl,new T2(1,_1yw,new T2(1,_1yu,_10))));});return B(_y(B(_1qQ(new T2(1,new T(function(){return B(_I(0,_1uG,_10));}),_1yt))),_1rw));}),_1yC=__app2(E(_1sw),toJSStr(E(_1rm)),B(_1fP(B(_1uu(B(unAppCStr("\"",_1ys)))))));return new F(function(){return _1wV(_,_1qY);});break;default:return new F(function(){return _1wV(_,_1rn);});}};if(!E(_1vw)){var _1yD=B(_1qL(_1us,_1sW,_));return new F(function(){return _1vT(_);});}else{var _1yE=B(_1qL(_1us,_1sV,_));return new F(function(){return _1vT(_);});}},_1yF=E(_1uS);if(!_1yF._){var _1yG=B(_1qL(_1us,_1rv,_));return new F(function(){return _1vR(_);});}else{var _1yH=new T(function(){var _1yI=E(_1yF.a),_1yJ=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1yK){return new F(function(){return _1sy(_1yI.a,_1yK);});},new T2(1,function(_1yL){return new F(function(){return _1sy(_1yI.b,_1yL);});},_10)),new T2(1,_G,new T(function(){return B(_1sB(_1yF.b));}))));});return new T2(1,_H,_1yJ);}),_1yM=B(_1qL(_1us,new T2(1,_2C,_1yH),_));return new F(function(){return _1vR(_);});}},_1yN=E(_1uR);if(!_1yN._){var _1yO=B(_1qL(_1us,_1rv,_));return new F(function(){return _1vQ(_);});}else{var _1yP=new T(function(){return B(_I(0,E(_1yN.a),new T(function(){return B(_1sJ(_1yN.b));})));}),_1yQ=B(_1qL(_1us,new T2(1,_2C,_1yP),_));return new F(function(){return _1vQ(_);});}},_1yR=E(_1uQ);if(!_1yR._){var _1yS=B(_1qL(_1us,_1rv,_));return new F(function(){return _1vP(_);});}else{var _1yT=new T(function(){var _1yU=E(_1yR.a),_1yV=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1yW){return new F(function(){return _1sy(_1yU.a,_1yW);});},new T2(1,function(_1yX){return new F(function(){return _1sy(_1yU.b,_1yX);});},_10)),new T2(1,_G,new T(function(){return B(_1sN(_1yR.b));}))));});return new T2(1,_H,_1yV);}),_1yY=B(_1qL(_1us,new T2(1,_2C,_1yT),_));return new F(function(){return _1vP(_);});}},_1yZ=E(_1v1);if(!_1yZ._){return new F(function(){return _1vm(_,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1vf,_1uO,_1uP,_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc);});}else{var _1z0=E(_1yZ.b);if(!_1z0._){return new F(function(){return _1vm(_,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1vf,_1uO,_1uP,_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc);});}else{var _1z1=E(_1z0.b);if(!_1z1._){return new F(function(){return _1vm(_,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1vf,_1uO,_1uP,_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc);});}else{var _1z2=_1z1.a,_1z3=E(_1z1.b);if(!_1z3._){return new F(function(){return _1vm(_,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1vf,_1uO,_1uP,_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc);});}else{if(!E(_1z3.b)._){var _1z4=B(_14V(B(_mt(_1z2,0)),_1uI,new T(function(){var _1z5=B(_Gc(B(_sx(_YB,_1yZ.a))));if(!_1z5._){return E(_1sj);}else{if(!E(_1z5.b)._){if(E(_1z5.a)==2){return E(_1sn);}else{return E(_1sj);}}else{return E(_1sj);}}}),_)),_1z6=E(_1z4),_1z7=_1z6.a,_1z8=new T(function(){var _1z9=new T(function(){return B(_6e(function(_1za){var _1zb=B(_sk(_3M,_1za,B(_Go(_1rq,_1z2))));return (_1zb._==0)?E(_1rc):E(_1zb.a);},B(_6e(_1sX,B(_1tf(B(_1so(_1z7,_1sk))))))));}),_1zc=B(_RD(B(unAppCStr("e.==.m1:",_1z3.a)),{_:0,a:E(_1uC),b:E(_1uD),c:_1uE,d:_1uF,e:_1uG,f:E(B(_y(_1uH,new T2(1,new T2(0,new T2(0,_1z0.a,_1rp),_1uG),new T2(1,new T2(0,new T2(0,_1z9,_1rp),_1uG),_10))))),g:E(_1z6.b),h:E(_1uJ),i:E(_1uK),j:E(_1uL)},_1vf,_1uO,B(_y(_1uP,new T(function(){return B(_1qB(_1z7,_1z2));},1))),_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc)),_1zd=B(_1g0(_1z2,_1zc.a,_1zc.b,_1zc.c,_1zc.d,_1zc.e,_1zc.f,_1zc.g,_1zc.h,_1zc.i,_1zc.j,_1zc.k,_1zc.l,_1zc.m,_1zc.n,_1zc.o,_1zc.p,_1zc.q,_1zc.r,_1zc.s));return {_:0,a:E(_1zd.a),b:E(_1zd.b),c:E(_1zd.c),d:E(_1zd.d),e:E(_1zd.e),f:E(_1zd.f),g:E(_1zd.g),h:E(_1zd.h),i:_1zd.i,j:_1zd.j,k:_1zd.k,l:_1zd.l,m:E(_1zd.m),n:_1zd.n,o:E(_1zd.o),p:E(_1zd.p),q:_1zd.q,r:E(_1zd.r),s:E(_1zd.s)};}),_1ze=function(_){var _1zf=function(_){var _1zg=function(_){var _1zh=new T(function(){var _1zi=E(E(_1z8).a);return new T5(0,_1zi,_1zi.a,_1zi.g,_1zi.h,_1zi.j);}),_1zj=B(_1qL(_1us,new T2(1,_6D,new T(function(){return B(_8k(E(_1zh).d,_1rz));})),_)),_1zk=E(_1zh),_1zl=_1zk.b,_1zm=function(_){var _1zn=B(_1qL(_1us,B(_I(0,_1uY,_10)),_)),_1zo=B(_13A(_1rb,_1zk.c,_)),_1zp=E(_1uy),_1zq=_1zp.a,_1zr=_1zp.b,_1zs=new T(function(){return B(_1gJ(E(_1uB)));}),_1zt=new T(function(){var _1zu=function(_1zv,_1zw){var _1zx=E(_1zk.a),_1zy=E(_1zx.a);return new F(function(){return _1mC(_1zv,_1zw,_1zy.a,_1zy.b,_1zx.b,_1zx.c,_1zx.d,_1zx.e,_1zx.f,_1zx.g,_1zx.h,_1zx.i,_1zx.j);});};switch(E(_1zs)){case 72:var _1zz=E(_1zl),_1zA=_1zz.a,_1zB=E(_1zz.b);if(0<=(_1zB-1|0)){var _1zC=B(_1zu(E(_1zA),_1zB-1|0));return {_:0,a:E(_1zC.a),b:E(_1zC.b),c:_1zC.c,d:_1zC.d,e:_1zC.e,f:E(_1zC.f),g:_1zC.g,h:E(_1zC.h),i:E(_1zC.i),j:E(_1zC.j)};}else{var _1zD=B(_1zu(E(_1zA),_1zB));return {_:0,a:E(_1zD.a),b:E(_1zD.b),c:_1zD.c,d:_1zD.d,e:_1zD.e,f:E(_1zD.f),g:_1zD.g,h:E(_1zD.h),i:E(_1zD.i),j:E(_1zD.j)};}break;case 75:var _1zE=E(_1zl),_1zF=_1zE.b,_1zG=E(_1zE.a);if(0<=(_1zG-1|0)){var _1zH=B(_1zu(_1zG-1|0,E(_1zF)));return {_:0,a:E(_1zH.a),b:E(_1zH.b),c:_1zH.c,d:_1zH.d,e:_1zH.e,f:E(_1zH.f),g:_1zH.g,h:E(_1zH.h),i:E(_1zH.i),j:E(_1zH.j)};}else{var _1zI=B(_1zu(_1zG,E(_1zF)));return {_:0,a:E(_1zI.a),b:E(_1zI.b),c:_1zI.c,d:_1zI.d,e:_1zI.e,f:E(_1zI.f),g:_1zI.g,h:E(_1zI.h),i:E(_1zI.i),j:E(_1zI.j)};}break;case 77:var _1zJ=E(_1zl),_1zK=_1zJ.b,_1zL=E(_1zJ.a);if(E(_1uM)!=(_1zL+1|0)){var _1zM=B(_1zu(_1zL+1|0,E(_1zK)));return {_:0,a:E(_1zM.a),b:E(_1zM.b),c:_1zM.c,d:_1zM.d,e:_1zM.e,f:E(_1zM.f),g:_1zM.g,h:E(_1zM.h),i:E(_1zM.i),j:E(_1zM.j)};}else{var _1zN=B(_1zu(_1zL,E(_1zK)));return {_:0,a:E(_1zN.a),b:E(_1zN.b),c:_1zN.c,d:_1zN.d,e:_1zN.e,f:E(_1zN.f),g:_1zN.g,h:E(_1zN.h),i:E(_1zN.i),j:E(_1zN.j)};}break;case 80:var _1zO=E(_1zl),_1zP=_1zO.a,_1zQ=E(_1zO.b);if(E(_1uN)!=(_1zQ+1|0)){var _1zR=B(_1zu(E(_1zP),_1zQ+1|0));return {_:0,a:E(_1zR.a),b:E(_1zR.b),c:_1zR.c,d:_1zR.d,e:_1zR.e,f:E(_1zR.f),g:_1zR.g,h:E(_1zR.h),i:E(_1zR.i),j:E(_1zR.j)};}else{var _1zS=B(_1zu(E(_1zP),_1zQ));return {_:0,a:E(_1zS.a),b:E(_1zS.b),c:_1zS.c,d:_1zS.d,e:_1zS.e,f:E(_1zS.f),g:_1zS.g,h:E(_1zS.h),i:E(_1zS.i),j:E(_1zS.j)};}break;case 104:var _1zT=E(_1zl),_1zU=_1zT.b,_1zV=E(_1zT.a);if(0<=(_1zV-1|0)){var _1zW=B(_1zu(_1zV-1|0,E(_1zU)));return {_:0,a:E(_1zW.a),b:E(_1zW.b),c:_1zW.c,d:_1zW.d,e:_1zW.e,f:E(_1zW.f),g:_1zW.g,h:E(_1zW.h),i:E(_1zW.i),j:E(_1zW.j)};}else{var _1zX=B(_1zu(_1zV,E(_1zU)));return {_:0,a:E(_1zX.a),b:E(_1zX.b),c:_1zX.c,d:_1zX.d,e:_1zX.e,f:E(_1zX.f),g:_1zX.g,h:E(_1zX.h),i:E(_1zX.i),j:E(_1zX.j)};}break;case 106:var _1zY=E(_1zl),_1zZ=_1zY.a,_1A0=E(_1zY.b);if(E(_1uN)!=(_1A0+1|0)){var _1A1=B(_1zu(E(_1zZ),_1A0+1|0));return {_:0,a:E(_1A1.a),b:E(_1A1.b),c:_1A1.c,d:_1A1.d,e:_1A1.e,f:E(_1A1.f),g:_1A1.g,h:E(_1A1.h),i:E(_1A1.i),j:E(_1A1.j)};}else{var _1A2=B(_1zu(E(_1zZ),_1A0));return {_:0,a:E(_1A2.a),b:E(_1A2.b),c:_1A2.c,d:_1A2.d,e:_1A2.e,f:E(_1A2.f),g:_1A2.g,h:E(_1A2.h),i:E(_1A2.i),j:E(_1A2.j)};}break;case 107:var _1A3=E(_1zl),_1A4=_1A3.a,_1A5=E(_1A3.b);if(0<=(_1A5-1|0)){var _1A6=B(_1zu(E(_1A4),_1A5-1|0));return {_:0,a:E(_1A6.a),b:E(_1A6.b),c:_1A6.c,d:_1A6.d,e:_1A6.e,f:E(_1A6.f),g:_1A6.g,h:E(_1A6.h),i:E(_1A6.i),j:E(_1A6.j)};}else{var _1A7=B(_1zu(E(_1A4),_1A5));return {_:0,a:E(_1A7.a),b:E(_1A7.b),c:_1A7.c,d:_1A7.d,e:_1A7.e,f:E(_1A7.f),g:_1A7.g,h:E(_1A7.h),i:E(_1A7.i),j:E(_1A7.j)};}break;case 108:var _1A8=E(_1zl),_1A9=_1A8.b,_1Aa=E(_1A8.a);if(E(_1uM)!=(_1Aa+1|0)){var _1Ab=B(_1zu(_1Aa+1|0,E(_1A9)));return {_:0,a:E(_1Ab.a),b:E(_1Ab.b),c:_1Ab.c,d:_1Ab.d,e:_1Ab.e,f:E(_1Ab.f),g:_1Ab.g,h:E(_1Ab.h),i:E(_1Ab.i),j:E(_1Ab.j)};}else{var _1Ac=B(_1zu(_1Aa,E(_1A9)));return {_:0,a:E(_1Ac.a),b:E(_1Ac.b),c:_1Ac.c,d:_1Ac.d,e:_1Ac.e,f:E(_1Ac.f),g:_1Ac.g,h:E(_1Ac.h),i:E(_1Ac.i),j:E(_1Ac.j)};}break;default:var _1Ad=E(_1zl),_1Ae=B(_1zu(E(_1Ad.a),E(_1Ad.b)));return {_:0,a:E(_1Ae.a),b:E(_1Ae.b),c:_1Ae.c,d:_1Ae.d,e:_1Ae.e,f:E(_1Ae.f),g:_1Ae.g,h:E(_1Ae.h),i:E(_1Ae.i),j:E(_1Ae.j)};}}),_1Af=new T(function(){if(E(_1zs)==32){var _1Ag=E(_1zt),_1Ah=E(_1Ag.a),_1Ai=B(_1pW(_1Ah.a,E(_1Ah.b),_1Ag.b,_1Ag.c,_1Ag.d,_1Ag.e,_1Ag.f,_1Ag.g,_1Ag.h,_1Ag.i,_1Ag.j));return {_:0,a:E(_1Ai.a),b:E(_1Ai.b),c:_1Ai.c,d:_1Ai.d,e:_1Ai.e,f:E(_1Ai.f),g:_1Ai.g,h:E(_1Ai.h),i:E(_1Ai.i),j:E(_1Ai.j)};}else{return E(_1zt);}}),_1Aj=new T(function(){var _1Ak=E(_1z8),_1Al=_1Ak.e,_1Am=E(_1Af),_1An=_1Am.h,_1Ao=B(_1dG(_1ro,_1An,_1Al,{_:0,a:E(_1Am.a),b:E(_1Am.b),c:_1Am.c,d:_1Am.d,e:_1Am.e,f:E(_1Am.f),g:E(E(_1zo).b),h:E(_1An),i:E(_1Am.i),j:E(_1Am.j)},_1Ak.b,_1Ak.c,_1Ak.d,_1Al,_1Ak.f,_1Ak.g,_1Ak.h,_1Ak.i,_1Ak.j,_1Ak.k,_1Ak.l,_1Ak.m,_1Ak.n,_1Ak.o,_1Ak.p,_1Ak.q,_1Ak.r,_1Ak.s));return {_:0,a:E(_1Ao.a),b:E(_1Ao.b),c:E(_1Ao.c),d:E(_1Ao.d),e:E(_1Ao.e),f:E(_1Ao.f),g:E(_1Ao.g),h:E(_1Ao.h),i:_1Ao.i,j:_1Ao.j,k:_1Ao.k,l:_1Ao.l,m:E(_1Ao.m),n:_1Ao.n,o:E(_1Ao.o),p:E(_1Ao.p),q:_1Ao.q,r:E(_1Ao.r),s:E(_1Ao.s)};}),_1Ap=B(_nq(_1zq,_1zr,new T(function(){return E(_1vj)-E(E(E(_1Aj).b).a)|0;}),_nP,new T(function(){return E(E(E(_1Aj).a).b);}),_)),_1Aq=E(_1zs),_1Ar=function(_,_1As){var _1At=function(_1Au){var _1Av=B(_1qL(_1us,B(_8q(_1As)),_)),_1Aw=E(_1Aj),_1Ax=_1Aw.d,_1Ay=_1Aw.e,_1Az=_1Aw.f,_1AA=_1Aw.g,_1AB=_1Aw.i,_1AC=_1Aw.j,_1AD=_1Aw.k,_1AE=_1Aw.l,_1AF=_1Aw.m,_1AG=_1Aw.n,_1AH=_1Aw.o,_1AI=_1Aw.p,_1AJ=_1Aw.q,_1AK=_1Aw.s,_1AL=E(_1Aw.r),_1AM=_1AL.a,_1AN=_1AL.d,_1AO=_1AL.e,_1AP=_1AL.f,_1AQ=_1AL.g,_1AR=_1AL.h,_1AS=E(_1Aw.a),_1AT=_1AS.e,_1AU=_1AS.f,_1AV=_1AS.g,_1AW=E(_1Aw.h),_1AX=function(_1AY){var _1AZ=function(_1B0){if(_1B0!=E(_1rg)){var _1B1=B(_6R(_1ah,_1B0)),_1B2=_1B1.a,_1B3=E(_1B1.b),_1B4=B(_17q(_1B2,_1B3,new T(function(){return B(_6R(_1bv,_1B0));})));return new F(function(){return _1ux(_1zp,_1uz,_1uA,_1rf,B(_6R(_1aq,_1B0)),_1B4,B(_6R(_1aD,_1B0)),32,_1B0,_1AU,_1AV,B(_y(_1AS.h,new T2(1,_1re,new T(function(){return B(_I(0,_1AT,_10));})))),B(_1qk(_1rd,_1B4)),_ws,_1B2,_1B3,_10,_1Ax,_1Ay,_1Az,_1AA,_1AW.a,_1AW.b,_1AB,_1AC,_1AD, -1,_1AF,_1AG,_1AH,_1AI,_1AJ,_ws,_ws,_ws,_1AN,_1AO,_1AP,_1AQ,_1AR,_1AK,_);});}else{var _1B5=__app1(E(_ni),_1zr),_1B6=B(A2(_nj,_1zq,_)),_1B7=B(A(_mO,[_1zq,_j3,_1r4,_1rb,_1ra,_])),_1B8=B(A(_mO,[_1zq,_j3,_1r7,_1r9,_1r8,_])),_1B9=B(A(_mO,[_1zq,_j3,_1r7,_1r6,_1r5,_])),_1Ba=B(A(_mO,[_1zq,_j3,_1r4,_1r3,_1r2,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1am),b:E(_1r1),c:E(_1qZ),d:32,e:0,f:E(_1AU),g:_1AV,h:E(_10),i:E(_1AS.i),j:E(_ws)}),b:E(_1ae),c:E(_1Aw.c),d:E(_1Ax),e:E(_1Ay),f:E(_1Az),g:E(_1AA),h:E(_1AW),i:_1AB,j:_1AC,k:_1AD,l:_1AE,m:E(_1AF),n:_1AG,o:E(_1AH),p:E(_1AI),q:_1AJ,r:E({_:0,a:E(_1AM),b:E(_ws),c:E(_ws),d:E(_1AN),e:E(_1AO),f:E(_1AP),g:E(_1AQ),h:E(_1AR)}),s:E(_1AK)};});}};if(_1AE>=0){return new F(function(){return _1AZ(_1AE);});}else{return new F(function(){return _1AZ(_1AT+1|0);});}};if(!E(_1AM)){if(E(_1Aq)==110){return new F(function(){return _1AX(_);});}else{var _1Bb=new T(function(){return E(E(_1zt).a);});if(E(_1AS.d)==32){var _1Bc=B(A(_mO,[_1zq,_1rh,new T(function(){return (E(E(_1Bb).a)+1|0)+(E(_1vj)-E(_1uM)|0)|0;},1),new T(function(){return (E(E(_1Bb).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1rA(_1Af));}),_10),_]));return _1Aw;}else{var _1Bd=B(A(_mO,[_1zq,_1ri,new T(function(){return (E(E(_1Bb).a)+1|0)+(E(_1vj)-E(_1uM)|0)|0;},1),new T(function(){return (E(E(_1Bb).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1rA(_1Af));}),_10),_]));return _1Aw;}}}else{return new F(function(){return _1AX(_);});}};if(E(_1Aq)==114){if(!B(_69(_1As,_1rj))){var _1Be=E(_1As);if(!_1Be._){return _1Aj;}else{var _1Bf=_1Be.b;return new T(function(){var _1Bg=E(_1Aj),_1Bh=E(_1Bg.a),_1Bi=E(_1Be.a),_1Bj=E(_1Bi);if(_1Bj==34){var _1Bk=B(_Rf(_1Bi,_1Bf));if(!_1Bk._){var _1Bl=E(_1sv);}else{var _1Bm=E(_1Bk.b);if(!_1Bm._){var _1Bn=E(_1rx);}else{var _1Bo=_1Bm.a,_1Bp=E(_1Bm.b);if(!_1Bp._){var _1Bq=new T2(1,new T2(1,_1Bo,_10),_10);}else{var _1Br=E(_1Bo),_1Bs=new T(function(){var _1Bt=B(_H4(126,_1Bp.a,_1Bp.b));return new T2(0,_1Bt.a,_1Bt.b);});if(E(_1Br)==126){var _1Bu=new T2(1,_10,new T2(1,new T(function(){return E(E(_1Bs).a);}),new T(function(){return E(E(_1Bs).b);})));}else{var _1Bu=new T2(1,new T2(1,_1Br,new T(function(){return E(E(_1Bs).a);})),new T(function(){return E(E(_1Bs).b);}));}var _1Bq=_1Bu;}var _1Bn=_1Bq;}var _1Bl=_1Bn;}var _1Bv=_1Bl;}else{var _1Bw=E(_1Bf);if(!_1Bw._){var _1Bx=new T2(1,new T2(1,_1Bi,_10),_10);}else{var _1By=new T(function(){var _1Bz=B(_H4(126,_1Bw.a,_1Bw.b));return new T2(0,_1Bz.a,_1Bz.b);});if(E(_1Bj)==126){var _1BA=new T2(1,_10,new T2(1,new T(function(){return E(E(_1By).a);}),new T(function(){return E(E(_1By).b);})));}else{var _1BA=new T2(1,new T2(1,_1Bi,new T(function(){return E(E(_1By).a);})),new T(function(){return E(E(_1By).b);}));}var _1Bx=_1BA;}var _1Bv=_1Bx;}var _1BB=B(_Gc(B(_sx(_YB,new T(function(){return B(_Ja(_1Bv));})))));if(!_1BB._){return E(_Yz);}else{if(!E(_1BB.b)._){var _1BC=E(_1BB.a),_1BD=B(_6R(_1ah,_1BC)),_1BE=B(_6R(_1Bv,1));if(!_1BE._){var _1BF=__Z;}else{var _1BG=E(_1BE.b);if(!_1BG._){var _1BH=__Z;}else{var _1BI=E(_1BE.a),_1BJ=new T(function(){var _1BK=B(_H4(44,_1BG.a,_1BG.b));return new T2(0,_1BK.a,_1BK.b);});if(E(_1BI)==44){var _1BL=B(_Yr(_10,new T(function(){return E(E(_1BJ).a);}),new T(function(){return E(E(_1BJ).b);})));}else{var _1BL=B(_Yv(new T2(1,_1BI,new T(function(){return E(E(_1BJ).a);})),new T(function(){return E(E(_1BJ).b);})));}var _1BH=_1BL;}var _1BF=_1BH;}var _1BM=B(_6R(_1Bv,2));if(!_1BM._){var _1BN=E(_1ry);}else{var _1BO=_1BM.a,_1BP=E(_1BM.b);if(!_1BP._){var _1BQ=B(_6e(_YC,new T2(1,new T2(1,_1BO,_10),_10)));}else{var _1BR=E(_1BO),_1BS=new T(function(){var _1BT=B(_H4(44,_1BP.a,_1BP.b));return new T2(0,_1BT.a,_1BT.b);});if(E(_1BR)==44){var _1BU=B(_6e(_YC,new T2(1,_10,new T2(1,new T(function(){return E(E(_1BS).a);}),new T(function(){return E(E(_1BS).b);})))));}else{var _1BU=B(_6e(_YC,new T2(1,new T2(1,_1BR,new T(function(){return E(E(_1BS).a);})),new T(function(){return E(E(_1BS).b);}))));}var _1BQ=_1BU;}var _1BN=_1BQ;}return {_:0,a:E({_:0,a:E(B(_6R(_1aq,_1BC))),b:E(B(_17q(_1BD.a,E(_1BD.b),new T(function(){return B(_6R(_1bv,_1BC));})))),c:B(_6R(_1aD,_1BC)),d:32,e:_1BC,f:E(_1Bh.f),g:_1Bh.g,h:E(_1Bh.h),i:E(_1Bh.i),j:E(_1Bh.j)}),b:E(_1BD),c:E(_1Bg.c),d:E(_1Bg.d),e:E(_1BF),f:E(_1BN),g:E(_1Bg.g),h:E(_1Bg.h),i:_1Bg.i,j:_1Bg.j,k:_1Bg.k,l:_1Bg.l,m:E(_1Bg.m),n:_1Bg.n,o:E(_1Bg.o),p:E(_1Bg.p),q:_1Bg.q,r:E(_1Bg.r),s:E(_1Bg.s)};}else{return E(_YA);}}});}}else{return new F(function(){return _1At(_);});}}else{return new F(function(){return _1At(_);});}};switch(E(_1Aq)){case 100:var _1BV=__app1(E(_1st),toJSStr(E(_1rm)));return new F(function(){return _1Ar(_,_1qW);});break;case 114:var _1BW=B(_YM(_6w,toJSStr(E(_1rm)),_));return new F(function(){return _1Ar(_,new T(function(){var _1BX=E(_1BW);if(!_1BX._){return E(_1qX);}else{return fromJSStr(B(_1fP(_1BX.a)));}}));});break;case 115:var _1BY=new T(function(){var _1BZ=new T(function(){var _1C0=new T(function(){var _1C1=B(_6e(_6B,_1uR));if(!_1C1._){return __Z;}else{return B(_1qQ(new T2(1,_1C1.a,new T(function(){return B(_1rC(_1rk,_1C1.b));}))));}}),_1C2=new T(function(){var _1C3=function(_1C4){var _1C5=E(_1C4);if(!_1C5._){return __Z;}else{var _1C6=E(_1C5.a);return new T2(1,_1C6.a,new T2(1,_1C6.b,new T(function(){return B(_1C3(_1C5.b));})));}},_1C7=B(_1C3(_1uQ));if(!_1C7._){return __Z;}else{return B(_1qQ(new T2(1,_1C7.a,new T(function(){return B(_1rC(_1rk,_1C7.b));}))));}});return B(_1rC(_1rl,new T2(1,_1C2,new T2(1,_1C0,_10))));});return B(_y(B(_1qQ(new T2(1,new T(function(){return B(_I(0,_1uG,_10));}),_1BZ))),_1rw));}),_1C8=__app2(E(_1sw),toJSStr(E(_1rm)),B(_1fP(B(_1uu(B(unAppCStr("\"",_1BY)))))));return new F(function(){return _1Ar(_,_1qY);});break;default:return new F(function(){return _1Ar(_,_1rn);});}};if(!E(_1zk.e)){var _1C9=B(_1qL(_1us,_1sW,_));return new F(function(){return _1zm(_);});}else{var _1Ca=B(_1qL(_1us,_1sV,_));return new F(function(){return _1zm(_);});}},_1Cb=E(_1uS);if(!_1Cb._){var _1Cc=B(_1qL(_1us,_1rv,_));return new F(function(){return _1zg(_);});}else{var _1Cd=new T(function(){var _1Ce=E(_1Cb.a),_1Cf=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1Cg){return new F(function(){return _1sy(_1Ce.a,_1Cg);});},new T2(1,function(_1Ch){return new F(function(){return _1sy(_1Ce.b,_1Ch);});},_10)),new T2(1,_G,new T(function(){return B(_1sB(_1Cb.b));}))));});return new T2(1,_H,_1Cf);}),_1Ci=B(_1qL(_1us,new T2(1,_2C,_1Cd),_));return new F(function(){return _1zg(_);});}},_1Cj=E(_1uR);if(!_1Cj._){var _1Ck=B(_1qL(_1us,_1rv,_));return new F(function(){return _1zf(_);});}else{var _1Cl=new T(function(){return B(_I(0,E(_1Cj.a),new T(function(){return B(_1sJ(_1Cj.b));})));}),_1Cm=B(_1qL(_1us,new T2(1,_2C,_1Cl),_));return new F(function(){return _1zf(_);});}},_1Cn=E(_1uQ);if(!_1Cn._){var _1Co=B(_1qL(_1us,_1rv,_));return new F(function(){return _1ze(_);});}else{var _1Cp=new T(function(){var _1Cq=E(_1Cn.a),_1Cr=new T(function(){return B(A3(_sc,_6x,new T2(1,function(_1Cs){return new F(function(){return _1sy(_1Cq.a,_1Cs);});},new T2(1,function(_1Ct){return new F(function(){return _1sy(_1Cq.b,_1Ct);});},_10)),new T2(1,_G,new T(function(){return B(_1sN(_1Cn.b));}))));});return new T2(1,_H,_1Cr);}),_1Cu=B(_1qL(_1us,new T2(1,_2C,_1Cp),_));return new F(function(){return _1ze(_);});}}else{return new F(function(){return _1vm(_,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1vf,_1uO,_1uP,_1uQ,_1uR,_1uS,_1ve,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_10,_1v2,_1v3,_1vd,_1vc);});}}}}}}}else{if(!E(_1va)){return {_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E({_:0,a:E(_1v4),b:E(_1v5),c:E(_1v6),d:E(_ws),e:E(_1v8),f:E(_ws),g:E(_ws),h:E(_1vb)}),s:E(_1vc)};}else{var _1Cv=B(_1qL(_1us,_1ru,_)),_1Cw=new T(function(){var _1Cx=B(_1fT(_1uZ));return new T2(0,_1Cx.a,_1Cx.b);}),_1Cy=new T(function(){return E(E(_1Cw).a);}),_1Cz=function(_1CA,_1CB){var _1CC=E(_1CA);switch(_1CC){case  -2:return {_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)};case  -1:var _1CD=E(_1uy),_1CE=B(_nQ(_1CD.a,_1CD.b,_1vj,{_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)},_));return new T(function(){return {_:0,a:E(_1vg),b:E(_1vf),c:E(B(_19R(_10,new T(function(){return B(_6R(E(_1Cw).b,_1v0));})))),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E({_:0,a:E(_1v4),b:E(_1v5),c:E(_wt),d:E(_ws),e:E(_1v8),f:E(_ws),g:E(_ws),h:E(_1vb)}),s:E(_1vc)};});default:var _1CF=E(_1uy),_1CG=B(_nQ(_1CF.a,_1CF.b,_1vj,{_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)},_)),_1CH=new T(function(){if(!E(_1vb)){return E(_1r4);}else{return 2+(E(_1uN)+3|0)|0;}}),_1CI=B(_ja(_1CF,_1uA,0,_1CH,new T(function(){var _1CJ=E(_1uz)/28,_1CK=_1CJ&4294967295;if(_1CJ>=_1CK){return (_1CK-1|0)+_1uX|0;}else{return ((_1CK-1|0)-1|0)+_1uX|0;}}),_1CH,B(_Um(_1uO,_1Cy,_1CB)),_));return {_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1CC,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)};}};switch(E(B(_1gJ(E(_1uB))))){case 32:return new F(function(){return _1Cz( -1,_1qU);});break;case 72:var _1CL=E(_1v0);if(!_1CL){var _1CM=B(_mt(_1Cy,0))-1|0;return new F(function(){return _1Cz(_1CM,_1CM);});}else{var _1CN=_1CL-1|0;return new F(function(){return _1Cz(_1CN,_1CN);});}break;case 75:if(_1v0!=(B(_mt(_1Cy,0))-1|0)){var _1CO=_1v0+1|0;return new F(function(){return _1Cz(_1CO,_1CO);});}else{return new F(function(){return _1Cz(0,_1qT);});}break;case 77:var _1CP=E(_1v0);if(!_1CP){var _1CQ=B(_mt(_1Cy,0))-1|0;return new F(function(){return _1Cz(_1CQ,_1CQ);});}else{var _1CR=_1CP-1|0;return new F(function(){return _1Cz(_1CR,_1CR);});}break;case 80:if(_1v0!=(B(_mt(_1Cy,0))-1|0)){var _1CS=_1v0+1|0;return new F(function(){return _1Cz(_1CS,_1CS);});}else{return new F(function(){return _1Cz(0,_1qT);});}break;case 104:if(_1v0!=(B(_mt(_1Cy,0))-1|0)){var _1CT=_1v0+1|0;return new F(function(){return _1Cz(_1CT,_1CT);});}else{return new F(function(){return _1Cz(0,_1qT);});}break;case 106:if(_1v0!=(B(_mt(_1Cy,0))-1|0)){var _1CU=_1v0+1|0;return new F(function(){return _1Cz(_1CU,_1CU);});}else{return new F(function(){return _1Cz(0,_1qT);});}break;case 107:var _1CV=E(_1v0);if(!_1CV){var _1CW=B(_mt(_1Cy,0))-1|0;return new F(function(){return _1Cz(_1CW,_1CW);});}else{var _1CX=_1CV-1|0;return new F(function(){return _1Cz(_1CX,_1CX);});}break;case 108:var _1CY=E(_1v0);if(!_1CY){var _1CZ=B(_mt(_1Cy,0))-1|0;return new F(function(){return _1Cz(_1CZ,_1CZ);});}else{var _1D0=_1CY-1|0;return new F(function(){return _1Cz(_1D0,_1D0);});}break;default:return new F(function(){return _1Cz( -2,_1qV);});}}}};if(!E(_1v6)){return new F(function(){return _1vh(_);});}else{if(!E(_1v7)){return new F(function(){return _Xi(_1uy,_1uz,_1uA,_1uC,_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL,_1uM,_1uN,_1uO,_1uP,_1uQ,_1uR,_1uS,_1uT,_1uU,_1uV,_1uW,_1uX,_1uY,_1uZ,_1v0,_1v1,_1v2,_1v3,_1v4,_1v5,_ws,_1v8,_wt,_1va,_1vb,_1vc,_);});}else{return new F(function(){return _1vh(_);});}}}else{return {_:0,a:E(_1vg),b:E(_1vf),c:E(_1uO),d:E(_1uP),e:E(_1uQ),f:E(_1uR),g:E(_1uS),h:E(_1ve),i:_1uV,j:_1uW,k:_1uX,l:_1uY,m:E(_1uZ),n:_1v0,o:E(_1v1),p:E(_1v2),q:_1v3,r:E(_1vd),s:E(_1vc)};}},_1D1=function(_1D2,_1D3,_1D4){var _1D5=E(_1D4);if(!_1D5._){return 0;}else{var _1D6=_1D5.b,_1D7=E(_1D5.a),_1D8=_1D7.a,_1D9=_1D7.b;return (_1D2<=_1D8)?1+B(_1D1(_1D2,_1D3,_1D6))|0:(_1D2>=_1D8+_1D7.c)?1+B(_1D1(_1D2,_1D3,_1D6))|0:(_1D3<=_1D9)?1+B(_1D1(_1D2,_1D3,_1D6))|0:(_1D3>=_1D9+_1D7.d)?1+B(_1D1(_1D2,_1D3,_1D6))|0:1;}},_1Da=function(_1Db,_1Dc,_1Dd){var _1De=E(_1Dd);if(!_1De._){return 0;}else{var _1Df=_1De.b,_1Dg=E(_1De.a),_1Dh=_1Dg.a,_1Di=_1Dg.b;if(_1Db<=_1Dh){return 1+B(_1Da(_1Db,_1Dc,_1Df))|0;}else{if(_1Db>=_1Dh+_1Dg.c){return 1+B(_1Da(_1Db,_1Dc,_1Df))|0;}else{var _1Dj=E(_1Dc);return (_1Dj<=_1Di)?1+B(_1D1(_1Db,_1Dj,_1Df))|0:(_1Dj>=_1Di+_1Dg.d)?1+B(_1D1(_1Db,_1Dj,_1Df))|0:1;}}}},_1Dk=function(_1Dl,_1Dm,_1Dn){var _1Do=E(_1Dn);if(!_1Do._){return 0;}else{var _1Dp=_1Do.b,_1Dq=E(_1Do.a),_1Dr=_1Dq.a,_1Ds=_1Dq.b,_1Dt=E(_1Dl);if(_1Dt<=_1Dr){return 1+B(_1Da(_1Dt,_1Dm,_1Dp))|0;}else{if(_1Dt>=_1Dr+_1Dq.c){return 1+B(_1Da(_1Dt,_1Dm,_1Dp))|0;}else{var _1Du=E(_1Dm);return (_1Du<=_1Ds)?1+B(_1D1(_1Dt,_1Du,_1Dp))|0:(_1Du>=_1Ds+_1Dq.d)?1+B(_1D1(_1Dt,_1Du,_1Dp))|0:1;}}}},_1Dv=function(_1Dw,_1Dx){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1Dx)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1Dx)-100,E(_1Dw),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1Dw),100);}),new T2(1,new T(function(){return new T4(0,E(_1Dw)-100,100,100,E(_1Dx)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1Dw)-200,E(_1Dx)-200);}),_10)))));},_1Dy=32,_1Dz=76,_1DA=75,_1DB=74,_1DC=72,_1DD=64,_1DE=function(_1DF,_1DG,_1DH,_1DI){var _1DJ=new T(function(){var _1DK=E(_1DG),_1DL=E(_1DK.a),_1DM=_1DL.a,_1DN=_1DL.b,_1DO=B(_1Dv(_1DM,_1DN)),_1DP=new T(function(){var _1DQ=E(_1DK.b);return new T2(0,new T(function(){return B(_g8(_1DM,_1DQ.a));}),new T(function(){return B(_g8(_1DN,_1DQ.b));}));});switch(B(_1Dk(new T(function(){return E(_1DH)*E(E(_1DP).a);},1),new T(function(){return E(_1DI)*E(E(_1DP).b);},1),new T2(1,_1DO.a,_1DO.b)))){case 1:return E(_1DC);break;case 2:return E(_1DB);break;case 3:return E(_1DA);break;case 4:return E(_1Dz);break;case 5:return E(_1Dy);break;default:return E(_1DD);}});return function(_1DR,_){var _1DS=E(E(_1DG).a),_1DT=E(_1DR),_1DU=E(_1DT.a),_1DV=E(_1DT.b),_1DW=E(_1DT.h),_1DX=E(_1DT.r);return new F(function(){return _1ux(_1DF,_1DS.a,_1DS.b,_1DJ,_1DU.a,_1DU.b,_1DU.c,_1DU.d,_1DU.e,_1DU.f,_1DU.g,_1DU.h,_1DU.i,_1DU.j,_1DV.a,_1DV.b,_1DT.c,_1DT.d,_1DT.e,_1DT.f,_1DT.g,_1DW.a,_1DW.b,_1DT.i,_1DT.j,_1DT.k,_1DT.l,_1DT.m,_1DT.n,_1DT.o,_1DT.p,_1DT.q,_1DX.a,_1DX.b,_1DX.c,_1DX.d,_1DX.e,_1DX.f,_1DX.g,_1DX.h,_1DT.s,_);});};},_1DY=0,_1DZ=2,_1E0=2,_1E1=0,_1E2=new T(function(){return eval("document");}),_1E3=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1E4=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1E5=function(_1E6){return E(E(_1E6).b);},_1E7=function(_1E8,_1E9){return new F(function(){return A2(_1E5,_1E8,function(_){var _1Ea=E(_1E9),_1Eb=__app1(E(_1E4),_1Ea);if(!_1Eb){return _0;}else{var _1Ec=__app1(E(_1E3),_1Ea);return new T1(1,new T2(0,_1Ec,_1Ea));}});});},_1Ed=new T(function(){var _1Ee=E(_1aD);if(!_1Ee._){return E(_nh);}else{return {_:0,a:E(_1am),b:E(B(_17q(_1ab,5,_1b6))),c:E(_1Ee.a),d:32,e:0,f:E(_10),g:0,h:E(_10),i:E(_ws),j:E(_ws)};}}),_1Ef=0,_1Eg=new T2(0,_1Ef,_1Ef),_1Eh={_:0,a:E(_ws),b:E(_ws),c:E(_wt),d:E(_ws),e:E(_ws),f:E(_ws),g:E(_ws),h:E(_ws)},_1Ei=new T(function(){return {_:0,a:E(_1Ed),b:E(_1ae),c:E(_18B),d:E(_10),e:E(_10),f:E(_10),g:E(_10),h:E(_1Eg),i:0,j:0,k:0,l: -1,m:E(_10),n:0,o:E(_10),p:E(_10),q:0,r:E(_1Eh),s:E(_10)};}),_1Ej=new T1(0,100),_1Ek=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1El=new T6(0,_0,_2V,_10,_1Ek,_0,_0),_1Em=new T(function(){return B(_2T(_1El));}),_1En=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1Eo=new T6(0,_0,_2V,_10,_1En,_0,_0),_1Ep=new T(function(){return B(_2T(_1Eo));}),_1Eq=new T1(1,50),_1Er=function(_1Es){return E(E(_1Es).a);},_1Et=function(_1Eu){return E(E(_1Eu).a);},_1Ev=function(_1Ew){return E(E(_1Ew).b);},_1Ex=function(_1Ey){return E(E(_1Ey).b);},_1Ez=function(_1EA){return E(E(_1EA).a);},_1EB=function(_){return new F(function(){return nMV(_0);});},_1EC=new T(function(){return B(_3(_1EB));}),_1ED=function(_1EE){return E(E(_1EE).b);},_1EF=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1EG=function(_1EH){return E(E(_1EH).d);},_1EI=function(_1EJ,_1EK,_1EL,_1EM,_1EN,_1EO){var _1EP=B(_1Er(_1EJ)),_1EQ=B(_1Et(_1EP)),_1ER=new T(function(){return B(_1E5(_1EP));}),_1ES=new T(function(){return B(_1EG(_1EQ));}),_1ET=new T(function(){return B(A1(_1EK,_1EM));}),_1EU=new T(function(){return B(A2(_1Ez,_1EL,_1EN));}),_1EV=function(_1EW){return new F(function(){return A1(_1ES,new T3(0,_1EU,_1ET,_1EW));});},_1EX=function(_1EY){var _1EZ=new T(function(){var _1F0=new T(function(){var _1F1=__createJSFunc(2,function(_1F2,_){var _1F3=B(A2(E(_1EY),_1F2,_));return _7;}),_1F4=_1F1;return function(_){return new F(function(){return __app3(E(_1EF),E(_1ET),E(_1EU),_1F4);});};});return B(A1(_1ER,_1F0));});return new F(function(){return A3(_1Ev,_1EQ,_1EZ,_1EV);});},_1F5=new T(function(){var _1F6=new T(function(){return B(_1E5(_1EP));}),_1F7=function(_1F8){var _1F9=new T(function(){return B(A1(_1F6,function(_){var _=wMV(E(_1EC),new T1(1,_1F8));return new F(function(){return A(_1Ex,[_1EL,_1EN,_1F8,_]);});}));});return new F(function(){return A3(_1Ev,_1EQ,_1F9,_1EO);});};return B(A2(_1ED,_1EJ,_1F7));});return new F(function(){return A3(_1Ev,_1EQ,_1F5,_1EX);});},_1Fa=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1Fb=function(_){var _1Fc=rMV(E(_1EC)),_1Fd=E(_1Fc);if(!_1Fd._){var _1Fe=__app1(E(_1Fa),E(_7));return new F(function(){return _gF(_);});}else{var _1Ff=__app1(E(_1Fa),E(_1Fd.a));return new F(function(){return _gF(_);});}},_1Fg=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1Fh=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1Fi=function(_1Fj,_1Fk,_1Fl){var _1Fm=B(_1Er(_1Fj)),_1Fn=new T(function(){return B(_1E5(_1Fm));}),_1Fo=function(_1Fp){var _1Fq=function(_){var _1Fr=E(_1Fk);if(!_1Fr._){var _1Fs=B(A1(_1Fp,_gE)),_1Ft=__createJSFunc(0,function(_){var _1Fu=B(A1(_1Fs,_));return _7;}),_1Fv=__app2(E(_1Fh),_1Fr.a,_1Ft);return new T(function(){var _1Fw=Number(_1Fv),_1Fx=jsTrunc(_1Fw);return new T2(0,_1Fx,E(_1Fr));});}else{var _1Fy=B(A1(_1Fp,_gE)),_1Fz=__createJSFunc(0,function(_){var _1FA=B(A1(_1Fy,_));return _7;}),_1FB=__app2(E(_1Fg),_1Fr.a,_1Fz);return new T(function(){var _1FC=Number(_1FB),_1FD=jsTrunc(_1FC);return new T2(0,_1FD,E(_1Fr));});}};return new F(function(){return A1(_1Fn,_1Fq);});},_1FE=new T(function(){return B(A2(_1ED,_1Fj,function(_1FF){return E(_1Fl);}));});return new F(function(){return A3(_1Ev,B(_1Et(_1Fm)),_1FE,_1Fo);});},_1FG=function(_,_1FH){var _1FI=E(_1FH);if(!_1FI._){return new F(function(){return die(_1Em);});}else{var _1FJ=_1FI.a,_1FK=B(A3(_1E7,_5X,_1FJ,_)),_1FL=E(_1FK);if(!_1FL._){return new F(function(){return die(_1Ep);});}else{var _1FM=E(_1FL.a),_1FN=B(_63(_1FM.b,_)),_1FO=_1FN,_1FP=nMV(_1Ei),_1FQ=_1FP,_1FR=B(A(_1EI,[_5Y,_3E,_u,_1E2,_1DZ,function(_1FS,_){var _1FT=B(_1Fb(_)),_1FU=rMV(_1FQ),_1FV=E(E(_1FO).a),_1FW=E(_1FU),_1FX=E(_1FW.a),_1FY=E(_1FW.b),_1FZ=E(_1FW.h),_1G0=E(_1FW.r),_1G1=B(_1ux(_1FM,_1FV.a,_1FV.b,E(_1FS).a,_1FX.a,_1FX.b,_1FX.c,_1FX.d,_1FX.e,_1FX.f,_1FX.g,_1FX.h,_1FX.i,_1FX.j,_1FY.a,_1FY.b,_1FW.c,_1FW.d,_1FW.e,_1FW.f,_1FW.g,_1FZ.a,_1FZ.b,_1FW.i,_1FW.j,_1FW.k,_1FW.l,_1FW.m,_1FW.n,_1FW.o,_1FW.p,_1FW.q,_1G0.a,_1G0.b,_1G0.c,_1G0.d,_1G0.e,_1G0.f,_1G0.g,_1G0.h,_1FW.s,_)),_=wMV(_1FQ,_1G1);return _gE;},_])),_1G2=B(A(_1EI,[_5Y,_3E,_3D,_1FJ,_1DY,function(_1G3,_){var _1G4=E(E(_1G3).a),_1G5=rMV(_1FQ),_1G6=B(A(_1DE,[_1FM,_1FO,_1G4.a,_1G4.b,_1G5,_])),_=wMV(_1FQ,_1G6);return _gE;},_])),_1G7=B(A(_1EI,[_5Y,_3E,_5d,_1FJ,_1E1,function(_1G8,_){var _1G9=E(_1G8),_1Ga=rMV(_1FQ),_1Gb=E(_1Ga);if(!E(E(_1Gb.r).e)){var _=wMV(_1FQ,_1Gb);return _gE;}else{var _1Gc=B(_1Fb(_)),_=wMV(_1FQ,_1Gb);return _gE;}},_])),_1Gd=function(_){var _1Ge=rMV(_1FQ),_=wMV(_1FQ,new T(function(){var _1Gf=E(_1Ge),_1Gg=E(_1Gf.r);return {_:0,a:E(_1Gf.a),b:E(_1Gf.b),c:E(_1Gf.c),d:E(_1Gf.d),e:E(_1Gf.e),f:E(_1Gf.f),g:E(_1Gf.g),h:E(_1Gf.h),i:_1Gf.i,j:_1Gf.j,k:_1Gf.k,l:_1Gf.l,m:E(_1Gf.m),n:_1Gf.n,o:E(_1Gf.o),p:E(_1Gf.p),q:_1Gf.q,r:E({_:0,a:E(_1Gg.a),b:E(_1Gg.b),c:E(_1Gg.c),d:E(_1Gg.d),e:E(_ws),f:E(_1Gg.f),g:E(_1Gg.g),h:E(_1Gg.h)}),s:E(_1Gf.s)};}));return _gE;},_1Gh=function(_1Gi,_){var _1Gj=E(_1Gi),_1Gk=rMV(_1FQ),_=wMV(_1FQ,new T(function(){var _1Gl=E(_1Gk),_1Gm=E(_1Gl.r);return {_:0,a:E(_1Gl.a),b:E(_1Gl.b),c:E(_1Gl.c),d:E(_1Gl.d),e:E(_1Gl.e),f:E(_1Gl.f),g:E(_1Gl.g),h:E(_1Gl.h),i:_1Gl.i,j:_1Gl.j,k:_1Gl.k,l:_1Gl.l,m:E(_1Gl.m),n:_1Gl.n,o:E(_1Gl.o),p:E(_1Gl.p),q:_1Gl.q,r:E({_:0,a:E(_1Gm.a),b:E(_1Gm.b),c:E(_1Gm.c),d:E(_1Gm.d),e:E(_wt),f:E(_1Gm.f),g:E(_1Gm.g),h:E(_1Gm.h)}),s:E(_1Gl.s)};})),_1Gn=B(A(_1Fi,[_5Y,_1Ej,_1Gd,_]));return _gE;},_1Go=B(A(_1EI,[_5Y,_3E,_5d,_1FJ,_1E0,_1Gh,_])),_1Gp=B(A(_1Fi,[_5Y,_1Eq,function(_){var _1Gq=rMV(_1FQ),_1Gr=E(E(_1FO).a),_1Gs=E(_1Gq),_1Gt=E(_1Gs.a),_1Gu=E(_1Gs.b),_1Gv=E(_1Gs.h),_1Gw=E(_1Gs.r),_1Gx=B(_V1(_1FM,_1Gr.a,_1Gr.b,_1Gt.a,_1Gt.b,_1Gt.c,_1Gt.d,_1Gt.e,_1Gt.f,_1Gt.g,_1Gt.h,_1Gt.i,_1Gt.j,_1Gu.a,_1Gu.b,_1Gs.c,_1Gs.d,_1Gs.e,_1Gs.f,_1Gs.g,_1Gv.a,_1Gv.b,_1Gs.i,_1Gs.j,_1Gs.k,_1Gs.l,_1Gs.m,_1Gs.n,_1Gs.o,_1Gs.p,_1Gs.q,_1Gw.a,_1Gw.b,_1Gw.c,_1Gw.d,_1Gw.e,_1Gw.f,_1Gw.g,_1Gw.h,_1Gs.s,_)),_=wMV(_1FQ,_1Gx);return _gE;},_]));return _gE;}}},_1Gy="src",_1Gz=new T(function(){return B(unCStr("img"));}),_1GA=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1GB=function(_1GC,_1GD){return new F(function(){return A2(_1E5,_1GC,function(_){var _1GE=__app1(E(_1GA),toJSStr(E(_1Gz))),_1GF=__app3(E(_i1),_1GE,E(_1Gy),E(_1GD));return _1GE;});});},_1GG=new T(function(){return B(unCStr(".png"));}),_1GH=function(_1GI,_1GJ){var _1GK=E(_1GI);if(_1GK==( -1)){return __Z;}else{var _1GL=new T(function(){var _1GM=new T(function(){return toJSStr(B(_y(_1GJ,new T(function(){return B(_y(B(_I(0,_1GK,_10)),_1GG));},1))));});return B(_1GB(_5X,_1GM));});return new F(function(){return _y(B(_1GH(_1GK-1|0,_1GJ)),new T2(1,_1GL,_10));});}},_1GN=new T(function(){return B(unCStr("WstImage/wst"));}),_1GO=new T(function(){return B(_1GH(120,_1GN));}),_1GP=function(_1GQ,_){var _1GR=E(_1GQ);if(!_1GR._){return _10;}else{var _1GS=B(A1(_1GR.a,_)),_1GT=B(_1GP(_1GR.b,_));return new T2(1,_1GS,_1GT);}},_1GU=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1GV=new T(function(){return B(_1GH(57,_1GU));}),_1GW=function(_1GX,_){var _1GY=E(_1GX);if(!_1GY._){return _10;}else{var _1GZ=B(A1(_1GY.a,_)),_1H0=B(_1GW(_1GY.b,_));return new T2(1,_1GZ,_1H0);}},_1H1=new T(function(){return B(unCStr("Images/img"));}),_1H2=new T(function(){return B(_1GH(5,_1H1));}),_1H3=function(_1H4,_){var _1H5=E(_1H4);if(!_1H5._){return _10;}else{var _1H6=B(A1(_1H5.a,_)),_1H7=B(_1H3(_1H5.b,_));return new T2(1,_1H6,_1H7);}},_1H8=function(_){var _1H9=B(_1H3(_1H2,_)),_1Ha=B(_1GW(_1GV,_)),_1Hb=B(_1GP(_1GO,_)),_1Hc=__app1(E(_1),"canvas"),_1Hd=__eq(_1Hc,E(_7));if(!E(_1Hd)){var _1He=__isUndef(_1Hc);if(!E(_1He)){return new F(function(){return _1FG(_,new T1(1,_1Hc));});}else{return new F(function(){return _1FG(_,_0);});}}else{return new F(function(){return _1FG(_,_0);});}},_1Hf=function(_){return new F(function(){return _1H8(_);});};
var hasteMain = function() {B(A(_1Hf, [0]));};window.onload = hasteMain;