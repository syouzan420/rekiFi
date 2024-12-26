"use strict";
var __haste_prog_id = '95be907d71df419d107a78e89bdcbbbf9cd199df2c3963221955743373cf14b4';
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

var _0=function(_1,_2){while(1){var _3=B((function(_4,_5){var _6=E(_5);if(!_6._){_1=new T2(1,new T2(0,_6.b,_6.c),new T(function(){return B(_0(_4,_6.e));}));_2=_6.d;return __continue;}else{return E(_4);}})(_1,_2));if(_3!=__continue){return _3;}}},_7="metaKey",_8="shiftKey",_9="altKey",_a="ctrlKey",_b="keyCode",_c=function(_d,_){var _e=__get(_d,E(_b)),_f=__get(_d,E(_a)),_g=__get(_d,E(_9)),_h=__get(_d,E(_8)),_i=__get(_d,E(_7));return new T(function(){var _j=Number(_e),_k=jsTrunc(_j);return new T5(0,_k,E(_f),E(_g),E(_h),E(_i));});},_l=function(_m,_n,_){return new F(function(){return _c(E(_n),_);});},_o="keydown",_p="keyup",_q="keypress",_r=function(_s){switch(E(_s)){case 0:return E(_q);case 1:return E(_p);default:return E(_o);}},_t=new T2(0,_r,_l),_u="deltaZ",_v="deltaY",_w="deltaX",_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return B(_x(_A.b,_z));}));},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _x(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{return new T2(1,_G,new T(function(){var _L=jsShowI(_J);return B(_x(fromJSStr(_L),new T2(1,_F,_K)));}));}}},_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(_H(0,2,_M));}),_O=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_N));}),_P=function(_Q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_H(0,_Q,_O));}))));});},_R=function(_S,_){return new T(function(){var _T=Number(E(_S)),_U=jsTrunc(_T);if(_U<0){return B(_P(_U));}else{if(_U>2){return B(_P(_U));}else{return _U;}}});},_V=0,_W=new T3(0,_V,_V,_V),_X="button",_Y=new T(function(){return eval("jsGetMouseCoords");}),_Z=__Z,_10=function(_11,_){var _12=E(_11);if(!_12._){return _Z;}else{var _13=B(_10(_12.b,_));return new T2(1,new T(function(){var _14=Number(E(_12.a));return jsTrunc(_14);}),_13);}},_15=function(_16,_){var _17=__arr2lst(0,_16);return new F(function(){return _10(_17,_);});},_18=function(_19,_){return new F(function(){return _15(E(_19),_);});},_1a=function(_1b,_){return new T(function(){var _1c=Number(E(_1b));return jsTrunc(_1c);});},_1d=new T2(0,_1a,_18),_1e=function(_1f,_){var _1g=E(_1f);if(!_1g._){return _Z;}else{var _1h=B(_1e(_1g.b,_));return new T2(1,_1g.a,_1h);}},_1i=new T(function(){return B(unCStr("base"));}),_1j=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1k=new T(function(){return B(unCStr("IOException"));}),_1l=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1i,_1j,_1k),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1l,_Z,_Z),_1n=function(_1o){return E(_1m);},_1p=function(_1q){return E(E(_1q).a);},_1r=function(_1s,_1t,_1u){var _1v=B(A1(_1s,_)),_1w=B(A1(_1t,_)),_1x=hs_eqWord64(_1v.a,_1w.a);if(!_1x){return __Z;}else{var _1y=hs_eqWord64(_1v.b,_1w.b);return (!_1y)?__Z:new T1(1,_1u);}},_1z=function(_1A){var _1B=E(_1A);return new F(function(){return _1r(B(_1p(_1B.a)),_1n,_1B.b);});},_1C=new T(function(){return B(unCStr(": "));}),_1D=new T(function(){return B(unCStr(")"));}),_1E=new T(function(){return B(unCStr(" ("));}),_1F=new T(function(){return B(unCStr("interrupted"));}),_1G=new T(function(){return B(unCStr("system error"));}),_1H=new T(function(){return B(unCStr("unsatisified constraints"));}),_1I=new T(function(){return B(unCStr("user error"));}),_1J=new T(function(){return B(unCStr("permission denied"));}),_1K=new T(function(){return B(unCStr("illegal operation"));}),_1L=new T(function(){return B(unCStr("end of file"));}),_1M=new T(function(){return B(unCStr("resource exhausted"));}),_1N=new T(function(){return B(unCStr("resource busy"));}),_1O=new T(function(){return B(unCStr("does not exist"));}),_1P=new T(function(){return B(unCStr("already exists"));}),_1Q=new T(function(){return B(unCStr("resource vanished"));}),_1R=new T(function(){return B(unCStr("timeout"));}),_1S=new T(function(){return B(unCStr("unsupported operation"));}),_1T=new T(function(){return B(unCStr("hardware fault"));}),_1U=new T(function(){return B(unCStr("inappropriate type"));}),_1V=new T(function(){return B(unCStr("invalid argument"));}),_1W=new T(function(){return B(unCStr("failed"));}),_1X=new T(function(){return B(unCStr("protocol error"));}),_1Y=function(_1Z,_20){switch(E(_1Z)){case 0:return new F(function(){return _x(_1P,_20);});break;case 1:return new F(function(){return _x(_1O,_20);});break;case 2:return new F(function(){return _x(_1N,_20);});break;case 3:return new F(function(){return _x(_1M,_20);});break;case 4:return new F(function(){return _x(_1L,_20);});break;case 5:return new F(function(){return _x(_1K,_20);});break;case 6:return new F(function(){return _x(_1J,_20);});break;case 7:return new F(function(){return _x(_1I,_20);});break;case 8:return new F(function(){return _x(_1H,_20);});break;case 9:return new F(function(){return _x(_1G,_20);});break;case 10:return new F(function(){return _x(_1X,_20);});break;case 11:return new F(function(){return _x(_1W,_20);});break;case 12:return new F(function(){return _x(_1V,_20);});break;case 13:return new F(function(){return _x(_1U,_20);});break;case 14:return new F(function(){return _x(_1T,_20);});break;case 15:return new F(function(){return _x(_1S,_20);});break;case 16:return new F(function(){return _x(_1R,_20);});break;case 17:return new F(function(){return _x(_1Q,_20);});break;default:return new F(function(){return _x(_1F,_20);});}},_21=new T(function(){return B(unCStr("}"));}),_22=new T(function(){return B(unCStr("{handle: "));}),_23=function(_24,_25,_26,_27,_28,_29){var _2a=new T(function(){var _2b=new T(function(){var _2c=new T(function(){var _2d=E(_27);if(!_2d._){return E(_29);}else{var _2e=new T(function(){return B(_x(_2d,new T(function(){return B(_x(_1D,_29));},1)));},1);return B(_x(_1E,_2e));}},1);return B(_1Y(_25,_2c));}),_2f=E(_26);if(!_2f._){return E(_2b);}else{return B(_x(_2f,new T(function(){return B(_x(_1C,_2b));},1)));}}),_2g=E(_28);if(!_2g._){var _2h=E(_24);if(!_2h._){return E(_2a);}else{var _2i=E(_2h.a);if(!_2i._){var _2j=new T(function(){var _2k=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2k));},1);return new F(function(){return _x(_22,_2j);});}else{var _2l=new T(function(){var _2m=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2m));},1);return new F(function(){return _x(_22,_2l);});}}}else{return new F(function(){return _x(_2g.a,new T(function(){return B(_x(_1C,_2a));},1));});}},_2n=function(_2o){var _2p=E(_2o);return new F(function(){return _23(_2p.a,_2p.b,_2p.c,_2p.d,_2p.f,_Z);});},_2q=function(_2r,_2s,_2t){var _2u=E(_2s);return new F(function(){return _23(_2u.a,_2u.b,_2u.c,_2u.d,_2u.f,_2t);});},_2v=function(_2w,_2x){var _2y=E(_2w);return new F(function(){return _23(_2y.a,_2y.b,_2y.c,_2y.d,_2y.f,_2x);});},_2z=44,_2A=93,_2B=91,_2C=function(_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){return new F(function(){return unAppCStr("[]",_2F);});}else{var _2H=new T(function(){var _2I=new T(function(){var _2J=function(_2K){var _2L=E(_2K);if(!_2L._){return E(new T2(1,_2A,_2F));}else{var _2M=new T(function(){return B(A2(_2D,_2L.a,new T(function(){return B(_2J(_2L.b));})));});return new T2(1,_2z,_2M);}};return B(_2J(_2G.b));});return B(A2(_2D,_2G.a,_2I));});return new T2(1,_2B,_2H);}},_2N=function(_2O,_2P){return new F(function(){return _2C(_2v,_2O,_2P);});},_2Q=new T3(0,_2q,_2n,_2N),_2R=new T(function(){return new T5(0,_1n,_2Q,_2S,_1z,_2n);}),_2S=function(_2T){return new T2(0,_2R,_2T);},_2U=__Z,_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_2U,_2V,_Z,_2W,_2U,_2U),_2Y=new T(function(){return B(_2S(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1e(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_){return new F(function(){return __jsNull();});},_3d=function(_3e){var _3f=B(A1(_3e,_));return E(_3f);},_3g=new T(function(){return B(_3d(_3c));}),_3h=new T(function(){return E(_3g);}),_3i=function(_3j,_3k,_){if(E(_3j)==7){var _3l=__app1(E(_Y),_3k),_3m=B(_32(_1d,_1d,_3l,_)),_3n=__get(_3k,E(_w)),_3o=__get(_3k,E(_v)),_3p=__get(_3k,E(_u));return new T(function(){return new T3(0,E(_3m),E(_2U),E(new T3(0,_3n,_3o,_3p)));});}else{var _3q=__app1(E(_Y),_3k),_3r=B(_32(_1d,_1d,_3q,_)),_3s=__get(_3k,E(_X)),_3t=__eq(_3s,E(_3h));if(!E(_3t)){var _3u=__isUndef(_3s);if(!E(_3u)){var _3v=B(_R(_3s,_));return new T(function(){return new T3(0,E(_3r),E(new T1(1,_3v)),E(_W));});}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}},_3w=function(_3x,_3y,_){return new F(function(){return _3i(_3x,E(_3y),_);});},_3z="mouseout",_3A="mouseover",_3B="mousemove",_3C="mouseup",_3D="mousedown",_3E="dblclick",_3F="click",_3G="wheel",_3H=function(_3I){switch(E(_3I)){case 0:return E(_3F);case 1:return E(_3E);case 2:return E(_3D);case 3:return E(_3C);case 4:return E(_3B);case 5:return E(_3A);case 6:return E(_3z);default:return E(_3G);}},_3J=new T2(0,_3H,_3w),_3K=function(_3L){return E(_3L);},_3M=function(_3N,_3O){return E(_3N)==E(_3O);},_3P=function(_3Q,_3R){return E(_3Q)!=E(_3R);},_3S=new T2(0,_3M,_3P),_3T="screenY",_3U="screenX",_3V="clientY",_3W="clientX",_3X="pageY",_3Y="pageX",_3Z="target",_40="identifier",_41=function(_42,_){var _43=__get(_42,E(_40)),_44=__get(_42,E(_3Z)),_45=__get(_42,E(_3Y)),_46=__get(_42,E(_3X)),_47=__get(_42,E(_3W)),_48=__get(_42,E(_3V)),_49=__get(_42,E(_3U)),_4a=__get(_42,E(_3T));return new T(function(){var _4b=Number(_43),_4c=jsTrunc(_4b);return new T5(0,_4c,_44,E(new T2(0,new T(function(){var _4d=Number(_45);return jsTrunc(_4d);}),new T(function(){var _4e=Number(_46);return jsTrunc(_4e);}))),E(new T2(0,new T(function(){var _4f=Number(_47);return jsTrunc(_4f);}),new T(function(){var _4g=Number(_48);return jsTrunc(_4g);}))),E(new T2(0,new T(function(){var _4h=Number(_49);return jsTrunc(_4h);}),new T(function(){var _4i=Number(_4a);return jsTrunc(_4i);}))));});},_4j=function(_4k,_){var _4l=E(_4k);if(!_4l._){return _Z;}else{var _4m=B(_41(E(_4l.a),_)),_4n=B(_4j(_4l.b,_));return new T2(1,_4m,_4n);}},_4o="touches",_4p=function(_4q){return E(E(_4q).b);},_4r=function(_4s,_4t,_){var _4u=__arr2lst(0,_4t),_4v=new T(function(){return B(_4p(_4s));}),_4w=function(_4x,_){var _4y=E(_4x);if(!_4y._){return _Z;}else{var _4z=B(A2(_4v,_4y.a,_)),_4A=B(_4w(_4y.b,_));return new T2(1,_4z,_4A);}};return new F(function(){return _4w(_4u,_);});},_4B=function(_4C,_){return new F(function(){return _4r(_1d,E(_4C),_);});},_4D=new T2(0,_18,_4B),_4E=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4F=function(_4G){return E(E(_4G).a);},_4H=function(_4I,_4J,_4K){while(1){var _4L=E(_4K);if(!_4L._){return false;}else{if(!B(A3(_4F,_4I,_4J,_4L.a))){_4K=_4L.b;continue;}else{return true;}}}},_4M=function(_4N,_4O){while(1){var _4P=B((function(_4Q,_4R){var _4S=E(_4R);if(!_4S._){return __Z;}else{var _4T=_4S.a,_4U=_4S.b;if(!B(A1(_4Q,_4T))){var _4V=_4Q;_4N=_4V;_4O=_4U;return __continue;}else{return new T2(1,_4T,new T(function(){return B(_4M(_4Q,_4U));}));}}})(_4N,_4O));if(_4P!=__continue){return _4P;}}},_4W=function(_4X,_){var _4Y=__get(_4X,E(_4o)),_4Z=__arr2lst(0,_4Y),_50=B(_4j(_4Z,_)),_51=__app1(E(_4E),_4X),_52=B(_32(_4D,_4D,_51,_)),_53=E(_52),_54=new T(function(){var _55=function(_56){return new F(function(){return _4H(_3S,new T(function(){return E(_56).a;}),_53.a);});};return B(_4M(_55,_50));}),_57=new T(function(){var _58=function(_59){return new F(function(){return _4H(_3S,new T(function(){return E(_59).a;}),_53.b);});};return B(_4M(_58,_50));});return new T3(0,_50,_57,_54);},_5a=function(_5b,_5c,_){return new F(function(){return _4W(E(_5c),_);});},_5d="touchcancel",_5e="touchend",_5f="touchmove",_5g="touchstart",_5h=function(_5i){switch(E(_5i)){case 0:return E(_5g);case 1:return E(_5f);case 2:return E(_5e);default:return E(_5d);}},_5j=new T2(0,_5h,_5a),_5k=function(_5l,_5m,_){var _5n=B(A1(_5l,_)),_5o=B(A1(_5m,_));return _5n;},_5p=function(_5q,_5r,_){var _5s=B(A1(_5q,_)),_5t=B(A1(_5r,_));return new T(function(){return B(A1(_5s,_5t));});},_5u=function(_5v,_5w,_){var _5x=B(A1(_5w,_));return _5v;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5A,_));return new T(function(){return B(A1(_5z,_5B));});},_5C=new T2(0,_5y,_5u),_5D=function(_5E,_){return _5E;},_5F=function(_5G,_5H,_){var _5I=B(A1(_5G,_));return new F(function(){return A1(_5H,_);});},_5J=new T5(0,_5C,_5D,_5p,_5F,_5k),_5K=new T(function(){return E(_2R);}),_5L=function(_5M){return E(E(_5M).c);},_5N=function(_5O){return new T6(0,_2U,_2V,_Z,_5O,_2U,_2U);},_5P=function(_5Q,_){var _5R=new T(function(){return B(A2(_5L,_5K,new T(function(){return B(A1(_5N,_5Q));})));});return new F(function(){return die(_5R);});},_5S=function(_5T,_){return new F(function(){return _5P(_5T,_);});},_5U=function(_5V){return new F(function(){return A1(_5S,_5V);});},_5W=function(_5X,_5Y,_){var _5Z=B(A1(_5X,_));return new F(function(){return A2(_5Y,_5Z,_);});},_60=new T5(0,_5J,_5W,_5F,_5D,_5U),_61=function(_62){return E(_62);},_63=new T2(0,_60,_61),_64=new T2(0,_63,_5D),_65=function(_66,_67){while(1){var _68=E(_66);if(!_68._){return (E(_67)._==0)?1:0;}else{var _69=E(_67);if(!_69._){return 2;}else{var _6a=E(_68.a),_6b=E(_69.a);if(_6a!=_6b){return (_6a>_6b)?2:0;}else{_66=_68.b;_67=_69.b;continue;}}}}},_6c=new T0(1),_6d=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_6e=function(_6f){return new F(function(){return err(_6d);});},_6g=new T(function(){return B(_6e(_));}),_6h=function(_6i,_6j,_6k,_6l){var _6m=E(_6k);if(!_6m._){var _6n=_6m.a,_6o=E(_6l);if(!_6o._){var _6p=_6o.a,_6q=_6o.b,_6r=_6o.c;if(_6p<=(imul(3,_6n)|0)){return new T5(0,(1+_6n|0)+_6p|0,E(_6i),_6j,E(_6m),E(_6o));}else{var _6s=E(_6o.d);if(!_6s._){var _6t=_6s.a,_6u=_6s.b,_6v=_6s.c,_6w=_6s.d,_6x=E(_6o.e);if(!_6x._){var _6y=_6x.a;if(_6t>=(imul(2,_6y)|0)){var _6z=function(_6A){var _6B=E(_6i),_6C=E(_6s.e);return (_6C._==0)?new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,(1+_6y|0)+_6C.a|0,E(_6q),_6r,E(_6C),E(_6x)))):new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,1+_6y|0,E(_6q),_6r,E(_6c),E(_6x))));},_6D=E(_6w);if(!_6D._){return new F(function(){return _6z(_6D.a);});}else{return new F(function(){return _6z(0);});}}else{return new T5(0,(1+_6n|0)+_6p|0,E(_6q),_6r,E(new T5(0,(1+_6n|0)+_6t|0,E(_6i),_6j,E(_6m),E(_6s))),E(_6x));}}else{return E(_6g);}}else{return E(_6g);}}}else{return new T5(0,1+_6n|0,E(_6i),_6j,E(_6m),E(_6c));}}else{var _6E=E(_6l);if(!_6E._){var _6F=_6E.a,_6G=_6E.b,_6H=_6E.c,_6I=_6E.e,_6J=E(_6E.d);if(!_6J._){var _6K=_6J.a,_6L=_6J.b,_6M=_6J.c,_6N=_6J.d,_6O=E(_6I);if(!_6O._){var _6P=_6O.a;if(_6K>=(imul(2,_6P)|0)){var _6Q=function(_6R){var _6S=E(_6i),_6T=E(_6J.e);return (_6T._==0)?new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,(1+_6P|0)+_6T.a|0,E(_6G),_6H,E(_6T),E(_6O)))):new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,1+_6P|0,E(_6G),_6H,E(_6c),E(_6O))));},_6U=E(_6N);if(!_6U._){return new F(function(){return _6Q(_6U.a);});}else{return new F(function(){return _6Q(0);});}}else{return new T5(0,1+_6F|0,E(_6G),_6H,E(new T5(0,1+_6K|0,E(_6i),_6j,E(_6c),E(_6J))),E(_6O));}}else{return new T5(0,3,E(_6L),_6M,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(new T5(0,1,E(_6G),_6H,E(_6c),E(_6c))));}}else{var _6V=E(_6I);return (_6V._==0)?new T5(0,3,E(_6G),_6H,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(_6V)):new T5(0,2,E(_6i),_6j,E(_6c),E(_6E));}}else{return new T5(0,1,E(_6i),_6j,E(_6c),E(_6c));}}},_6W=function(_6X,_6Y){return new T5(0,1,E(_6X),_6Y,E(_6c),E(_6c));},_6Z=function(_70,_71,_72){var _73=E(_72);if(!_73._){return new F(function(){return _6h(_73.b,_73.c,_73.d,B(_6Z(_70,_71,_73.e)));});}else{return new F(function(){return _6W(_70,_71);});}},_74=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_75=function(_76){return new F(function(){return err(_74);});},_77=new T(function(){return B(_75(_));}),_78=function(_79,_7a,_7b,_7c){var _7d=E(_7c);if(!_7d._){var _7e=_7d.a,_7f=E(_7b);if(!_7f._){var _7g=_7f.a,_7h=_7f.b,_7i=_7f.c;if(_7g<=(imul(3,_7e)|0)){return new T5(0,(1+_7g|0)+_7e|0,E(_79),_7a,E(_7f),E(_7d));}else{var _7j=E(_7f.d);if(!_7j._){var _7k=_7j.a,_7l=E(_7f.e);if(!_7l._){var _7m=_7l.a,_7n=_7l.b,_7o=_7l.c,_7p=_7l.d;if(_7m>=(imul(2,_7k)|0)){var _7q=function(_7r){var _7s=E(_7l.e);return (_7s._==0)?new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,(1+_7e|0)+_7s.a|0,E(_79),_7a,E(_7s),E(_7d)))):new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d))));},_7t=E(_7p);if(!_7t._){return new F(function(){return _7q(_7t.a);});}else{return new F(function(){return _7q(0);});}}else{return new T5(0,(1+_7g|0)+_7e|0,E(_7h),_7i,E(_7j),E(new T5(0,(1+_7e|0)+_7m|0,E(_79),_7a,E(_7l),E(_7d))));}}else{return E(_77);}}else{return E(_77);}}}else{return new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d));}}else{var _7u=E(_7b);if(!_7u._){var _7v=_7u.a,_7w=_7u.b,_7x=_7u.c,_7y=_7u.e,_7z=E(_7u.d);if(!_7z._){var _7A=_7z.a,_7B=E(_7y);if(!_7B._){var _7C=_7B.a,_7D=_7B.b,_7E=_7B.c,_7F=_7B.d;if(_7C>=(imul(2,_7A)|0)){var _7G=function(_7H){var _7I=E(_7B.e);return (_7I._==0)?new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1+_7I.a|0,E(_79),_7a,E(_7I),E(_6c)))):new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));},_7J=E(_7F);if(!_7J._){return new F(function(){return _7G(_7J.a);});}else{return new F(function(){return _7G(0);});}}else{return new T5(0,1+_7v|0,E(_7w),_7x,E(_7z),E(new T5(0,1+_7C|0,E(_79),_7a,E(_7B),E(_6c))));}}else{return new T5(0,3,E(_7w),_7x,E(_7z),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));}}else{var _7K=E(_7y);return (_7K._==0)?new T5(0,3,E(_7K.b),_7K.c,E(new T5(0,1,E(_7w),_7x,E(_6c),E(_6c))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c)))):new T5(0,2,E(_79),_7a,E(_7u),E(_6c));}}else{return new T5(0,1,E(_79),_7a,E(_6c),E(_6c));}}},_7L=function(_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _78(_7P.b,_7P.c,B(_7L(_7M,_7N,_7P.d)),_7P.e);});}else{return new F(function(){return _6W(_7M,_7N);});}},_7Q=function(_7R,_7S,_7T,_7U,_7V,_7W,_7X){return new F(function(){return _78(_7U,_7V,B(_7L(_7R,_7S,_7W)),_7X);});},_7Y=function(_7Z,_80,_81,_82,_83,_84,_85,_86){var _87=E(_81);if(!_87._){var _88=_87.a,_89=_87.b,_8a=_87.c,_8b=_87.d,_8c=_87.e;if((imul(3,_88)|0)>=_82){if((imul(3,_82)|0)>=_88){return new T5(0,(_88+_82|0)+1|0,E(_7Z),_80,E(_87),E(new T5(0,_82,E(_83),_84,E(_85),E(_86))));}else{return new F(function(){return _6h(_89,_8a,_8b,B(_7Y(_7Z,_80,_8c,_82,_83,_84,_85,_86)));});}}else{return new F(function(){return _78(_83,_84,B(_8d(_7Z,_80,_88,_89,_8a,_8b,_8c,_85)),_86);});}}else{return new F(function(){return _7Q(_7Z,_80,_82,_83,_84,_85,_86);});}},_8d=function(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l){var _8m=E(_8l);if(!_8m._){var _8n=_8m.a,_8o=_8m.b,_8p=_8m.c,_8q=_8m.d,_8r=_8m.e;if((imul(3,_8g)|0)>=_8n){if((imul(3,_8n)|0)>=_8g){return new T5(0,(_8g+_8n|0)+1|0,E(_8e),_8f,E(new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k))),E(_8m));}else{return new F(function(){return _6h(_8h,_8i,_8j,B(_7Y(_8e,_8f,_8k,_8n,_8o,_8p,_8q,_8r)));});}}else{return new F(function(){return _78(_8o,_8p,B(_8d(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8q)),_8r);});}}else{return new F(function(){return _6Z(_8e,_8f,new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k)));});}},_8s=function(_8t,_8u,_8v,_8w){var _8x=E(_8v);if(!_8x._){var _8y=_8x.a,_8z=_8x.b,_8A=_8x.c,_8B=_8x.d,_8C=_8x.e,_8D=E(_8w);if(!_8D._){var _8E=_8D.a,_8F=_8D.b,_8G=_8D.c,_8H=_8D.d,_8I=_8D.e;if((imul(3,_8y)|0)>=_8E){if((imul(3,_8E)|0)>=_8y){return new T5(0,(_8y+_8E|0)+1|0,E(_8t),_8u,E(_8x),E(_8D));}else{return new F(function(){return _6h(_8z,_8A,_8B,B(_7Y(_8t,_8u,_8C,_8E,_8F,_8G,_8H,_8I)));});}}else{return new F(function(){return _78(_8F,_8G,B(_8d(_8t,_8u,_8y,_8z,_8A,_8B,_8C,_8H)),_8I);});}}else{return new F(function(){return _6Z(_8t,_8u,_8x);});}}else{return new F(function(){return _7L(_8t,_8u,_8w);});}},_8J=function(_8K,_8L,_8M,_8N){var _8O=E(_8K);if(_8O==1){var _8P=E(_8N);return (_8P._==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_Z):(B(_65(_8L,E(_8P.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_8P,_Z):new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_8P);}else{var _8Q=B(_8J(_8O>>1,_8L,_8M,_8N)),_8R=_8Q.a,_8S=_8Q.c,_8T=E(_8Q.b);if(!_8T._){return new T3(0,_8R,_Z,_8S);}else{var _8U=E(_8T.a),_8V=_8U.a,_8W=_8U.b,_8X=E(_8T.b);if(!_8X._){return new T3(0,new T(function(){return B(_6Z(_8V,_8W,_8R));}),_Z,_8S);}else{var _8Y=E(_8X.a),_8Z=_8Y.a;if(!B(_65(_8V,_8Z))){var _90=B(_8J(_8O>>1,_8Z,_8Y.b,_8X.b));return new T3(0,new T(function(){return B(_8s(_8V,_8W,_8R,_90.a));}),_90.b,_90.c);}else{return new T3(0,_8R,_Z,_8T);}}}}},_91=function(_92,_93,_94){var _95=E(_92),_96=E(_94);if(!_96._){var _97=_96.b,_98=_96.c,_99=_96.d,_9a=_96.e;switch(B(_65(_95,_97))){case 0:return new F(function(){return _78(_97,_98,B(_91(_95,_93,_99)),_9a);});break;case 1:return new T5(0,_96.a,E(_95),_93,E(_99),E(_9a));default:return new F(function(){return _6h(_97,_98,_99,B(_91(_95,_93,_9a)));});}}else{return new T5(0,1,E(_95),_93,E(_6c),E(_6c));}},_9b=function(_9c,_9d){while(1){var _9e=E(_9d);if(!_9e._){return E(_9c);}else{var _9f=E(_9e.a),_9g=B(_91(_9f.a,_9f.b,_9c));_9c=_9g;_9d=_9e.b;continue;}}},_9h=function(_9i,_9j,_9k,_9l){return new F(function(){return _9b(B(_91(_9j,_9k,_9i)),_9l);});},_9m=function(_9n,_9o,_9p){var _9q=E(_9o);return new F(function(){return _9b(B(_91(_9q.a,_9q.b,_9n)),_9p);});},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v._){return E(_9t);}else{var _9w=E(_9v.a),_9x=_9w.a,_9y=_9w.b,_9z=E(_9v.b);if(!_9z._){return new F(function(){return _6Z(_9x,_9y,_9t);});}else{var _9A=E(_9z.a),_9B=_9A.a;if(!B(_65(_9x,_9B))){var _9C=B(_8J(_9s,_9B,_9A.b,_9z.b)),_9D=_9C.a,_9E=E(_9C.c);if(!_9E._){var _9F=_9s<<1,_9G=B(_8s(_9x,_9y,_9t,_9D));_9s=_9F;_9t=_9G;_9u=_9C.b;continue;}else{return new F(function(){return _9m(B(_8s(_9x,_9y,_9t,_9D)),_9E.a,_9E.b);});}}else{return new F(function(){return _9h(_9t,_9x,_9y,_9z);});}}}}},_9H=function(_9I,_9J,_9K,_9L,_9M){var _9N=E(_9M);if(!_9N._){return new F(function(){return _6Z(_9K,_9L,_9J);});}else{var _9O=E(_9N.a),_9P=_9O.a;if(!B(_65(_9K,_9P))){var _9Q=B(_8J(_9I,_9P,_9O.b,_9N.b)),_9R=_9Q.a,_9S=E(_9Q.c);if(!_9S._){return new F(function(){return _9r(_9I<<1,B(_8s(_9K,_9L,_9J,_9R)),_9Q.b);});}else{return new F(function(){return _9m(B(_8s(_9K,_9L,_9J,_9R)),_9S.a,_9S.b);});}}else{return new F(function(){return _9h(_9J,_9K,_9L,_9N);});}}},_9T=function(_9U){var _9V=E(_9U);if(!_9V._){return new T0(1);}else{var _9W=E(_9V.a),_9X=_9W.a,_9Y=_9W.b,_9Z=E(_9V.b);if(!_9Z._){return new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c));}else{var _a0=_9Z.b,_a1=E(_9Z.a),_a2=_a1.a,_a3=_a1.b;if(!B(_65(_9X,_a2))){return new F(function(){return _9H(1,new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}else{return new F(function(){return _9h(new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}}}},_a4=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_a5=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_a6=new T(function(){return eval("(function(cv){return cv.height})");}),_a7=new T(function(){return eval("(function(cv){return cv.width})");}),_a8=function(_a9,_){var _aa=__app1(E(_a7),_a9),_ab=__app1(E(_a6),_a9),_ac=__app1(E(_a5),_a9),_ad=__app1(E(_a4),_a9);return new T2(0,new T2(0,_aa,_ab),new T2(0,_ac,_ad));},_ae=function(_af,_ag){while(1){var _ah=E(_af);if(!_ah._){return (E(_ag)._==0)?true:false;}else{var _ai=E(_ag);if(!_ai._){return false;}else{if(E(_ah.a)!=E(_ai.a)){return false;}else{_af=_ah.b;_ag=_ai.b;continue;}}}}},_aj=function(_ak,_al){var _am=E(_al);return (_am._==0)?__Z:new T2(1,new T(function(){return B(A1(_ak,_am.a));}),new T(function(){return B(_aj(_ak,_am.b));}));},_an=function(_ao){return new T1(3,E(B(_aj(_61,_ao))));},_ap="Tried to deserialie a non-array to a list!",_aq=new T1(0,_ap),_ar=new T1(1,_Z),_as=function(_at){var _au=E(_at);if(!_au._){return E(_ar);}else{var _av=B(_as(_au.b));return (_av._==0)?new T1(0,_av.a):new T1(1,new T2(1,_au.a,_av.a));}},_aw=function(_ax){var _ay=E(_ax);if(_ay._==3){return new F(function(){return _as(_ay.a);});}else{return E(_aq);}},_az=function(_aA){return new T1(1,_aA);},_aB=new T4(0,_61,_an,_az,_aw),_aC=function(_aD,_aE,_aF){return new F(function(){return A1(_aD,new T2(1,_2z,new T(function(){return B(A1(_aE,_aF));})));});},_aG=function(_aH){return new F(function(){return _H(0,E(_aH),_Z);});},_aI=34,_aJ=new T2(1,_aI,_Z),_aK=new T(function(){return B(unCStr("!!: negative index"));}),_aL=new T(function(){return B(unCStr("Prelude."));}),_aM=new T(function(){return B(_x(_aL,_aK));}),_aN=new T(function(){return B(err(_aM));}),_aO=new T(function(){return B(unCStr("!!: index too large"));}),_aP=new T(function(){return B(_x(_aL,_aO));}),_aQ=new T(function(){return B(err(_aP));}),_aR=function(_aS,_aT){while(1){var _aU=E(_aS);if(!_aU._){return E(_aQ);}else{var _aV=E(_aT);if(!_aV){return E(_aU.a);}else{_aS=_aU.b;_aT=_aV-1|0;continue;}}}},_aW=function(_aX,_aY){if(_aY>=0){return new F(function(){return _aR(_aX,_aY);});}else{return E(_aN);}},_aZ=new T(function(){return B(unCStr("ACK"));}),_b0=new T(function(){return B(unCStr("BEL"));}),_b1=new T(function(){return B(unCStr("BS"));}),_b2=new T(function(){return B(unCStr("SP"));}),_b3=new T2(1,_b2,_Z),_b4=new T(function(){return B(unCStr("US"));}),_b5=new T2(1,_b4,_b3),_b6=new T(function(){return B(unCStr("RS"));}),_b7=new T2(1,_b6,_b5),_b8=new T(function(){return B(unCStr("GS"));}),_b9=new T2(1,_b8,_b7),_ba=new T(function(){return B(unCStr("FS"));}),_bb=new T2(1,_ba,_b9),_bc=new T(function(){return B(unCStr("ESC"));}),_bd=new T2(1,_bc,_bb),_be=new T(function(){return B(unCStr("SUB"));}),_bf=new T2(1,_be,_bd),_bg=new T(function(){return B(unCStr("EM"));}),_bh=new T2(1,_bg,_bf),_bi=new T(function(){return B(unCStr("CAN"));}),_bj=new T2(1,_bi,_bh),_bk=new T(function(){return B(unCStr("ETB"));}),_bl=new T2(1,_bk,_bj),_bm=new T(function(){return B(unCStr("SYN"));}),_bn=new T2(1,_bm,_bl),_bo=new T(function(){return B(unCStr("NAK"));}),_bp=new T2(1,_bo,_bn),_bq=new T(function(){return B(unCStr("DC4"));}),_br=new T2(1,_bq,_bp),_bs=new T(function(){return B(unCStr("DC3"));}),_bt=new T2(1,_bs,_br),_bu=new T(function(){return B(unCStr("DC2"));}),_bv=new T2(1,_bu,_bt),_bw=new T(function(){return B(unCStr("DC1"));}),_bx=new T2(1,_bw,_bv),_by=new T(function(){return B(unCStr("DLE"));}),_bz=new T2(1,_by,_bx),_bA=new T(function(){return B(unCStr("SI"));}),_bB=new T2(1,_bA,_bz),_bC=new T(function(){return B(unCStr("SO"));}),_bD=new T2(1,_bC,_bB),_bE=new T(function(){return B(unCStr("CR"));}),_bF=new T2(1,_bE,_bD),_bG=new T(function(){return B(unCStr("FF"));}),_bH=new T2(1,_bG,_bF),_bI=new T(function(){return B(unCStr("VT"));}),_bJ=new T2(1,_bI,_bH),_bK=new T(function(){return B(unCStr("LF"));}),_bL=new T2(1,_bK,_bJ),_bM=new T(function(){return B(unCStr("HT"));}),_bN=new T2(1,_bM,_bL),_bO=new T2(1,_b1,_bN),_bP=new T2(1,_b0,_bO),_bQ=new T2(1,_aZ,_bP),_bR=new T(function(){return B(unCStr("ENQ"));}),_bS=new T2(1,_bR,_bQ),_bT=new T(function(){return B(unCStr("EOT"));}),_bU=new T2(1,_bT,_bS),_bV=new T(function(){return B(unCStr("ETX"));}),_bW=new T2(1,_bV,_bU),_bX=new T(function(){return B(unCStr("STX"));}),_bY=new T2(1,_bX,_bW),_bZ=new T(function(){return B(unCStr("SOH"));}),_c0=new T2(1,_bZ,_bY),_c1=new T(function(){return B(unCStr("NUL"));}),_c2=new T2(1,_c1,_c0),_c3=92,_c4=new T(function(){return B(unCStr("\\DEL"));}),_c5=new T(function(){return B(unCStr("\\a"));}),_c6=new T(function(){return B(unCStr("\\\\"));}),_c7=new T(function(){return B(unCStr("\\SO"));}),_c8=new T(function(){return B(unCStr("\\r"));}),_c9=new T(function(){return B(unCStr("\\f"));}),_ca=new T(function(){return B(unCStr("\\v"));}),_cb=new T(function(){return B(unCStr("\\n"));}),_cc=new T(function(){return B(unCStr("\\t"));}),_cd=new T(function(){return B(unCStr("\\b"));}),_ce=function(_cf,_cg){if(_cf<=127){var _ch=E(_cf);switch(_ch){case 92:return new F(function(){return _x(_c6,_cg);});break;case 127:return new F(function(){return _x(_c4,_cg);});break;default:if(_ch<32){var _ci=E(_ch);switch(_ci){case 7:return new F(function(){return _x(_c5,_cg);});break;case 8:return new F(function(){return _x(_cd,_cg);});break;case 9:return new F(function(){return _x(_cc,_cg);});break;case 10:return new F(function(){return _x(_cb,_cg);});break;case 11:return new F(function(){return _x(_ca,_cg);});break;case 12:return new F(function(){return _x(_c9,_cg);});break;case 13:return new F(function(){return _x(_c8,_cg);});break;case 14:return new F(function(){return _x(_c7,new T(function(){var _cj=E(_cg);if(!_cj._){return __Z;}else{if(E(_cj.a)==72){return B(unAppCStr("\\&",_cj));}else{return E(_cj);}}},1));});break;default:return new F(function(){return _x(new T2(1,_c3,new T(function(){return B(_aW(_c2,_ci));})),_cg);});}}else{return new T2(1,_ch,_cg);}}}else{var _ck=new T(function(){var _cl=jsShowI(_cf);return B(_x(fromJSStr(_cl),new T(function(){var _cm=E(_cg);if(!_cm._){return __Z;}else{var _cn=E(_cm.a);if(_cn<48){return E(_cm);}else{if(_cn>57){return E(_cm);}else{return B(unAppCStr("\\&",_cm));}}}},1)));});return new T2(1,_c3,_ck);}},_co=new T(function(){return B(unCStr("\\\""));}),_cp=function(_cq,_cr){var _cs=E(_cq);if(!_cs._){return E(_cr);}else{var _ct=_cs.b,_cu=E(_cs.a);if(_cu==34){return new F(function(){return _x(_co,new T(function(){return B(_cp(_ct,_cr));},1));});}else{return new F(function(){return _ce(_cu,new T(function(){return B(_cp(_ct,_cr));}));});}}},_cv=function(_cw){return new T2(1,_aI,new T(function(){return B(_cp(_cw,_aJ));}));},_cx=function(_cy,_cz){if(_cy<=_cz){var _cA=function(_cB){return new T2(1,_cB,new T(function(){if(_cB!=_cz){return B(_cA(_cB+1|0));}else{return __Z;}}));};return new F(function(){return _cA(_cy);});}else{return __Z;}},_cC=function(_cD){return new F(function(){return _cx(E(_cD),2147483647);});},_cE=function(_cF,_cG,_cH){if(_cH<=_cG){var _cI=new T(function(){var _cJ=_cG-_cF|0,_cK=function(_cL){return (_cL>=(_cH-_cJ|0))?new T2(1,_cL,new T(function(){return B(_cK(_cL+_cJ|0));})):new T2(1,_cL,_Z);};return B(_cK(_cG));});return new T2(1,_cF,_cI);}else{return (_cH<=_cF)?new T2(1,_cF,_Z):__Z;}},_cM=function(_cN,_cO,_cP){if(_cP>=_cO){var _cQ=new T(function(){var _cR=_cO-_cN|0,_cS=function(_cT){return (_cT<=(_cP-_cR|0))?new T2(1,_cT,new T(function(){return B(_cS(_cT+_cR|0));})):new T2(1,_cT,_Z);};return B(_cS(_cO));});return new T2(1,_cN,_cQ);}else{return (_cP>=_cN)?new T2(1,_cN,_Z):__Z;}},_cU=function(_cV,_cW){if(_cW<_cV){return new F(function(){return _cE(_cV,_cW, -2147483648);});}else{return new F(function(){return _cM(_cV,_cW,2147483647);});}},_cX=function(_cY,_cZ){return new F(function(){return _cU(E(_cY),E(_cZ));});},_d0=function(_d1,_d2,_d3){if(_d2<_d1){return new F(function(){return _cE(_d1,_d2,_d3);});}else{return new F(function(){return _cM(_d1,_d2,_d3);});}},_d4=function(_d5,_d6,_d7){return new F(function(){return _d0(E(_d5),E(_d6),E(_d7));});},_d8=function(_d9,_da){return new F(function(){return _cx(E(_d9),E(_da));});},_db=function(_dc){return E(_dc);},_dd=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_de=new T(function(){return B(err(_dd));}),_df=function(_dg){var _dh=E(_dg);return (_dh==( -2147483648))?E(_de):_dh-1|0;},_di=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_dj=new T(function(){return B(err(_di));}),_dk=function(_dl){var _dm=E(_dl);return (_dm==2147483647)?E(_dj):_dm+1|0;},_dn={_:0,a:_dk,b:_df,c:_db,d:_db,e:_cC,f:_cX,g:_d8,h:_d4},_do=function(_dp,_dq){if(_dp<=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{if(_dq>=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{return quot(_dp-1|0,_dq)-1|0;}}},_dr=new T(function(){return B(unCStr("base"));}),_ds=new T(function(){return B(unCStr("GHC.Exception"));}),_dt=new T(function(){return B(unCStr("ArithException"));}),_du=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_dr,_ds,_dt),_dv=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_du,_Z,_Z),_dw=function(_dx){return E(_dv);},_dy=function(_dz){var _dA=E(_dz);return new F(function(){return _1r(B(_1p(_dA.a)),_dw,_dA.b);});},_dB=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_dC=new T(function(){return B(unCStr("denormal"));}),_dD=new T(function(){return B(unCStr("divide by zero"));}),_dE=new T(function(){return B(unCStr("loss of precision"));}),_dF=new T(function(){return B(unCStr("arithmetic underflow"));}),_dG=new T(function(){return B(unCStr("arithmetic overflow"));}),_dH=function(_dI,_dJ){switch(E(_dI)){case 0:return new F(function(){return _x(_dG,_dJ);});break;case 1:return new F(function(){return _x(_dF,_dJ);});break;case 2:return new F(function(){return _x(_dE,_dJ);});break;case 3:return new F(function(){return _x(_dD,_dJ);});break;case 4:return new F(function(){return _x(_dC,_dJ);});break;default:return new F(function(){return _x(_dB,_dJ);});}},_dK=function(_dL){return new F(function(){return _dH(_dL,_Z);});},_dM=function(_dN,_dO,_dP){return new F(function(){return _dH(_dO,_dP);});},_dQ=function(_dR,_dS){return new F(function(){return _2C(_dH,_dR,_dS);});},_dT=new T3(0,_dM,_dK,_dQ),_dU=new T(function(){return new T5(0,_dw,_dT,_dV,_dy,_dK);}),_dV=function(_dW){return new T2(0,_dU,_dW);},_dX=3,_dY=new T(function(){return B(_dV(_dX));}),_dZ=new T(function(){return die(_dY);}),_e0=0,_e1=new T(function(){return B(_dV(_e0));}),_e2=new T(function(){return die(_e1);}),_e3=function(_e4,_e5){var _e6=E(_e5);switch(_e6){case  -1:var _e7=E(_e4);if(_e7==( -2147483648)){return E(_e2);}else{return new F(function(){return _do(_e7, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return _do(_e4,_e6);});}},_e8=function(_e9,_ea){return new F(function(){return _e3(E(_e9),E(_ea));});},_eb=0,_ec=new T2(0,_e2,_eb),_ed=function(_ee,_ef){var _eg=E(_ee),_eh=E(_ef);switch(_eh){case  -1:var _ei=E(_eg);if(_ei==( -2147483648)){return E(_ec);}else{if(_ei<=0){if(_ei>=0){var _ej=quotRemI(_ei, -1);return new T2(0,_ej.a,_ej.b);}else{var _ek=quotRemI(_ei, -1);return new T2(0,_ek.a,_ek.b);}}else{var _el=quotRemI(_ei-1|0, -1);return new T2(0,_el.a-1|0,(_el.b+( -1)|0)+1|0);}}break;case 0:return E(_dZ);default:if(_eg<=0){if(_eg>=0){var _em=quotRemI(_eg,_eh);return new T2(0,_em.a,_em.b);}else{if(_eh<=0){var _en=quotRemI(_eg,_eh);return new T2(0,_en.a,_en.b);}else{var _eo=quotRemI(_eg+1|0,_eh);return new T2(0,_eo.a-1|0,(_eo.b+_eh|0)-1|0);}}}else{if(_eh>=0){if(_eg>=0){var _ep=quotRemI(_eg,_eh);return new T2(0,_ep.a,_ep.b);}else{if(_eh<=0){var _eq=quotRemI(_eg,_eh);return new T2(0,_eq.a,_eq.b);}else{var _er=quotRemI(_eg+1|0,_eh);return new T2(0,_er.a-1|0,(_er.b+_eh|0)-1|0);}}}else{var _es=quotRemI(_eg-1|0,_eh);return new T2(0,_es.a-1|0,(_es.b+_eh|0)+1|0);}}}},_et=function(_eu,_ev){var _ew=_eu%_ev;if(_eu<=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ex=E(_ew);return (_ex==0)?0:_ex+_ev|0;}}}else{if(_ev>=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ey=E(_ew);return (_ey==0)?0:_ey+_ev|0;}}}else{var _ez=E(_ew);return (_ez==0)?0:_ez+_ev|0;}}},_eA=function(_eB,_eC){var _eD=E(_eC);switch(_eD){case  -1:return E(_eb);case 0:return E(_dZ);default:return new F(function(){return _et(E(_eB),_eD);});}},_eE=function(_eF,_eG){var _eH=E(_eF),_eI=E(_eG);switch(_eI){case  -1:var _eJ=E(_eH);if(_eJ==( -2147483648)){return E(_e2);}else{return new F(function(){return quot(_eJ, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return quot(_eH,_eI);});}},_eK=function(_eL,_eM){var _eN=E(_eL),_eO=E(_eM);switch(_eO){case  -1:var _eP=E(_eN);if(_eP==( -2147483648)){return E(_ec);}else{var _eQ=quotRemI(_eP, -1);return new T2(0,_eQ.a,_eQ.b);}break;case 0:return E(_dZ);default:var _eR=quotRemI(_eN,_eO);return new T2(0,_eR.a,_eR.b);}},_eS=function(_eT,_eU){var _eV=E(_eU);switch(_eV){case  -1:return E(_eb);case 0:return E(_dZ);default:return E(_eT)%_eV;}},_eW=function(_eX){return new T1(0,_eX);},_eY=function(_eZ){return new F(function(){return _eW(E(_eZ));});},_f0=new T1(0,1),_f1=function(_f2){return new T2(0,E(B(_eW(E(_f2)))),E(_f0));},_f3=function(_f4,_f5){return imul(E(_f4),E(_f5))|0;},_f6=function(_f7,_f8){return E(_f7)+E(_f8)|0;},_f9=function(_fa,_fb){return E(_fa)-E(_fb)|0;},_fc=function(_fd){var _fe=E(_fd);return (_fe<0)? -_fe:E(_fe);},_ff=function(_fg){var _fh=E(_fg);if(!_fh._){return E(_fh.a);}else{return new F(function(){return I_toInt(_fh.a);});}},_fi=function(_fj){return new F(function(){return _ff(_fj);});},_fk=function(_fl){return  -E(_fl);},_fm= -1,_fn=0,_fo=1,_fp=function(_fq){var _fr=E(_fq);return (_fr>=0)?(E(_fr)==0)?E(_fn):E(_fo):E(_fm);},_fs={_:0,a:_f6,b:_f9,c:_f3,d:_fk,e:_fc,f:_fp,g:_fi},_ft=function(_fu,_fv){var _fw=E(_fu),_fx=E(_fv);return (_fw>_fx)?E(_fw):E(_fx);},_fy=function(_fz,_fA){var _fB=E(_fz),_fC=E(_fA);return (_fB>_fC)?E(_fC):E(_fB);},_fD=function(_fE,_fF){return (_fE>=_fF)?(_fE!=_fF)?2:1:0;},_fG=function(_fH,_fI){return new F(function(){return _fD(E(_fH),E(_fI));});},_fJ=function(_fK,_fL){return E(_fK)>=E(_fL);},_fM=function(_fN,_fO){return E(_fN)>E(_fO);},_fP=function(_fQ,_fR){return E(_fQ)<=E(_fR);},_fS=function(_fT,_fU){return E(_fT)<E(_fU);},_fV={_:0,a:_3S,b:_fG,c:_fS,d:_fP,e:_fM,f:_fJ,g:_ft,h:_fy},_fW=new T3(0,_fs,_fV,_f1),_fX={_:0,a:_fW,b:_dn,c:_eE,d:_eS,e:_e8,f:_eA,g:_eK,h:_ed,i:_eY},_fY=function(_fZ){var _g0=E(_fZ);return new F(function(){return Math.log(_g0+(_g0+1)*Math.sqrt((_g0-1)/(_g0+1)));});},_g1=function(_g2){var _g3=E(_g2);return new F(function(){return Math.log(_g3+Math.sqrt(1+_g3*_g3));});},_g4=function(_g5){var _g6=E(_g5);return 0.5*Math.log((1+_g6)/(1-_g6));},_g7=function(_g8,_g9){return Math.log(E(_g9))/Math.log(E(_g8));},_ga=3.141592653589793,_gb=new T1(0,1),_gc=function(_gd,_ge){var _gf=E(_gd);if(!_gf._){var _gg=_gf.a,_gh=E(_ge);if(!_gh._){var _gi=_gh.a;return (_gg!=_gi)?(_gg>_gi)?2:0:1;}else{var _gj=I_compareInt(_gh.a,_gg);return (_gj<=0)?(_gj>=0)?1:2:0;}}else{var _gk=_gf.a,_gl=E(_ge);if(!_gl._){var _gm=I_compareInt(_gk,_gl.a);return (_gm>=0)?(_gm<=0)?1:2:0;}else{var _gn=I_compare(_gk,_gl.a);return (_gn>=0)?(_gn<=0)?1:2:0;}}},_go=function(_gp,_gq){var _gr=E(_gp);return (_gr._==0)?_gr.a*Math.pow(2,_gq):I_toNumber(_gr.a)*Math.pow(2,_gq);},_gs=function(_gt,_gu){var _gv=E(_gt);if(!_gv._){var _gw=_gv.a,_gx=E(_gu);return (_gx._==0)?_gw==_gx.a:(I_compareInt(_gx.a,_gw)==0)?true:false;}else{var _gy=_gv.a,_gz=E(_gu);return (_gz._==0)?(I_compareInt(_gy,_gz.a)==0)?true:false:(I_compare(_gy,_gz.a)==0)?true:false;}},_gA=function(_gB,_gC){while(1){var _gD=E(_gB);if(!_gD._){var _gE=_gD.a,_gF=E(_gC);if(!_gF._){var _gG=_gF.a,_gH=addC(_gE,_gG);if(!E(_gH.b)){return new T1(0,_gH.a);}else{_gB=new T1(1,I_fromInt(_gE));_gC=new T1(1,I_fromInt(_gG));continue;}}else{_gB=new T1(1,I_fromInt(_gE));_gC=_gF;continue;}}else{var _gI=E(_gC);if(!_gI._){_gB=_gD;_gC=new T1(1,I_fromInt(_gI.a));continue;}else{return new T1(1,I_add(_gD.a,_gI.a));}}}},_gJ=function(_gK,_gL){while(1){var _gM=E(_gK);if(!_gM._){var _gN=E(_gM.a);if(_gN==( -2147483648)){_gK=new T1(1,I_fromInt( -2147483648));continue;}else{var _gO=E(_gL);if(!_gO._){var _gP=_gO.a;return new T2(0,new T1(0,quot(_gN,_gP)),new T1(0,_gN%_gP));}else{_gK=new T1(1,I_fromInt(_gN));_gL=_gO;continue;}}}else{var _gQ=E(_gL);if(!_gQ._){_gK=_gM;_gL=new T1(1,I_fromInt(_gQ.a));continue;}else{var _gR=I_quotRem(_gM.a,_gQ.a);return new T2(0,new T1(1,_gR.a),new T1(1,_gR.b));}}}},_gS=new T1(0,0),_gT=function(_gU,_gV){while(1){var _gW=E(_gU);if(!_gW._){_gU=new T1(1,I_fromInt(_gW.a));continue;}else{return new T1(1,I_shiftLeft(_gW.a,_gV));}}},_gX=function(_gY,_gZ,_h0){if(!B(_gs(_h0,_gS))){var _h1=B(_gJ(_gZ,_h0)),_h2=_h1.a;switch(B(_gc(B(_gT(_h1.b,1)),_h0))){case 0:return new F(function(){return _go(_h2,_gY);});break;case 1:if(!(B(_ff(_h2))&1)){return new F(function(){return _go(_h2,_gY);});}else{return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}break;default:return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}}else{return E(_dZ);}},_h3=function(_h4,_h5){var _h6=E(_h4);if(!_h6._){var _h7=_h6.a,_h8=E(_h5);return (_h8._==0)?_h7>_h8.a:I_compareInt(_h8.a,_h7)<0;}else{var _h9=_h6.a,_ha=E(_h5);return (_ha._==0)?I_compareInt(_h9,_ha.a)>0:I_compare(_h9,_ha.a)>0;}},_hb=new T1(0,1),_hc=function(_hd,_he){var _hf=E(_hd);if(!_hf._){var _hg=_hf.a,_hh=E(_he);return (_hh._==0)?_hg<_hh.a:I_compareInt(_hh.a,_hg)>0;}else{var _hi=_hf.a,_hj=E(_he);return (_hj._==0)?I_compareInt(_hi,_hj.a)<0:I_compare(_hi,_hj.a)<0;}},_hk=new T(function(){return B(unCStr("base"));}),_hl=new T(function(){return B(unCStr("Control.Exception.Base"));}),_hm=new T(function(){return B(unCStr("PatternMatchFail"));}),_hn=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hk,_hl,_hm),_ho=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hn,_Z,_Z),_hp=function(_hq){return E(_ho);},_hr=function(_hs){var _ht=E(_hs);return new F(function(){return _1r(B(_1p(_ht.a)),_hp,_ht.b);});},_hu=function(_hv){return E(E(_hv).a);},_hw=function(_hx){return new T2(0,_hy,_hx);},_hz=function(_hA,_hB){return new F(function(){return _x(E(_hA).a,_hB);});},_hC=function(_hD,_hE){return new F(function(){return _2C(_hz,_hD,_hE);});},_hF=function(_hG,_hH,_hI){return new F(function(){return _x(E(_hH).a,_hI);});},_hJ=new T3(0,_hF,_hu,_hC),_hy=new T(function(){return new T5(0,_hp,_hJ,_hw,_hr,_hu);}),_hK=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_hL=function(_hM,_hN){return new F(function(){return die(new T(function(){return B(A2(_5L,_hN,_hM));}));});},_hO=function(_hP,_dW){return new F(function(){return _hL(_hP,_dW);});},_hQ=function(_hR,_hS){var _hT=E(_hS);if(!_hT._){return new T2(0,_Z,_Z);}else{var _hU=_hT.a;if(!B(A1(_hR,_hU))){return new T2(0,_Z,_hT);}else{var _hV=new T(function(){var _hW=B(_hQ(_hR,_hT.b));return new T2(0,_hW.a,_hW.b);});return new T2(0,new T2(1,_hU,new T(function(){return E(E(_hV).a);})),new T(function(){return E(E(_hV).b);}));}}},_hX=32,_hY=new T(function(){return B(unCStr("\n"));}),_hZ=function(_i0){return (E(_i0)==124)?false:true;},_i1=function(_i2,_i3){var _i4=B(_hQ(_hZ,B(unCStr(_i2)))),_i5=_i4.a,_i6=function(_i7,_i8){var _i9=new T(function(){var _ia=new T(function(){return B(_x(_i3,new T(function(){return B(_x(_i8,_hY));},1)));});return B(unAppCStr(": ",_ia));},1);return new F(function(){return _x(_i7,_i9);});},_ib=E(_i4.b);if(!_ib._){return new F(function(){return _i6(_i5,_Z);});}else{if(E(_ib.a)==124){return new F(function(){return _i6(_i5,new T2(1,_hX,_ib.b));});}else{return new F(function(){return _i6(_i5,_Z);});}}},_ic=function(_id){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_id,_hK));})),_hy);});},_ie=function(_if){var _ig=function(_ih,_ii){while(1){if(!B(_hc(_ih,_if))){if(!B(_h3(_ih,_if))){if(!B(_gs(_ih,_if))){return new F(function(){return _ic("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ii);}}else{return _ii-1|0;}}else{var _ij=B(_gT(_ih,1)),_ik=_ii+1|0;_ih=_ij;_ii=_ik;continue;}}};return new F(function(){return _ig(_hb,0);});},_il=function(_im){var _in=E(_im);if(!_in._){var _io=_in.a>>>0;if(!_io){return  -1;}else{var _ip=function(_iq,_ir){while(1){if(_iq>=_io){if(_iq<=_io){if(_iq!=_io){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ir);}}else{return _ir-1|0;}}else{var _is=imul(_iq,2)>>>0,_it=_ir+1|0;_iq=_is;_ir=_it;continue;}}};return new F(function(){return _ip(1,0);});}}else{return new F(function(){return _ie(_in);});}},_iu=function(_iv){var _iw=E(_iv);if(!_iw._){var _ix=_iw.a>>>0;if(!_ix){return new T2(0, -1,0);}else{var _iy=function(_iz,_iA){while(1){if(_iz>=_ix){if(_iz<=_ix){if(_iz!=_ix){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_iA);}}else{return _iA-1|0;}}else{var _iB=imul(_iz,2)>>>0,_iC=_iA+1|0;_iz=_iB;_iA=_iC;continue;}}};return new T2(0,B(_iy(1,0)),(_ix&_ix-1>>>0)>>>0&4294967295);}}else{var _iD=_iw.a;return new T2(0,B(_il(_iw)),I_compareInt(I_and(_iD,I_sub(_iD,I_fromInt(1))),0));}},_iE=function(_iF,_iG){var _iH=E(_iF);if(!_iH._){var _iI=_iH.a,_iJ=E(_iG);return (_iJ._==0)?_iI<=_iJ.a:I_compareInt(_iJ.a,_iI)>=0;}else{var _iK=_iH.a,_iL=E(_iG);return (_iL._==0)?I_compareInt(_iK,_iL.a)<=0:I_compare(_iK,_iL.a)<=0;}},_iM=function(_iN,_iO){while(1){var _iP=E(_iN);if(!_iP._){var _iQ=_iP.a,_iR=E(_iO);if(!_iR._){return new T1(0,(_iQ>>>0&_iR.a>>>0)>>>0&4294967295);}else{_iN=new T1(1,I_fromInt(_iQ));_iO=_iR;continue;}}else{var _iS=E(_iO);if(!_iS._){_iN=_iP;_iO=new T1(1,I_fromInt(_iS.a));continue;}else{return new T1(1,I_and(_iP.a,_iS.a));}}}},_iT=function(_iU,_iV){while(1){var _iW=E(_iU);if(!_iW._){var _iX=_iW.a,_iY=E(_iV);if(!_iY._){var _iZ=_iY.a,_j0=subC(_iX,_iZ);if(!E(_j0.b)){return new T1(0,_j0.a);}else{_iU=new T1(1,I_fromInt(_iX));_iV=new T1(1,I_fromInt(_iZ));continue;}}else{_iU=new T1(1,I_fromInt(_iX));_iV=_iY;continue;}}else{var _j1=E(_iV);if(!_j1._){_iU=_iW;_iV=new T1(1,I_fromInt(_j1.a));continue;}else{return new T1(1,I_sub(_iW.a,_j1.a));}}}},_j2=new T1(0,2),_j3=function(_j4,_j5){var _j6=E(_j4);if(!_j6._){var _j7=(_j6.a>>>0&(2<<_j5>>>0)-1>>>0)>>>0,_j8=1<<_j5>>>0;return (_j8<=_j7)?(_j8>=_j7)?1:2:0;}else{var _j9=B(_iM(_j6,B(_iT(B(_gT(_j2,_j5)),_hb)))),_ja=B(_gT(_hb,_j5));return (!B(_h3(_ja,_j9)))?(!B(_hc(_ja,_j9)))?1:2:0;}},_jb=function(_jc,_jd){while(1){var _je=E(_jc);if(!_je._){_jc=new T1(1,I_fromInt(_je.a));continue;}else{return new T1(1,I_shiftRight(_je.a,_jd));}}},_jf=function(_jg,_jh,_ji,_jj){var _jk=B(_iu(_jj)),_jl=_jk.a;if(!E(_jk.b)){var _jm=B(_il(_ji));if(_jm<((_jl+_jg|0)-1|0)){var _jn=_jl+(_jg-_jh|0)|0;if(_jn>0){if(_jn>_jm){if(_jn<=(_jm+1|0)){if(!E(B(_iu(_ji)).b)){return 0;}else{return new F(function(){return _go(_gb,_jg-_jh|0);});}}else{return 0;}}else{var _jo=B(_jb(_ji,_jn));switch(B(_j3(_ji,_jn-1|0))){case 0:return new F(function(){return _go(_jo,_jg-_jh|0);});break;case 1:if(!(B(_ff(_jo))&1)){return new F(function(){return _go(_jo,_jg-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}break;default:return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}}}else{return new F(function(){return _go(_ji,(_jg-_jh|0)-_jn|0);});}}else{if(_jm>=_jh){var _jp=B(_jb(_ji,(_jm+1|0)-_jh|0));switch(B(_j3(_ji,_jm-_jh|0))){case 0:return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});break;case 2:return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});break;default:if(!(B(_ff(_jp))&1)){return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});}}}else{return new F(function(){return _go(_ji, -_jl);});}}}else{var _jq=B(_il(_ji))-_jl|0,_jr=function(_js){var _jt=function(_ju,_jv){if(!B(_iE(B(_gT(_jv,_jh)),_ju))){return new F(function(){return _gX(_js-_jh|0,_ju,_jv);});}else{return new F(function(){return _gX((_js-_jh|0)+1|0,_ju,B(_gT(_jv,1)));});}};if(_js>=_jh){if(_js!=_jh){return new F(function(){return _jt(_ji,new T(function(){return B(_gT(_jj,_js-_jh|0));}));});}else{return new F(function(){return _jt(_ji,_jj);});}}else{return new F(function(){return _jt(new T(function(){return B(_gT(_ji,_jh-_js|0));}),_jj);});}};if(_jg>_jq){return new F(function(){return _jr(_jg);});}else{return new F(function(){return _jr(_jq);});}}},_jw=new T1(0,2147483647),_jx=new T(function(){return B(_gA(_jw,_hb));}),_jy=function(_jz){var _jA=E(_jz);if(!_jA._){var _jB=E(_jA.a);return (_jB==( -2147483648))?E(_jx):new T1(0, -_jB);}else{return new T1(1,I_negate(_jA.a));}},_jC=new T(function(){return 0/0;}),_jD=new T(function(){return  -1/0;}),_jE=new T(function(){return 1/0;}),_jF=0,_jG=function(_jH,_jI){if(!B(_gs(_jI,_gS))){if(!B(_gs(_jH,_gS))){if(!B(_hc(_jH,_gS))){return new F(function(){return _jf( -1021,53,_jH,_jI);});}else{return  -B(_jf( -1021,53,B(_jy(_jH)),_jI));}}else{return E(_jF);}}else{return (!B(_gs(_jH,_gS)))?(!B(_hc(_jH,_gS)))?E(_jE):E(_jD):E(_jC);}},_jJ=function(_jK){var _jL=E(_jK);return new F(function(){return _jG(_jL.a,_jL.b);});},_jM=function(_jN){return 1/E(_jN);},_jO=function(_jP){var _jQ=E(_jP);return (_jQ!=0)?(_jQ<=0)? -_jQ:E(_jQ):E(_jF);},_jR=function(_jS){var _jT=E(_jS);if(!_jT._){return _jT.a;}else{return new F(function(){return I_toNumber(_jT.a);});}},_jU=function(_jV){return new F(function(){return _jR(_jV);});},_jW=1,_jX= -1,_jY=function(_jZ){var _k0=E(_jZ);return (_k0<=0)?(_k0>=0)?E(_k0):E(_jX):E(_jW);},_k1=function(_k2,_k3){return E(_k2)-E(_k3);},_k4=function(_k5){return  -E(_k5);},_k6=function(_k7,_k8){return E(_k7)+E(_k8);},_k9=function(_ka,_kb){return E(_ka)*E(_kb);},_kc={_:0,a:_k6,b:_k1,c:_k9,d:_k4,e:_jO,f:_jY,g:_jU},_kd=function(_ke,_kf){return E(_ke)/E(_kf);},_kg=new T4(0,_kc,_kd,_jM,_jJ),_kh=function(_ki){return new F(function(){return Math.acos(E(_ki));});},_kj=function(_kk){return new F(function(){return Math.asin(E(_kk));});},_kl=function(_km){return new F(function(){return Math.atan(E(_km));});},_kn=function(_ko){return new F(function(){return Math.cos(E(_ko));});},_kp=function(_kq){return new F(function(){return cosh(E(_kq));});},_kr=function(_ks){return new F(function(){return Math.exp(E(_ks));});},_kt=function(_ku){return new F(function(){return Math.log(E(_ku));});},_kv=function(_kw,_kx){return new F(function(){return Math.pow(E(_kw),E(_kx));});},_ky=function(_kz){return new F(function(){return Math.sin(E(_kz));});},_kA=function(_kB){return new F(function(){return sinh(E(_kB));});},_kC=function(_kD){return new F(function(){return Math.sqrt(E(_kD));});},_kE=function(_kF){return new F(function(){return Math.tan(E(_kF));});},_kG=function(_kH){return new F(function(){return tanh(E(_kH));});},_kI={_:0,a:_kg,b:_ga,c:_kr,d:_kt,e:_kC,f:_kv,g:_g7,h:_ky,i:_kn,j:_kE,k:_kj,l:_kh,m:_kl,n:_kA,o:_kp,p:_kG,q:_g1,r:_fY,s:_g4},_kJ=0,_kK=function(_){return _kJ;},_kL=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_kM=new T(function(){return eval("(function(ctx){ctx.save();})");}),_kN=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_kO=function(_kP,_kQ,_kR,_){var _kS=__app1(E(_kM),_kR),_kT=__app2(E(_kN),_kR,E(_kP)),_kU=B(A2(_kQ,_kR,_)),_kV=__app1(E(_kL),_kR);return new F(function(){return _kK(_);});},_kW=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_kX=function(_kY,_kZ,_l0,_l1,_){var _l2=__app1(E(_kM),_l1),_l3=__app3(E(_kW),_l1,E(_kY),E(_kZ)),_l4=B(A2(_l0,_l1,_)),_l5=__app1(E(_kL),_l1);return new F(function(){return _kK(_);});},_l6=function(_l7,_l8){return E(_l7)!=E(_l8);},_l9=function(_la,_lb){return E(_la)==E(_lb);},_lc=new T2(0,_l9,_l6),_ld=function(_le){return E(E(_le).a);},_lf=function(_lg){return E(E(_lg).a);},_lh=function(_li){return E(E(_li).b);},_lj=function(_lk){return E(E(_lk).g);},_ll=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_lm=0,_ln=3.3333333333333335,_lo=16.666666666666668,_lp=function(_lq){return E(E(_lq).b);},_lr=new T1(0,0),_ls=new T1(0,2),_lt=function(_lu){return E(E(_lu).i);},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC,_lD){var _lE=new T(function(){var _lF=E(_lD);if(_lF<=31){return B(_4H(_lc,_lF,_ll));}else{if(_lF>=128){return B(_4H(_lc,_lF,_ll));}else{return true;}}}),_lG=new T(function(){if(E(_lz)==8){return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28+20;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24+8*(E(_lA)-1);}));}else{return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24;}));}}),_lH=new T(function(){var _lI=B(_ld(_lw));if(!E(_lE)){return B(A2(_lj,B(_lf(_lI)),_lr));}else{return B(A3(_lh,_lI,new T(function(){return B(_lp(_lw));}),new T(function(){return B(A2(_lj,B(_lf(_lI)),_ls));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_lG).a);}),new T(function(){return E(E(_lG).b);})),new T2(0,new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_ln);}}),new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_lo);}})),_lH);},_lJ=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_lK=function(_lL,_lM,_lN){var _lO=new T(function(){return toJSStr(E(_lN));});return function(_lP,_){var _lQ=__app4(E(_lJ),E(_lP),E(_lO),E(_lL),E(_lM));return new F(function(){return _kK(_);});};},_lR=0,_lS=",",_lT="rgba(",_lU=new T(function(){return toJSStr(_Z);}),_lV="rgb(",_lW=")",_lX=new T2(1,_lW,_Z),_lY=function(_lZ){var _m0=E(_lZ);if(!_m0._){var _m1=jsCat(new T2(1,_lV,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),_lX)))))),E(_lU));return E(_m1);}else{var _m2=jsCat(new T2(1,_lT,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.d);}),_lX)))))))),E(_lU));return E(_m2);}},_m3="strokeStyle",_m4="fillStyle",_m5=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_m6=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_m7=function(_m8,_m9){var _ma=new T(function(){return B(_lY(_m8));});return function(_mb,_){var _mc=E(_mb),_md=E(_m4),_me=E(_m5),_mf=__app2(_me,_mc,_md),_mg=E(_m3),_mh=__app2(_me,_mc,_mg),_mi=E(_ma),_mj=E(_m6),_mk=__app3(_mj,_mc,_md,_mi),_ml=__app3(_mj,_mc,_mg,_mi),_mm=B(A2(_m9,_mc,_)),_mn=String(_mf),_mo=__app3(_mj,_mc,_md,_mn),_mp=String(_mh),_mq=__app3(_mj,_mc,_mg,_mp);return new F(function(){return _kK(_);});};},_mr="font",_ms=function(_mt,_mu){var _mv=new T(function(){return toJSStr(E(_mt));});return function(_mw,_){var _mx=E(_mw),_my=E(_mr),_mz=__app2(E(_m5),_mx,_my),_mA=E(_m6),_mB=__app3(_mA,_mx,_my,E(_mv)),_mC=B(A2(_mu,_mx,_)),_mD=String(_mz),_mE=__app3(_mA,_mx,_my,_mD);return new F(function(){return _kK(_);});};},_mF=new T(function(){return B(unCStr("px IPAGothic"));}),_mG=function(_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_){var _mO=new T(function(){var _mP=new T(function(){var _mQ=B(_lv(_kI,_fX,_fX,_mJ,_mK,_mL,_mM,_mN)),_mR=E(_mQ.a),_mS=E(_mQ.b);return new T5(0,_mR.a,_mR.b,_mS.a,_mS.b,_mQ.c);}),_mT=new T(function(){var _mU=E(_mP);return E(_mU.a)+E(_mU.c);}),_mV=new T(function(){var _mW=E(_mP);return E(_mW.b)-E(_mW.d);}),_mX=new T(function(){return E(E(_mP).e);}),_mY=new T(function(){return B(_lK(_lR,_lR,new T2(1,_mN,_Z)));}),_mZ=function(_n0,_){return new F(function(){return _kO(_mX,_mY,E(_n0),_);});};return B(_ms(new T(function(){return B(_x(B(_H(0,E(_mJ),_Z)),_mF));},1),function(_n1,_){return new F(function(){return _kX(_mT,_mV,_mZ,E(_n1),_);});}));});return new F(function(){return A(_m7,[_mI,_mO,_mH,_]);});},_n2=new T3(0,153,255,255),_n3=new T2(1,_n2,_Z),_n4=new T3(0,255,153,204),_n5=new T2(1,_n4,_n3),_n6=new T3(0,255,204,153),_n7=new T2(1,_n6,_n5),_n8=new T3(0,200,255,200),_n9=new T2(1,_n8,_n7),_na=20,_nb=64,_nc=1,_nd=2,_ne=8,_nf=function(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_){while(1){var _nn=B((function(_no,_np,_nq,_nr,_ns,_nt,_nu,_){var _nv=E(_nu);if(!_nv._){return _kJ;}else{var _nw=_nv.b,_nx=E(_nv.a),_ny=E(_nx);switch(_ny){case 10:var _nz=_no,_nA=_np,_nB=_nr,_nC=_nr;_ng=_nz;_nh=_nA;_ni=0;_nj=_nB;_nk=new T(function(){return E(_ns)-1|0;});_nl=_nC;_nm=_nw;return __continue;case 123:return new F(function(){return _nD(_no,_np,_nq,_nr,_ns,_nt,_nw,_);});break;case 65306:var _nE=new T(function(){return B(_aW(_n9,_nq));}),_nF=function(_nG,_nH,_nI,_nJ,_nK,_nL,_){while(1){var _nM=B((function(_nN,_nO,_nP,_nQ,_nR,_nS,_){var _nT=E(_nS);if(!_nT._){return _kJ;}else{var _nU=_nT.b,_nV=E(_nT.a);if(E(_nV)==65306){var _nW=new T(function(){var _nX=E(_nR);if((_nX+1)*24<=E(_np)-10){return new T2(0,_nQ,_nX+1|0);}else{return new T2(0,new T(function(){return E(_nQ)-1|0;}),_nO);}});return new F(function(){return _nf(_nN,_np,_nq,_nO,new T(function(){return E(E(_nW).a);}),new T(function(){return E(E(_nW).b);}),_nU,_);});}else{var _nY=E(_nN),_nZ=B(_mG(_nY.a,_nE,_ne,_nP,_nQ,_nR,_nV,_)),_o0=_nO,_o1=_nP+1,_o2=_nQ,_o3=_nR;_nG=_nY;_nH=_o0;_nI=_o1;_nJ=_o2;_nK=_o3;_nL=_nU;return __continue;}}})(_nG,_nH,_nI,_nJ,_nK,_nL,_));if(_nM!=__continue){return _nM;}}};return new F(function(){return _nF(_no,_nr,0,new T(function(){if(E(_nr)!=E(_nt)){return E(_ns);}else{return E(_ns)+1|0;}}),new T(function(){var _o4=E(_nt);if(E(_nr)!=_o4){return _o4-1|0;}else{var _o5=(E(_np)-10)/24,_o6=_o5&4294967295;if(_o5>=_o6){return _o6;}else{return _o6-1|0;}}}),_nw,_);});break;default:var _o7=function(_o8,_o9){var _oa=new T(function(){switch(E(_ny)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _nq;}}),_ob=new T(function(){var _oc=E(_nt);if((_oc+1)*24<=E(_np)-10){return new T2(0,_ns,_oc+1|0);}else{return new T2(0,new T(function(){return E(_ns)-1|0;}),_nr);}});if(E(_o8)==64){return new F(function(){return _od(_no,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}else{var _oe=E(_no),_of=B(_mG(_oe.a,new T(function(){return B(_aW(_n9,E(_oa)));},1),_na,_lR,_ns,_nt,_o9,_));return new F(function(){return _od(_oe,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}},_og=E(_ny);switch(_og){case 42:return new F(function(){return _o7(64,_nb);});break;case 12289:return new F(function(){return _o7(64,_nb);});break;case 12290:return new F(function(){return _o7(64,_nb);});break;default:return new F(function(){return _o7(_og,_nx);});}}}})(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_));if(_nn!=__continue){return _nn;}}},_od=function(_oh,_oi,_oj,_ok,_ol,_om,_on,_){var _oo=E(_on);if(!_oo._){return _kJ;}else{var _op=_oo.b,_oq=E(_oo.a),_or=E(_oq);switch(_or){case 10:return new F(function(){return _nf(_oh,_oi,0,_ok,new T(function(){return E(_ol)-1|0;}),_ok,_op,_);});break;case 123:return new F(function(){return _nD(_oh,_oi,_oj,_ok,_ol,_om,_op,_);});break;case 65306:var _os=new T(function(){return B(_aW(_n9,E(_oj)));}),_ot=function(_ou,_ov,_ow,_ox,_oy,_oz,_){while(1){var _oA=B((function(_oB,_oC,_oD,_oE,_oF,_oG,_){var _oH=E(_oG);if(!_oH._){return _kJ;}else{var _oI=_oH.b,_oJ=E(_oH.a);if(E(_oJ)==65306){var _oK=new T(function(){var _oL=E(_oF);if((_oL+1)*24<=E(_oi)-10){return new T2(0,_oE,_oL+1|0);}else{return new T2(0,new T(function(){return E(_oE)-1|0;}),_oC);}});return new F(function(){return _od(_oB,_oi,_oj,_oC,new T(function(){return E(E(_oK).a);}),new T(function(){return E(E(_oK).b);}),_oI,_);});}else{var _oM=E(_oB),_oN=B(_mG(_oM.a,_os,_ne,_oD,_oE,_oF,_oJ,_)),_oO=_oC,_oP=_oD+1,_oQ=_oE,_oR=_oF;_ou=_oM;_ov=_oO;_ow=_oP;_ox=_oQ;_oy=_oR;_oz=_oI;return __continue;}}})(_ou,_ov,_ow,_ox,_oy,_oz,_));if(_oA!=__continue){return _oA;}}};return new F(function(){return _ot(_oh,_ok,0,new T(function(){if(E(_ok)!=E(_om)){return E(_ol);}else{return E(_ol)+1|0;}}),new T(function(){var _oS=E(_om);if(E(_ok)!=_oS){return _oS-1|0;}else{var _oT=(E(_oi)-10)/24,_oU=_oT&4294967295;if(_oT>=_oU){return _oU;}else{return _oU-1|0;}}}),_op,_);});break;default:var _oV=function(_oW,_oX){var _oY=new T(function(){switch(E(_or)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return E(_oj);}}),_oZ=new T(function(){var _p0=E(_om);if((_p0+1)*24<=E(_oi)-10){return new T2(0,_ol,_p0+1|0);}else{return new T2(0,new T(function(){return E(_ol)-1|0;}),_ok);}});if(E(_oW)==64){return new F(function(){return _od(_oh,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}else{var _p1=E(_oh),_p2=B(_mG(_p1.a,new T(function(){return B(_aW(_n9,E(_oY)));},1),_na,_lR,_ol,_om,_oX,_));return new F(function(){return _od(_p1,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}},_p3=E(_or);switch(_p3){case 42:return new F(function(){return _oV(64,_nb);});break;case 12289:return new F(function(){return _oV(64,_nb);});break;case 12290:return new F(function(){return _oV(64,_nb);});break;default:return new F(function(){return _oV(_p3,_oq);});}}}},_nD=function(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_){while(1){var _pb=B((function(_pc,_pd,_pe,_pf,_pg,_ph,_pi,_){var _pj=E(_pi);if(!_pj._){return _kJ;}else{var _pk=_pj.b;if(E(_pj.a)==125){var _pl=new T(function(){var _pm=E(_ph);if((_pm+1)*24<=E(_pd)-10){return new T2(0,_pg,_pm+1|0);}else{return new T2(0,new T(function(){return E(_pg)-1|0;}),_pf);}});return new F(function(){return _od(_pc,_pd,_pe,_pf,new T(function(){return E(E(_pl).a);}),new T(function(){return E(E(_pl).b);}),_pk,_);});}else{var _pn=_pc,_po=_pd,_pp=_pe,_pq=_pf,_pr=_pg,_ps=_ph;_p4=_pn;_p5=_po;_p6=_pp;_p7=_pq;_p8=_pr;_p9=_ps;_pa=_pk;return __continue;}}})(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_));if(_pb!=__continue){return _pb;}}},_pt=function(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_){while(1){var _pC=B((function(_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_){var _pL=E(_pK);if(!_pL._){return _kJ;}else{var _pM=_pL.b,_pN=E(_pL.a),_pO=E(_pN);switch(_pO){case 10:var _pP=_pD,_pQ=_pE,_pR=_pF,_pS=_pH,_pT=_pH;_pu=_pP;_pv=_pQ;_pw=_pR;_px=0;_py=_pS;_pz=new T(function(){return E(_pI)-1|0;});_pA=_pT;_pB=_pM;return __continue;case 123:return new F(function(){return _nD(new T2(0,_pD,_pE),_pF,_pG,_pH,_pI,_pJ,_pM,_);});break;case 65306:var _pU=new T(function(){return B(_aW(_n9,_pG));}),_pV=function(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_){while(1){var _q3=B((function(_q4,_q5,_q6,_q7,_q8,_q9,_qa,_){var _qb=E(_qa);if(!_qb._){return _kJ;}else{var _qc=_qb.b,_qd=E(_qb.a);if(E(_qd)==65306){var _qe=new T(function(){var _qf=E(_q9);if((_qf+1)*24<=E(_pF)-10){return new T2(0,_q8,_qf+1|0);}else{return new T2(0,new T(function(){return E(_q8)-1|0;}),_q6);}});return new F(function(){return _pt(_q4,_q5,_pF,_pG,_q6,new T(function(){return E(E(_qe).a);}),new T(function(){return E(E(_qe).b);}),_qc,_);});}else{var _qg=B(_mG(_q4,_pU,_ne,_q7,_q8,_q9,_qd,_)),_qh=_q4,_qi=_q5,_qj=_q6,_qk=_q7+1,_ql=_q8,_qm=_q9;_pW=_qh;_pX=_qi;_pY=_qj;_pZ=_qk;_q0=_ql;_q1=_qm;_q2=_qc;return __continue;}}})(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_));if(_q3!=__continue){return _q3;}}};return new F(function(){return _pV(_pD,_pE,_pH,0,new T(function(){if(E(_pH)!=E(_pJ)){return E(_pI);}else{return E(_pI)+1|0;}}),new T(function(){var _qn=E(_pJ);if(E(_pH)!=_qn){return _qn-1|0;}else{var _qo=(E(_pF)-10)/24,_qp=_qo&4294967295;if(_qo>=_qp){return _qp;}else{return _qp-1|0;}}}),_pM,_);});break;default:var _qq=function(_qr,_qs){var _qt=new T(function(){switch(E(_pO)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _pG;}}),_qu=new T(function(){var _qv=E(_pJ);if((_qv+1)*24<=E(_pF)-10){return new T2(0,_pI,_qv+1|0);}else{return new T2(0,new T(function(){return E(_pI)-1|0;}),_pH);}});if(E(_qr)==64){return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}else{var _qw=B(_mG(_pD,new T(function(){return B(_aW(_n9,E(_qt)));},1),_na,_lR,_pI,_pJ,_qs,_));return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}},_qx=E(_pO);switch(_qx){case 42:return new F(function(){return _qq(64,_nb);});break;case 12289:return new F(function(){return _qq(64,_nb);});break;case 12290:return new F(function(){return _qq(64,_nb);});break;default:return new F(function(){return _qq(_qx,_pN);});}}}})(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_));if(_pC!=__continue){return _pC;}}},_qy=function(_qz,_qA){while(1){var _qB=E(_qz);if(!_qB._){return E(_qA);}else{var _qC=_qA+1|0;_qz=_qB.b;_qA=_qC;continue;}}},_qD=function(_qE){return E(E(_qE).a);},_qF=function(_qG,_qH){var _qI=E(_qH),_qJ=new T(function(){var _qK=B(_lf(_qG)),_qL=B(_qF(_qG,B(A3(_qD,_qK,_qI,new T(function(){return B(A2(_lj,_qK,_f0));})))));return new T2(1,_qL.a,_qL.b);});return new T2(0,_qI,_qJ);},_qM=new T(function(){var _qN=B(_qF(_kg,_lR));return new T2(1,_qN.a,_qN.b);}),_qO=new T(function(){return B(unCStr("px Courier"));}),_qP=new T(function(){return B(_H(0,20,_Z));}),_qQ=new T(function(){return B(_x(_qP,_qO));}),_qR=function(_qS,_){return _kJ;},_qT=function(_qU,_qV,_qW,_qX,_qY){var _qZ=new T(function(){return E(_qW)*16;}),_r0=new T(function(){return E(_qX)*20;}),_r1=function(_r2,_r3){var _r4=E(_r2);if(!_r4._){return E(_qR);}else{var _r5=E(_r3);if(!_r5._){return E(_qR);}else{var _r6=new T(function(){return B(_r1(_r4.b,_r5.b));}),_r7=new T(function(){var _r8=new T(function(){var _r9=new T(function(){return B(_lK(new T(function(){return E(_qZ)+16*E(_r5.a);}),_r0,new T2(1,_r4.a,_Z)));});return B(_ms(_qQ,_r9));});return B(_m7(_qV,_r8));});return function(_ra,_){var _rb=B(A2(_r7,_ra,_));return new F(function(){return A2(_r6,_ra,_);});};}}};return new F(function(){return A3(_r1,_qY,_qM,_qU);});},_rc=45,_rd=new T(function(){return B(unCStr("-"));}),_re=new T2(1,_rc,_rd),_rf=function(_rg){var _rh=E(_rg);return (_rh==1)?E(_re):new T2(1,_rc,new T(function(){return B(_rf(_rh-1|0));}));},_ri=new T(function(){return B(unCStr(": empty list"));}),_rj=function(_rk){return new F(function(){return err(B(_x(_aL,new T(function(){return B(_x(_rk,_ri));},1))));});},_rl=new T(function(){return B(unCStr("head"));}),_rm=new T(function(){return B(_rj(_rl));}),_rn=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ro=new T(function(){return B(_lK(_lR,_lR,_Z));}),_rp=32,_rq=new T(function(){return B(unCStr("|"));}),_rr=function(_rs){var _rt=E(_rs);return (_rt._==0)?E(_rq):new T2(1,new T(function(){var _ru=E(_rt.a);switch(E(_ru.b)){case 7:return E(_rp);break;case 8:return E(_rp);break;default:return E(_ru.a);}}),new T(function(){return B(_rr(_rt.b));}));},_rv=function(_rw,_rx,_ry,_rz,_rA,_){var _rB=__app1(E(_rn),_rx),_rC=B(A2(_ro,_rw,_)),_rD=B(unAppCStr("-",new T(function(){var _rE=E(_rA);if(!_rE._){return E(_rm);}else{var _rF=B(_qy(_rE.a,0));if(0>=_rF){return E(_rd);}else{return B(_rf(_rF));}}}))),_rG=B(A(_qT,[_rw,_n8,_ry,_rz,_rD,_])),_rH=function(_rI,_rJ,_rK,_){while(1){var _rL=B((function(_rM,_rN,_rO,_){var _rP=E(_rO);if(!_rP._){return new F(function(){return A(_qT,[_rw,_n8,_rM,_rN,_rD,_]);});}else{var _rQ=B(A(_qT,[_rw,_n8,_rM,_rN,B(unAppCStr("|",new T(function(){return B(_rr(_rP.a));}))),_])),_rR=_rM;_rI=_rR;_rJ=new T(function(){return E(_rN)+1|0;});_rK=_rP.b;return __continue;}})(_rI,_rJ,_rK,_));if(_rL!=__continue){return _rL;}}};return new F(function(){return _rH(_ry,new T(function(){return E(_rz)+1|0;}),_rA,_);});},_rS=new T(function(){return B(_aW(_n9,1));}),_rT=new T(function(){return B(_aW(_n9,2));}),_rU=2,_rV=function(_rW,_rX,_rY,_rZ,_){var _s0=__app1(E(_rn),_rX),_s1=B(A2(_ro,_rW,_)),_s2=E(_rZ),_s3=E(_s2.b).a,_s4=E(_s2.a),_s5=_s4.a;if(!E(E(_s2.u).h)){return _kJ;}else{var _s6=B(_rv(_rW,_rX,new T(function(){return E(_rY)-E(_s3)|0;}),_rU,_s4.b,_));return new F(function(){return A(_qT,[_rW,new T(function(){if(E(_s4.e)==32){return E(_rS);}else{return E(_rT);}}),new T(function(){return ((E(E(_s5).a)+1|0)+E(_rY)|0)-E(_s3)|0;},1),new T(function(){return (E(E(_s5).b)+2|0)+1|0;},1),new T2(1,_s4.d,_Z),_]);});}},_s7=function(_s8){return E(E(_s8).a);},_s9=function(_sa){return E(E(_sa).a);},_sb=function(_sc,_sd){while(1){var _se=E(_sc);if(!_se._){return E(_sd);}else{_sc=_se.b;_sd=_se.a;continue;}}},_sf=function(_sg,_sh,_si){return new F(function(){return _sb(_sh,_sg);});},_sj=new T1(0,2),_sk=function(_sl,_sm){while(1){var _sn=E(_sl);if(!_sn._){var _so=_sn.a,_sp=E(_sm);if(!_sp._){var _sq=_sp.a;if(!(imul(_so,_sq)|0)){return new T1(0,imul(_so,_sq)|0);}else{_sl=new T1(1,I_fromInt(_so));_sm=new T1(1,I_fromInt(_sq));continue;}}else{_sl=new T1(1,I_fromInt(_so));_sm=_sp;continue;}}else{var _sr=E(_sm);if(!_sr._){_sl=_sn;_sm=new T1(1,I_fromInt(_sr.a));continue;}else{return new T1(1,I_mul(_sn.a,_sr.a));}}}},_ss=function(_st,_su,_sv){while(1){if(!(_su%2)){var _sw=B(_sk(_st,_st)),_sx=quot(_su,2);_st=_sw;_su=_sx;continue;}else{var _sy=E(_su);if(_sy==1){return new F(function(){return _sk(_st,_sv);});}else{var _sw=B(_sk(_st,_st)),_sz=B(_sk(_st,_sv));_st=_sw;_su=quot(_sy-1|0,2);_sv=_sz;continue;}}}},_sA=function(_sB,_sC){while(1){if(!(_sC%2)){var _sD=B(_sk(_sB,_sB)),_sE=quot(_sC,2);_sB=_sD;_sC=_sE;continue;}else{var _sF=E(_sC);if(_sF==1){return E(_sB);}else{return new F(function(){return _ss(B(_sk(_sB,_sB)),quot(_sF-1|0,2),_sB);});}}}},_sG=function(_sH){return E(E(_sH).c);},_sI=function(_sJ){return E(E(_sJ).a);},_sK=function(_sL){return E(E(_sL).b);},_sM=function(_sN){return E(E(_sN).b);},_sO=function(_sP){return E(E(_sP).c);},_sQ=new T1(0,0),_sR=new T1(0,2),_sS=function(_sT){return E(E(_sT).d);},_sU=function(_sV,_sW){var _sX=B(_s7(_sV)),_sY=new T(function(){return B(_s9(_sX));}),_sZ=new T(function(){return B(A3(_sS,_sV,_sW,new T(function(){return B(A2(_lj,_sY,_sR));})));});return new F(function(){return A3(_4F,B(_sI(B(_sK(_sX)))),_sZ,new T(function(){return B(A2(_lj,_sY,_sQ));}));});},_t0=new T(function(){return B(unCStr("Negative exponent"));}),_t1=new T(function(){return B(err(_t0));}),_t2=function(_t3){return E(E(_t3).c);},_t4=function(_t5,_t6,_t7,_t8){var _t9=B(_s7(_t6)),_ta=new T(function(){return B(_s9(_t9));}),_tb=B(_sK(_t9));if(!B(A3(_sO,_tb,_t8,new T(function(){return B(A2(_lj,_ta,_sQ));})))){if(!B(A3(_4F,B(_sI(_tb)),_t8,new T(function(){return B(A2(_lj,_ta,_sQ));})))){var _tc=new T(function(){return B(A2(_lj,_ta,_sR));}),_td=new T(function(){return B(A2(_lj,_ta,_f0));}),_te=B(_sI(_tb)),_tf=function(_tg,_th,_ti){while(1){var _tj=B((function(_tk,_tl,_tm){if(!B(_sU(_t6,_tl))){if(!B(A3(_4F,_te,_tl,_td))){var _tn=new T(function(){return B(A3(_t2,_t6,new T(function(){return B(A3(_sM,_ta,_tl,_td));}),_tc));});_tg=new T(function(){return B(A3(_sG,_t5,_tk,_tk));});_th=_tn;_ti=new T(function(){return B(A3(_sG,_t5,_tk,_tm));});return __continue;}else{return new F(function(){return A3(_sG,_t5,_tk,_tm);});}}else{var _to=_tm;_tg=new T(function(){return B(A3(_sG,_t5,_tk,_tk));});_th=new T(function(){return B(A3(_t2,_t6,_tl,_tc));});_ti=_to;return __continue;}})(_tg,_th,_ti));if(_tj!=__continue){return _tj;}}},_tp=function(_tq,_tr){while(1){var _ts=B((function(_tt,_tu){if(!B(_sU(_t6,_tu))){if(!B(A3(_4F,_te,_tu,_td))){var _tv=new T(function(){return B(A3(_t2,_t6,new T(function(){return B(A3(_sM,_ta,_tu,_td));}),_tc));});return new F(function(){return _tf(new T(function(){return B(A3(_sG,_t5,_tt,_tt));}),_tv,_tt);});}else{return E(_tt);}}else{_tq=new T(function(){return B(A3(_sG,_t5,_tt,_tt));});_tr=new T(function(){return B(A3(_t2,_t6,_tu,_tc));});return __continue;}})(_tq,_tr));if(_ts!=__continue){return _ts;}}};return new F(function(){return _tp(_t7,_t8);});}else{return new F(function(){return A2(_lj,_t5,_f0);});}}else{return E(_t1);}},_tw=new T(function(){return B(err(_t0));}),_tx=function(_ty){var _tz=I_decodeDouble(_ty);return new T2(0,new T1(1,_tz.b),_tz.a);},_tA=function(_tB,_tC){var _tD=B(_tx(_tC)),_tE=_tD.a,_tF=_tD.b,_tG=new T(function(){return B(_s9(new T(function(){return B(_s7(_tB));})));});if(_tF<0){var _tH= -_tF;if(_tH>=0){var _tI=E(_tH);if(!_tI){var _tJ=E(_f0);}else{var _tJ=B(_sA(_sj,_tI));}if(!B(_gs(_tJ,_gS))){var _tK=B(_gJ(_tE,_tJ));return new T2(0,new T(function(){return B(A2(_lj,_tG,_tK.a));}),new T(function(){return B(_go(_tK.b,_tF));}));}else{return E(_dZ);}}else{return E(_tw);}}else{var _tL=new T(function(){var _tM=new T(function(){return B(_t4(_tG,_fX,new T(function(){return B(A2(_lj,_tG,_sj));}),_tF));});return B(A3(_sG,_tG,new T(function(){return B(A2(_lj,_tG,_tE));}),_tM));});return new T2(0,_tL,_jF);}},_tN=function(_tO,_tP){while(1){var _tQ=E(_tP);if(!_tQ._){return __Z;}else{var _tR=_tQ.b,_tS=E(_tO);if(_tS==1){return E(_tR);}else{_tO=_tS-1|0;_tP=_tR;continue;}}}},_tT=function(_tU,_tV){var _tW=E(_tV);if(!_tW._){return __Z;}else{var _tX=_tW.a,_tY=E(_tU);return (_tY==1)?new T2(1,_tX,_Z):new T2(1,_tX,new T(function(){return B(_tT(_tY-1|0,_tW.b));}));}},_tZ=function(_u0,_u1,_u2,_u3){while(1){if(B(_aW(new T2(1,_u2,_u3),_u1))!=_u0){var _u4=_u1+1|0;_u1=_u4;continue;}else{if(0>=_u1){return __Z;}else{return new F(function(){return _tT(_u1,new T2(1,_u2,_u3));});}}}},_u5=function(_u6,_u7,_u8){var _u9=E(_u8);if(!_u9._){return __Z;}else{var _ua=E(_u6);if(B(_aW(_u9,_u7))!=_ua){return new F(function(){return _tZ(_ua,_u7+1|0,_u9.a,_u9.b);});}else{if(0>=_u7){return __Z;}else{return new F(function(){return _tT(_u7,_u9);});}}}},_ub=function(_uc,_ud,_ue){var _uf=_ud+1|0;if(_uf>0){return new F(function(){return _tN(_uf,B(_u5(_uc,_uf,_ue)));});}else{return new F(function(){return _u5(_uc,_uf,_ue);});}},_ug=function(_uh,_ui){return (!B(_ae(_uh,_ui)))?true:false;},_uj=new T2(0,_ae,_ug),_uk=0,_ul=new T(function(){return B(_ic("Event.hs:(81,1)-(82,68)|function addEvent"));}),_um=function(_un,_uo,_up,_uq,_ur,_us,_ut,_uu,_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,_uH,_uI,_uJ){while(1){var _uK=E(_un);if(!_uK._){return {_:0,a:_uo,b:_up,c:_uq,d:_ur,e:_us,f:_ut,g:_uu,h:_uv,i:_uw,j:_ux,k:_uy,l:_uz,m:_uA,n:_uB,o:_uC,p:_uD,q:_uE,r:_uF,s:_uG,t:_uH,u:_uI,v:_uJ};}else{var _uL=E(_uK.b);if(!_uL._){return E(_ul);}else{var _uM=new T2(1,new T2(0,_uK.a,_uL.a),_us),_uN=new T2(1,_uk,_ut);_un=_uL.b;_us=_uM;_ut=_uN;continue;}}}},_uO=function(_uP,_uQ,_uR){var _uS=E(_uR);if(!_uS._){return __Z;}else{var _uT=_uS.a,_uU=_uS.b;return (!B(A2(_uP,_uQ,_uT)))?new T2(1,_uT,new T(function(){return B(_uO(_uP,_uQ,_uU));})):E(_uU);}},_uV=function(_uW,_uX){while(1){var _uY=E(_uW);if(!_uY._){return (E(_uX)._==0)?true:false;}else{var _uZ=E(_uX);if(!_uZ._){return false;}else{if(E(_uY.a)!=E(_uZ.a)){return false;}else{_uW=_uY.b;_uX=_uZ.b;continue;}}}}},_v0=function(_v1,_v2){while(1){var _v3=E(_v1);if(!_v3._){return (E(_v2)._==0)?true:false;}else{var _v4=E(_v2);if(!_v4._){return false;}else{if(!B(_ae(_v3.a,_v4.a))){return false;}else{_v1=_v3.b;_v2=_v4.b;continue;}}}}},_v5=function(_v6,_v7){switch(E(_v6)){case 0:return (E(_v7)==0)?true:false;case 1:return (E(_v7)==1)?true:false;case 2:return (E(_v7)==2)?true:false;case 3:return (E(_v7)==3)?true:false;case 4:return (E(_v7)==4)?true:false;case 5:return (E(_v7)==5)?true:false;case 6:return (E(_v7)==6)?true:false;case 7:return (E(_v7)==7)?true:false;default:return (E(_v7)==8)?true:false;}},_v8=function(_v9,_va,_vb,_vc){if(_v9!=_vb){return false;}else{return new F(function(){return _v5(_va,_vc);});}},_vd=function(_ve,_vf){var _vg=E(_ve),_vh=E(_vf);return new F(function(){return _v8(E(_vg.a),_vg.b,E(_vh.a),_vh.b);});},_vi=function(_vj,_vk,_vl,_vm){if(_vj!=_vl){return true;}else{switch(E(_vk)){case 0:return (E(_vm)==0)?false:true;case 1:return (E(_vm)==1)?false:true;case 2:return (E(_vm)==2)?false:true;case 3:return (E(_vm)==3)?false:true;case 4:return (E(_vm)==4)?false:true;case 5:return (E(_vm)==5)?false:true;case 6:return (E(_vm)==6)?false:true;case 7:return (E(_vm)==7)?false:true;default:return (E(_vm)==8)?false:true;}}},_vn=function(_vo,_vp){var _vq=E(_vo),_vr=E(_vp);return new F(function(){return _vi(E(_vq.a),_vq.b,E(_vr.a),_vr.b);});},_vs=new T2(0,_vd,_vn),_vt=0,_vu=function(_vv,_vw){var _vx=E(_vw);if(!_vx._){return 0;}else{var _vy=_vx.b,_vz=E(_vv),_vA=E(_vx.a),_vB=_vA.b;if(E(_vz.a)!=E(_vA.a)){return 1+B(_vu(_vz,_vy))|0;}else{switch(E(_vz.b)){case 0:return (E(_vB)==0)?0:1+B(_vu(_vz,_vy))|0;case 1:return (E(_vB)==1)?0:1+B(_vu(_vz,_vy))|0;case 2:return (E(_vB)==2)?0:1+B(_vu(_vz,_vy))|0;case 3:return (E(_vB)==3)?0:1+B(_vu(_vz,_vy))|0;case 4:return (E(_vB)==4)?0:1+B(_vu(_vz,_vy))|0;case 5:return (E(_vB)==5)?0:1+B(_vu(_vz,_vy))|0;case 6:return (E(_vB)==6)?0:1+B(_vu(_vz,_vy))|0;case 7:return (E(_vB)==7)?0:1+B(_vu(_vz,_vy))|0;default:return (E(_vB)==8)?0:1+B(_vu(_vz,_vy))|0;}}}},_vC=function(_vD,_vE){return new F(function(){return _vu(_vD,_vE);});},_vF=function(_vG,_vH){var _vI=E(_vH);if(!_vI._){return new T2(0,_vt,_vt);}else{var _vJ=_vI.a,_vK=_vI.b;return (!B(_4H(_vs,_vG,_vJ)))?new T2(0,new T(function(){return E(B(_vF(_vG,_vK)).a);}),new T(function(){return 1+E(B(_vF(_vG,_vK)).b)|0;})):new T2(0,new T(function(){return B(_vC(_vG,_vJ));}),_vt);}},_vL=function(_vM,_vN){while(1){var _vO=E(_vN);if(!_vO._){return __Z;}else{var _vP=_vO.b,_vQ=E(_vM);if(_vQ==1){return E(_vP);}else{_vM=_vQ-1|0;_vN=_vP;continue;}}}},_vR=new T(function(){return B(unCStr("getch"));}),_vS=new T(function(){return B(unCStr("=="));}),_vT=new T(function(){return B(unCStr("&&"));}),_vU=new T(function(){return B(unCStr("||"));}),_vV=new T(function(){return B(unCStr("getpos"));}),_vW=new T(function(){return B(unCStr("ch"));}),_vX=new T(function(){return B(unCStr("tp"));}),_vY=new T2(1,_vX,_Z),_vZ=new T2(1,_vW,_vY),_w0=new T2(0,_vV,_vZ),_w1=new T(function(){return B(unCStr("a"));}),_w2=new T(function(){return B(unCStr("b"));}),_w3=new T2(1,_w2,_Z),_w4=new T2(1,_w1,_w3),_w5=new T2(0,_vS,_w4),_w6=new T2(0,_vT,_w4),_w7=new T2(0,_vU,_w4),_w8=new T2(1,_w7,_Z),_w9=new T2(1,_w6,_w8),_wa=new T2(1,_w5,_w9),_wb=new T2(1,_w0,_wa),_wc=new T(function(){return B(unCStr("p"));}),_wd=new T(function(){return B(unCStr("q"));}),_we=new T2(1,_wd,_Z),_wf=new T2(1,_wc,_we),_wg=new T2(0,_vR,_wf),_wh=new T2(1,_wg,_wb),_wi=new T(function(){return B(unCStr("foldr1"));}),_wj=new T(function(){return B(_rj(_wi));}),_wk=function(_wl,_wm){var _wn=E(_wm);if(!_wn._){return E(_wj);}else{var _wo=_wn.a,_wp=E(_wn.b);if(!_wp._){return E(_wo);}else{return new F(function(){return A2(_wl,_wo,new T(function(){return B(_wk(_wl,_wp));}));});}}},_wq=function(_wr){return E(E(_wr).a);},_ws=function(_wt,_wu,_wv){while(1){var _ww=E(_wv);if(!_ww._){return __Z;}else{var _wx=E(_ww.a);if(!B(A3(_4F,_wt,_wu,_wx.a))){_wv=_ww.b;continue;}else{return new T1(1,_wx.b);}}}},_wy=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_wz=new T(function(){return B(err(_wy));}),_wA=new T(function(){return B(unCStr("T"));}),_wB=new T(function(){return B(unCStr("F"));}),_wC=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_wD=new T(function(){return B(err(_wC));}),_wE=new T(function(){return B(unCStr("empty"));}),_wF=new T2(1,_wE,_Z),_wG=new T(function(){return B(_ic("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_wH=function(_wI,_wJ){while(1){var _wK=B((function(_wL,_wM){var _wN=E(_wL);switch(_wN._){case 0:var _wO=E(_wM);if(!_wO._){return __Z;}else{_wI=B(A1(_wN.a,_wO.a));_wJ=_wO.b;return __continue;}break;case 1:var _wP=B(A1(_wN.a,_wM)),_wQ=_wM;_wI=_wP;_wJ=_wQ;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_wN.a,_wM),new T(function(){return B(_wH(_wN.b,_wM));}));default:return E(_wN.a);}})(_wI,_wJ));if(_wK!=__continue){return _wK;}}},_wR=function(_wS,_wT){var _wU=function(_wV){var _wW=E(_wT);if(_wW._==3){return new T2(3,_wW.a,new T(function(){return B(_wR(_wS,_wW.b));}));}else{var _wX=E(_wS);if(_wX._==2){return E(_wW);}else{var _wY=E(_wW);if(_wY._==2){return E(_wX);}else{var _wZ=function(_x0){var _x1=E(_wY);if(_x1._==4){var _x2=function(_x3){return new T1(4,new T(function(){return B(_x(B(_wH(_wX,_x3)),_x1.a));}));};return new T1(1,_x2);}else{var _x4=E(_wX);if(_x4._==1){var _x5=_x4.a,_x6=E(_x1);if(!_x6._){return new T1(1,function(_x7){return new F(function(){return _wR(B(A1(_x5,_x7)),_x6);});});}else{var _x8=function(_x9){return new F(function(){return _wR(B(A1(_x5,_x9)),new T(function(){return B(A1(_x6.a,_x9));}));});};return new T1(1,_x8);}}else{var _xa=E(_x1);if(!_xa._){return E(_wG);}else{var _xb=function(_xc){return new F(function(){return _wR(_x4,new T(function(){return B(A1(_xa.a,_xc));}));});};return new T1(1,_xb);}}}},_xd=E(_wX);switch(_xd._){case 1:var _xe=E(_wY);if(_xe._==4){var _xf=function(_xg){return new T1(4,new T(function(){return B(_x(B(_wH(B(A1(_xd.a,_xg)),_xg)),_xe.a));}));};return new T1(1,_xf);}else{return new F(function(){return _wZ(_);});}break;case 4:var _xh=_xd.a,_xi=E(_wY);switch(_xi._){case 0:var _xj=function(_xk){var _xl=new T(function(){return B(_x(_xh,new T(function(){return B(_wH(_xi,_xk));},1)));});return new T1(4,_xl);};return new T1(1,_xj);case 1:var _xm=function(_xn){var _xo=new T(function(){return B(_x(_xh,new T(function(){return B(_wH(B(A1(_xi.a,_xn)),_xn));},1)));});return new T1(4,_xo);};return new T1(1,_xm);default:return new T1(4,new T(function(){return B(_x(_xh,_xi.a));}));}break;default:return new F(function(){return _wZ(_);});}}}}},_xp=E(_wS);switch(_xp._){case 0:var _xq=E(_wT);if(!_xq._){var _xr=function(_xs){return new F(function(){return _wR(B(A1(_xp.a,_xs)),new T(function(){return B(A1(_xq.a,_xs));}));});};return new T1(0,_xr);}else{return new F(function(){return _wU(_);});}break;case 3:return new T2(3,_xp.a,new T(function(){return B(_wR(_xp.b,_wT));}));default:return new F(function(){return _wU(_);});}},_xt=new T(function(){return B(unCStr("("));}),_xu=new T(function(){return B(unCStr(")"));}),_xv=function(_xw,_xx){var _xy=E(_xw);switch(_xy._){case 0:return new T1(0,function(_xz){return new F(function(){return _xv(B(A1(_xy.a,_xz)),_xx);});});case 1:return new T1(1,function(_xA){return new F(function(){return _xv(B(A1(_xy.a,_xA)),_xx);});});case 2:return new T0(2);case 3:return new F(function(){return _wR(B(A1(_xx,_xy.a)),new T(function(){return B(_xv(_xy.b,_xx));}));});break;default:var _xB=function(_xC){var _xD=E(_xC);if(!_xD._){return __Z;}else{var _xE=E(_xD.a);return new F(function(){return _x(B(_wH(B(A1(_xx,_xE.a)),_xE.b)),new T(function(){return B(_xB(_xD.b));},1));});}},_xF=B(_xB(_xy.a));return (_xF._==0)?new T0(2):new T1(4,_xF);}},_xG=new T0(2),_xH=function(_xI){return new T2(3,_xI,_xG);},_xJ=function(_xK,_xL){var _xM=E(_xK);if(!_xM){return new F(function(){return A1(_xL,_kJ);});}else{var _xN=new T(function(){return B(_xJ(_xM-1|0,_xL));});return new T1(0,function(_xO){return E(_xN);});}},_xP=function(_xQ,_xR,_xS){var _xT=new T(function(){return B(A1(_xQ,_xH));}),_xU=function(_xV,_xW,_xX,_xY){while(1){var _xZ=B((function(_y0,_y1,_y2,_y3){var _y4=E(_y0);switch(_y4._){case 0:var _y5=E(_y1);if(!_y5._){return new F(function(){return A1(_xR,_y3);});}else{var _y6=_y2+1|0,_y7=_y3;_xV=B(A1(_y4.a,_y5.a));_xW=_y5.b;_xX=_y6;_xY=_y7;return __continue;}break;case 1:var _y8=B(A1(_y4.a,_y1)),_y9=_y1,_y6=_y2,_y7=_y3;_xV=_y8;_xW=_y9;_xX=_y6;_xY=_y7;return __continue;case 2:return new F(function(){return A1(_xR,_y3);});break;case 3:var _ya=new T(function(){return B(_xv(_y4,_y3));});return new F(function(){return _xJ(_y2,function(_yb){return E(_ya);});});break;default:return new F(function(){return _xv(_y4,_y3);});}})(_xV,_xW,_xX,_xY));if(_xZ!=__continue){return _xZ;}}};return function(_yc){return new F(function(){return _xU(_xT,_yc,0,_xS);});};},_yd=function(_ye){return new F(function(){return A1(_ye,_Z);});},_yf=function(_yg,_yh){var _yi=function(_yj){var _yk=E(_yj);if(!_yk._){return E(_yd);}else{var _yl=_yk.a;if(!B(A1(_yg,_yl))){return E(_yd);}else{var _ym=new T(function(){return B(_yi(_yk.b));}),_yn=function(_yo){var _yp=new T(function(){return B(A1(_ym,function(_yq){return new F(function(){return A1(_yo,new T2(1,_yl,_yq));});}));});return new T1(0,function(_yr){return E(_yp);});};return E(_yn);}}};return function(_ys){return new F(function(){return A2(_yi,_ys,_yh);});};},_yt=new T0(6),_yu=new T(function(){return B(unCStr("valDig: Bad base"));}),_yv=new T(function(){return B(err(_yu));}),_yw=function(_yx,_yy){var _yz=function(_yA,_yB){var _yC=E(_yA);if(!_yC._){var _yD=new T(function(){return B(A1(_yB,_Z));});return function(_yE){return new F(function(){return A1(_yE,_yD);});};}else{var _yF=E(_yC.a),_yG=function(_yH){var _yI=new T(function(){return B(_yz(_yC.b,function(_yJ){return new F(function(){return A1(_yB,new T2(1,_yH,_yJ));});}));}),_yK=function(_yL){var _yM=new T(function(){return B(A1(_yI,_yL));});return new T1(0,function(_yN){return E(_yM);});};return E(_yK);};switch(E(_yx)){case 8:if(48>_yF){var _yO=new T(function(){return B(A1(_yB,_Z));});return function(_yP){return new F(function(){return A1(_yP,_yO);});};}else{if(_yF>55){var _yQ=new T(function(){return B(A1(_yB,_Z));});return function(_yR){return new F(function(){return A1(_yR,_yQ);});};}else{return new F(function(){return _yG(_yF-48|0);});}}break;case 10:if(48>_yF){var _yS=new T(function(){return B(A1(_yB,_Z));});return function(_yT){return new F(function(){return A1(_yT,_yS);});};}else{if(_yF>57){var _yU=new T(function(){return B(A1(_yB,_Z));});return function(_yV){return new F(function(){return A1(_yV,_yU);});};}else{return new F(function(){return _yG(_yF-48|0);});}}break;case 16:if(48>_yF){if(97>_yF){if(65>_yF){var _yW=new T(function(){return B(A1(_yB,_Z));});return function(_yX){return new F(function(){return A1(_yX,_yW);});};}else{if(_yF>70){var _yY=new T(function(){return B(A1(_yB,_Z));});return function(_yZ){return new F(function(){return A1(_yZ,_yY);});};}else{return new F(function(){return _yG((_yF-65|0)+10|0);});}}}else{if(_yF>102){if(65>_yF){var _z0=new T(function(){return B(A1(_yB,_Z));});return function(_z1){return new F(function(){return A1(_z1,_z0);});};}else{if(_yF>70){var _z2=new T(function(){return B(A1(_yB,_Z));});return function(_z3){return new F(function(){return A1(_z3,_z2);});};}else{return new F(function(){return _yG((_yF-65|0)+10|0);});}}}else{return new F(function(){return _yG((_yF-97|0)+10|0);});}}}else{if(_yF>57){if(97>_yF){if(65>_yF){var _z4=new T(function(){return B(A1(_yB,_Z));});return function(_z5){return new F(function(){return A1(_z5,_z4);});};}else{if(_yF>70){var _z6=new T(function(){return B(A1(_yB,_Z));});return function(_z7){return new F(function(){return A1(_z7,_z6);});};}else{return new F(function(){return _yG((_yF-65|0)+10|0);});}}}else{if(_yF>102){if(65>_yF){var _z8=new T(function(){return B(A1(_yB,_Z));});return function(_z9){return new F(function(){return A1(_z9,_z8);});};}else{if(_yF>70){var _za=new T(function(){return B(A1(_yB,_Z));});return function(_zb){return new F(function(){return A1(_zb,_za);});};}else{return new F(function(){return _yG((_yF-65|0)+10|0);});}}}else{return new F(function(){return _yG((_yF-97|0)+10|0);});}}}else{return new F(function(){return _yG(_yF-48|0);});}}break;default:return E(_yv);}}},_zc=function(_zd){var _ze=E(_zd);if(!_ze._){return new T0(2);}else{return new F(function(){return A1(_yy,_ze);});}};return function(_zf){return new F(function(){return A3(_yz,_zf,_61,_zc);});};},_zg=16,_zh=8,_zi=function(_zj){var _zk=function(_zl){return new F(function(){return A1(_zj,new T1(5,new T2(0,_zh,_zl)));});},_zm=function(_zn){return new F(function(){return A1(_zj,new T1(5,new T2(0,_zg,_zn)));});},_zo=function(_zp){switch(E(_zp)){case 79:return new T1(1,B(_yw(_zh,_zk)));case 88:return new T1(1,B(_yw(_zg,_zm)));case 111:return new T1(1,B(_yw(_zh,_zk)));case 120:return new T1(1,B(_yw(_zg,_zm)));default:return new T0(2);}};return function(_zq){return (E(_zq)==48)?E(new T1(0,_zo)):new T0(2);};},_zr=function(_zs){return new T1(0,B(_zi(_zs)));},_zt=function(_zu){return new F(function(){return A1(_zu,_2U);});},_zv=function(_zw){return new F(function(){return A1(_zw,_2U);});},_zx=10,_zy=new T1(0,10),_zz=function(_zA){return new F(function(){return _eW(E(_zA));});},_zB=new T(function(){return B(unCStr("this should not happen"));}),_zC=new T(function(){return B(err(_zB));}),_zD=function(_zE,_zF){var _zG=E(_zF);if(!_zG._){return __Z;}else{var _zH=E(_zG.b);return (_zH._==0)?E(_zC):new T2(1,B(_gA(B(_sk(_zG.a,_zE)),_zH.a)),new T(function(){return B(_zD(_zE,_zH.b));}));}},_zI=new T1(0,0),_zJ=function(_zK,_zL,_zM){while(1){var _zN=B((function(_zO,_zP,_zQ){var _zR=E(_zQ);if(!_zR._){return E(_zI);}else{if(!E(_zR.b)._){return E(_zR.a);}else{var _zS=E(_zP);if(_zS<=40){var _zT=function(_zU,_zV){while(1){var _zW=E(_zV);if(!_zW._){return E(_zU);}else{var _zX=B(_gA(B(_sk(_zU,_zO)),_zW.a));_zU=_zX;_zV=_zW.b;continue;}}};return new F(function(){return _zT(_zI,_zR);});}else{var _zY=B(_sk(_zO,_zO));if(!(_zS%2)){var _zZ=B(_zD(_zO,_zR));_zK=_zY;_zL=quot(_zS+1|0,2);_zM=_zZ;return __continue;}else{var _zZ=B(_zD(_zO,new T2(1,_zI,_zR)));_zK=_zY;_zL=quot(_zS+1|0,2);_zM=_zZ;return __continue;}}}}})(_zK,_zL,_zM));if(_zN!=__continue){return _zN;}}},_A0=function(_A1,_A2){return new F(function(){return _zJ(_A1,new T(function(){return B(_qy(_A2,0));},1),B(_aj(_zz,_A2)));});},_A3=function(_A4){var _A5=new T(function(){var _A6=new T(function(){var _A7=function(_A8){return new F(function(){return A1(_A4,new T1(1,new T(function(){return B(_A0(_zy,_A8));})));});};return new T1(1,B(_yw(_zx,_A7)));}),_A9=function(_Aa){if(E(_Aa)==43){var _Ab=function(_Ac){return new F(function(){return A1(_A4,new T1(1,new T(function(){return B(_A0(_zy,_Ac));})));});};return new T1(1,B(_yw(_zx,_Ab)));}else{return new T0(2);}},_Ad=function(_Ae){if(E(_Ae)==45){var _Af=function(_Ag){return new F(function(){return A1(_A4,new T1(1,new T(function(){return B(_jy(B(_A0(_zy,_Ag))));})));});};return new T1(1,B(_yw(_zx,_Af)));}else{return new T0(2);}};return B(_wR(B(_wR(new T1(0,_Ad),new T1(0,_A9))),_A6));});return new F(function(){return _wR(new T1(0,function(_Ah){return (E(_Ah)==101)?E(_A5):new T0(2);}),new T1(0,function(_Ai){return (E(_Ai)==69)?E(_A5):new T0(2);}));});},_Aj=function(_Ak){var _Al=function(_Am){return new F(function(){return A1(_Ak,new T1(1,_Am));});};return function(_An){return (E(_An)==46)?new T1(1,B(_yw(_zx,_Al))):new T0(2);};},_Ao=function(_Ap){return new T1(0,B(_Aj(_Ap)));},_Aq=function(_Ar){var _As=function(_At){var _Au=function(_Av){return new T1(1,B(_xP(_A3,_zt,function(_Aw){return new F(function(){return A1(_Ar,new T1(5,new T3(1,_At,_Av,_Aw)));});})));};return new T1(1,B(_xP(_Ao,_zv,_Au)));};return new F(function(){return _yw(_zx,_As);});},_Ax=function(_Ay){return new T1(1,B(_Aq(_Ay)));},_Az=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_AA=function(_AB){return new F(function(){return _4H(_lc,_AB,_Az);});},_AC=false,_AD=true,_AE=function(_AF){var _AG=new T(function(){return B(A1(_AF,_zh));}),_AH=new T(function(){return B(A1(_AF,_zg));});return function(_AI){switch(E(_AI)){case 79:return E(_AG);case 88:return E(_AH);case 111:return E(_AG);case 120:return E(_AH);default:return new T0(2);}};},_AJ=function(_AK){return new T1(0,B(_AE(_AK)));},_AL=function(_AM){return new F(function(){return A1(_AM,_zx);});},_AN=function(_AO){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_H(9,_AO,_Z));}))));});},_AP=function(_AQ){return new T0(2);},_AR=function(_AS){var _AT=E(_AS);if(!_AT._){return E(_AP);}else{var _AU=_AT.a,_AV=E(_AT.b);if(!_AV._){return E(_AU);}else{var _AW=new T(function(){return B(_AR(_AV));}),_AX=function(_AY){return new F(function(){return _wR(B(A1(_AU,_AY)),new T(function(){return B(A1(_AW,_AY));}));});};return E(_AX);}}},_AZ=function(_B0,_B1){var _B2=function(_B3,_B4,_B5){var _B6=E(_B3);if(!_B6._){return new F(function(){return A1(_B5,_B0);});}else{var _B7=E(_B4);if(!_B7._){return new T0(2);}else{if(E(_B6.a)!=E(_B7.a)){return new T0(2);}else{var _B8=new T(function(){return B(_B2(_B6.b,_B7.b,_B5));});return new T1(0,function(_B9){return E(_B8);});}}}};return function(_Ba){return new F(function(){return _B2(_B0,_Ba,_B1);});};},_Bb=new T(function(){return B(unCStr("SO"));}),_Bc=14,_Bd=function(_Be){var _Bf=new T(function(){return B(A1(_Be,_Bc));});return new T1(1,B(_AZ(_Bb,function(_Bg){return E(_Bf);})));},_Bh=new T(function(){return B(unCStr("SOH"));}),_Bi=1,_Bj=function(_Bk){var _Bl=new T(function(){return B(A1(_Bk,_Bi));});return new T1(1,B(_AZ(_Bh,function(_Bm){return E(_Bl);})));},_Bn=function(_Bo){return new T1(1,B(_xP(_Bj,_Bd,_Bo)));},_Bp=new T(function(){return B(unCStr("NUL"));}),_Bq=0,_Br=function(_Bs){var _Bt=new T(function(){return B(A1(_Bs,_Bq));});return new T1(1,B(_AZ(_Bp,function(_Bu){return E(_Bt);})));},_Bv=new T(function(){return B(unCStr("STX"));}),_Bw=2,_Bx=function(_By){var _Bz=new T(function(){return B(A1(_By,_Bw));});return new T1(1,B(_AZ(_Bv,function(_BA){return E(_Bz);})));},_BB=new T(function(){return B(unCStr("ETX"));}),_BC=3,_BD=function(_BE){var _BF=new T(function(){return B(A1(_BE,_BC));});return new T1(1,B(_AZ(_BB,function(_BG){return E(_BF);})));},_BH=new T(function(){return B(unCStr("EOT"));}),_BI=4,_BJ=function(_BK){var _BL=new T(function(){return B(A1(_BK,_BI));});return new T1(1,B(_AZ(_BH,function(_BM){return E(_BL);})));},_BN=new T(function(){return B(unCStr("ENQ"));}),_BO=5,_BP=function(_BQ){var _BR=new T(function(){return B(A1(_BQ,_BO));});return new T1(1,B(_AZ(_BN,function(_BS){return E(_BR);})));},_BT=new T(function(){return B(unCStr("ACK"));}),_BU=6,_BV=function(_BW){var _BX=new T(function(){return B(A1(_BW,_BU));});return new T1(1,B(_AZ(_BT,function(_BY){return E(_BX);})));},_BZ=new T(function(){return B(unCStr("BEL"));}),_C0=7,_C1=function(_C2){var _C3=new T(function(){return B(A1(_C2,_C0));});return new T1(1,B(_AZ(_BZ,function(_C4){return E(_C3);})));},_C5=new T(function(){return B(unCStr("BS"));}),_C6=8,_C7=function(_C8){var _C9=new T(function(){return B(A1(_C8,_C6));});return new T1(1,B(_AZ(_C5,function(_Ca){return E(_C9);})));},_Cb=new T(function(){return B(unCStr("HT"));}),_Cc=9,_Cd=function(_Ce){var _Cf=new T(function(){return B(A1(_Ce,_Cc));});return new T1(1,B(_AZ(_Cb,function(_Cg){return E(_Cf);})));},_Ch=new T(function(){return B(unCStr("LF"));}),_Ci=10,_Cj=function(_Ck){var _Cl=new T(function(){return B(A1(_Ck,_Ci));});return new T1(1,B(_AZ(_Ch,function(_Cm){return E(_Cl);})));},_Cn=new T(function(){return B(unCStr("VT"));}),_Co=11,_Cp=function(_Cq){var _Cr=new T(function(){return B(A1(_Cq,_Co));});return new T1(1,B(_AZ(_Cn,function(_Cs){return E(_Cr);})));},_Ct=new T(function(){return B(unCStr("FF"));}),_Cu=12,_Cv=function(_Cw){var _Cx=new T(function(){return B(A1(_Cw,_Cu));});return new T1(1,B(_AZ(_Ct,function(_Cy){return E(_Cx);})));},_Cz=new T(function(){return B(unCStr("CR"));}),_CA=13,_CB=function(_CC){var _CD=new T(function(){return B(A1(_CC,_CA));});return new T1(1,B(_AZ(_Cz,function(_CE){return E(_CD);})));},_CF=new T(function(){return B(unCStr("SI"));}),_CG=15,_CH=function(_CI){var _CJ=new T(function(){return B(A1(_CI,_CG));});return new T1(1,B(_AZ(_CF,function(_CK){return E(_CJ);})));},_CL=new T(function(){return B(unCStr("DLE"));}),_CM=16,_CN=function(_CO){var _CP=new T(function(){return B(A1(_CO,_CM));});return new T1(1,B(_AZ(_CL,function(_CQ){return E(_CP);})));},_CR=new T(function(){return B(unCStr("DC1"));}),_CS=17,_CT=function(_CU){var _CV=new T(function(){return B(A1(_CU,_CS));});return new T1(1,B(_AZ(_CR,function(_CW){return E(_CV);})));},_CX=new T(function(){return B(unCStr("DC2"));}),_CY=18,_CZ=function(_D0){var _D1=new T(function(){return B(A1(_D0,_CY));});return new T1(1,B(_AZ(_CX,function(_D2){return E(_D1);})));},_D3=new T(function(){return B(unCStr("DC3"));}),_D4=19,_D5=function(_D6){var _D7=new T(function(){return B(A1(_D6,_D4));});return new T1(1,B(_AZ(_D3,function(_D8){return E(_D7);})));},_D9=new T(function(){return B(unCStr("DC4"));}),_Da=20,_Db=function(_Dc){var _Dd=new T(function(){return B(A1(_Dc,_Da));});return new T1(1,B(_AZ(_D9,function(_De){return E(_Dd);})));},_Df=new T(function(){return B(unCStr("NAK"));}),_Dg=21,_Dh=function(_Di){var _Dj=new T(function(){return B(A1(_Di,_Dg));});return new T1(1,B(_AZ(_Df,function(_Dk){return E(_Dj);})));},_Dl=new T(function(){return B(unCStr("SYN"));}),_Dm=22,_Dn=function(_Do){var _Dp=new T(function(){return B(A1(_Do,_Dm));});return new T1(1,B(_AZ(_Dl,function(_Dq){return E(_Dp);})));},_Dr=new T(function(){return B(unCStr("ETB"));}),_Ds=23,_Dt=function(_Du){var _Dv=new T(function(){return B(A1(_Du,_Ds));});return new T1(1,B(_AZ(_Dr,function(_Dw){return E(_Dv);})));},_Dx=new T(function(){return B(unCStr("CAN"));}),_Dy=24,_Dz=function(_DA){var _DB=new T(function(){return B(A1(_DA,_Dy));});return new T1(1,B(_AZ(_Dx,function(_DC){return E(_DB);})));},_DD=new T(function(){return B(unCStr("EM"));}),_DE=25,_DF=function(_DG){var _DH=new T(function(){return B(A1(_DG,_DE));});return new T1(1,B(_AZ(_DD,function(_DI){return E(_DH);})));},_DJ=new T(function(){return B(unCStr("SUB"));}),_DK=26,_DL=function(_DM){var _DN=new T(function(){return B(A1(_DM,_DK));});return new T1(1,B(_AZ(_DJ,function(_DO){return E(_DN);})));},_DP=new T(function(){return B(unCStr("ESC"));}),_DQ=27,_DR=function(_DS){var _DT=new T(function(){return B(A1(_DS,_DQ));});return new T1(1,B(_AZ(_DP,function(_DU){return E(_DT);})));},_DV=new T(function(){return B(unCStr("FS"));}),_DW=28,_DX=function(_DY){var _DZ=new T(function(){return B(A1(_DY,_DW));});return new T1(1,B(_AZ(_DV,function(_E0){return E(_DZ);})));},_E1=new T(function(){return B(unCStr("GS"));}),_E2=29,_E3=function(_E4){var _E5=new T(function(){return B(A1(_E4,_E2));});return new T1(1,B(_AZ(_E1,function(_E6){return E(_E5);})));},_E7=new T(function(){return B(unCStr("RS"));}),_E8=30,_E9=function(_Ea){var _Eb=new T(function(){return B(A1(_Ea,_E8));});return new T1(1,B(_AZ(_E7,function(_Ec){return E(_Eb);})));},_Ed=new T(function(){return B(unCStr("US"));}),_Ee=31,_Ef=function(_Eg){var _Eh=new T(function(){return B(A1(_Eg,_Ee));});return new T1(1,B(_AZ(_Ed,function(_Ei){return E(_Eh);})));},_Ej=new T(function(){return B(unCStr("SP"));}),_Ek=32,_El=function(_Em){var _En=new T(function(){return B(A1(_Em,_Ek));});return new T1(1,B(_AZ(_Ej,function(_Eo){return E(_En);})));},_Ep=new T(function(){return B(unCStr("DEL"));}),_Eq=127,_Er=function(_Es){var _Et=new T(function(){return B(A1(_Es,_Eq));});return new T1(1,B(_AZ(_Ep,function(_Eu){return E(_Et);})));},_Ev=new T2(1,_Er,_Z),_Ew=new T2(1,_El,_Ev),_Ex=new T2(1,_Ef,_Ew),_Ey=new T2(1,_E9,_Ex),_Ez=new T2(1,_E3,_Ey),_EA=new T2(1,_DX,_Ez),_EB=new T2(1,_DR,_EA),_EC=new T2(1,_DL,_EB),_ED=new T2(1,_DF,_EC),_EE=new T2(1,_Dz,_ED),_EF=new T2(1,_Dt,_EE),_EG=new T2(1,_Dn,_EF),_EH=new T2(1,_Dh,_EG),_EI=new T2(1,_Db,_EH),_EJ=new T2(1,_D5,_EI),_EK=new T2(1,_CZ,_EJ),_EL=new T2(1,_CT,_EK),_EM=new T2(1,_CN,_EL),_EN=new T2(1,_CH,_EM),_EO=new T2(1,_CB,_EN),_EP=new T2(1,_Cv,_EO),_EQ=new T2(1,_Cp,_EP),_ER=new T2(1,_Cj,_EQ),_ES=new T2(1,_Cd,_ER),_ET=new T2(1,_C7,_ES),_EU=new T2(1,_C1,_ET),_EV=new T2(1,_BV,_EU),_EW=new T2(1,_BP,_EV),_EX=new T2(1,_BJ,_EW),_EY=new T2(1,_BD,_EX),_EZ=new T2(1,_Bx,_EY),_F0=new T2(1,_Br,_EZ),_F1=new T2(1,_Bn,_F0),_F2=new T(function(){return B(_AR(_F1));}),_F3=34,_F4=new T1(0,1114111),_F5=92,_F6=39,_F7=function(_F8){var _F9=new T(function(){return B(A1(_F8,_C0));}),_Fa=new T(function(){return B(A1(_F8,_C6));}),_Fb=new T(function(){return B(A1(_F8,_Cc));}),_Fc=new T(function(){return B(A1(_F8,_Ci));}),_Fd=new T(function(){return B(A1(_F8,_Co));}),_Fe=new T(function(){return B(A1(_F8,_Cu));}),_Ff=new T(function(){return B(A1(_F8,_CA));}),_Fg=new T(function(){return B(A1(_F8,_F5));}),_Fh=new T(function(){return B(A1(_F8,_F6));}),_Fi=new T(function(){return B(A1(_F8,_F3));}),_Fj=new T(function(){var _Fk=function(_Fl){var _Fm=new T(function(){return B(_eW(E(_Fl)));}),_Fn=function(_Fo){var _Fp=B(_A0(_Fm,_Fo));if(!B(_iE(_Fp,_F4))){return new T0(2);}else{return new F(function(){return A1(_F8,new T(function(){var _Fq=B(_ff(_Fp));if(_Fq>>>0>1114111){return B(_AN(_Fq));}else{return _Fq;}}));});}};return new T1(1,B(_yw(_Fl,_Fn)));},_Fr=new T(function(){var _Fs=new T(function(){return B(A1(_F8,_Ee));}),_Ft=new T(function(){return B(A1(_F8,_E8));}),_Fu=new T(function(){return B(A1(_F8,_E2));}),_Fv=new T(function(){return B(A1(_F8,_DW));}),_Fw=new T(function(){return B(A1(_F8,_DQ));}),_Fx=new T(function(){return B(A1(_F8,_DK));}),_Fy=new T(function(){return B(A1(_F8,_DE));}),_Fz=new T(function(){return B(A1(_F8,_Dy));}),_FA=new T(function(){return B(A1(_F8,_Ds));}),_FB=new T(function(){return B(A1(_F8,_Dm));}),_FC=new T(function(){return B(A1(_F8,_Dg));}),_FD=new T(function(){return B(A1(_F8,_Da));}),_FE=new T(function(){return B(A1(_F8,_D4));}),_FF=new T(function(){return B(A1(_F8,_CY));}),_FG=new T(function(){return B(A1(_F8,_CS));}),_FH=new T(function(){return B(A1(_F8,_CM));}),_FI=new T(function(){return B(A1(_F8,_CG));}),_FJ=new T(function(){return B(A1(_F8,_Bc));}),_FK=new T(function(){return B(A1(_F8,_BU));}),_FL=new T(function(){return B(A1(_F8,_BO));}),_FM=new T(function(){return B(A1(_F8,_BI));}),_FN=new T(function(){return B(A1(_F8,_BC));}),_FO=new T(function(){return B(A1(_F8,_Bw));}),_FP=new T(function(){return B(A1(_F8,_Bi));}),_FQ=new T(function(){return B(A1(_F8,_Bq));}),_FR=function(_FS){switch(E(_FS)){case 64:return E(_FQ);case 65:return E(_FP);case 66:return E(_FO);case 67:return E(_FN);case 68:return E(_FM);case 69:return E(_FL);case 70:return E(_FK);case 71:return E(_F9);case 72:return E(_Fa);case 73:return E(_Fb);case 74:return E(_Fc);case 75:return E(_Fd);case 76:return E(_Fe);case 77:return E(_Ff);case 78:return E(_FJ);case 79:return E(_FI);case 80:return E(_FH);case 81:return E(_FG);case 82:return E(_FF);case 83:return E(_FE);case 84:return E(_FD);case 85:return E(_FC);case 86:return E(_FB);case 87:return E(_FA);case 88:return E(_Fz);case 89:return E(_Fy);case 90:return E(_Fx);case 91:return E(_Fw);case 92:return E(_Fv);case 93:return E(_Fu);case 94:return E(_Ft);case 95:return E(_Fs);default:return new T0(2);}};return B(_wR(new T1(0,function(_FT){return (E(_FT)==94)?E(new T1(0,_FR)):new T0(2);}),new T(function(){return B(A1(_F2,_F8));})));});return B(_wR(new T1(1,B(_xP(_AJ,_AL,_Fk))),_Fr));});return new F(function(){return _wR(new T1(0,function(_FU){switch(E(_FU)){case 34:return E(_Fi);case 39:return E(_Fh);case 92:return E(_Fg);case 97:return E(_F9);case 98:return E(_Fa);case 102:return E(_Fe);case 110:return E(_Fc);case 114:return E(_Ff);case 116:return E(_Fb);case 118:return E(_Fd);default:return new T0(2);}}),_Fj);});},_FV=function(_FW){return new F(function(){return A1(_FW,_kJ);});},_FX=function(_FY){var _FZ=E(_FY);if(!_FZ._){return E(_FV);}else{var _G0=E(_FZ.a),_G1=_G0>>>0,_G2=new T(function(){return B(_FX(_FZ.b));});if(_G1>887){var _G3=u_iswspace(_G0);if(!E(_G3)){return E(_FV);}else{var _G4=function(_G5){var _G6=new T(function(){return B(A1(_G2,_G5));});return new T1(0,function(_G7){return E(_G6);});};return E(_G4);}}else{var _G8=E(_G1);if(_G8==32){var _G9=function(_Ga){var _Gb=new T(function(){return B(A1(_G2,_Ga));});return new T1(0,function(_Gc){return E(_Gb);});};return E(_G9);}else{if(_G8-9>>>0>4){if(E(_G8)==160){var _Gd=function(_Ge){var _Gf=new T(function(){return B(A1(_G2,_Ge));});return new T1(0,function(_Gg){return E(_Gf);});};return E(_Gd);}else{return E(_FV);}}else{var _Gh=function(_Gi){var _Gj=new T(function(){return B(A1(_G2,_Gi));});return new T1(0,function(_Gk){return E(_Gj);});};return E(_Gh);}}}}},_Gl=function(_Gm){var _Gn=new T(function(){return B(_Gl(_Gm));}),_Go=function(_Gp){return (E(_Gp)==92)?E(_Gn):new T0(2);},_Gq=function(_Gr){return E(new T1(0,_Go));},_Gs=new T1(1,function(_Gt){return new F(function(){return A2(_FX,_Gt,_Gq);});}),_Gu=new T(function(){return B(_F7(function(_Gv){return new F(function(){return A1(_Gm,new T2(0,_Gv,_AD));});}));}),_Gw=function(_Gx){var _Gy=E(_Gx);if(_Gy==38){return E(_Gn);}else{var _Gz=_Gy>>>0;if(_Gz>887){var _GA=u_iswspace(_Gy);return (E(_GA)==0)?new T0(2):E(_Gs);}else{var _GB=E(_Gz);return (_GB==32)?E(_Gs):(_GB-9>>>0>4)?(E(_GB)==160)?E(_Gs):new T0(2):E(_Gs);}}};return new F(function(){return _wR(new T1(0,function(_GC){return (E(_GC)==92)?E(new T1(0,_Gw)):new T0(2);}),new T1(0,function(_GD){var _GE=E(_GD);if(E(_GE)==92){return E(_Gu);}else{return new F(function(){return A1(_Gm,new T2(0,_GE,_AC));});}}));});},_GF=function(_GG,_GH){var _GI=new T(function(){return B(A1(_GH,new T1(1,new T(function(){return B(A1(_GG,_Z));}))));}),_GJ=function(_GK){var _GL=E(_GK),_GM=E(_GL.a);if(E(_GM)==34){if(!E(_GL.b)){return E(_GI);}else{return new F(function(){return _GF(function(_GN){return new F(function(){return A1(_GG,new T2(1,_GM,_GN));});},_GH);});}}else{return new F(function(){return _GF(function(_GO){return new F(function(){return A1(_GG,new T2(1,_GM,_GO));});},_GH);});}};return new F(function(){return _Gl(_GJ);});},_GP=new T(function(){return B(unCStr("_\'"));}),_GQ=function(_GR){var _GS=u_iswalnum(_GR);if(!E(_GS)){return new F(function(){return _4H(_lc,_GR,_GP);});}else{return true;}},_GT=function(_GU){return new F(function(){return _GQ(E(_GU));});},_GV=new T(function(){return B(unCStr(",;()[]{}`"));}),_GW=new T(function(){return B(unCStr("=>"));}),_GX=new T2(1,_GW,_Z),_GY=new T(function(){return B(unCStr("~"));}),_GZ=new T2(1,_GY,_GX),_H0=new T(function(){return B(unCStr("@"));}),_H1=new T2(1,_H0,_GZ),_H2=new T(function(){return B(unCStr("->"));}),_H3=new T2(1,_H2,_H1),_H4=new T(function(){return B(unCStr("<-"));}),_H5=new T2(1,_H4,_H3),_H6=new T(function(){return B(unCStr("|"));}),_H7=new T2(1,_H6,_H5),_H8=new T(function(){return B(unCStr("\\"));}),_H9=new T2(1,_H8,_H7),_Ha=new T(function(){return B(unCStr("="));}),_Hb=new T2(1,_Ha,_H9),_Hc=new T(function(){return B(unCStr("::"));}),_Hd=new T2(1,_Hc,_Hb),_He=new T(function(){return B(unCStr(".."));}),_Hf=new T2(1,_He,_Hd),_Hg=function(_Hh){var _Hi=new T(function(){return B(A1(_Hh,_yt));}),_Hj=new T(function(){var _Hk=new T(function(){var _Hl=function(_Hm){var _Hn=new T(function(){return B(A1(_Hh,new T1(0,_Hm)));});return new T1(0,function(_Ho){return (E(_Ho)==39)?E(_Hn):new T0(2);});};return B(_F7(_Hl));}),_Hp=function(_Hq){var _Hr=E(_Hq);switch(E(_Hr)){case 39:return new T0(2);case 92:return E(_Hk);default:var _Hs=new T(function(){return B(A1(_Hh,new T1(0,_Hr)));});return new T1(0,function(_Ht){return (E(_Ht)==39)?E(_Hs):new T0(2);});}},_Hu=new T(function(){var _Hv=new T(function(){return B(_GF(_61,_Hh));}),_Hw=new T(function(){var _Hx=new T(function(){var _Hy=new T(function(){var _Hz=function(_HA){var _HB=E(_HA),_HC=u_iswalpha(_HB);return (E(_HC)==0)?(E(_HB)==95)?new T1(1,B(_yf(_GT,function(_HD){return new F(function(){return A1(_Hh,new T1(3,new T2(1,_HB,_HD)));});}))):new T0(2):new T1(1,B(_yf(_GT,function(_HE){return new F(function(){return A1(_Hh,new T1(3,new T2(1,_HB,_HE)));});})));};return B(_wR(new T1(0,_Hz),new T(function(){return new T1(1,B(_xP(_zr,_Ax,_Hh)));})));}),_HF=function(_HG){return (!B(_4H(_lc,_HG,_Az)))?new T0(2):new T1(1,B(_yf(_AA,function(_HH){var _HI=new T2(1,_HG,_HH);if(!B(_4H(_uj,_HI,_Hf))){return new F(function(){return A1(_Hh,new T1(4,_HI));});}else{return new F(function(){return A1(_Hh,new T1(2,_HI));});}})));};return B(_wR(new T1(0,_HF),_Hy));});return B(_wR(new T1(0,function(_HJ){if(!B(_4H(_lc,_HJ,_GV))){return new T0(2);}else{return new F(function(){return A1(_Hh,new T1(2,new T2(1,_HJ,_Z)));});}}),_Hx));});return B(_wR(new T1(0,function(_HK){return (E(_HK)==34)?E(_Hv):new T0(2);}),_Hw));});return B(_wR(new T1(0,function(_HL){return (E(_HL)==39)?E(new T1(0,_Hp)):new T0(2);}),_Hu));});return new F(function(){return _wR(new T1(1,function(_HM){return (E(_HM)._==0)?E(_Hi):new T0(2);}),_Hj);});},_HN=0,_HO=function(_HP,_HQ){var _HR=new T(function(){var _HS=new T(function(){var _HT=function(_HU){var _HV=new T(function(){var _HW=new T(function(){return B(A1(_HQ,_HU));});return B(_Hg(function(_HX){var _HY=E(_HX);return (_HY._==2)?(!B(_uV(_HY.a,_xu)))?new T0(2):E(_HW):new T0(2);}));}),_HZ=function(_I0){return E(_HV);};return new T1(1,function(_I1){return new F(function(){return A2(_FX,_I1,_HZ);});});};return B(A2(_HP,_HN,_HT));});return B(_Hg(function(_I2){var _I3=E(_I2);return (_I3._==2)?(!B(_uV(_I3.a,_xt)))?new T0(2):E(_HS):new T0(2);}));}),_I4=function(_I5){return E(_HR);};return function(_I6){return new F(function(){return A2(_FX,_I6,_I4);});};},_I7=function(_I8,_I9){var _Ia=function(_Ib){var _Ic=new T(function(){return B(A1(_I8,_Ib));}),_Id=function(_Ie){return new F(function(){return _wR(B(A1(_Ic,_Ie)),new T(function(){return new T1(1,B(_HO(_Ia,_Ie)));}));});};return E(_Id);},_If=new T(function(){return B(A1(_I8,_I9));}),_Ig=function(_Ih){return new F(function(){return _wR(B(A1(_If,_Ih)),new T(function(){return new T1(1,B(_HO(_Ia,_Ih)));}));});};return E(_Ig);},_Ii=0,_Ij=function(_Ik,_Il){return new F(function(){return A1(_Il,_Ii);});},_Im=new T(function(){return B(unCStr("Fr"));}),_In=new T2(0,_Im,_Ij),_Io=1,_Ip=function(_Iq,_Ir){return new F(function(){return A1(_Ir,_Io);});},_Is=new T(function(){return B(unCStr("Bl"));}),_It=new T2(0,_Is,_Ip),_Iu=2,_Iv=function(_Iw,_Ix){return new F(function(){return A1(_Ix,_Iu);});},_Iy=new T(function(){return B(unCStr("Ex"));}),_Iz=new T2(0,_Iy,_Iv),_IA=3,_IB=function(_IC,_ID){return new F(function(){return A1(_ID,_IA);});},_IE=new T(function(){return B(unCStr("Mv"));}),_IF=new T2(0,_IE,_IB),_IG=4,_IH=function(_II,_IJ){return new F(function(){return A1(_IJ,_IG);});},_IK=new T(function(){return B(unCStr("Pn"));}),_IL=new T2(0,_IK,_IH),_IM=8,_IN=function(_IO,_IP){return new F(function(){return A1(_IP,_IM);});},_IQ=new T(function(){return B(unCStr("DF"));}),_IR=new T2(0,_IQ,_IN),_IS=new T2(1,_IR,_Z),_IT=7,_IU=function(_IV,_IW){return new F(function(){return A1(_IW,_IT);});},_IX=new T(function(){return B(unCStr("DB"));}),_IY=new T2(0,_IX,_IU),_IZ=new T2(1,_IY,_IS),_J0=6,_J1=function(_J2,_J3){return new F(function(){return A1(_J3,_J0);});},_J4=new T(function(){return B(unCStr("Cm"));}),_J5=new T2(0,_J4,_J1),_J6=new T2(1,_J5,_IZ),_J7=5,_J8=function(_J9,_Ja){return new F(function(){return A1(_Ja,_J7);});},_Jb=new T(function(){return B(unCStr("Wn"));}),_Jc=new T2(0,_Jb,_J8),_Jd=new T2(1,_Jc,_J6),_Je=new T2(1,_IL,_Jd),_Jf=new T2(1,_IF,_Je),_Jg=new T2(1,_Iz,_Jf),_Jh=new T2(1,_It,_Jg),_Ji=new T2(1,_In,_Jh),_Jj=function(_Jk,_Jl,_Jm){var _Jn=E(_Jk);if(!_Jn._){return new T0(2);}else{var _Jo=E(_Jn.a),_Jp=_Jo.a,_Jq=new T(function(){return B(A2(_Jo.b,_Jl,_Jm));}),_Jr=new T(function(){return B(_Hg(function(_Js){var _Jt=E(_Js);switch(_Jt._){case 3:return (!B(_uV(_Jp,_Jt.a)))?new T0(2):E(_Jq);case 4:return (!B(_uV(_Jp,_Jt.a)))?new T0(2):E(_Jq);default:return new T0(2);}}));}),_Ju=function(_Jv){return E(_Jr);};return new F(function(){return _wR(new T1(1,function(_Jw){return new F(function(){return A2(_FX,_Jw,_Ju);});}),new T(function(){return B(_Jj(_Jn.b,_Jl,_Jm));}));});}},_Jx=function(_Jy,_Jz){return new F(function(){return _Jj(_Ji,_Jy,_Jz);});},_JA=function(_JB){var _JC=function(_JD){return E(new T2(3,_JB,_xG));};return new T1(1,function(_JE){return new F(function(){return A2(_FX,_JE,_JC);});});},_JF=new T(function(){return B(A3(_I7,_Jx,_HN,_JA));}),_JG=new T(function(){return B(err(_wy));}),_JH=new T(function(){return B(err(_wC));}),_JI=function(_JJ,_JK){var _JL=function(_JM,_JN){var _JO=function(_JP){return new F(function(){return A1(_JN,new T(function(){return  -E(_JP);}));});},_JQ=new T(function(){return B(_Hg(function(_JR){return new F(function(){return A3(_JJ,_JR,_JM,_JO);});}));}),_JS=function(_JT){return E(_JQ);},_JU=function(_JV){return new F(function(){return A2(_FX,_JV,_JS);});},_JW=new T(function(){return B(_Hg(function(_JX){var _JY=E(_JX);if(_JY._==4){var _JZ=E(_JY.a);if(!_JZ._){return new F(function(){return A3(_JJ,_JY,_JM,_JN);});}else{if(E(_JZ.a)==45){if(!E(_JZ.b)._){return E(new T1(1,_JU));}else{return new F(function(){return A3(_JJ,_JY,_JM,_JN);});}}else{return new F(function(){return A3(_JJ,_JY,_JM,_JN);});}}}else{return new F(function(){return A3(_JJ,_JY,_JM,_JN);});}}));}),_K0=function(_K1){return E(_JW);};return new T1(1,function(_K2){return new F(function(){return A2(_FX,_K2,_K0);});});};return new F(function(){return _I7(_JL,_JK);});},_K3=function(_K4){var _K5=E(_K4);if(!_K5._){var _K6=_K5.b,_K7=new T(function(){return B(_zJ(new T(function(){return B(_eW(E(_K5.a)));}),new T(function(){return B(_qy(_K6,0));},1),B(_aj(_zz,_K6))));});return new T1(1,_K7);}else{return (E(_K5.b)._==0)?(E(_K5.c)._==0)?new T1(1,new T(function(){return B(_A0(_zy,_K5.a));})):__Z:__Z;}},_K8=function(_K9,_Ka){return new T0(2);},_Kb=function(_Kc){var _Kd=E(_Kc);if(_Kd._==5){var _Ke=B(_K3(_Kd.a));if(!_Ke._){return E(_K8);}else{var _Kf=new T(function(){return B(_ff(_Ke.a));});return function(_Kg,_Kh){return new F(function(){return A1(_Kh,_Kf);});};}}else{return E(_K8);}},_Ki=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_Kj=new T2(1,_F,_Z),_Kk=function(_Kl){while(1){var _Km=B((function(_Kn){var _Ko=E(_Kn);if(!_Ko._){return __Z;}else{var _Kp=_Ko.b,_Kq=E(_Ko.a);if(!E(_Kq.b)._){return new T2(1,_Kq.a,new T(function(){return B(_Kk(_Kp));}));}else{_Kl=_Kp;return __continue;}}})(_Kl));if(_Km!=__continue){return _Km;}}},_Kr=function(_Ks,_Kt){while(1){var _Ku=E(_Ks);if(!_Ku._){return E(_Kt);}else{var _Kv=new T2(1,_Ku.a,_Kt);_Ks=_Ku.b;_Kt=_Kv;continue;}}},_Kw=function(_Kx,_Ky){var _Kz=E(_Kx);if(!_Kz._){return __Z;}else{var _KA=E(_Ky);return (_KA._==0)?__Z:new T2(1,new T2(0,_Kz.a,_KA.a),new T(function(){return B(_Kw(_Kz.b,_KA.b));}));}},_KB=function(_KC,_KD,_KE){while(1){var _KF=B((function(_KG,_KH,_KI){var _KJ=E(_KI);if(!_KJ._){return E(_KH);}else{var _KK=_KJ.a,_KL=_KJ.b,_KM=B(_ws(_uj,_KK,_wh));if(!_KM._){var _KN=E(_wF);}else{var _KN=E(_KM.a);}if(!B(_v0(_KN,_wF))){var _KO=B(_Kr(B(_Kw(B(_Kr(_KH,_Z)),new T(function(){return B(_Kr(_KN,_Z));},1))),_Z)),_KP=B(_qy(_KO,0)),_KQ=new T(function(){var _KR=B(_aj(_wq,_KO));if(!_KR._){return __Z;}else{var _KS=_KR.a,_KT=E(_KR.b);if(!_KT._){return __Z;}else{var _KU=_KT.a;if(!E(_KT.b)._){if(!B(_uV(_KK,_vT))){if(!B(_uV(_KK,_vS))){if(!B(_uV(_KK,_vR))){if(!B(_uV(_KK,_vV))){if(!B(_uV(_KK,_vU))){return __Z;}else{if(!B(_uV(_KS,_wA))){if(!B(_uV(_KU,_wA))){return E(_wB);}else{return E(_wA);}}else{return E(_wA);}}}else{var _KV=B(_vF(new T2(0,new T(function(){var _KW=E(_KS);if(!_KW._){return E(_rm);}else{return E(_KW.a);}}),new T(function(){var _KX=B(_Kk(B(_wH(_JF,_KU))));if(!_KX._){return E(_wz);}else{if(!E(_KX.b)._){return E(_KX.a);}else{return E(_wD);}}})),E(E(_KG).a).b)),_KY=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_KZ){return new F(function(){return _H(0,E(_KV.a),_KZ);});},new T2(1,function(_L0){return new F(function(){return _H(0,E(_KV.b),_L0);});},_Z)),_Kj));});return new T2(1,_G,_KY);}}else{return new T2(1,new T(function(){var _L1=B(_Kk(B(_wH(_Ki,_KS))));if(!_L1._){return E(_JG);}else{if(!E(_L1.b)._){var _L2=B(_Kk(B(_wH(_Ki,_KU))));if(!_L2._){return E(_JG);}else{if(!E(_L2.b)._){return E(B(_aW(B(_aW(E(E(_KG).a).b,E(_L2.a))),E(_L1.a))).a);}else{return E(_JH);}}}else{return E(_JH);}}}),_Z);}}else{if(!B(_uV(_KS,_KU))){return E(_wB);}else{return E(_wA);}}}else{if(!B(_uV(_KS,_wA))){return E(_wB);}else{if(!B(_uV(_KU,_wA))){return E(_wB);}else{return E(_wA);}}}}else{return __Z;}}}});if(_KP>0){var _L3=_KG,_L4=B(_x(B(_Kr(B(_vL(_KP,B(_Kr(_KH,_Z)))),_Z)),new T2(1,_KQ,_Z)));_KC=_L3;_KD=_L4;_KE=_KL;return __continue;}else{var _L3=_KG,_L4=B(_x(B(_Kr(B(_Kr(_KH,_Z)),_Z)),new T2(1,_KQ,_Z)));_KC=_L3;_KD=_L4;_KE=_KL;return __continue;}}else{var _L3=_KG,_L4=B(_x(_KH,new T2(1,_KK,_Z)));_KC=_L3;_KD=_L4;_KE=_KL;return __continue;}}})(_KC,_KD,_KE));if(_KF!=__continue){return _KF;}}},_L5=new T(function(){return B(_ic("Event.hs:(102,1)-(106,73)|function addMemory"));}),_L6=function(_L7,_L8){var _L9=E(_L7),_La=E(_L8);if(!B(_uV(_L9.a,_La.a))){return false;}else{return new F(function(){return _uV(_L9.b,_La.b);});}},_Lb=new T2(1,_Z,_Z),_Lc=function(_Ld,_Le,_Lf){var _Lg=E(_Lf);if(!_Lg._){return new T2(0,new T2(1,_Le,_Z),_Z);}else{var _Lh=E(_Le),_Li=new T(function(){var _Lj=B(_Lc(_Ld,_Lg.a,_Lg.b));return new T2(0,_Lj.a,_Lj.b);});return (_Ld!=_Lh)?new T2(0,new T2(1,_Lh,new T(function(){return E(E(_Li).a);})),new T(function(){return E(E(_Li).b);})):new T2(0,_Z,new T2(1,new T(function(){return E(E(_Li).a);}),new T(function(){return E(E(_Li).b);})));}},_Lk=32,_Ll=function(_Lm){var _Ln=E(_Lm);if(!_Ln._){return __Z;}else{var _Lo=new T(function(){return B(_x(_Ln.a,new T(function(){return B(_Ll(_Ln.b));},1)));});return new T2(1,_Lk,_Lo);}},_Lp=function(_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM){while(1){var _LN=B((function(_LO,_LP,_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma){var _Mb=E(_LO);if(!_Mb._){return {_:0,a:_LP,b:_LQ,c:_LR,d:_LS,e:_LT,f:_LU,g:_LV,h:_LW,i:_LX,j:_LY,k:_LZ,l:_M0,m:_M1,n:_M2,o:_M3,p:_M4,q:_M5,r:_M6,s:_M7,t:_M8,u:_M9,v:_Ma};}else{var _Mc=_Mb.a,_Md=E(_Mb.b);if(!_Md._){return E(_L5);}else{var _Me=new T(function(){var _Mf=E(_Md.a);if(!_Mf._){var _Mg=B(_KB({_:0,a:E(_LP),b:E(_LQ),c:E(_LR),d:E(_LS),e:E(_LT),f:E(_LU),g:E(_LV),h:E(_LW),i:_LX,j:_LY,k:_LZ,l:_M0,m:E(_M1),n:_M2,o:E(_M3),p:E(_M4),q:_M5,r:E(_M6),s:E(_M7),t:_M8,u:E(_M9),v:E(_Ma)},_Z,_Lb));if(!_Mg._){return __Z;}else{return B(_x(_Mg.a,new T(function(){return B(_Ll(_Mg.b));},1)));}}else{var _Mh=_Mf.a,_Mi=E(_Mf.b);if(!_Mi._){var _Mj=B(_KB({_:0,a:E(_LP),b:E(_LQ),c:E(_LR),d:E(_LS),e:E(_LT),f:E(_LU),g:E(_LV),h:E(_LW),i:_LX,j:_LY,k:_LZ,l:_M0,m:E(_M1),n:_M2,o:E(_M3),p:E(_M4),q:_M5,r:E(_M6),s:E(_M7),t:_M8,u:E(_M9),v:E(_Ma)},_Z,new T2(1,new T2(1,_Mh,_Z),_Z)));if(!_Mj._){return __Z;}else{return B(_x(_Mj.a,new T(function(){return B(_Ll(_Mj.b));},1)));}}else{var _Mk=E(_Mh),_Ml=new T(function(){var _Mm=B(_Lc(95,_Mi.a,_Mi.b));return new T2(0,_Mm.a,_Mm.b);});if(E(_Mk)==95){var _Mn=B(_KB({_:0,a:E(_LP),b:E(_LQ),c:E(_LR),d:E(_LS),e:E(_LT),f:E(_LU),g:E(_LV),h:E(_LW),i:_LX,j:_LY,k:_LZ,l:_M0,m:E(_M1),n:_M2,o:E(_M3),p:E(_M4),q:_M5,r:E(_M6),s:E(_M7),t:_M8,u:E(_M9),v:E(_Ma)},_Z,new T2(1,_Z,new T2(1,new T(function(){return E(E(_Ml).a);}),new T(function(){return E(E(_Ml).b);})))));if(!_Mn._){return __Z;}else{return B(_x(_Mn.a,new T(function(){return B(_Ll(_Mn.b));},1)));}}else{var _Mo=B(_KB({_:0,a:E(_LP),b:E(_LQ),c:E(_LR),d:E(_LS),e:E(_LT),f:E(_LU),g:E(_LV),h:E(_LW),i:_LX,j:_LY,k:_LZ,l:_M0,m:E(_M1),n:_M2,o:E(_M3),p:E(_M4),q:_M5,r:E(_M6),s:E(_M7),t:_M8,u:E(_M9),v:E(_Ma)},_Z,new T2(1,new T2(1,_Mk,new T(function(){return E(E(_Ml).a);})),new T(function(){return E(E(_Ml).b);}))));if(!_Mo._){return __Z;}else{return B(_x(_Mo.a,new T(function(){return B(_Ll(_Mo.b));},1)));}}}}}),_Mp=_LP,_Mq=_LQ,_Mr=_LR,_Ms=_LS,_Mt=_LT,_Mu=_LU,_Mv=_LW,_Mw=_LX,_Mx=_LY,_My=_LZ,_Mz=_M0,_MA=_M1,_MB=_M2,_MC=_M3,_MD=_M4,_ME=_M5,_MF=_M6,_MG=_M7,_MH=_M8,_MI=_M9,_MJ=_Ma;_Lq=_Md.b;_Lr=_Mp;_Ls=_Mq;_Lt=_Mr;_Lu=_Ms;_Lv=_Mt;_Lw=_Mu;_Lx=new T2(1,new T2(0,_Mc,_Me),new T(function(){var _MK=B(_ws(_uj,_Mc,_LV));if(!_MK._){var _ML=__Z;}else{var _ML=E(_MK.a);}if(!B(_uV(_ML,_Z))){return B(_uO(_L6,new T2(0,_Mc,_ML),_LV));}else{return E(_LV);}}));_Ly=_Mv;_Lz=_Mw;_LA=_Mx;_LB=_My;_LC=_Mz;_LD=_MA;_LE=_MB;_LF=_MC;_LG=_MD;_LH=_ME;_LI=_MF;_LJ=_MG;_LK=_MH;_LL=_MI;_LM=_MJ;return __continue;}}})(_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI,_LJ,_LK,_LL,_LM));if(_LN!=__continue){return _LN;}}},_MM=function(_MN){var _MO=E(_MN);if(!_MO._){return new T2(0,_Z,_Z);}else{var _MP=E(_MO.a),_MQ=new T(function(){var _MR=B(_MM(_MO.b));return new T2(0,_MR.a,_MR.b);});return new T2(0,new T2(1,_MP.a,new T(function(){return E(E(_MQ).a);})),new T2(1,_MP.b,new T(function(){return E(E(_MQ).b);})));}},_MS=function(_MT,_MU,_MV){while(1){var _MW=B((function(_MX,_MY,_MZ){var _N0=E(_MZ);if(!_N0._){return __Z;}else{var _N1=_N0.b;if(_MY!=E(_N0.a)){var _N2=_MX+1|0,_N3=_MY;_MT=_N2;_MU=_N3;_MV=_N1;return __continue;}else{return new T2(1,_MX,new T(function(){return B(_MS(_MX+1|0,_MY,_N1));}));}}})(_MT,_MU,_MV));if(_MW!=__continue){return _MW;}}},_N4=function(_N5,_N6,_N7){var _N8=E(_N7);if(!_N8._){return __Z;}else{var _N9=_N8.b,_Na=E(_N6);if(_Na!=E(_N8.a)){return new F(function(){return _MS(_N5+1|0,_Na,_N9);});}else{return new T2(1,_N5,new T(function(){return B(_MS(_N5+1|0,_Na,_N9));}));}}},_Nb=function(_Nc,_Nd,_Ne,_Nf){var _Ng=E(_Nf);if(!_Ng._){return __Z;}else{var _Nh=_Ng.b;return (!B(_4H(_3S,_Nc,_Ne)))?new T2(1,_Ng.a,new T(function(){return B(_Nb(_Nc+1|0,_Nd,_Ne,_Nh));})):new T2(1,_Nd,new T(function(){return B(_Nb(_Nc+1|0,_Nd,_Ne,_Nh));}));}},_Ni=function(_Nj,_Nk,_Nl){var _Nm=E(_Nl);if(!_Nm._){return __Z;}else{var _Nn=new T(function(){var _No=B(_MM(_Nm.a)),_Np=_No.a,_Nq=new T(function(){return B(_Nb(0,_Nk,new T(function(){return B(_N4(0,_Nj,_Np));}),_No.b));},1);return B(_Kw(_Np,_Nq));});return new T2(1,_Nn,new T(function(){return B(_Ni(_Nj,_Nk,_Nm.b));}));}},_Nr=function(_Ns){var _Nt=E(_Ns);return (_Nt._==0)?E(_rm):E(_Nt.a);},_Nu=new T(function(){return B(_ic("Event.hs:(75,1)-(78,93)|function changeType"));}),_Nv=new T(function(){return B(_ic("Event.hs:72:16-116|case"));}),_Nw=new T(function(){return B(unCStr("Wn"));}),_Nx=new T(function(){return B(unCStr("Pn"));}),_Ny=new T(function(){return B(unCStr("Mv"));}),_Nz=new T(function(){return B(unCStr("Fr"));}),_NA=new T(function(){return B(unCStr("Ex"));}),_NB=new T(function(){return B(unCStr("DF"));}),_NC=new T(function(){return B(unCStr("DB"));}),_ND=new T(function(){return B(unCStr("Cm"));}),_NE=new T(function(){return B(unCStr("Bl"));}),_NF=function(_NG){return (!B(_uV(_NG,_NE)))?(!B(_uV(_NG,_ND)))?(!B(_uV(_NG,_NC)))?(!B(_uV(_NG,_NB)))?(!B(_uV(_NG,_NA)))?(!B(_uV(_NG,_Nz)))?(!B(_uV(_NG,_Ny)))?(!B(_uV(_NG,_Nx)))?(!B(_uV(_NG,_Nw)))?E(_Nv):5:4:3:0:2:8:7:6:1;},_NH=function(_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4){while(1){var _O5=B((function(_O6,_O7,_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os){var _Ot=E(_O6);if(!_Ot._){return {_:0,a:_O7,b:_O8,c:_O9,d:_Oa,e:_Ob,f:_Oc,g:_Od,h:_Oe,i:_Of,j:_Og,k:_Oh,l:_Oi,m:_Oj,n:_Ok,o:_Ol,p:_Om,q:_On,r:_Oo,s:_Op,t:_Oq,u:_Or,v:_Os};}else{var _Ou=E(_Ot.b);if(!_Ou._){return E(_Nu);}else{var _Ov=E(_O7),_Ow=_O8,_Ox=_O9,_Oy=_Oa,_Oz=_Ob,_OA=_Oc,_OB=_Od,_OC=_Oe,_OD=_Of,_OE=_Og,_OF=_Oh,_OG=_Oi,_OH=_Oj,_OI=_Ok,_OJ=_Ol,_OK=_Om,_OL=_On,_OM=_Oo,_ON=_Op,_OO=_Oq,_OP=_Or,_OQ=_Os;_NI=_Ou.b;_NJ={_:0,a:E(_Ov.a),b:E(B(_Ni(new T(function(){return B(_Nr(_Ot.a));}),new T(function(){return B(_NF(_Ou.a));}),_Ov.b))),c:E(_Ov.c),d:_Ov.d,e:_Ov.e,f:_Ov.f,g:E(_Ov.g),h:_Ov.h,i:E(_Ov.i),j:E(_Ov.j),k:E(_Ov.k)};_NK=_Ow;_NL=_Ox;_NM=_Oy;_NN=_Oz;_NO=_OA;_NP=_OB;_NQ=_OC;_NR=_OD;_NS=_OE;_NT=_OF;_NU=_OG;_NV=_OH;_NW=_OI;_NX=_OJ;_NY=_OK;_NZ=_OL;_O0=_OM;_O1=_ON;_O2=_OO;_O3=_OP;_O4=_OQ;return __continue;}}})(_NI,_NJ,_NK,_NL,_NM,_NN,_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4));if(_O5!=__continue){return _O5;}}},_OR=function(_OS,_OT){while(1){var _OU=E(_OT);if(!_OU._){return __Z;}else{var _OV=_OU.b,_OW=E(_OS);if(_OW==1){return E(_OV);}else{_OS=_OW-1|0;_OT=_OV;continue;}}}},_OX=function(_OY,_OZ){while(1){var _P0=E(_OZ);if(!_P0._){return __Z;}else{var _P1=_P0.b,_P2=E(_OY);if(_P2==1){return E(_P1);}else{_OY=_P2-1|0;_OZ=_P1;continue;}}}},_P3=function(_P4,_P5,_P6,_P7,_P8){var _P9=new T(function(){var _Pa=E(_P4),_Pb=new T(function(){return B(_aW(_P8,_P5));}),_Pc=new T2(1,new T2(0,_P6,_P7),new T(function(){var _Pd=_Pa+1|0;if(_Pd>0){return B(_OX(_Pd,_Pb));}else{return E(_Pb);}}));if(0>=_Pa){return E(_Pc);}else{var _Pe=function(_Pf,_Pg){var _Ph=E(_Pf);if(!_Ph._){return E(_Pc);}else{var _Pi=_Ph.a,_Pj=E(_Pg);return (_Pj==1)?new T2(1,_Pi,_Pc):new T2(1,_Pi,new T(function(){return B(_Pe(_Ph.b,_Pj-1|0));}));}};return B(_Pe(_Pb,_Pa));}}),_Pk=new T2(1,_P9,new T(function(){var _Pl=_P5+1|0;if(_Pl>0){return B(_OR(_Pl,_P8));}else{return E(_P8);}}));if(0>=_P5){return E(_Pk);}else{var _Pm=function(_Pn,_Po){var _Pp=E(_Pn);if(!_Pp._){return E(_Pk);}else{var _Pq=_Pp.a,_Pr=E(_Po);return (_Pr==1)?new T2(1,_Pq,_Pk):new T2(1,_Pq,new T(function(){return B(_Pm(_Pp.b,_Pr-1|0));}));}};return new F(function(){return _Pm(_P8,_P5);});}},_Ps=32,_Pt=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_Pu=function(_Pv){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_Pv,_Pt));})),_hy);});},_Pw=function(_Px){return new F(function(){return _Pu("Event.hs:58:27-53|(x\' : y\' : _)");});},_Py=new T(function(){return B(_Pw(_));}),_Pz=function(_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI,_PJ,_PK,_PL,_PM,_PN,_PO,_PP,_PQ,_PR,_PS,_PT,_PU,_PV,_PW){while(1){var _PX=B((function(_PY,_PZ,_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk){var _Ql=E(_PY);if(!_Ql._){return {_:0,a:_PZ,b:_Q0,c:_Q1,d:_Q2,e:_Q3,f:_Q4,g:_Q5,h:_Q6,i:_Q7,j:_Q8,k:_Q9,l:_Qa,m:_Qb,n:_Qc,o:_Qd,p:_Qe,q:_Qf,r:_Qg,s:_Qh,t:_Qi,u:_Qj,v:_Qk};}else{var _Qm=E(_PZ),_Qn=new T(function(){var _Qo=E(_Ql.a);if(!_Qo._){return E(_Py);}else{var _Qp=E(_Qo.b);if(!_Qp._){return E(_Py);}else{var _Qq=_Qp.a,_Qr=_Qp.b,_Qs=E(_Qo.a);if(E(_Qs)==44){return new T2(0,_Z,new T(function(){return E(B(_Lc(44,_Qq,_Qr)).a);}));}else{var _Qt=B(_Lc(44,_Qq,_Qr)),_Qu=E(_Qt.b);if(!_Qu._){return E(_Py);}else{return new T2(0,new T2(1,_Qs,_Qt.a),_Qu.a);}}}}}),_Qv=B(_Kk(B(_wH(_Ki,new T(function(){return E(E(_Qn).b);})))));if(!_Qv._){return E(_JG);}else{if(!E(_Qv.b)._){var _Qw=new T(function(){var _Qx=B(_Kk(B(_wH(_Ki,new T(function(){return E(E(_Qn).a);})))));if(!_Qx._){return E(_JG);}else{if(!E(_Qx.b)._){return E(_Qx.a);}else{return E(_JH);}}},1),_Qy=_Q0,_Qz=_Q1,_QA=_Q2,_QB=_Q3,_QC=_Q4,_QD=_Q5,_QE=_Q6,_QF=_Q7,_QG=_Q8,_QH=_Q9,_QI=_Qa,_QJ=_Qb,_QK=_Qc,_QL=_Qd,_QM=_Qe,_QN=_Qf,_QO=_Qg,_QP=_Qh,_QQ=_Qi,_QR=_Qj,_QS=_Qk;_PA=_Ql.b;_PB={_:0,a:E(_Qm.a),b:E(B(_P3(_Qw,E(_Qv.a),_Ps,_Ii,_Qm.b))),c:E(_Qm.c),d:_Qm.d,e:_Qm.e,f:_Qm.f,g:E(_Qm.g),h:_Qm.h,i:E(_Qm.i),j:E(_Qm.j),k:E(_Qm.k)};_PC=_Qy;_PD=_Qz;_PE=_QA;_PF=_QB;_PG=_QC;_PH=_QD;_PI=_QE;_PJ=_QF;_PK=_QG;_PL=_QH;_PM=_QI;_PN=_QJ;_PO=_QK;_PP=_QL;_PQ=_QM;_PR=_QN;_PS=_QO;_PT=_QP;_PU=_QQ;_PV=_QR;_PW=_QS;return __continue;}else{return E(_JH);}}}})(_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI,_PJ,_PK,_PL,_PM,_PN,_PO,_PP,_PQ,_PR,_PS,_PT,_PU,_PV,_PW));if(_PX!=__continue){return _PX;}}},_QT=function(_QU,_QV,_QW){var _QX=E(_QW);return (_QX._==0)?0:(!B(A3(_4F,_QU,_QV,_QX.a)))?1+B(_QT(_QU,_QV,_QX.b))|0:0;},_QY=function(_QZ,_R0){while(1){var _R1=E(_R0);if(!_R1._){return __Z;}else{var _R2=_R1.b,_R3=E(_QZ);if(_R3==1){return E(_R2);}else{_QZ=_R3-1|0;_R0=_R2;continue;}}}},_R4=function(_R5,_R6){var _R7=new T(function(){var _R8=_R5+1|0;if(_R8>0){return B(_QY(_R8,_R6));}else{return E(_R6);}});if(0>=_R5){return E(_R7);}else{var _R9=function(_Ra,_Rb){var _Rc=E(_Ra);if(!_Rc._){return E(_R7);}else{var _Rd=_Rc.a,_Re=E(_Rb);return (_Re==1)?new T2(1,_Rd,_R7):new T2(1,_Rd,new T(function(){return B(_R9(_Rc.b,_Re-1|0));}));}};return new F(function(){return _R9(_R6,_R5);});}},_Rf=function(_Rg,_Rh){return new F(function(){return _R4(E(_Rg),_Rh);});},_Ri= -1,_Rj=function(_Rk,_Rl,_Rm,_Rn,_Ro,_Rp,_Rq,_Rr,_Rs,_Rt,_Ru,_Rv,_Rw,_Rx,_Ry,_Rz,_RA,_RB,_RC,_RD,_RE,_RF,_RG){while(1){var _RH=B((function(_RI,_RJ,_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4){var _S5=E(_RI);if(!_S5._){return {_:0,a:_RJ,b:_RK,c:_RL,d:_RM,e:_RN,f:_RO,g:_RP,h:_RQ,i:_RR,j:_RS,k:_RT,l:_RU,m:_RV,n:_RW,o:_RX,p:_RY,q:_RZ,r:_S0,s:_S1,t:_S2,u:_S3,v:_S4};}else{var _S6=_S5.a,_S7=B(_aj(_wq,_RN)),_S8=B(_4H(_uj,_S6,_S7)),_S9=new T(function(){if(!E(_S8)){return E(_Ri);}else{return B(_QT(_uj,_S6,_S7));}});if(!E(_S8)){var _Sa=E(_RN);}else{var _Sa=B(_Rf(_S9,_RN));}if(!E(_S8)){var _Sb=E(_RO);}else{var _Sb=B(_Rf(_S9,_RO));}var _Sc=_RJ,_Sd=_RK,_Se=_RL,_Sf=_RM,_Sg=_RP,_Sh=_RQ,_Si=_RR,_Sj=_RS,_Sk=_RT,_Sl=_RU,_Sm=_RV,_Sn=_RW,_So=_RX,_Sp=_RY,_Sq=_RZ,_Sr=_S0,_Ss=_S1,_St=_S2,_Su=_S3,_Sv=_S4;_Rk=_S5.b;_Rl=_Sc;_Rm=_Sd;_Rn=_Se;_Ro=_Sf;_Rp=_Sa;_Rq=_Sb;_Rr=_Sg;_Rs=_Sh;_Rt=_Si;_Ru=_Sj;_Rv=_Sk;_Rw=_Sl;_Rx=_Sm;_Ry=_Sn;_Rz=_So;_RA=_Sp;_RB=_Sq;_RC=_Sr;_RD=_Ss;_RE=_St;_RF=_Su;_RG=_Sv;return __continue;}})(_Rk,_Rl,_Rm,_Rn,_Ro,_Rp,_Rq,_Rr,_Rs,_Rt,_Ru,_Rv,_Rw,_Rx,_Ry,_Rz,_RA,_RB,_RC,_RD,_RE,_RF,_RG));if(_RH!=__continue){return _RH;}}},_Sw=function(_Sx){var _Sy=E(_Sx);if(!_Sy._){return new T2(0,_Z,_Z);}else{var _Sz=E(_Sy.a),_SA=new T(function(){var _SB=B(_Sw(_Sy.b));return new T2(0,_SB.a,_SB.b);});return new T2(0,new T2(1,_Sz.a,new T(function(){return E(E(_SA).a);})),new T2(1,_Sz.b,new T(function(){return E(E(_SA).b);})));}},_SC=function(_SD,_SE){while(1){var _SF=E(_SD);if(!_SF._){return E(_SE);}else{var _SG=_SE+E(_SF.a)|0;_SD=_SF.b;_SE=_SG;continue;}}},_SH=function(_SI,_SJ){while(1){var _SK=E(_SJ);if(!_SK._){return __Z;}else{var _SL=_SK.b,_SM=E(_SI);if(_SM==1){return E(_SL);}else{_SI=_SM-1|0;_SJ=_SL;continue;}}}},_SN=function(_SO,_SP,_SQ,_SR,_SS,_ST,_SU,_SV,_SW,_SX,_SY,_SZ,_T0,_T1,_T2,_T3,_T4,_T5,_T6,_T7,_T8,_T9,_Ta){while(1){var _Tb=B((function(_Tc,_Td,_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty){var _Tz=E(_Tc);if(!_Tz._){return {_:0,a:_Td,b:_Te,c:_Tf,d:_Tg,e:_Th,f:_Ti,g:_Tj,h:_Tk,i:_Tl,j:_Tm,k:_Tn,l:_To,m:_Tp,n:_Tq,o:_Tr,p:_Ts,q:_Tt,r:_Tu,s:_Tv,t:_Tw,u:_Tx,v:_Ty};}else{var _TA=new T(function(){var _TB=B(_Kk(B(_wH(_Ki,_Tz.a))));if(!_TB._){return E(_JG);}else{if(!E(_TB.b)._){return B(_x(B(_H(0,B(_aW(_Tu,E(_TB.a))),_Z)),new T(function(){if(_Tl>0){return B(_SH(_Tl,_Tf));}else{return E(_Tf);}},1)));}else{return E(_JH);}}});if(0>=_Tl){var _TC=E(_TA);}else{var _TD=function(_TE,_TF){var _TG=E(_TE);if(!_TG._){return E(_TA);}else{var _TH=_TG.a,_TI=E(_TF);return (_TI==1)?new T2(1,_TH,_TA):new T2(1,_TH,new T(function(){return B(_TD(_TG.b,_TI-1|0));}));}},_TC=B(_TD(_Tf,_Tl));}var _TJ=_Td,_TK=_Te,_TL=_Tg,_TM=_Th,_TN=_Ti,_TO=_Tj,_TP=_Tk,_TQ=_Tl,_TR=_Tm,_TS=_Tn,_TT=_To,_TU=_Tp,_TV=_Tq,_TW=_Tr,_TX=_Ts,_TY=_Tt,_TZ=_Tu,_U0=_Tv,_U1=_Tw,_U2=_Tx,_U3=_Ty;_SO=_Tz.b;_SP=_TJ;_SQ=_TK;_SR=_TC;_SS=_TL;_ST=_TM;_SU=_TN;_SV=_TO;_SW=_TP;_SX=_TQ;_SY=_TR;_SZ=_TS;_T0=_TT;_T1=_TU;_T2=_TV;_T3=_TW;_T4=_TX;_T5=_TY;_T6=_TZ;_T7=_U0;_T8=_U1;_T9=_U2;_Ta=_U3;return __continue;}})(_SO,_SP,_SQ,_SR,_SS,_ST,_SU,_SV,_SW,_SX,_SY,_SZ,_T0,_T1,_T2,_T3,_T4,_T5,_T6,_T7,_T8,_T9,_Ta));if(_Tb!=__continue){return _Tb;}}},_U4=function(_U5){return new F(function(){return _Pu("Event.hs:119:28-52|(c : d : _)");});},_U6=new T(function(){return B(_U4(_));}),_U7=function(_U8,_U9,_Ua,_Ub,_Uc,_Ud,_Ue,_Uf,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB){while(1){var _UC=B((function(_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1,_V2,_V3,_V4,_V5,_V6){var _V7=E(_UD);if(!_V7._){return {_:0,a:E(_UE),b:E(_UF),c:E(_UG),d:E(_UH),e:E(_UI),f:E(_UJ),g:E(_UK),h:E(_UL),i:_UM,j:_UN,k:_UO,l:_UP,m:E(_UQ),n:_UR,o:E(_US),p:E(_UT),q:_UU,r:E(_UV),s:E(_UW),t:_UX,u:E({_:0,a:E(_UY),b:E(_UZ),c:E(_V0),d:E(_AD),e:E(_V2),f:E(_V3),g:E(_AD),h:E(_V5)}),v:E(_V6)};}else{var _V8=new T(function(){var _V9=E(_V7.a);if(!_V9._){return E(_U6);}else{var _Va=E(_V9.b);if(!_Va._){return E(_U6);}else{var _Vb=_Va.a,_Vc=_Va.b,_Vd=E(_V9.a);if(E(_Vd)==44){return new T2(0,_Z,new T(function(){return E(B(_Lc(44,_Vb,_Vc)).a);}));}else{var _Ve=B(_Lc(44,_Vb,_Vc)),_Vf=E(_Ve.b);if(!_Vf._){return E(_U6);}else{return new T2(0,new T2(1,_Vd,_Ve.a),_Vf.a);}}}}}),_Vg=_UE,_Vh=_UF,_Vi=_UG,_Vj=_UH,_Vk=_UI,_Vl=_UJ,_Vm=_UK,_Vn=_UL,_Vo=_UM,_Vp=_UN,_Vq=_UO,_Vr=_UP,_Vs=B(_x(_UQ,new T2(1,new T2(0,new T(function(){return E(E(_V8).a);}),new T(function(){return E(E(_V8).b);})),_Z))),_Vt=_UR,_Vu=_US,_Vv=_UT,_Vw=_UU,_Vx=_UV,_Vy=_UW,_Vz=_UX,_VA=_UY,_VB=_UZ,_VC=_V0,_VD=_V1,_VE=_V2,_VF=_V3,_VG=_V4,_VH=_V5,_VI=_V6;_U8=_V7.b;_U9=_Vg;_Ua=_Vh;_Ub=_Vi;_Uc=_Vj;_Ud=_Vk;_Ue=_Vl;_Uf=_Vm;_Ug=_Vn;_Uh=_Vo;_Ui=_Vp;_Uj=_Vq;_Uk=_Vr;_Ul=_Vs;_Um=_Vt;_Un=_Vu;_Uo=_Vv;_Up=_Vw;_Uq=_Vx;_Ur=_Vy;_Us=_Vz;_Ut=_VA;_Uu=_VB;_Uv=_VC;_Uw=_VD;_Ux=_VE;_Uy=_VF;_Uz=_VG;_UA=_VH;_UB=_VI;return __continue;}})(_U8,_U9,_Ua,_Ub,_Uc,_Ud,_Ue,_Uf,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA,_UB));if(_UC!=__continue){return _UC;}}},_VJ=function(_VK){return new F(function(){return _Pu("Event.hs:65:27-53|(x\' : y\' : _)");});},_VL=new T(function(){return B(_VJ(_));}),_VM=function(_VN){return new F(function(){return _Pu("Event.hs:66:27-55|(chs : tps : _)");});},_VO=new T(function(){return B(_VM(_));}),_VP=new T(function(){return B(_ic("Event.hs:(63,1)-(69,83)|function putCell"));}),_VQ=function(_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd){while(1){var _We=B((function(_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB){var _WC=E(_Wf);if(!_WC._){return {_:0,a:_Wg,b:_Wh,c:_Wi,d:_Wj,e:_Wk,f:_Wl,g:_Wm,h:_Wn,i:_Wo,j:_Wp,k:_Wq,l:_Wr,m:_Ws,n:_Wt,o:_Wu,p:_Wv,q:_Ww,r:_Wx,s:_Wy,t:_Wz,u:_WA,v:_WB};}else{var _WD=E(_WC.b);if(!_WD._){return E(_VP);}else{var _WE=E(_Wg),_WF=new T(function(){var _WG=E(_WC.a);if(!_WG._){return E(_VL);}else{var _WH=E(_WG.b);if(!_WH._){return E(_VL);}else{var _WI=_WH.a,_WJ=_WH.b,_WK=E(_WG.a);if(E(_WK)==44){return new T2(0,_Z,new T(function(){return E(B(_Lc(44,_WI,_WJ)).a);}));}else{var _WL=B(_Lc(44,_WI,_WJ)),_WM=E(_WL.b);if(!_WM._){return E(_VL);}else{return new T2(0,new T2(1,_WK,_WL.a),_WM.a);}}}}}),_WN=B(_Kk(B(_wH(_Ki,new T(function(){return E(E(_WF).b);})))));if(!_WN._){return E(_JG);}else{if(!E(_WN.b)._){var _WO=new T(function(){var _WP=E(_WD.a);if(!_WP._){return E(_VO);}else{var _WQ=E(_WP.b);if(!_WQ._){return E(_VO);}else{var _WR=_WQ.a,_WS=_WQ.b,_WT=E(_WP.a);if(E(_WT)==44){return new T2(0,_Z,new T(function(){return E(B(_Lc(44,_WR,_WS)).a);}));}else{var _WU=B(_Lc(44,_WR,_WS)),_WV=E(_WU.b);if(!_WV._){return E(_VO);}else{return new T2(0,new T2(1,_WT,_WU.a),_WV.a);}}}}}),_WW=new T(function(){var _WX=B(_Kk(B(_wH(_Ki,new T(function(){return E(E(_WF).a);})))));if(!_WX._){return E(_JG);}else{if(!E(_WX.b)._){return E(_WX.a);}else{return E(_JH);}}},1),_WY=_Wh,_WZ=_Wi,_X0=_Wj,_X1=_Wk,_X2=_Wl,_X3=_Wm,_X4=_Wn,_X5=_Wo,_X6=_Wp,_X7=_Wq,_X8=_Wr,_X9=_Ws,_Xa=_Wt,_Xb=_Wu,_Xc=_Wv,_Xd=_Ww,_Xe=_Wx,_Xf=_Wy,_Xg=_Wz,_Xh=_WA,_Xi=_WB;_VR=_WD.b;_VS={_:0,a:E(_WE.a),b:E(B(_P3(_WW,E(_WN.a),new T(function(){return B(_Nr(E(_WO).a));}),new T(function(){return B(_NF(E(_WO).b));}),_WE.b))),c:E(_WE.c),d:_WE.d,e:_WE.e,f:_WE.f,g:E(_WE.g),h:_WE.h,i:E(_WE.i),j:E(_WE.j),k:E(_WE.k)};_VT=_WY;_VU=_WZ;_VV=_X0;_VW=_X1;_VX=_X2;_VY=_X3;_VZ=_X4;_W0=_X5;_W1=_X6;_W2=_X7;_W3=_X8;_W4=_X9;_W5=_Xa;_W6=_Xb;_W7=_Xc;_W8=_Xd;_W9=_Xe;_Wa=_Xf;_Wb=_Xg;_Wc=_Xh;_Wd=_Xi;return __continue;}else{return E(_JH);}}}}})(_VR,_VS,_VT,_VU,_VV,_VW,_VX,_VY,_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6,_W7,_W8,_W9,_Wa,_Wb,_Wc,_Wd));if(_We!=__continue){return _We;}}},_Xj=function(_Xk,_Xl){while(1){var _Xm=E(_Xl);if(!_Xm._){return __Z;}else{var _Xn=_Xm.b,_Xo=E(_Xk);if(_Xo==1){return E(_Xn);}else{_Xk=_Xo-1|0;_Xl=_Xn;continue;}}}},_Xp=function(_Xq){var _Xr=E(_Xq);if(!_Xr._){return new T2(0,_Z,_Z);}else{var _Xs=E(_Xr.a),_Xt=new T(function(){var _Xu=B(_Xp(_Xr.b));return new T2(0,_Xu.a,_Xu.b);});return new T2(0,new T2(1,_Xs.a,new T(function(){return E(E(_Xt).a);})),new T2(1,_Xs.b,new T(function(){return E(E(_Xt).b);})));}},_Xv=32,_Xw=function(_Xx,_Xy,_Xz,_XA){var _XB=E(_XA);if(!_XB._){return __Z;}else{var _XC=_XB.b;if(!B(_4H(_3S,_Xx,_Xz))){var _XD=new T(function(){return B(_Xw(new T(function(){return E(_Xx)+1|0;}),_Xy,_Xz,_XC));});return new T2(1,_XB.a,_XD);}else{var _XE=new T(function(){return B(_Xw(new T(function(){return E(_Xx)+1|0;}),_Xy,_Xz,_XC));});return new T2(1,_Xy,_XE);}}},_XF=function(_XG,_XH){var _XI=E(_XH);if(!_XI._){return __Z;}else{var _XJ=new T(function(){var _XK=B(_Xp(_XI.a)),_XL=_XK.a,_XM=new T(function(){return B(_N4(0,_XG,_XL));});return B(_Kw(B(_Xw(_vt,_Xv,_XM,_XL)),new T(function(){return B(_Nb(0,_Ii,_XM,_XK.b));},1)));});return new T2(1,_XJ,new T(function(){return B(_XF(_XG,_XI.b));}));}},_XN=function(_XO,_XP){var _XQ=E(_XP);return (_XQ._==0)?__Z:new T2(1,_XO,new T(function(){return B(_XN(_XQ.a,_XQ.b));}));},_XR=new T(function(){return B(unCStr("init"));}),_XS=new T(function(){return B(_rj(_XR));}),_XT=function(_XU,_XV){var _XW=function(_XX){var _XY=E(_XX);if(!_XY._){return __Z;}else{var _XZ=new T(function(){return B(_x(new T2(1,_XU,_Z),new T(function(){return B(_XW(_XY.b));},1)));},1);return new F(function(){return _x(_XY.a,_XZ);});}},_Y0=B(_XW(_XV));if(!_Y0._){return E(_XS);}else{return new F(function(){return _XN(_Y0.a,_Y0.b);});}},_Y1=61,_Y2=46,_Y3=new T(function(){return B(_ic("Event.hs:(109,1)-(115,61)|function makeDecision"));}),_Y4=new T(function(){return B(unCStr("sm"));}),_Y5=new T(function(){return B(unCStr("rt"));}),_Y6=new T(function(){return B(unCStr("rs"));}),_Y7=new T(function(){return B(unCStr("rk"));}),_Y8=new T(function(){return B(unCStr("if"));}),_Y9=new T(function(){return B(unCStr("hm"));}),_Ya=new T(function(){return B(unCStr("cleq"));}),_Yb=new T(function(){return B(unCStr("da"));}),_Yc=new T(function(){return B(unCStr("ct"));}),_Yd=function(_Ye,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA){var _YB=function(_YC,_YD){var _YE=function(_YF){if(!B(_uV(_YC,_Yc))){if(!B(_uV(_YC,_Yb))){var _YG=function(_YH){if(!B(_uV(_YC,_Ya))){var _YI=function(_YJ){if(!B(_uV(_YC,_vW))){if(!B(_uV(_YC,_Y9))){if(!B(_uV(_YC,_Y8))){if(!B(_uV(_YC,_Y7))){if(!B(_uV(_YC,_Y6))){if(!B(_uV(_YC,_Y5))){if(!B(_uV(_YC,_Y4))){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{var _YK=E(_Yz);return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E({_:0,a:E(_YK.a),b:E(_YK.b),c:E(_YK.c),d:E(_YK.d),e:E(_YK.e),f:E(_YK.f),g:E(_YK.g),h:E(_AD)}),v:E(_YA)};}}else{var _YL=B(_SN(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_YL.a),b:E(_YL.b),c:E(_YL.c),d:E(_YL.d),e:E(_YL.e),f:E(_YL.f),g:E(_YL.g),h:E(_YL.h),i:_YL.i,j:_YL.j,k:_YL.k,l:_YL.l,m:E(_YL.m),n:_YL.n,o:E(_YL.o),p:E(_YL.p),q:_YL.q,r:E(_YL.r),s:E(_YL.s),t:_YL.t,u:E(_YL.u),v:E(_YL.v)};}}else{var _YM=new T(function(){return B(_x(B(_H(0,600-B(_SC(_Yw,0))|0,_Z)),new T(function(){if(_Yn>0){return B(_Xj(_Yn,_Yh));}else{return E(_Yh);}},1)));});if(0>=_Yn){var _YN=E(_YM);}else{var _YO=function(_YP,_YQ){var _YR=E(_YP);if(!_YR._){return E(_YM);}else{var _YS=_YR.a,_YT=E(_YQ);return (_YT==1)?new T2(1,_YS,_YM):new T2(1,_YS,new T(function(){return B(_YO(_YR.b,_YT-1|0));}));}},_YN=B(_YO(_Yh,_Yn));}return {_:0,a:E(_Yf),b:E(_Yg),c:E(_YN),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}}else{return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_YD),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}}else{var _YU=E(_YD);if(!_YU._){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{var _YV=_YU.a,_YW=E(_YU.b);if(!_YW._){return E(_Y3);}else{var _YX=_YW.a,_YY=B(_Sw(_Yl)),_YZ=_YY.a,_Z0=_YY.b,_Z1=function(_Z2){if(!B(_4H(_uj,_YV,_YZ))){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{if(!B(_uV(_YX,B(_aW(_Z0,B(_QT(_uj,_YV,_YZ))))))){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{return new F(function(){return _Yd(_Z2,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}}},_Z3=B(_XT(_Y2,_YW.b));if(!_Z3._){return new F(function(){return _Z1(_Z);});}else{var _Z4=_Z3.a,_Z5=E(_Z3.b);if(!_Z5._){return new F(function(){return _Z1(new T2(1,_Z4,_Z));});}else{var _Z6=_Z5.a,_Z7=_Z5.b,_Z8=E(_Z4);if(E(_Z8)==47){if(!B(_4H(_uj,_YV,_YZ))){return new F(function(){return _Yd(B(_Lc(47,_Z6,_Z7)).a,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}else{if(!B(_uV(_YX,B(_aW(_Z0,B(_QT(_uj,_YV,_YZ))))))){return new F(function(){return _Yd(B(_Lc(47,_Z6,_Z7)).a,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}else{return new F(function(){return _Yd(_Z,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}}}else{if(!B(_4H(_uj,_YV,_YZ))){var _Z9=E(B(_Lc(47,_Z6,_Z7)).b);if(!_Z9._){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{return new F(function(){return _Yd(_Z9.a,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}}else{if(!B(_uV(_YX,B(_aW(_Z0,B(_QT(_uj,_YV,_YZ))))))){var _Za=E(B(_Lc(47,_Z6,_Z7)).b);if(!_Za._){return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}else{return new F(function(){return _Yd(_Za.a,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}}else{return new F(function(){return _Yd(new T2(1,_Z8,new T(function(){return E(B(_Lc(47,_Z6,_Z7)).a);})),_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA);});}}}}}}}}}else{var _Zb=E(_Yz);return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E({_:0,a:E(_Zb.a),b:E(_Zb.b),c:E(_Zb.c),d:E(_Zb.d),e:E(_Zb.e),f:E(_Zb.f),g:E(_Zb.g),h:E(_AC)}),v:E(_YA)};}}else{var _Zc=E(_Yz);return new F(function(){return _U7(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Z,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Zc.a,_Zc.b,_Zc.c,_Zc.d,_Zc.e,_Zc.f,_Zc.g,_Zc.h,_YA);});}},_Zd=E(_YC);if(!_Zd._){return new F(function(){return _YI(_);});}else{if(E(_Zd.a)==109){if(!E(_Zd.b)._){var _Ze=B(_Lp(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Ze.a),b:E(_Ze.b),c:E(_Ze.c),d:E(_Ze.d),e:E(_Ze.e),f:E(_Ze.f),g:E(_Ze.g),h:E(_Ze.h),i:_Ze.i,j:_Ze.j,k:_Ze.k,l:_Ze.l,m:E(_Ze.m),n:_Ze.n,o:E(_Ze.o),p:E(_Ze.p),q:_Ze.q,r:E(_Ze.r),s:E(_Ze.s),t:_Ze.t,u:E(_Ze.u),v:E(_Ze.v)};}else{return new F(function(){return _YI(_);});}}else{return new F(function(){return _YI(_);});}}}else{var _Zf=E(_Yf);return {_:0,a:E({_:0,a:E(_Zf.a),b:E(B(_XF(_Y1,_Zf.b))),c:E(_Zf.c),d:_Zf.d,e:_Zf.e,f:_Zf.f,g:E(_Zf.g),h:_Zf.h,i:E(_Zf.i),j:E(_Zf.j),k:E(_Zf.k)}),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Yj),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}},_Zg=E(_YC);if(!_Zg._){return new F(function(){return _YG(_);});}else{var _Zh=_Zg.b;switch(E(_Zg.a)){case 99:if(!E(_Zh)._){var _Zi=B(_Pz(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Zi.a),b:E(_Zi.b),c:E(_Zi.c),d:E(_Zi.d),e:E(_Zi.e),f:E(_Zi.f),g:E(_Zi.g),h:E(_Zi.h),i:_Zi.i,j:_Zi.j,k:_Zi.k,l:_Zi.l,m:E(_Zi.m),n:_Zi.n,o:E(_Zi.o),p:E(_Zi.p),q:_Zi.q,r:E(_Zi.r),s:E(_Zi.s),t:_Zi.t,u:E(_Zi.u),v:E(_Zi.v)};}else{return new F(function(){return _YG(_);});}break;case 112:if(!E(_Zh)._){var _Zj=B(_VQ(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Zj.a),b:E(_Zj.b),c:E(_Zj.c),d:E(_Zj.d),e:E(_Zj.e),f:E(_Zj.f),g:E(_Zj.g),h:E(_Zj.h),i:_Zj.i,j:_Zj.j,k:_Zj.k,l:_Zj.l,m:E(_Zj.m),n:_Zj.n,o:E(_Zj.o),p:E(_Zj.p),q:_Zj.q,r:E(_Zj.r),s:E(_Zj.s),t:_Zj.t,u:E(_Zj.u),v:E(_Zj.v)};}else{return new F(function(){return _YG(_);});}break;default:return new F(function(){return _YG(_);});}}}else{return {_:0,a:E(_Yf),b:E(_Yg),c:E(_Yh),d:E(_Yi),e:E(_Z),f:E(_Yk),g:E(_Yl),h:E(_Ym),i:_Yn,j:_Yo,k:_Yp,l:_Yq,m:E(_Yr),n:_Ys,o:E(_Yt),p:E(_Yu),q:_Yv,r:E(_Yw),s:E(_Yx),t:_Yy,u:E(_Yz),v:E(_YA)};}}else{var _Zk=B(_NH(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Zk.a),b:E(_Zk.b),c:E(_Zk.c),d:E(_Zk.d),e:E(_Zk.e),f:E(_Zk.f),g:E(_Zk.g),h:E(_Zk.h),i:_Zk.i,j:_Zk.j,k:_Zk.k,l:_Zk.l,m:E(_Zk.m),n:_Zk.n,o:E(_Zk.o),p:E(_Zk.p),q:_Zk.q,r:E(_Zk.r),s:E(_Zk.s),t:_Zk.t,u:E(_Zk.u),v:E(_Zk.v)};}},_Zl=E(_YC);if(!_Zl._){return new F(function(){return _YE(_);});}else{var _Zm=_Zl.b;switch(E(_Zl.a)){case 100:if(!E(_Zm)._){var _Zn=B(_Rj(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Zn.a),b:E(_Zn.b),c:E(_Zn.c),d:E(_Zn.d),e:E(_Zn.e),f:E(_Zn.f),g:E(_Zn.g),h:E(_Zn.h),i:_Zn.i,j:_Zn.j,k:_Zn.k,l:_Zn.l,m:E(_Zn.m),n:_Zn.n,o:E(_Zn.o),p:E(_Zn.p),q:_Zn.q,r:E(_Zn.r),s:E(_Zn.s),t:_Zn.t,u:E(_Zn.u),v:E(_Zn.v)};}else{return new F(function(){return _YE(_);});}break;case 101:if(!E(_Zm)._){var _Zo=B(_um(_YD,_Yf,_Yg,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy,_Yz,_YA));return {_:0,a:E(_Zo.a),b:E(_Zo.b),c:E(_Zo.c),d:E(_Zo.d),e:E(_Zo.e),f:E(_Zo.f),g:E(_Zo.g),h:E(_Zo.h),i:_Zo.i,j:_Zo.j,k:_Zo.k,l:_Zo.l,m:E(_Zo.m),n:_Zo.n,o:E(_Zo.o),p:E(_Zo.p),q:_Zo.q,r:E(_Zo.r),s:E(_Zo.s),t:_Zo.t,u:E(_Zo.u),v:E(_Zo.v)};}else{return new F(function(){return _YE(_);});}break;default:return new F(function(){return _YE(_);});}}},_Zp=E(_Ye);if(!_Zp._){return new F(function(){return _YB(_Z,_Z);});}else{var _Zq=_Zp.a,_Zr=E(_Zp.b);if(!_Zr._){return new F(function(){return _YB(new T2(1,_Zq,_Z),_Z);});}else{var _Zs=E(_Zq),_Zt=new T(function(){var _Zu=B(_Lc(46,_Zr.a,_Zr.b));return new T2(0,_Zu.a,_Zu.b);});if(E(_Zs)==46){return new F(function(){return _YB(_Z,new T2(1,new T(function(){return E(E(_Zt).a);}),new T(function(){return E(E(_Zt).b);})));});}else{return new F(function(){return _YB(new T2(1,_Zs,new T(function(){return E(E(_Zt).a);})),new T(function(){return E(E(_Zt).b);}));});}}}},_Zv=new T(function(){return B(unCStr("last"));}),_Zw=new T(function(){return B(_rj(_Zv));}),_Zx=32,_Zy=0,_Zz=65306,_ZA=125,_ZB=new T1(0,1),_ZC=function(_ZD,_ZE,_ZF,_ZG,_ZH){var _ZI=new T(function(){return E(_ZH).i;}),_ZJ=new T(function(){var _ZK=E(_ZE)/28,_ZL=_ZK&4294967295;if(_ZK>=_ZL){return _ZL-1|0;}else{return (_ZL-1|0)-1|0;}}),_ZM=new T(function(){if(!E(E(_ZG).h)){return E(_nd);}else{return 2+(E(E(E(_ZH).b).b)+3|0)|0;}}),_ZN=new T(function(){if(!E(_ZI)){return new T2(0,_ZJ,_ZM);}else{return E(E(_ZH).h);}}),_ZO=new T(function(){return E(E(_ZH).c);}),_ZP=new T(function(){var _ZQ=E(_ZI)+1|0;if(0>=_ZQ){return E(_Zx);}else{var _ZR=B(_tT(_ZQ,_ZO));if(!_ZR._){return E(_Zx);}else{return B(_sf(_ZR.a,_ZR.b,_Zw));}}}),_ZS=new T(function(){var _ZT=E(_ZP);switch(E(_ZT)){case 125:return E(_Zx);break;case 12289:return E(_Zx);break;case 12290:return E(_Zx);break;default:return E(_ZT);}}),_ZU=new T(function(){if(E(_ZS)==10){return true;}else{return false;}}),_ZV=new T(function(){return E(E(_ZN).b);}),_ZW=new T(function(){if(!E(_ZU)){if(E(_ZS)==12300){return E(_nc);}else{return E(_ZH).j;}}else{return E(_Zy);}}),_ZX=new T(function(){return E(E(_ZN).a);}),_ZY=new T(function(){if(E(_ZS)==65306){return true;}else{return false;}}),_ZZ=new T(function(){if(!E(_ZY)){if(!E(_ZU)){var _100=E(_ZV);if((_100+1)*24<=E(_ZF)-10){return new T2(0,_ZX,_100+1|0);}else{return new T2(0,new T(function(){return E(_ZX)-1|0;}),_ZM);}}else{return new T2(0,new T(function(){return E(_ZX)-1|0;}),_ZM);}}else{return new T2(0,_ZX,_ZV);}}),_101=new T(function(){if(E(E(_ZZ).a)==1){if(E(_ZX)==1){return false;}else{return true;}}else{return false;}}),_102=new T(function(){return B(_qy(_ZO,0))-1|0;}),_103=new T(function(){if(!E(_ZY)){return __Z;}else{return B(_ub(_Zz,E(_ZI),_ZO));}}),_104=new T(function(){if(E(_ZS)==123){return true;}else{return false;}}),_105=new T(function(){if(!E(_104)){return __Z;}else{return B(_ub(_ZA,E(_ZI),_ZO));}}),_106=new T(function(){if(!E(_ZY)){if(!E(_104)){return E(_nc);}else{return B(_qy(_105,0))+2|0;}}else{return B(_qy(_103,0))+2|0;}}),_107=new T(function(){var _108=E(_ZH),_109=_108.a,_10a=_108.b,_10b=_108.c,_10c=_108.d,_10d=_108.e,_10e=_108.f,_10f=_108.g,_10g=_108.h,_10h=_108.j,_10i=_108.k,_10j=_108.l,_10k=_108.m,_10l=_108.n,_10m=_108.o,_10n=_108.p,_10o=_108.q,_10p=_108.r,_10q=_108.s,_10r=_108.t,_10s=_108.v,_10t=E(_ZI),_10u=E(_106);if((_10t+_10u|0)<=E(_102)){var _10v=E(_ZG),_10w=_10v.a,_10x=_10v.b,_10y=_10v.c,_10z=_10v.e,_10A=_10v.f,_10B=_10v.g,_10C=_10v.h;if(E(_ZP)==12290){var _10D=true;}else{var _10D=false;}if(!E(_104)){return {_:0,a:E(_109),b:E(_10a),c:E(_10b),d:E(_10c),e:E(_10d),f:E(_10e),g:E(_10f),h:E(_10g),i:_10t+_10u|0,j:_10h,k:_10i,l:_10j,m:E(_10k),n:_10l,o:E(_10m),p:E(_10n),q:_10o,r:E(_10p),s:E(_10q),t:_10r,u:E({_:0,a:E(_10w),b:E(_10x),c:E(_10y),d:E(_10D),e:E(_10z),f:E(_10A),g:E(_10B),h:E(_10C)}),v:E(_10s)};}else{return B(_Yd(_105,_109,_10a,_10b,_10c,_10d,_10e,_10f,_10g,_10t+_10u|0,_10h,_10i,_10j,_10k,_10l,_10m,_10n,_10o,_10p,_10q,_10r,{_:0,a:E(_10w),b:E(_10x),c:E(_10y),d:E(_10D),e:E(_10z),f:E(_10A),g:E(_10B),h:E(_10C)},_10s));}}else{var _10E=E(_ZG),_10F=_10E.a,_10G=_10E.b,_10H=_10E.c,_10I=_10E.e,_10J=_10E.f,_10K=_10E.g,_10L=_10E.h;if(E(_ZP)==12290){var _10M=true;}else{var _10M=false;}if(!E(_104)){return {_:0,a:E(_109),b:E(_10a),c:E(_10b),d:E(_10c),e:E(_10d),f:E(_10e),g:E(_10f),h:E(_10g),i:0,j:_10h,k:_10i,l:_10j,m:E(_10k),n:_10l,o:E(_10m),p:E(_10n),q:_10o,r:E(_10p),s:E(_10q),t:_10r,u:E({_:0,a:E(_10F),b:E(_10G),c:E(_10H),d:E(_10M),e:E(_10I),f:E(_10J),g:E(_10K),h:E(_10L)}),v:E(_10s)};}else{return B(_Yd(_105,_109,_10a,_10b,_10c,_10d,_10e,_10f,_10g,0,_10h,_10i,_10j,_10k,_10l,_10m,_10n,_10o,_10p,_10q,_10r,{_:0,a:E(_10F),b:E(_10G),c:E(_10H),d:E(_10M),e:E(_10I),f:E(_10J),g:E(_10K),h:E(_10L)},_10s));}}}),_10N=new T(function(){return E(E(_107).u);}),_10O=new T(function(){if(!E(_ZI)){return E(_Zy);}else{return E(_107).k;}}),_10P=new T(function(){var _10Q=B(_s9(B(_s7(_ZD)))),_10R=new T(function(){var _10S=B(_tA(_ZD,E(_ZE)/16)),_10T=_10S.a;if(E(_10S.b)>=0){return E(_10T);}else{return B(A3(_sM,_10Q,_10T,new T(function(){return B(A2(_lj,_10Q,_ZB));})));}});return B(A3(_sM,_10Q,_10R,new T(function(){return B(A2(_lj,_10Q,_ls));})));});return {_:0,a:_ZS,b:_ZX,c:_ZV,d:new T(function(){if(E(_ZM)!=E(_ZV)){return E(_ZX);}else{return E(_ZX)+1|0;}}),e:new T(function(){var _10U=E(_ZV);if(E(_ZM)!=_10U){return _10U-1|0;}else{var _10V=(E(_ZF)-10)/24,_10W=_10V&4294967295;if(_10V>=_10W){return _10W;}else{return _10W-1|0;}}}),f:_ZM,g:_ZI,h:_ZO,i:new T(function(){return B(_aW(_n9,E(_ZW)));}),j:_103,k:_ZJ,l:_10P,m:_10O,n:_ne,o:_ZY,p:_104,q:_101,r:_10N,s:_107,t:new T(function(){var _10X=E(_107),_10Y=_10X.a,_10Z=_10X.b,_110=_10X.c,_111=_10X.d,_112=_10X.e,_113=_10X.f,_114=_10X.g,_115=_10X.i,_116=_10X.l,_117=_10X.m,_118=_10X.n,_119=_10X.o,_11a=_10X.p,_11b=_10X.q,_11c=_10X.r,_11d=_10X.s,_11e=_10X.t,_11f=_10X.v;if(!E(_101)){var _11g=E(_ZZ);}else{var _11g=new T2(0,_ZX,_ZM);}var _11h=E(_ZW);if(!E(_101)){var _11i=E(_10N);return {_:0,a:E(_10Y),b:E(_10Z),c:E(_110),d:E(_111),e:E(_112),f:E(_113),g:E(_114),h:E(_11g),i:_115,j:_11h,k:E(_10O),l:_116,m:E(_117),n:_118,o:E(_119),p:E(_11a),q:_11b,r:E(_11c),s:E(_11d),t:_11e,u:E({_:0,a:E(_11i.a),b:E(_11i.b),c:(E(_ZI)+E(_106)|0)<=E(_102),d:E(_11i.d),e:E(_11i.e),f:E(_11i.f),g:E(_11i.g),h:E(_11i.h)}),v:E(_11f)};}else{var _11j=E(_10N);return {_:0,a:E(_10Y),b:E(_10Z),c:E(_110),d:E(_111),e:E(_112),f:E(_113),g:E(_114),h:E(_11g),i:_115,j:_11h,k:E(_10O)+1|0,l:_116,m:E(_117),n:_118,o:E(_119),p:E(_11a),q:_11b,r:E(_11c),s:E(_11d),t:_11e,u:E({_:0,a:E(_11j.a),b:E(_11j.b),c:(E(_ZI)+E(_106)|0)<=E(_102),d:E(_11j.d),e:E(_11j.e),f:E(_11j.f),g:E(_11j.g),h:E(_11j.h)}),v:E(_11f)};}})};},_11k=function(_11l){var _11m=E(_11l);if(!_11m._){return new T2(0,_Z,_Z);}else{var _11n=E(_11m.a),_11o=new T(function(){var _11p=B(_11k(_11m.b));return new T2(0,_11p.a,_11p.b);});return new T2(0,new T2(1,_11n.a,new T(function(){return E(E(_11o).a);})),new T2(1,_11n.b,new T(function(){return E(E(_11o).b);})));}},_11q=42,_11r=32,_11s=function(_11t,_11u,_11v){var _11w=E(_11t);if(!_11w._){return __Z;}else{var _11x=_11w.a,_11y=_11w.b;if(_11u!=_11v){var _11z=E(_11x);return (_11z._==0)?E(_rm):(E(_11z.a)==42)?new T2(1,new T2(1,_11r,_11z.b),new T(function(){return B(_11s(_11y,_11u,_11v+1|0));})):new T2(1,new T2(1,_11r,_11z),new T(function(){return B(_11s(_11y,_11u,_11v+1|0));}));}else{var _11A=E(_11x);return (_11A._==0)?E(_rm):(E(_11A.a)==42)?new T2(1,new T2(1,_11r,_11A),new T(function(){return B(_11s(_11y,_11u,_11v+1|0));})):new T2(1,new T2(1,_11q,_11A),new T(function(){return B(_11s(_11y,_11u,_11v+1|0));}));}}},_11B=new T(function(){return B(unCStr("\n\n"));}),_11C=function(_11D){var _11E=E(_11D);if(!_11E._){return __Z;}else{var _11F=new T(function(){return B(_x(_11B,new T(function(){return B(_11C(_11E.b));},1)));},1);return new F(function(){return _x(_11E.a,_11F);});}},_11G=function(_11H,_11I,_11J){var _11K=new T(function(){var _11L=new T(function(){var _11M=E(_11I);if(!_11M._){return B(_11C(_Z));}else{var _11N=_11M.a,_11O=_11M.b,_11P=E(_11J);if(!_11P){var _11Q=E(_11N);if(!_11Q._){return E(_rm);}else{if(E(_11Q.a)==42){return B(_11C(new T2(1,new T2(1,_11r,_11Q),new T(function(){return B(_11s(_11O,0,1));}))));}else{return B(_11C(new T2(1,new T2(1,_11q,_11Q),new T(function(){return B(_11s(_11O,0,1));}))));}}}else{var _11R=E(_11N);if(!_11R._){return E(_rm);}else{if(E(_11R.a)==42){return B(_11C(new T2(1,new T2(1,_11r,_11R.b),new T(function(){return B(_11s(_11O,_11P,1));}))));}else{return B(_11C(new T2(1,new T2(1,_11r,_11R),new T(function(){return B(_11s(_11O,_11P,1));}))));}}}}});return B(unAppCStr("\n\n",_11L));},1);return new F(function(){return _x(_11H,_11K);});},_11S=function(_11T){return E(E(_11T).c);},_11U=function(_11V,_11W,_11X,_11Y,_11Z,_120,_121,_122,_123){var _124=new T(function(){if(!E(_11W)){return E(_11X);}else{return false;}}),_125=new T(function(){if(!E(_11W)){return false;}else{return E(E(_122).g);}}),_126=new T(function(){if(!E(_125)){if(!E(_124)){return B(A2(_lj,_11V,_lr));}else{return B(A3(_qD,_11V,new T(function(){return B(A3(_qD,_11V,_120,_121));}),new T(function(){return B(A2(_lj,_11V,_ZB));})));}}else{return B(A3(_qD,_11V,_120,_121));}}),_127=new T(function(){if(!E(_125)){if(!E(_124)){return __Z;}else{var _128=E(_11Y)+1|0;if(0>=_128){return __Z;}else{return B(_tT(_128,_11Z));}}}else{return B(_11G(B(_11S(_123)),new T(function(){return E(B(_11k(E(_123).m)).a);},1),new T(function(){return E(_123).n;},1)));}});return new T4(0,_125,_124,_127,_126);},_129=function(_12a,_12b,_12c){var _12d=E(_12b),_12e=E(_12c),_12f=new T(function(){var _12g=B(_lf(_12a)),_12h=B(_129(_12a,_12e,B(A3(_sM,_12g,new T(function(){return B(A3(_qD,_12g,_12e,_12e));}),_12d))));return new T2(1,_12h.a,_12h.b);});return new T2(0,_12d,_12f);},_12i=1,_12j=new T(function(){var _12k=B(_129(_kg,_lR,_12i));return new T2(1,_12k.a,_12k.b);}),_12l=function(_12m,_12n,_12o,_12p,_12q,_12r,_12s,_12t,_12u,_12v,_12w,_12x,_12y,_12z,_12A,_12B,_12C,_12D,_12E,_12F,_12G,_12H,_12I,_12J,_12K,_12L,_12M,_12N,_12O,_12P,_12Q,_12R,_12S,_12T,_){var _12U={_:0,a:E(_12L),b:E(_12M),c:E(_12N),d:E(_12O),e:E(_12P),f:E(_12Q),g:E(_12R),h:E(_12S)};if(!E(_12N)){return {_:0,a:E(_12p),b:E(new T2(0,_12q,_12r)),c:E(_12s),d:E(_12t),e:E(_12u),f:E(_12v),g:E(_12w),h:E(new T2(0,_12x,_12y)),i:_12z,j:_12A,k:_12B,l:_12C,m:E(_12D),n:_12E,o:E(_12F),p:E(_12G),q:_12H,r:E(_12I),s:E(_12J),t:_12K,u:E(_12U),v:E(_12T)};}else{if(!E(_12O)){var _12V=B(_ZC(_fX,_12n,_12o,_12U,{_:0,a:E(_12p),b:E(new T2(0,_12q,_12r)),c:E(_12s),d:E(_12t),e:E(_12u),f:E(_12v),g:E(_12w),h:E(new T2(0,_12x,_12y)),i:_12z,j:_12A,k:_12B,l:_12C,m:E(_12D),n:_12E,o:E(_12F),p:E(_12G),q:_12H,r:E(_12I),s:E(_12J),t:_12K,u:E(_12U),v:E(_12T)})),_12W=_12V.d,_12X=_12V.e,_12Y=_12V.f,_12Z=_12V.i,_130=_12V.n,_131=_12V.p,_132=_12V.q,_133=_12V.s,_134=_12V.t;if(!E(_12V.o)){var _135=B(_11U(_fs,_131,_132,_12V.g,_12V.h,_12V.k,_12V.m,_12V.r,_133)),_136=_135.c,_137=_135.d,_138=function(_){var _139=function(_){if(!E(_131)){if(!E(_132)){var _13a=B(_mG(E(_12m).a,_12Z,_na,_lR,_12V.b,_12V.c,_12V.a,_));return _134;}else{return _134;}}else{return _134;}};if(!E(_135.b)){return new F(function(){return _139(_);});}else{var _13b=E(_12m),_13c=_13b.a,_13d=_13b.b,_13e=B(_rV(_13c,_13d,_12V.l,_133,_)),_13f=B(_pt(_13c,_13d,_12o,0,_12Y,_137,_12Y,_136,_));return new F(function(){return _139(_);});}};if(!E(_135.a)){return new F(function(){return _138(_);});}else{var _13g=B(_nf(_12m,_12o,0,_12Y,_137,_12Y,_136,_));return new F(function(){return _138(_);});}}else{var _13h=E(_12V.j);if(!_13h._){return _134;}else{var _13i=E(_12j);if(!_13i._){return _134;}else{var _13j=E(_12m).a,_13k=B(_mG(_13j,_12Z,_130,_13i.a,_12W,_12X,_13h.a,_)),_13l=function(_13m,_13n,_){while(1){var _13o=E(_13m);if(!_13o._){return _kJ;}else{var _13p=E(_13n);if(!_13p._){return _kJ;}else{var _13q=B(_mG(_13j,_12Z,_130,_13p.a,_12W,_12X,_13o.a,_));_13m=_13o.b;_13n=_13p.b;continue;}}}},_13r=B(_13l(_13h.b,_13i.b,_));return _134;}}}}else{return {_:0,a:E(_12p),b:E(new T2(0,_12q,_12r)),c:E(_12s),d:E(_12t),e:E(_12u),f:E(_12v),g:E(_12w),h:E(new T2(0,_12x,_12y)),i:_12z,j:_12A,k:_12B,l:_12C,m:E(_12D),n:_12E,o:E(_12F),p:E(_12G),q:_12H,r:E(_12I),s:E(_12J),t:_12K,u:E(_12U),v:E(_12T)};}}},_13s=function(_13t,_13u,_13v,_13w,_13x,_13y,_13z,_13A,_13B,_13C,_13D,_13E,_13F,_13G,_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_13S,_13T,_13U,_13V,_13W,_13X,_13Y,_13Z,_140,_){while(1){var _141=B(_12l(_13t,_13u,_13v,_13w,_13x,_13y,_13z,_13A,_13B,_13C,_13D,_13E,_13F,_13G,_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_13S,_13T,_13U,_13V,_13W,_13X,_13Y,_13Z,_140,_)),_142=E(_141),_143=_142.a,_144=_142.c,_145=_142.d,_146=_142.e,_147=_142.f,_148=_142.g,_149=_142.i,_14a=_142.j,_14b=_142.k,_14c=_142.l,_14d=_142.m,_14e=_142.n,_14f=_142.o,_14g=_142.p,_14h=_142.q,_14i=_142.r,_14j=_142.s,_14k=_142.t,_14l=_142.v,_14m=E(_142.u),_14n=_14m.a,_14o=_14m.b,_14p=_14m.c,_14q=_14m.e,_14r=_14m.g,_14s=_14m.h,_14t=E(_142.b),_14u=E(_142.h);if(!E(_14m.d)){if(!E(_13U)){return {_:0,a:E(_143),b:E(_14t),c:E(_144),d:E(_145),e:E(_146),f:E(_147),g:E(_148),h:E(_14u),i:_149,j:_14a,k:_14b,l:_14c,m:E(_14d),n:_14e,o:E(_14f),p:E(_14g),q:_14h,r:E(_14i),s:E(_14j),t:_14k,u:E({_:0,a:E(_14n),b:E(_14o),c:E(_14p),d:E(_AC),e:E(_14q),f:E(_AC),g:E(_14r),h:E(_14s)}),v:E(_14l)};}else{_13w=_143;_13x=_14t.a;_13y=_14t.b;_13z=_144;_13A=_145;_13B=_146;_13C=_147;_13D=_148;_13E=_14u.a;_13F=_14u.b;_13G=_149;_13H=_14a;_13I=_14b;_13J=_14c;_13K=_14d;_13L=_14e;_13M=_14f;_13N=_14g;_13O=_14h;_13P=_14i;_13Q=_14j;_13R=_14k;_13S=_14n;_13T=_14o;_13U=_14p;_13V=_AC;_13W=_14q;_13X=_14m.f;_13Y=_14r;_13Z=_14s;_140=_14l;continue;}}else{return {_:0,a:E(_143),b:E(_14t),c:E(_144),d:E(_145),e:E(_146),f:E(_147),g:E(_148),h:E(_14u),i:_149,j:_14a,k:_14b,l:_14c,m:E(_14d),n:_14e,o:E(_14f),p:E(_14g),q:_14h,r:E(_14i),s:E(_14j),t:_14k,u:E({_:0,a:E(_14n),b:E(_14o),c:E(_14p),d:E(_AD),e:E(_14q),f:E(_AC),g:E(_14r),h:E(_14s)}),v:E(_14l)};}}},_14v=function(_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_14W,_14X,_14Y,_14Z,_150,_151,_152,_){var _153=B(_12l(_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_14W,_AD,_14X,_14Y,_14Z,_150,_151,_152,_)),_154=E(_153),_155=_154.a,_156=_154.c,_157=_154.d,_158=_154.e,_159=_154.f,_15a=_154.g,_15b=_154.i,_15c=_154.j,_15d=_154.k,_15e=_154.l,_15f=_154.m,_15g=_154.n,_15h=_154.o,_15i=_154.p,_15j=_154.q,_15k=_154.r,_15l=_154.s,_15m=_154.t,_15n=_154.v,_15o=E(_154.u),_15p=_15o.a,_15q=_15o.b,_15r=_15o.c,_15s=_15o.e,_15t=_15o.g,_15u=_15o.h,_15v=E(_154.b),_15w=E(_154.h);if(!E(_15o.d)){return new F(function(){return _13s(_14w,_14x,_14y,_155,_15v.a,_15v.b,_156,_157,_158,_159,_15a,_15w.a,_15w.b,_15b,_15c,_15d,_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15p,_15q,_15r,_AC,_15s,_15o.f,_15t,_15u,_15n,_);});}else{return {_:0,a:E(_155),b:E(_15v),c:E(_156),d:E(_157),e:E(_158),f:E(_159),g:E(_15a),h:E(_15w),i:_15b,j:_15c,k:_15d,l:_15e,m:E(_15f),n:_15g,o:E(_15h),p:E(_15i),q:_15j,r:E(_15k),s:E(_15l),t:_15m,u:E({_:0,a:E(_15p),b:E(_15q),c:E(_15r),d:E(_AD),e:E(_15s),f:E(_AC),g:E(_15t),h:E(_15u)}),v:E(_15n)};}},_15x=function(_15y){var _15z=E(_15y);if(!_15z._){return __Z;}else{var _15A=E(_15z.b);return (_15A._==0)?__Z:new T2(1,new T2(0,_15z.a,_15A.a),new T(function(){return B(_15x(_15A.b));}));}},_15B=function(_15C,_15D,_15E){return new T2(1,new T2(0,_15C,_15D),new T(function(){return B(_15x(_15E));}));},_15F=function(_15G,_15H){var _15I=E(_15H);return (_15I._==0)?__Z:new T2(1,new T2(0,_15G,_15I.a),new T(function(){return B(_15x(_15I.b));}));},_15J="Invalid JSON!",_15K=new T1(0,_15J),_15L="No such value",_15M=new T1(0,_15L),_15N=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_15O=function(_15P){return E(E(_15P).c);},_15Q=function(_15R,_15S,_){var _15T=__app1(E(_15N),_15S),_15U=__eq(_15T,E(_3h));if(!E(_15U)){var _15V=__isUndef(_15T);return (E(_15V)==0)?new T(function(){var _15W=String(_15T),_15X=jsParseJSON(_15W);if(!_15X._){return E(_15K);}else{return B(A2(_15O,_15R,_15X.a));}}):_15M;}else{return _15M;}},_15Y=new T1(0,0),_15Z=function(_160,_161){while(1){var _162=E(_160);if(!_162._){var _163=_162.a,_164=E(_161);if(!_164._){return new T1(0,(_163>>>0|_164.a>>>0)>>>0&4294967295);}else{_160=new T1(1,I_fromInt(_163));_161=_164;continue;}}else{var _165=E(_161);if(!_165._){_160=_162;_161=new T1(1,I_fromInt(_165.a));continue;}else{return new T1(1,I_or(_162.a,_165.a));}}}},_166=function(_167){var _168=E(_167);if(!_168._){return E(_15Y);}else{return new F(function(){return _15Z(new T1(0,E(_168.a)),B(_gT(B(_166(_168.b)),31)));});}},_169=function(_16a,_16b){if(!E(_16a)){return new F(function(){return _jy(B(_166(_16b)));});}else{return new F(function(){return _166(_16b);});}},_16c=1420103680,_16d=465,_16e=new T2(1,_16d,_Z),_16f=new T2(1,_16c,_16e),_16g=new T(function(){return B(_169(_AD,_16f));}),_16h=function(_16i){return E(_16g);},_16j=new T(function(){return B(unCStr("s"));}),_16k=function(_16l,_16m){while(1){var _16n=E(_16l);if(!_16n._){return E(_16m);}else{_16l=_16n.b;_16m=_16n.a;continue;}}},_16o=function(_16p,_16q,_16r){return new F(function(){return _16k(_16q,_16p);});},_16s=new T1(0,1),_16t=function(_16u,_16v){var _16w=E(_16u);return new T2(0,_16w,new T(function(){var _16x=B(_16t(B(_gA(_16w,_16v)),_16v));return new T2(1,_16x.a,_16x.b);}));},_16y=function(_16z){var _16A=B(_16t(_16z,_16s));return new T2(1,_16A.a,_16A.b);},_16B=function(_16C,_16D){var _16E=B(_16t(_16C,new T(function(){return B(_iT(_16D,_16C));})));return new T2(1,_16E.a,_16E.b);},_16F=new T1(0,0),_16G=function(_16H,_16I){var _16J=E(_16H);if(!_16J._){var _16K=_16J.a,_16L=E(_16I);return (_16L._==0)?_16K>=_16L.a:I_compareInt(_16L.a,_16K)<=0;}else{var _16M=_16J.a,_16N=E(_16I);return (_16N._==0)?I_compareInt(_16M,_16N.a)>=0:I_compare(_16M,_16N.a)>=0;}},_16O=function(_16P,_16Q,_16R){if(!B(_16G(_16Q,_16F))){var _16S=function(_16T){return (!B(_hc(_16T,_16R)))?new T2(1,_16T,new T(function(){return B(_16S(B(_gA(_16T,_16Q))));})):__Z;};return new F(function(){return _16S(_16P);});}else{var _16U=function(_16V){return (!B(_h3(_16V,_16R)))?new T2(1,_16V,new T(function(){return B(_16U(B(_gA(_16V,_16Q))));})):__Z;};return new F(function(){return _16U(_16P);});}},_16W=function(_16X,_16Y,_16Z){return new F(function(){return _16O(_16X,B(_iT(_16Y,_16X)),_16Z);});},_170=function(_171,_172){return new F(function(){return _16O(_171,_16s,_172);});},_173=function(_174){return new F(function(){return _ff(_174);});},_175=function(_176){return new F(function(){return _iT(_176,_16s);});},_177=function(_178){return new F(function(){return _gA(_178,_16s);});},_179=function(_17a){return new F(function(){return _eW(E(_17a));});},_17b={_:0,a:_177,b:_175,c:_179,d:_173,e:_16y,f:_16B,g:_170,h:_16W},_17c=function(_17d,_17e){while(1){var _17f=E(_17d);if(!_17f._){var _17g=E(_17f.a);if(_17g==( -2147483648)){_17d=new T1(1,I_fromInt( -2147483648));continue;}else{var _17h=E(_17e);if(!_17h._){return new T1(0,B(_do(_17g,_17h.a)));}else{_17d=new T1(1,I_fromInt(_17g));_17e=_17h;continue;}}}else{var _17i=_17f.a,_17j=E(_17e);return (_17j._==0)?new T1(1,I_div(_17i,I_fromInt(_17j.a))):new T1(1,I_div(_17i,_17j.a));}}},_17k=function(_17l,_17m){if(!B(_gs(_17m,_sQ))){return new F(function(){return _17c(_17l,_17m);});}else{return E(_dZ);}},_17n=function(_17o,_17p){while(1){var _17q=E(_17o);if(!_17q._){var _17r=E(_17q.a);if(_17r==( -2147483648)){_17o=new T1(1,I_fromInt( -2147483648));continue;}else{var _17s=E(_17p);if(!_17s._){var _17t=_17s.a;return new T2(0,new T1(0,B(_do(_17r,_17t))),new T1(0,B(_et(_17r,_17t))));}else{_17o=new T1(1,I_fromInt(_17r));_17p=_17s;continue;}}}else{var _17u=E(_17p);if(!_17u._){_17o=_17q;_17p=new T1(1,I_fromInt(_17u.a));continue;}else{var _17v=I_divMod(_17q.a,_17u.a);return new T2(0,new T1(1,_17v.a),new T1(1,_17v.b));}}}},_17w=function(_17x,_17y){if(!B(_gs(_17y,_sQ))){var _17z=B(_17n(_17x,_17y));return new T2(0,_17z.a,_17z.b);}else{return E(_dZ);}},_17A=function(_17B,_17C){while(1){var _17D=E(_17B);if(!_17D._){var _17E=E(_17D.a);if(_17E==( -2147483648)){_17B=new T1(1,I_fromInt( -2147483648));continue;}else{var _17F=E(_17C);if(!_17F._){return new T1(0,B(_et(_17E,_17F.a)));}else{_17B=new T1(1,I_fromInt(_17E));_17C=_17F;continue;}}}else{var _17G=_17D.a,_17H=E(_17C);return (_17H._==0)?new T1(1,I_mod(_17G,I_fromInt(_17H.a))):new T1(1,I_mod(_17G,_17H.a));}}},_17I=function(_17J,_17K){if(!B(_gs(_17K,_sQ))){return new F(function(){return _17A(_17J,_17K);});}else{return E(_dZ);}},_17L=function(_17M,_17N){while(1){var _17O=E(_17M);if(!_17O._){var _17P=E(_17O.a);if(_17P==( -2147483648)){_17M=new T1(1,I_fromInt( -2147483648));continue;}else{var _17Q=E(_17N);if(!_17Q._){return new T1(0,quot(_17P,_17Q.a));}else{_17M=new T1(1,I_fromInt(_17P));_17N=_17Q;continue;}}}else{var _17R=_17O.a,_17S=E(_17N);return (_17S._==0)?new T1(0,I_toInt(I_quot(_17R,I_fromInt(_17S.a)))):new T1(1,I_quot(_17R,_17S.a));}}},_17T=function(_17U,_17V){if(!B(_gs(_17V,_sQ))){return new F(function(){return _17L(_17U,_17V);});}else{return E(_dZ);}},_17W=function(_17X,_17Y){if(!B(_gs(_17Y,_sQ))){var _17Z=B(_gJ(_17X,_17Y));return new T2(0,_17Z.a,_17Z.b);}else{return E(_dZ);}},_180=function(_181,_182){while(1){var _183=E(_181);if(!_183._){var _184=E(_183.a);if(_184==( -2147483648)){_181=new T1(1,I_fromInt( -2147483648));continue;}else{var _185=E(_182);if(!_185._){return new T1(0,_184%_185.a);}else{_181=new T1(1,I_fromInt(_184));_182=_185;continue;}}}else{var _186=_183.a,_187=E(_182);return (_187._==0)?new T1(1,I_rem(_186,I_fromInt(_187.a))):new T1(1,I_rem(_186,_187.a));}}},_188=function(_189,_18a){if(!B(_gs(_18a,_sQ))){return new F(function(){return _180(_189,_18a);});}else{return E(_dZ);}},_18b=function(_18c){return E(_18c);},_18d=function(_18e){return E(_18e);},_18f=function(_18g){var _18h=E(_18g);if(!_18h._){var _18i=E(_18h.a);return (_18i==( -2147483648))?E(_jx):(_18i<0)?new T1(0, -_18i):E(_18h);}else{var _18j=_18h.a;return (I_compareInt(_18j,0)>=0)?E(_18h):new T1(1,I_negate(_18j));}},_18k=new T1(0, -1),_18l=function(_18m){var _18n=E(_18m);if(!_18n._){var _18o=_18n.a;return (_18o>=0)?(E(_18o)==0)?E(_15Y):E(_hb):E(_18k);}else{var _18p=I_compareInt(_18n.a,0);return (_18p<=0)?(E(_18p)==0)?E(_15Y):E(_18k):E(_hb);}},_18q={_:0,a:_gA,b:_iT,c:_sk,d:_jy,e:_18f,f:_18l,g:_18d},_18r=function(_18s,_18t){var _18u=E(_18s);if(!_18u._){var _18v=_18u.a,_18w=E(_18t);return (_18w._==0)?_18v!=_18w.a:(I_compareInt(_18w.a,_18v)==0)?false:true;}else{var _18x=_18u.a,_18y=E(_18t);return (_18y._==0)?(I_compareInt(_18x,_18y.a)==0)?false:true:(I_compare(_18x,_18y.a)==0)?false:true;}},_18z=new T2(0,_gs,_18r),_18A=function(_18B,_18C){return (!B(_iE(_18B,_18C)))?E(_18B):E(_18C);},_18D=function(_18E,_18F){return (!B(_iE(_18E,_18F)))?E(_18F):E(_18E);},_18G={_:0,a:_18z,b:_gc,c:_hc,d:_iE,e:_h3,f:_16G,g:_18A,h:_18D},_18H=function(_18I){return new T2(0,E(_18I),E(_f0));},_18J=new T3(0,_18q,_18G,_18H),_18K={_:0,a:_18J,b:_17b,c:_17T,d:_188,e:_17k,f:_17I,g:_17W,h:_17w,i:_18b},_18L=new T1(0,0),_18M=function(_18N,_18O,_18P){var _18Q=B(A1(_18N,_18O));if(!B(_gs(_18Q,_18L))){return new F(function(){return _17c(B(_sk(_18O,_18P)),_18Q);});}else{return E(_dZ);}},_18R=function(_18S,_18T){while(1){if(!B(_gs(_18T,_sQ))){var _18U=_18T,_18V=B(_188(_18S,_18T));_18S=_18U;_18T=_18V;continue;}else{return E(_18S);}}},_18W=5,_18X=new T(function(){return B(_dV(_18W));}),_18Y=new T(function(){return die(_18X);}),_18Z=function(_190,_191){if(!B(_gs(_191,_sQ))){var _192=B(_18R(B(_18f(_190)),B(_18f(_191))));return (!B(_gs(_192,_sQ)))?new T2(0,B(_17L(_190,_192)),B(_17L(_191,_192))):E(_dZ);}else{return E(_18Y);}},_193=function(_194,_195,_196,_197){var _198=B(_sk(_195,_196));return new F(function(){return _18Z(B(_sk(B(_sk(_194,_197)),B(_18l(_198)))),B(_18f(_198)));});},_199=function(_19a,_19b,_19c){var _19d=new T(function(){if(!B(_gs(_19c,_sQ))){var _19e=B(_gJ(_19b,_19c));return new T2(0,_19e.a,_19e.b);}else{return E(_dZ);}}),_19f=new T(function(){return B(A2(_lj,B(_s9(B(_s7(_19a)))),new T(function(){return E(E(_19d).a);})));});return new T2(0,_19f,new T(function(){return new T2(0,E(E(_19d).b),E(_19c));}));},_19g=function(_19h,_19i,_19j){var _19k=B(_199(_19h,_19i,_19j)),_19l=_19k.a,_19m=E(_19k.b);if(!B(_hc(B(_sk(_19m.a,_f0)),B(_sk(_sQ,_19m.b))))){return E(_19l);}else{var _19n=B(_s9(B(_s7(_19h))));return new F(function(){return A3(_sM,_19n,_19l,new T(function(){return B(A2(_lj,_19n,_f0));}));});}},_19o=479723520,_19p=40233135,_19q=new T2(1,_19p,_Z),_19r=new T2(1,_19o,_19q),_19s=new T(function(){return B(_169(_AD,_19r));}),_19t=new T1(0,40587),_19u=function(_19v){var _19w=new T(function(){var _19x=B(_193(_19v,_f0,_16g,_f0)),_19y=B(_193(_19s,_f0,_16g,_f0)),_19z=B(_193(_19x.a,_19x.b,_19y.a,_19y.b));return B(_19g(_18K,_19z.a,_19z.b));});return new T2(0,new T(function(){return B(_gA(_19t,_19w));}),new T(function(){return B(_iT(_19v,B(_18M(_16h,B(_sk(_19w,_16g)),_19s))));}));},_19A=function(_19B,_){var _19C=__get(_19B,0),_19D=__get(_19B,1),_19E=Number(_19C),_19F=jsTrunc(_19E),_19G=Number(_19D),_19H=jsTrunc(_19G);return new T2(0,_19F,_19H);},_19I=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_19J=660865024,_19K=465661287,_19L=new T2(1,_19K,_Z),_19M=new T2(1,_19J,_19L),_19N=new T(function(){return B(_169(_AD,_19M));}),_19O=function(_){var _19P=__app0(E(_19I)),_19Q=B(_19A(_19P,_));return new T(function(){var _19R=E(_19Q);if(!B(_gs(_19N,_18L))){return B(_gA(B(_sk(B(_eW(E(_19R.a))),_16g)),B(_17c(B(_sk(B(_sk(B(_eW(E(_19R.b))),_16g)),_16g)),_19N))));}else{return E(_dZ);}});},_19S=new T(function(){return B(err(_wC));}),_19T=new T(function(){return B(err(_wy));}),_19U=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_19V=new T1(0,1),_19W=new T1(0,10),_19X=function(_19Y){while(1){var _19Z=E(_19Y);if(!_19Z._){_19Y=new T1(1,I_fromInt(_19Z.a));continue;}else{return new F(function(){return I_toString(_19Z.a);});}}},_1a0=function(_1a1,_1a2){return new F(function(){return _x(fromJSStr(B(_19X(_1a1))),_1a2);});},_1a3=new T1(0,0),_1a4=function(_1a5,_1a6,_1a7){if(_1a5<=6){return new F(function(){return _1a0(_1a6,_1a7);});}else{if(!B(_hc(_1a6,_1a3))){return new F(function(){return _1a0(_1a6,_1a7);});}else{return new T2(1,_G,new T(function(){return B(_x(fromJSStr(B(_19X(_1a6))),new T2(1,_F,_1a7)));}));}}},_1a8=function(_1a9){return new F(function(){return _1a4(0,_1a9,_Z);});},_1aa=new T(function(){return B(_gs(_19W,_18L));}),_1ab=function(_1ac){while(1){if(!B(_gs(_1ac,_18L))){if(!E(_1aa)){if(!B(_gs(B(_17A(_1ac,_19W)),_18L))){return new F(function(){return _1a8(_1ac);});}else{var _1ad=B(_17c(_1ac,_19W));_1ac=_1ad;continue;}}else{return E(_dZ);}}else{return __Z;}}},_1ae=46,_1af=48,_1ag=function(_1ah,_1ai,_1aj){if(!B(_hc(_1aj,_18L))){var _1ak=B(A1(_1ah,_1aj));if(!B(_gs(_1ak,_18L))){var _1al=B(_17n(_1aj,_1ak)),_1am=_1al.b,_1an=new T(function(){var _1ao=Math.log(B(_jR(_1ak)))/Math.log(10),_1ap=_1ao&4294967295,_1aq=function(_1ar){if(_1ar>=0){var _1as=E(_1ar);if(!_1as){var _1at=B(_17c(B(_iT(B(_gA(B(_sk(_1am,_f0)),_1ak)),_19V)),_1ak));}else{var _1at=B(_17c(B(_iT(B(_gA(B(_sk(_1am,B(_sA(_19W,_1as)))),_1ak)),_19V)),_1ak));}var _1au=function(_1av){var _1aw=B(_1a4(0,_1at,_Z)),_1ax=_1ar-B(_qy(_1aw,0))|0;if(0>=_1ax){if(!E(_1ai)){return E(_1aw);}else{return new F(function(){return _1ab(_1at);});}}else{var _1ay=new T(function(){if(!E(_1ai)){return E(_1aw);}else{return B(_1ab(_1at));}}),_1az=function(_1aA){var _1aB=E(_1aA);return (_1aB==1)?E(new T2(1,_1af,_1ay)):new T2(1,_1af,new T(function(){return B(_1az(_1aB-1|0));}));};return new F(function(){return _1az(_1ax);});}};if(!E(_1ai)){var _1aC=B(_1au(_));return (_1aC._==0)?__Z:new T2(1,_1ae,_1aC);}else{if(!B(_gs(_1at,_18L))){var _1aD=B(_1au(_));return (_1aD._==0)?__Z:new T2(1,_1ae,_1aD);}else{return __Z;}}}else{return E(_tw);}};if(_1ap>=_1ao){return B(_1aq(_1ap));}else{return B(_1aq(_1ap+1|0));}},1);return new F(function(){return _x(B(_1a4(0,_1al.a,_Z)),_1an);});}else{return E(_dZ);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_1ag(_1ah,_1ai,B(_jy(_1aj))));}));});}},_1aE=function(_1aF,_1aG,_){var _1aH=B(_19O(_)),_1aI=new T(function(){var _1aJ=new T(function(){var _1aK=new T(function(){var _1aL=B(_x(B(_1ag(_16h,_AD,B(_19u(_1aH)).b)),_16j));if(!_1aL._){return E(_XS);}else{var _1aM=B(_XN(_1aL.a,_1aL.b));if(!_1aM._){return B(_16o(_Z,_Z,_Zw));}else{var _1aN=_1aM.a,_1aO=E(_1aM.b);if(!_1aO._){return B(_16o(new T2(1,_1aN,_Z),_Z,_Zw));}else{var _1aP=E(_1aN),_1aQ=new T(function(){var _1aR=B(_Lc(46,_1aO.a,_1aO.b));return new T2(0,_1aR.a,_1aR.b);});if(E(_1aP)==46){return B(_16o(_Z,new T2(1,new T(function(){return E(E(_1aQ).a);}),new T(function(){return E(E(_1aQ).b);})),_Zw));}else{return B(_16o(new T2(1,_1aP,new T(function(){return E(E(_1aQ).a);})),new T(function(){return E(E(_1aQ).b);}),_Zw));}}}}}),_1aS=B(_Kk(B(_wH(_19U,_1aK))));if(!_1aS._){return E(_19T);}else{if(!E(_1aS.b)._){return B(_tT(3,B(_H(0,E(_1aS.a)+(imul(E(_1aG),E(_1aF)-1|0)|0)|0,_Z))));}else{return E(_19S);}}}),_1aT=B(_Kk(B(_wH(_19U,_1aJ))));if(!_1aT._){return E(_19T);}else{if(!E(_1aT.b)._){return E(_1aT.a);}else{return E(_19S);}}});return new T2(0,new T(function(){return B(_eA(_1aI,_1aF));}),_1aI);},_1aU=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1aV=function(_1aW,_1aX,_1aY,_1aZ,_){var _1b0=__app1(E(_kM),_1aZ),_1b1=__app3(E(_1aU),_1aZ,E(_1aW),E(_1aX)),_1b2=B(A2(_1aY,_1aZ,_)),_1b3=__app1(E(_kL),_1aZ);return new F(function(){return _kK(_);});},_1b4=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_1b5=function(_1b6,_1b7,_1b8,_1b9,_){var _1ba=__app4(E(_1b4),_1b9,_1b6,_1b7,_1b8);return new F(function(){return _kK(_);});},_1bb=2,_1bc=function(_1bd,_1be,_1bf,_1bg,_1bh,_1bi,_){var _1bj=function(_1bk,_){return new F(function(){return _1aV(_1bb,_1bb,function(_1bl,_){return new F(function(){return _1b5(B(_aW(_1be,E(_1bi))),0,0,E(_1bl),_);});},E(_1bk),_);});};return new F(function(){return _kX(new T(function(){return E(_1bf)-E(_1bg)*16;},1),new T(function(){return E(_1bh)*20;},1),_1bj,_1bd,_);});},_1bm=1,_1bn=new T(function(){return B(_aW(_n9,1));}),_1bo=function(_1bp){return E(_1bp).d;},_1bq=function(_1br,_1bs,_1bt,_1bu,_1bv,_1bw,_){var _1bx=new T(function(){return E(E(_1bw).s);}),_1by=new T(function(){return E(E(_1bx).a);}),_1bz=new T(function(){if(!B(_et(E(_1bw).t,10))){var _1bA=E(E(_1bx).b);if(!(_1bA%2)){return _1bA+1|0;}else{return _1bA-1|0;}}else{return E(E(_1bx).b);}}),_1bB=new T(function(){var _1bC=E(_1bw);return {_:0,a:E(_1bC.a),b:E(_1bC.b),c:E(_1bC.c),d:E(_1bC.d),e:E(_1bC.e),f:E(_1bC.f),g:E(_1bC.g),h:E(_1bC.h),i:_1bC.i,j:_1bC.j,k:_1bC.k,l:_1bC.l,m:E(_1bC.m),n:_1bC.n,o:E(_1bC.o),p:E(_1bC.p),q:_1bC.q,r:E(_1bC.r),s:E(new T2(0,_1by,_1bz)),t:_1bC.t,u:E(_1bC.u),v:E(_1bC.v)};}),_1bD=new T(function(){return E(E(_1bB).a);}),_1bE=new T(function(){return E(E(_1bB).b);}),_1bF=new T(function(){return E(E(_1bE).a);}),_1bG=new T(function(){var _1bH=E(_1bt)/16,_1bI=_1bH&4294967295;if(_1bH>=_1bI){return _1bI-2|0;}else{return (_1bI-1|0)-2|0;}}),_1bJ=B(_rv(_1br,_1bs,new T(function(){return B(_f9(_1bG,_1bF));}),_rU,new T(function(){return E(E(_1bD).b);}),_)),_1bK=new T(function(){return E(E(E(_1bB).a).a);}),_1bL=B(A(_qT,[_1br,new T(function(){if(E(E(_1bD).e)==32){return E(_rS);}else{return E(_rT);}}),new T(function(){return ((E(E(_1bK).a)+E(_1bG)|0)-E(_1bF)|0)+1|0;},1),new T(function(){return (E(E(_1bK).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1bo(_1bD));}),_Z),_])),_1bM=E(_1bB),_1bN=_1bM.c,_1bO=_1bM.k,_1bP=E(_1bM.u),_1bQ=new T(function(){var _1bR=E(_1bt)/28,_1bS=_1bR&4294967295;if(_1bR>=_1bS){return (_1bS-1|0)+_1bO|0;}else{return ((_1bS-1|0)-1|0)+_1bO|0;}}),_1bT=new T(function(){return (2+E(E(_1bE).b)|0)+3|0;}),_1bU=new T2(0,_1br,_1bs),_1bV=function(_){var _1bW=function(_){var _1bX=function(_){var _1bY=B(_1bc(_1br,new T(function(){return E(E(_1bv).b);},1),_1bt,new T(function(){return E(_1bF)+10|0;},1),_rU,new T(function(){return (imul(E(_1by),8)|0)+E(_1bz)|0;},1),_));return _1bM;};if(!E(_1bM.p)._){return new F(function(){return _1bX(_);});}else{var _1bZ=B(A(_qT,[_1br,_1bn,_1bm,_1bm,B(_H(0,_1bM.q,_Z)),_]));return new F(function(){return _1bX(_);});}};if(!E(_1bP.g)){return new F(function(){return _1bW(_);});}else{var _1c0=B(_nf(_1bU,_1bu,0,_1bT,_1bQ,_1bT,B(_11G(_1bN,new T(function(){return B(_aj(_wq,_1bM.m));},1),_1bM.n)),_));return new F(function(){return _1bW(_);});}};if(!E(_1bP.c)){var _1c1=B(_nf(_1bU,_1bu,0,_1bT,_1bQ,_1bT,_1bN,_));return new F(function(){return _1bV(_);});}else{return new F(function(){return _1bV(_);});}},_1c2=function(_1c3,_1c4){while(1){var _1c5=E(_1c4);if(!_1c5._){return __Z;}else{var _1c6=_1c5.b,_1c7=E(_1c3);if(_1c7==1){return E(_1c6);}else{_1c3=_1c7-1|0;_1c4=_1c6;continue;}}}},_1c8=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1c9=new T(function(){return B(err(_1c8));}),_1ca=0,_1cb=function(_1cc,_1cd,_1ce){return new F(function(){return _H(E(_1cc),E(_1cd),_1ce);});},_1cf=function(_1cg,_1ch){return new F(function(){return _H(0,E(_1cg),_1ch);});},_1ci=function(_1cj,_1ck){return new F(function(){return _2C(_1cf,_1cj,_1ck);});},_1cl=new T3(0,_1cb,_aG,_1ci),_1cm=0,_1cn=new T(function(){return B(unCStr(" out of range "));}),_1co=new T(function(){return B(unCStr("}.index: Index "));}),_1cp=new T(function(){return B(unCStr("Ix{"));}),_1cq=new T2(1,_F,_Z),_1cr=new T2(1,_F,_1cq),_1cs=0,_1ct=function(_1cu){return E(E(_1cu).a);},_1cv=function(_1cw,_1cx,_1cy,_1cz,_1cA){var _1cB=new T(function(){var _1cC=new T(function(){var _1cD=new T(function(){var _1cE=new T(function(){var _1cF=new T(function(){return B(A3(_wk,_aC,new T2(1,new T(function(){return B(A3(_1ct,_1cy,_1cs,_1cz));}),new T2(1,new T(function(){return B(A3(_1ct,_1cy,_1cs,_1cA));}),_Z)),_1cr));});return B(_x(_1cn,new T2(1,_G,new T2(1,_G,_1cF))));});return B(A(_1ct,[_1cy,_1cm,_1cx,new T2(1,_F,_1cE)]));});return B(_x(_1co,new T2(1,_G,_1cD)));},1);return B(_x(_1cw,_1cC));},1);return new F(function(){return err(B(_x(_1cp,_1cB)));});},_1cG=function(_1cH,_1cI,_1cJ,_1cK,_1cL){return new F(function(){return _1cv(_1cH,_1cI,_1cL,_1cJ,_1cK);});},_1cM=function(_1cN,_1cO,_1cP,_1cQ){var _1cR=E(_1cP);return new F(function(){return _1cG(_1cN,_1cO,_1cR.a,_1cR.b,_1cQ);});},_1cS=function(_1cT,_1cU,_1cV,_1cW){return new F(function(){return _1cM(_1cW,_1cV,_1cU,_1cT);});},_1cX=new T(function(){return B(unCStr("Int"));}),_1cY=function(_1cZ,_1d0,_1d1){return new F(function(){return _1cS(_1cl,new T2(0,_1d0,_1d1),_1cZ,_1cX);});},_1d2=new T(function(){return B(unCStr("Negative range size"));}),_1d3=new T(function(){return B(err(_1d2));}),_1d4=function(_1d5){var _1d6=B(A1(_1d5,_));return E(_1d6);},_1d7=function(_1d8,_1d9,_1da,_){var _1db=E(_1d8);if(!_1db){return new T2(0,_Z,_1d9);}else{var _1dc=new T(function(){return B(_qy(_1da,0))-1|0;}),_1dd=B(_1aE(new T(function(){return E(_1dc)+1|0;}),_1d9,_)),_1de=E(_1dd),_1df=_1de.a,_1dg=_1de.b,_1dh=new T(function(){var _1di=E(_1df);if(B(_qy(_1da,0))>=(_1di+1|0)){var _1dj=new T(function(){var _1dk=_1di+1|0;if(_1dk>0){return B(_1c2(_1dk,_1da));}else{return E(_1da);}});if(0>=_1di){return E(_1dj);}else{var _1dl=function(_1dm,_1dn){var _1do=E(_1dm);if(!_1do._){return E(_1dj);}else{var _1dp=_1do.a,_1dq=E(_1dn);return (_1dq==1)?new T2(1,_1dp,_1dj):new T2(1,_1dp,new T(function(){return B(_1dl(_1do.b,_1dq-1|0));}));}};return B(_1dl(_1da,_1di));}}else{return E(_1da);}}),_1dr=B(_1d7(_1db-1|0,_1dg,_1dh,_)),_1ds=new T(function(){var _1dt=function(_){var _1du=E(_1dc),_1dv=function(_1dw){if(_1dw>=0){var _1dx=newArr(_1dw,_1c9),_1dy=_1dx,_1dz=E(_1dw);if(!_1dz){return new T4(0,E(_1ca),E(_1du),0,_1dy);}else{var _1dA=function(_1dB,_1dC,_){while(1){var _1dD=E(_1dB);if(!_1dD._){return E(_);}else{var _=_1dy[_1dC]=_1dD.a;if(_1dC!=(_1dz-1|0)){var _1dE=_1dC+1|0;_1dB=_1dD.b;_1dC=_1dE;continue;}else{return E(_);}}}},_=B(_1dA(_1da,0,_));return new T4(0,E(_1ca),E(_1du),_1dz,_1dy);}}else{return E(_1d3);}};if(0>_1du){return new F(function(){return _1dv(0);});}else{return new F(function(){return _1dv(_1du+1|0);});}},_1dF=B(_1d4(_1dt)),_1dG=E(_1dF.a),_1dH=E(_1dF.b),_1dI=E(_1df);if(_1dG>_1dI){return B(_1cY(_1dI,_1dG,_1dH));}else{if(_1dI>_1dH){return B(_1cY(_1dI,_1dG,_1dH));}else{return E(_1dF.d[_1dI-_1dG|0]);}}});return new T2(0,new T2(1,_1ds,new T(function(){return B(_wq(_1dr));})),_1dg);}},_1dJ=function(_1dK,_1dL){while(1){var _1dM=E(_1dK);if(!_1dM._){return E(_1dL);}else{_1dK=_1dM.b;_1dL=_1dM.a;continue;}}},_1dN=function(_1dO,_1dP,_1dQ){return new F(function(){return _1dJ(_1dP,_1dO);});},_1dR=function(_1dS,_1dT){while(1){var _1dU=E(_1dS);if(!_1dU._){return E(_1dT);}else{_1dS=_1dU.b;_1dT=_1dU.a;continue;}}},_1dV=function(_1dW,_1dX,_1dY){return new F(function(){return _1dR(_1dX,_1dW);});},_1dZ=function(_1e0,_1e1){while(1){var _1e2=E(_1e1);if(!_1e2._){return __Z;}else{var _1e3=_1e2.b,_1e4=E(_1e0);if(_1e4==1){return E(_1e3);}else{_1e0=_1e4-1|0;_1e1=_1e3;continue;}}}},_1e5=function(_1e6,_1e7){var _1e8=new T(function(){var _1e9=_1e6+1|0;if(_1e9>0){return B(_1dZ(_1e9,_1e7));}else{return E(_1e7);}});if(0>=_1e6){return E(_1e8);}else{var _1ea=function(_1eb,_1ec){var _1ed=E(_1eb);if(!_1ed._){return E(_1e8);}else{var _1ee=_1ed.a,_1ef=E(_1ec);return (_1ef==1)?new T2(1,_1ee,_1e8):new T2(1,_1ee,new T(function(){return B(_1ea(_1ed.b,_1ef-1|0));}));}};return new F(function(){return _1ea(_1e7,_1e6);});}},_1eg=new T(function(){return B(unCStr(":"));}),_1eh=function(_1ei){var _1ej=E(_1ei);if(!_1ej._){return __Z;}else{var _1ek=new T(function(){return B(_x(_1eg,new T(function(){return B(_1eh(_1ej.b));},1)));},1);return new F(function(){return _x(_1ej.a,_1ek);});}},_1el=function(_1em,_1en){var _1eo=new T(function(){return B(_x(_1eg,new T(function(){return B(_1eh(_1en));},1)));},1);return new F(function(){return _x(_1em,_1eo);});},_1ep=function(_1eq){return new F(function(){return _Pu("Check.hs:173:7-35|(co : na : xs)");});},_1er=new T(function(){return B(_1ep(_));}),_1es=new T(function(){return B(err(_wy));}),_1et=new T(function(){return B(err(_wC));}),_1eu=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_1ev=0,_1ew=new T(function(){return B(unCStr("!"));}),_1ex=function(_1ey,_1ez){var _1eA=E(_1ez);if(!_1eA._){return E(_1er);}else{var _1eB=E(_1eA.b);if(!_1eB._){return E(_1er);}else{var _1eC=E(_1eA.a),_1eD=new T(function(){var _1eE=B(_Lc(58,_1eB.a,_1eB.b));return new T2(0,_1eE.a,_1eE.b);}),_1eF=function(_1eG,_1eH,_1eI){var _1eJ=function(_1eK){if((_1ey+1|0)!=_1eK){return new T3(0,_1ey+1|0,_1eH,_1eA);}else{var _1eL=E(_1eI);return (_1eL._==0)?new T3(0,_1ev,_1eH,_Z):new T3(0,_1ev,_1eH,new T(function(){var _1eM=B(_1el(_1eL.a,_1eL.b));if(!_1eM._){return E(_XS);}else{return B(_XN(_1eM.a,_1eM.b));}}));}};if(!B(_uV(_1eG,_1ew))){var _1eN=B(_Kk(B(_wH(_1eu,_1eG))));if(!_1eN._){return E(_1es);}else{if(!E(_1eN.b)._){return new F(function(){return _1eJ(E(_1eN.a));});}else{return E(_1et);}}}else{return new F(function(){return _1eJ( -1);});}};if(E(_1eC)==58){return new F(function(){return _1eF(_Z,new T(function(){return E(E(_1eD).a);}),new T(function(){return E(E(_1eD).b);}));});}else{var _1eO=E(_1eD),_1eP=E(_1eO.b);if(!_1eP._){return E(_1er);}else{return new F(function(){return _1eF(new T2(1,_1eC,_1eO.a),_1eP.a,_1eP.b);});}}}}},_1eQ=function(_1eR,_1eS){while(1){var _1eT=E(_1eS);if(!_1eT._){return __Z;}else{var _1eU=_1eT.b,_1eV=E(_1eR);if(_1eV==1){return E(_1eU);}else{_1eR=_1eV-1|0;_1eS=_1eU;continue;}}}},_1eW=function(_1eX,_1eY,_1eZ){var _1f0=new T2(1,_1eY,new T(function(){var _1f1=_1eX+1|0;if(_1f1>0){return B(_1eQ(_1f1,_1eZ));}else{return E(_1eZ);}}));if(0>=_1eX){return E(_1f0);}else{var _1f2=function(_1f3,_1f4){var _1f5=E(_1f3);if(!_1f5._){return E(_1f0);}else{var _1f6=_1f5.a,_1f7=E(_1f4);return (_1f7==1)?new T2(1,_1f6,_1f0):new T2(1,_1f6,new T(function(){return B(_1f2(_1f5.b,_1f7-1|0));}));}};return new F(function(){return _1f2(_1eZ,_1eX);});}},_1f8=new T2(0,_Xv,_Ii),_1f9=function(_1fa,_1fb,_1fc){while(1){var _1fd=E(_1fc);if(!_1fd._){return E(_1f8);}else{var _1fe=_1fd.b,_1ff=E(_1fd.a),_1fg=E(_1ff.a);if(_1fa!=E(_1fg.a)){_1fc=_1fe;continue;}else{if(_1fb!=E(_1fg.b)){_1fc=_1fe;continue;}else{return E(_1ff.b);}}}}},_1fh=function(_1fi,_1fj){while(1){var _1fk=E(_1fj);if(!_1fk._){return __Z;}else{var _1fl=_1fk.b,_1fm=E(_1fi);if(_1fm==1){return E(_1fl);}else{_1fi=_1fm-1|0;_1fj=_1fl;continue;}}}},_1fn=function(_1fo,_1fp,_1fq){var _1fr=E(_1fo);if(_1fr==1){return E(_1fq);}else{return new F(function(){return _1fh(_1fr-1|0,_1fq);});}},_1fs=function(_1ft,_1fu,_1fv){return new T2(1,new T(function(){if(0>=_1ft){return __Z;}else{return B(_tT(_1ft,new T2(1,_1fu,_1fv)));}}),new T(function(){if(_1ft>0){return B(_1fw(_1ft,B(_1fn(_1ft,_1fu,_1fv))));}else{return B(_1fs(_1ft,_1fu,_1fv));}}));},_1fw=function(_1fx,_1fy){var _1fz=E(_1fy);if(!_1fz._){return __Z;}else{var _1fA=_1fz.a,_1fB=_1fz.b;return new T2(1,new T(function(){if(0>=_1fx){return __Z;}else{return B(_tT(_1fx,_1fz));}}),new T(function(){if(_1fx>0){return B(_1fw(_1fx,B(_1fn(_1fx,_1fA,_1fB))));}else{return B(_1fs(_1fx,_1fA,_1fB));}}));}},_1fC=function(_1fD,_1fE,_1fF){var _1fG=_1fE-1|0;if(0<=_1fG){var _1fH=E(_1fD),_1fI=function(_1fJ){var _1fK=new T(function(){if(_1fJ!=_1fG){return B(_1fI(_1fJ+1|0));}else{return __Z;}}),_1fL=function(_1fM){var _1fN=E(_1fM);return (_1fN._==0)?E(_1fK):new T2(1,new T(function(){var _1fO=E(_1fF);if(!_1fO._){return E(_1f8);}else{var _1fP=_1fO.b,_1fQ=E(_1fO.a),_1fR=E(_1fQ.a),_1fS=E(_1fN.a);if(_1fS!=E(_1fR.a)){return B(_1f9(_1fS,_1fJ,_1fP));}else{if(_1fJ!=E(_1fR.b)){return B(_1f9(_1fS,_1fJ,_1fP));}else{return E(_1fQ.b);}}}}),new T(function(){return B(_1fL(_1fN.b));}));};return new F(function(){return _1fL(B(_cx(0,_1fH-1|0)));});};return new F(function(){return _1fw(_1fH,B(_1fI(0)));});}else{return __Z;}},_1fT=function(_1fU){return new F(function(){return _Pu("Check.hs:72:21-47|(l : r : _)");});},_1fV=new T(function(){return B(_1fT(_));}),_1fW=61,_1fX=function(_1fY,_1fZ){while(1){var _1g0=E(_1fY);if(!_1g0._){return E(_1fZ);}else{_1fY=_1g0.b;_1fZ=_1g0.a;continue;}}},_1g1=function(_1g2,_1g3,_1g4){return new F(function(){return _1fX(_1g3,_1g2);});},_1g5=function(_1g6,_1g7){var _1g8=E(_1g7);if(!_1g8._){return new T2(0,_Z,_Z);}else{var _1g9=_1g8.a;if(!B(A1(_1g6,_1g9))){var _1ga=new T(function(){var _1gb=B(_1g5(_1g6,_1g8.b));return new T2(0,_1gb.a,_1gb.b);});return new T2(0,new T2(1,_1g9,new T(function(){return E(E(_1ga).a);})),new T(function(){return E(E(_1ga).b);}));}else{return new T2(0,_Z,_1g8);}}},_1gc=function(_1gd,_1ge){while(1){var _1gf=E(_1ge);if(!_1gf._){return __Z;}else{if(!B(A1(_1gd,_1gf.a))){return E(_1gf);}else{_1ge=_1gf.b;continue;}}}},_1gg=function(_1gh){var _1gi=_1gh>>>0;if(_1gi>887){var _1gj=u_iswspace(_1gh);return (E(_1gj)==0)?false:true;}else{var _1gk=E(_1gi);return (_1gk==32)?true:(_1gk-9>>>0>4)?(E(_1gk)==160)?true:false:true;}},_1gl=function(_1gm){return new F(function(){return _1gg(E(_1gm));});},_1gn=function(_1go){var _1gp=B(_1gc(_1gl,_1go));if(!_1gp._){return __Z;}else{var _1gq=new T(function(){var _1gr=B(_1g5(_1gl,_1gp));return new T2(0,_1gr.a,_1gr.b);});return new T2(1,new T(function(){return E(E(_1gq).a);}),new T(function(){return B(_1gn(E(_1gq).b));}));}},_1gs=function(_1gt){if(!B(_4H(_lc,_1fW,_1gt))){return new T2(0,_1gt,_Z);}else{var _1gu=new T(function(){var _1gv=E(_1gt);if(!_1gv._){return E(_1fV);}else{var _1gw=E(_1gv.b);if(!_1gw._){return E(_1fV);}else{var _1gx=_1gw.a,_1gy=_1gw.b,_1gz=E(_1gv.a);if(E(_1gz)==61){return new T2(0,_Z,new T(function(){return E(B(_Lc(61,_1gx,_1gy)).a);}));}else{var _1gA=B(_Lc(61,_1gx,_1gy)),_1gB=E(_1gA.b);if(!_1gB._){return E(_1fV);}else{return new T2(0,new T2(1,_1gz,_1gA.a),_1gB.a);}}}}});return new T2(0,new T(function(){var _1gC=B(_1gn(E(_1gu).a));if(!_1gC._){return __Z;}else{return B(_1g1(_1gC.a,_1gC.b,_Zw));}}),new T(function(){var _1gD=B(_1gn(E(_1gu).b));if(!_1gD._){return __Z;}else{return E(_1gD.a);}}));}},_1gE=function(_1gF,_1gG){return new F(function(){return _1e5(E(_1gF),_1gG);});},_1gH=function(_1gI){var _1gJ=E(_1gI);if(!_1gJ._){return new T2(0,_Z,_Z);}else{var _1gK=E(_1gJ.a),_1gL=new T(function(){var _1gM=B(_1gH(_1gJ.b));return new T2(0,_1gM.a,_1gM.b);});return new T2(0,new T2(1,_1gK.a,new T(function(){return E(E(_1gL).a);})),new T2(1,_1gK.b,new T(function(){return E(E(_1gL).b);})));}},_1gN=new T(function(){return B(unCStr("\u570b\uff1a\u3053\u304f\uff1a\u53f2\uff1a\u3057\uff1a\u4e26\uff1a\u306a\u3089\uff1a\u3079\u66ff\uff1a\u304b\uff1a\u3078\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_1gO=new T(function(){return B(unCStr("t0"));}),_1gP=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u30de\u30c3\u30d7\u4e0a\u306e\uff20\u3092\u52d5\uff1a\u3046\u3054\uff1a\u304b\u3057\u307e\u3059\u3002\n\u753b\uff1a\u304c\uff1a\u9762\uff1a\u3081\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u4e0b\uff1a\u304b\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u5de6\uff1a\u3072\u3060\u308a\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u30fb\u53f3\uff1a\u307f\u304e\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u306a\u3069\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3068\uff20\u306f\u305d\u306e\u65b9\uff1a\u306f\u3046\uff1a\u5411\uff1a\u304b\u3046\uff1a\u3078\u52d5\u304d\u307e\u3059\u3002\n{e.ea.m1:t1}{e.eb.m1:t1}{e.ec.m1:t1}"));}),_1gQ=new T2(0,_1gO,_1gP),_1gR=new T(function(){return B(unCStr("t1"));}),_1gS=new T(function(){return B(unCStr("\n\u3053\u308c\u3089\u306e\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u306e\u65b9\u5411\u3078\u884c\uff1a\u3044\uff1a\u304f\u3068 \u3042\u306a\u305f\u306f \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 <\u6301\uff1a\u3082\uff1a\u3063\u305f> \u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u306b\u306a\u308a\u307e\u3059\u3002\n\u3053\u306e\u3068\u304d\uff20\u306e\u8272\uff1a\u3044\u308d\uff1a\u304c\u6fc3\uff1a\u3053\uff1a\u304f\u306a\u3063\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f \uff20\u3092\u3069\u3053\u304b \u5225\uff1a\u3079\u3064\uff1a\u306e\u3068\u3053\u308d\u3078\u6301\u3063\u3066\u3044\u304d \u753b\u9762\u306e\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u90e8\uff1a\u3076\uff1a\u3092\u30bf\u30c3\u30d7\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n{da}{e.oa.m1:t2}{e.ob.m1:t2}{e.oc.m1:t2}"));}),_1gT=new T2(0,_1gR,_1gS),_1gU=new T(function(){return B(unCStr("t2"));}),_1gV=new T(function(){return B(unCStr("\n{da}\n\u3053\u306e\u3068\u304d \u6301\u3063\u3066\u3090\u305f\u6587\u5b57\u304c\u958b\uff1a\u304b\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3055\u308c \u30de\u30c3\u30d7\u4e0a\u306b \u7f6e\uff1a\u304a\uff1a\u304b\u308c\u305f\u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u554f\u984c\u3092\u89e3\uff1a\u3068\uff1a\u304f\u3068\u304d \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 \u30a4\u30b3\u30fc\u30eb <\uff1d>\u306e\u53f3\uff1a\u307f\u304e\uff1a\u306b \u5de6\uff1a\u3072\u3060\u308a\uff1a\u304b\u3089\u9806\uff1a\u3058\u3085\u3093\uff1a\u756a\uff1a\u3070\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u304c\u3042\u308a\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f\u554f\u984c\u3092\u59cb\uff1a\u306f\u3058\uff1a\u3081\u307e\u3059\u3002{e.X.m1:t3}"));}),_1gW=new T2(0,_1gU,_1gV),_1gX=new T(function(){return B(unCStr("t3"));}),_1gY=new T(function(){return B(unCStr("\n\u3088\u308d\u3057\u3044\u3067\u3059\u304b\uff1f{ch.\u306f\u3044,t4.\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u304b\u3089,t0}"));}),_1gZ=new T2(0,_1gX,_1gY),_1h0=new T(function(){return B(unCStr("t4"));}),_1h1=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f\u59cb\u3081\u307e\u3059 {e.X.jl0}\n{e.X.m1:s0}"));}),_1h2=new T2(0,_1h0,_1h1),_1h3=new T(function(){return B(unCStr("s0"));}),_1h4=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abc.s0c}{e.b=0.m0:s0eq}"));}),_1h5=new T2(0,_1h3,_1h4),_1h6=new T(function(){return B(unCStr("s0eq"));}),_1h7=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1h8=new T2(0,_1h6,_1h7),_1h9=new T(function(){return B(unCStr("s0c"));}),_1ha=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s1}"));}),_1hb=new T2(0,_1h9,_1ha),_1hc=new T(function(){return B(unCStr("s1"));}),_1hd=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.1.z.abc.s1c}{e.b=0.m0:s1eq}"));}),_1he=new T2(0,_1hc,_1hd),_1hf=new T(function(){return B(unCStr("s1eq"));}),_1hg=new T2(0,_1hf,_1h7),_1hh=new T(function(){return B(unCStr("s1c"));}),_1hi=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s2}"));}),_1hj=new T2(0,_1hh,_1hi),_1hk=new T(function(){return B(unCStr("s2"));}),_1hl=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n}"));}),_1hm=new T2(0,_1hk,_1hl),_1hn=new T(function(){return B(unCStr("s2A0"));}),_1ho=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\uff1a\u3058\uff1a\u5206\uff1a\u3076\u3093\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3092\u77e5\uff1a\u3057\uff1a\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1hp=new T2(0,_1hn,_1ho),_1hq=new T(function(){return B(unCStr("s2A1_0"));}),_1hr=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\uff1a\u306a\u3093\uff1a\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1hs=new T2(0,_1hq,_1hr),_1ht=new T(function(){return B(unCStr("s2A1_1"));}),_1hu=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\uff1a\u3080\uff1a\u7406\uff1a\u308a\uff1a\u306b\u77e5\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1hv=new T2(0,_1ht,_1hu),_1hw=new T(function(){return B(unCStr("s2A1_2"));}),_1hx=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1hy=new T2(0,_1hw,_1hx),_1hz=new T(function(){return B(unCStr("s2B0"));}),_1hA=new T(function(){return B(unCStr("\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u306e\u6301\uff1a\u3082\uff1a\u3063\u3066\u3090\u308b\u60c5\uff1a\u3058\u3083\u3046\uff1a\u5831\uff1a\u307b\u3046\uff1a\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\uff1a\u3064\u304f\uff1a\u308b\u306e\u306b\u4f7f\uff1a\u3064\u304b\uff1a\u306f\u308c\u305f\u77f3\uff1a\u3044\u3057\uff1a\u306f \u7a7a\uff1a\u304f\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306b\u6301\uff1a\u3082\uff1a\u3061\u4e0a\uff1a\u3042\uff1a\u3052\u3089\u308c\u3066 \u7d44\uff1a\u304f\uff1a\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1hB=new T2(0,_1hz,_1hA),_1hC=new T(function(){return B(unCStr("s2C0"));}),_1hD=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3092\u8a2a\uff1a\u304a\u3068\u3065\uff1a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u306f \u305d\u306e\u5f62\uff1a\u3051\u3044\uff1a\u8de1\uff1a\u305b\u304d\uff1a\u304c \u3044\u304f\u3064\u3082\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\uff1a\u304b\u308c\uff1a\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\uff1a\u3072\uff1a\u6280\uff1a\u304e\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\uff1a\u304d\uff1a\u9332\uff1a\u308d\u304f\uff1a\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1hE=new T2(0,_1hC,_1hD),_1hF=new T(function(){return B(unCStr("s2D0"));}),_1hG=new T(function(){return B(unCStr("\n\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u3084 \u50b3\u3078\u308b\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u89c0\uff1a\u304b\u3093\uff1a \u50b3\u3078\u305f\u7576\uff1a\u305f\u3046\uff1a\u6642\uff1a\u3058\uff1a\u306b\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u305f\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3046\uff1a\u306e\u7a2e\uff1a\u3057\u3085\uff1a\u985e\uff1a\u308b\u3044\uff1a\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\uff1a\u3055\u3046\uff1a\u7576\uff1a\u305f\u3046\uff1a\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u305f\u50b3\uff1a\u3064\u305f\uff1a\u3078\u65b9\uff1a\u304b\u305f\uff1a\u304c\u70ba\uff1a\u306a\uff1a\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\uff1a\u304b\u304f\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u306a\u6b74\u53f2\u306f\u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u305b\u305a \u6b74\u53f2\u3092\u5b78\uff1a\u307e\u306a\uff1a\u3076\u610f\uff1a\u3044\uff1a\u7fa9\uff1a\u304e\uff1a\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\uff1a\u306a\u3063\uff1a\u5f97\uff1a\u3068\u304f\uff1a\u3057 \u4ed6\uff1a\u307b\u304b\uff1a\u306e\u4eba\uff1a\u3072\u3068\uff1a\u9054\uff1a\u305f\u3061\uff1a\u3068\u5171\uff1a\u304d\u3087\u3046\uff1a\u6709\uff1a\u3044\u3046\n\uff1a\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\uff1a\u3058\uff1a\u8eab\uff1a\u3057\u3093\uff1a\u304c\u898b\uff1a\u307f\uff1a\u51fa\uff1a\u3044\u3060\uff1a\u3057 \u7d21\uff1a\u3064\u3080\uff1a\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\uff1a\u3057\uff1a\u7d44\uff1a\u304f\uff1a\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\uff1a\u304b\uff1a\u5024\uff1a\u3061\uff1a\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\uff1a\u3044\uff1a\u304d\u308b\u610f\uff1a\u3044\uff1a\u5473\uff1a\u307f\uff1a\u306b\u3082 \u7e4b\uff1a\u3064\u306a\uff1a\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1hH=new T2(0,_1hF,_1hG),_1hI=new T(function(){return B(unCStr("s2n"));}),_1hJ=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n1.\u9032\u307e\u306a\u3044,s2n0}"));}),_1hK=new T2(0,_1hI,_1hJ),_1hL=new T(function(){return B(unCStr("s2n0"));}),_1hM=new T(function(){return B(unCStr("\n\u884c\u304f\u306e\u3092\u3084\u3081\u307e\u3057\u305f\u3002"));}),_1hN=new T2(0,_1hL,_1hM),_1hO=new T(function(){return B(unCStr("s8I2"));}),_1hP=new T(function(){return B(unCStr("\n\u3067\u306f \u3088\u3044\u4e00\uff1a\u3044\u3061\uff1a\u65e5\uff1a\u306b\u3061\uff1a\u3092\u30fb\u30fb\u30fb\u3002{e.X.l}"));}),_1hQ=new T2(0,_1hO,_1hP),_1hR=new T2(1,_1hQ,_Z),_1hS=new T(function(){return B(unCStr("s8I1"));}),_1hT=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u59cb\u3081\u307e\u305b\u3046\u3002{da}{e.c8.m1:s0}{e.X.jl0}"));}),_1hU=new T2(0,_1hS,_1hT),_1hV=new T2(1,_1hU,_1hR),_1hW=new T(function(){return B(unCStr("s8I0"));}),_1hX=new T(function(){return B(unCStr("\n\u304a\u3064\u304b\u308c\u3055\u307e\u3067\u3059\u3002\n\u3042\u306a\u305f\u306e\u9ede\uff1a\u3066\u3093\uff1a\u6578\uff1a\u3059\u3046\uff1a\u306f{rs}\n\u9ede\uff1a\u3066\u3093\uff1a\u3067\u3059\u3002\n\u307e\u3046\u3044\u3061\u3069 \u3084\u308a\u307e\u3059\u304b\uff1f{ch.\u3084\u308b,s8I1.\u3084\u3081\u308b,s8I2}"));}),_1hY=new T2(0,_1hW,_1hX),_1hZ=new T2(1,_1hY,_1hV),_1i0=new T(function(){return B(unCStr("s8"));}),_1i1=new T(function(){return B(unCStr("\n\u3060\u308c\u304b\u3090\u307e\u3059\u3002{da}{e.bI.m0:s8I0}"));}),_1i2=new T2(0,_1i0,_1i1),_1i3=new T2(1,_1i2,_1hZ),_1i4=new T(function(){return B(unCStr("s7c"));}),_1i5=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s8}"));}),_1i6=new T2(0,_1i4,_1i5),_1i7=new T2(1,_1i6,_1i3),_1i8=new T(function(){return B(unCStr("s7eq"));}),_1i9=new T2(0,_1i8,_1h7),_1ia=new T2(1,_1i9,_1i7),_1ib=new T(function(){return B(unCStr("s7"));}),_1ic=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcde.s7c}{e.b=0.m0:s7eq}"));}),_1id=new T2(0,_1ib,_1ic),_1ie=new T2(1,_1id,_1ia),_1if=new T(function(){return B(unCStr("s6c"));}),_1ig=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s7}"));}),_1ih=new T2(0,_1if,_1ig),_1ii=new T2(1,_1ih,_1ie),_1ij=new T(function(){return B(unCStr("s6eq"));}),_1ik=new T2(0,_1ij,_1h7),_1il=new T2(1,_1ik,_1ii),_1im=new T(function(){return B(unCStr("s6"));}),_1in=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abcde.s6c}{e.b=0.m0:s6eq}"));}),_1io=new T2(0,_1im,_1in),_1ip=new T2(1,_1io,_1il),_1iq=new T(function(){return B(unCStr("s5n1"));}),_1ir=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s6}"));}),_1is=new T2(0,_1iq,_1ir),_1it=new T2(1,_1is,_1ip),_1iu=new T(function(){return B(unCStr("s5n0"));}),_1iv=new T2(0,_1iu,_1hM),_1iw=new T2(1,_1iv,_1it),_1ix=new T(function(){return B(unCStr("s5n"));}),_1iy=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n1.\u9032\u307e\u306a\u3044,s5n0}"));}),_1iz=new T2(0,_1ix,_1iy),_1iA=new T2(1,_1iz,_1iw),_1iB=new T(function(){return B(unCStr("s5H0"));}),_1iC=new T(function(){return B(unCStr("\n\u6211\uff1a\u308f\uff1a\u304c\u570b\uff1a\u304f\u306b\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u7279\uff1a\u3068\u304f\uff1a\u306b\u5f37\uff1a\u3064\u3088\uff1a\u307e\u3063\u305f \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8a9e\uff1a\u3054\uff1a\u306e\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u5de5\uff1a\u3053\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u306f \u305d\u308c\u3092\u4ed5\uff1a\u3057\uff1a\u639b\uff1a\u304b\uff1a\u3051\u305f\u4eba\uff1a\u3072\u3068\uff1a\u306e\u610f\uff1a\u3044\uff1a\u5716\uff1a\u3068\uff1a\u3068\u9006\uff1a\u304e\u3083\u304f\uff1a\u306b \u65e5\u672c\u8a9e\u3092\u5f37\uff1a\u304d\u3083\u3046\uff1a\u5316\uff1a\u304f\u308f\uff1a\u3057 \u305d\u306e\u67d4\uff1a\u3058\u3046\uff1a\u8edf\uff1a\u306a\u3093\uff1a\u3055\u3092 \u3088\u308a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u306b\u767c\uff1a\u306f\u3063\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u3059\u308b\u571f\uff1a\u3069\uff1a\u58cc\uff1a\u3058\u3083\u3046\uff1a\u3092\u4f5c\uff1a\u3064\u304f\uff1a\u3063\u305f\u306e\u3067\u306f\u306a\u3044\u304b\u3068 \u79c1\u306f\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u3066\u3090\u307e\u3059\u3002\n\u3067\u3059\u304b\u3089 \u304b\u306a\u9063\uff1a\u3065\u304b\uff1a\u3072\u3092\u6df7\uff1a\u3053\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3055\u305b\u305f\u308a \u6f22\uff1a\u304b\u3093\uff1a\u5b57\uff1a\u3058\uff1a\u3092\u3068\u3063\u305f\u308a\u3064\u3051\u305f\u308a\u3057\u305f\u3053\u3068\u304c \u9006\u306b\u65e5\u672c\u8a9e\u306e\u5f37\u3055 \u67d4\u8edf\u3055\u306e\u8a3c\uff1a\u3057\u3087\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u3092\u3082\u305f\u3089\u3057\u305f\u3068\u3082\u3044\u3078\u308b\u306e\u3067 \u65e5\u672c\u8a9e\u3092\u6df7\u4e82\u3055\u305b\u305f\u4eba\u3005\u306b \u79c1\u306f\u611f\uff1a\u304b\u3093\uff1a\u8b1d\uff1a\u3057\u3083\uff1a\u3057\u3066\u3090\u308b\u306e\u3067\u3059\u3002"));}),_1iD=new T2(0,_1iB,_1iC),_1iE=new T2(1,_1iD,_1iA),_1iF=new T(function(){return B(unCStr("s5G0"));}),_1iG=new T(function(){return B(unCStr("\n\u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e \u540c\u3058\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u898b\uff1a\u307f\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u9055\uff1a\u3061\u304c\uff1a\u3075\u306e\u306f\n\u4eca\uff1a\u3044\u307e\uff1a \u79c1\u3068 \u3042\u306a\u305f\u304c\u540c\u3058\u5834\u6240\u306b\u3090\u3066 \u305d\u3053\u306b\u5c45\uff1a\u3090\uff1a\u308b\u5225\uff1a\u3081\u3064\uff1a\u306e\u8ab0\uff1a\u3060\u308c\uff1a\u304b\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3059\u308b\u5370\uff1a\u3044\u3093\uff1a\u8c61\uff1a\u3057\u3083\u3046\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u3066\u3090\u308b\u3053\u3068\u3068 \u4f3c\uff1a\u306b\uff1a\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u306f \u81ea\uff1a\u3057\uff1a\u7136\uff1a\u305c\u3093\uff1a\u306a\u3053\u3068\u3067 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306e\u898b\u65b9\u304c\u9055\u3075\u306e\u306f \u5168\uff1a\u307e\u3063\u305f\uff1a\u304f\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u898b\u65b9\u304c\u5168\uff1a\u305c\u3093\uff1a\u7136\uff1a\u305c\u3093\uff1a\u7570\u306a\u3063\u3066\u3090\u3066\u3082 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306f \u5171\uff1a\u304d\u3087\u3046\uff1a\u611f\uff1a\u304b\u3093\uff1a\u3059\u308b\u559c\uff1a\u3088\u308d\u3053\uff1a\u3073\u3092\u5473\uff1a\u3042\u3058\uff1a\u306f\u3046\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1iH=new T2(0,_1iF,_1iG),_1iI=new T2(1,_1iH,_1iE),_1iJ=new T(function(){return B(unCStr("s5F0"));}),_1iK=new T(function(){return B(unCStr("\n\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u306f\u7576\uff1a\u305f\u3046\uff1a\u7136\uff1a\u305c\u3093\uff1a\u3055\u3046\u3067\u3059\u304c \u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3092\u6c7a\uff1a\u304d\uff1a\u3081\u308b\u306e\u3082 \u4eca\uff1a\u3044\u307e\uff1a\u306e\u3042\u306a\u305f\u6b21\uff1a\u3057\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002"));}),_1iL=new T2(0,_1iJ,_1iK),_1iM=new T2(1,_1iL,_1iI),_1iN=new T(function(){return B(unCStr("s5E0"));}),_1iO=new T(function(){return B(unCStr("\n\u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3082\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3082 \u305d\u3057\u3066\u5225\uff1a\u3079\u3064\uff1a\u306e\u4e26\uff1a\u3078\u3044\uff1a\u884c\uff1a\u304b\u3046\uff1a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u3082 \u3059\u3079\u3066\u306f \u4eca\uff1a\u3044\u307e\uff1a \u3053\u3053\u306b\u3042\u308a\u307e\u3059\u3002"));}),_1iP=new T2(0,_1iN,_1iO),_1iQ=new T2(1,_1iP,_1iM),_1iR=new T(function(){return B(unCStr("s5"));}),_1iS=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n}"));}),_1iT=new T2(0,_1iR,_1iS),_1iU=new T2(1,_1iT,_1iQ),_1iV=new T(function(){return B(unCStr("s4c"));}),_1iW=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s5}"));}),_1iX=new T2(0,_1iV,_1iW),_1iY=new T2(1,_1iX,_1iU),_1iZ=new T(function(){return B(unCStr("s4eq"));}),_1j0=new T2(0,_1iZ,_1h7),_1j1=new T2(1,_1j0,_1iY),_1j2=new T(function(){return B(unCStr("s4"));}),_1j3=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s4c}{e.b=0.m0:s4eq}"));}),_1j4=new T2(0,_1j2,_1j3),_1j5=new T2(1,_1j4,_1j1),_1j6=new T(function(){return B(unCStr("s3c"));}),_1j7=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s4}"));}),_1j8=new T2(0,_1j6,_1j7),_1j9=new T2(1,_1j8,_1j5),_1ja=new T(function(){return B(unCStr("s3eq"));}),_1jb=new T2(0,_1ja,_1h7),_1jc=new T2(1,_1jb,_1j9),_1jd=new T(function(){return B(unCStr("s3"));}),_1je=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s3c}{e.b=0.m0:s3eq}"));}),_1jf=new T2(0,_1jd,_1je),_1jg=new T2(1,_1jf,_1jc),_1jh=new T(function(){return B(unCStr("s2n1"));}),_1ji=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s3}"));}),_1jj=new T2(0,_1jh,_1ji),_1jk=new T2(1,_1jj,_1jg),_1jl=new T2(1,_1hN,_1jk),_1jm=new T2(1,_1hK,_1jl),_1jn=new T2(1,_1hH,_1jm),_1jo=new T2(1,_1hE,_1jn),_1jp=new T2(1,_1hB,_1jo),_1jq=new T2(1,_1hy,_1jp),_1jr=new T2(1,_1hv,_1jq),_1js=new T2(1,_1hs,_1jr),_1jt=new T2(1,_1hp,_1js),_1ju=new T2(1,_1hm,_1jt),_1jv=new T2(1,_1hj,_1ju),_1jw=new T2(1,_1hg,_1jv),_1jx=new T2(1,_1he,_1jw),_1jy=new T(function(){return B(unCStr("nubatama"));}),_1jz=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1jA=new T2(0,_1jy,_1jz),_1jB=new T2(1,_1jA,_1jx),_1jC=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1jD=new T(function(){return B(unCStr("msgW"));}),_1jE=new T2(0,_1jD,_1jC),_1jF=new T2(1,_1jE,_1jB),_1jG=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1jH=new T(function(){return B(unCStr("msgR"));}),_1jI=new T2(0,_1jH,_1jG),_1jJ=new T2(1,_1jI,_1jF),_1jK=new T2(1,_1hb,_1jJ),_1jL=new T2(1,_1h8,_1jK),_1jM=new T2(1,_1h5,_1jL),_1jN=new T2(1,_1h2,_1jM),_1jO=new T2(1,_1gZ,_1jN),_1jP=new T2(1,_1gW,_1jO),_1jQ=new T2(1,_1gT,_1jP),_1jR=new T2(1,_1gQ,_1jQ),_1jS=new T(function(){return B(unCStr("initMsg"));}),_1jT=function(_1jU,_1jV){var _1jW=new T(function(){var _1jX=B(_1gH(_1jU));return new T2(0,_1jX.a,_1jX.b);}),_1jY=function(_1jZ){var _1k0=E(_1jZ);if(!_1k0._){return E(_1jW);}else{var _1k1=E(_1k0.a),_1k2=new T(function(){return B(_1jY(_1k0.b));});return new T2(0,new T2(1,_1k1.a,new T(function(){return E(E(_1k2).a);})),new T2(1,_1k1.b,new T(function(){return E(E(_1k2).b);})));}},_1k3=function(_1k4,_1k5,_1k6){var _1k7=new T(function(){return B(_1jY(_1k6));});return new T2(0,new T2(1,_1k4,new T(function(){return E(E(_1k7).a);})),new T2(1,_1k5,new T(function(){return E(E(_1k7).b);})));},_1k8=B(_1k3(_1jS,_1gN,_1jR)),_1k9=_1k8.a;if(!B(_4H(_uj,_1jV,_1k9))){return __Z;}else{return new F(function(){return _aW(_1k8.b,B(_QT(_uj,_1jV,_1k9)));});}},_1ka=5,_1kb=new T2(0,_1ka,_1ka),_1kc=7,_1kd=new T2(0,_1kc,_1ka),_1ke=6,_1kf=new T2(0,_1ka,_1ke),_1kg=new T2(1,_1kf,_Z),_1kh=new T2(1,_1kd,_1kg),_1ki=new T2(1,_1kd,_1kh),_1kj=new T2(1,_1kf,_1ki),_1kk=new T2(1,_1kd,_1kj),_1kl=new T2(1,_1kd,_1kk),_1km=new T2(1,_1kf,_1kl),_1kn=new T2(1,_1kb,_1km),_1ko=new T2(1,_1kb,_1kn),_1kp=2,_1kq=new T2(0,_1kp,_1kp),_1kr=new T2(1,_1kq,_Z),_1ks=new T2(1,_1kq,_1kr),_1kt=new T2(1,_1kq,_1ks),_1ku=new T2(1,_1kq,_1kt),_1kv=new T2(1,_1kq,_1ku),_1kw=new T2(1,_1kq,_1kv),_1kx=new T2(1,_1kq,_1kw),_1ky=new T2(1,_1kq,_1kx),_1kz=new T2(1,_1kq,_1ky),_1kA=new T(function(){return B(unCStr("Int"));}),_1kB=function(_1kC,_1kD,_1kE){return new F(function(){return _1cS(_1cl,new T2(0,_1kD,_1kE),_1kC,_1kA);});},_1kF=new T(function(){return B(unCStr("msgR"));}),_1kG=new T(function(){return B(_1jT(_Z,_1kF));}),_1kH=new T(function(){return B(unCStr("msgW"));}),_1kI=new T(function(){return B(_1jT(_Z,_1kH));}),_1kJ=function(_1kK){var _1kL=E(_1kK);return 0;},_1kM=new T(function(){return B(unCStr("@@@@@@@@@"));}),_1kN=new T(function(){var _1kO=E(_1kM);if(!_1kO._){return E(_rm);}else{return E(_1kO.a);}}),_1kP=122,_1kQ=new T2(0,_1kP,_Io),_1kR=0,_1kS=new T2(0,_1kR,_1kR),_1kT=new T2(0,_1kS,_1kQ),_1kU=61,_1kV=new T2(0,_1kU,_Io),_1kW=1,_1kX=new T2(0,_1kW,_1kR),_1kY=new T2(0,_1kX,_1kV),_1kZ=97,_1l0=new T2(0,_1kZ,_Ii),_1l1=4,_1l2=new T2(0,_1kR,_1l1),_1l3=new T2(0,_1l2,_1l0),_1l4=98,_1l5=new T2(0,_1l4,_Ii),_1l6=new T2(0,_1kp,_1l1),_1l7=new T2(0,_1l6,_1l5),_1l8=99,_1l9=new T2(0,_1l8,_Ii),_1la=new T2(0,_1l1,_1l1),_1lb=new T2(0,_1la,_1l9),_1lc=new T2(1,_1lb,_Z),_1ld=new T2(1,_1l7,_1lc),_1le=new T2(1,_1l3,_1ld),_1lf=new T2(1,_1kY,_1le),_1lg=new T2(1,_1kT,_1lf),_1lh=new T(function(){return B(_1fC(_1ka,5,_1lg));}),_1li=new T(function(){return B(_Pu("Check.hs:142:22-33|(ch : po)"));}),_1lj=new T(function(){return B(_ic("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1lk=110,_1ll=new T2(0,_1lk,_Iu),_1lm=new T2(0,_1l1,_1ka),_1ln=new T2(0,_1lm,_1ll),_1lo=new T2(1,_1ln,_Z),_1lp=new T2(0,_1kp,_1ka),_1lq=66,_1lr=new T2(0,_1lq,_Io),_1ls=new T2(0,_1lp,_1lr),_1lt=new T2(1,_1ls,_1lo),_1lu=3,_1lv=new T2(0,_1kR,_1lu),_1lw=67,_1lx=new T2(0,_1lw,_Io),_1ly=new T2(0,_1lv,_1lx),_1lz=new T2(1,_1ly,_1lt),_1lA=new T2(0,_1l1,_1kW),_1lB=65,_1lC=new T2(0,_1lB,_Io),_1lD=new T2(0,_1lA,_1lC),_1lE=new T2(1,_1lD,_1lz),_1lF=68,_1lG=new T2(0,_1lF,_Io),_1lH=new T2(0,_1kX,_1lG),_1lI=new T2(1,_1lH,_1lE),_1lJ=100,_1lK=new T2(0,_1lJ,_Ii),_1lL=new T2(0,_1ke,_1l1),_1lM=new T2(0,_1lL,_1lK),_1lN=new T2(1,_1lM,_Z),_1lO=new T2(1,_1lb,_1lN),_1lP=new T2(1,_1l7,_1lO),_1lQ=new T2(1,_1l3,_1lP),_1lR=new T2(1,_1kY,_1lQ),_1lS=new T2(1,_1kT,_1lR),_1lT=70,_1lU=new T2(0,_1lT,_Io),_1lV=new T2(0,_1lp,_1lU),_1lW=new T2(1,_1lV,_1lo),_1lX=72,_1lY=new T2(0,_1lX,_Io),_1lZ=new T2(0,_1lv,_1lY),_1m0=new T2(1,_1lZ,_1lW),_1m1=69,_1m2=new T2(0,_1m1,_Io),_1m3=new T2(0,_1lA,_1m2),_1m4=new T2(1,_1m3,_1m0),_1m5=71,_1m6=new T2(0,_1m5,_Io),_1m7=new T2(0,_1kX,_1m6),_1m8=new T2(1,_1m7,_1m4),_1m9=101,_1ma=new T2(0,_1m9,_Ii),_1mb=new T2(0,_1l1,_1kp),_1mc=new T2(0,_1mb,_1ma),_1md=new T2(1,_1mc,_1lQ),_1me=new T2(1,_1kY,_1md),_1mf=new T2(1,_1kT,_1me),_1mg=73,_1mh=new T2(0,_1mg,_Io),_1mi=new T2(0,_1kp,_1kR),_1mj=new T2(0,_1mi,_1mh),_1mk=new T2(1,_1mj,_Z),_1ml=new T2(1,_1mk,_Z),_1mm=new T2(1,_1mf,_1ml),_1mn=new T2(1,_1mf,_1mm),_1mo=new T2(1,_1m8,_1mn),_1mp=new T2(1,_1lS,_1mo),_1mq=new T2(1,_1lS,_1mp),_1mr=new T2(1,_1lI,_1mq),_1ms=new T2(1,_1lg,_1mr),_1mt=new T2(1,_1lg,_1ms),_1mu=function(_1mv){var _1mw=E(_1mv);if(!_1mw._){return __Z;}else{var _1mx=_1mw.b,_1my=E(_1mw.a),_1mz=_1my.b,_1mA=E(_1my.a),_1mB=function(_1mC){if(E(_1mA)==32){return new T2(1,_1my,new T(function(){return B(_1mu(_1mx));}));}else{switch(E(_1mz)){case 0:return new T2(1,new T2(0,_1mA,_Ii),new T(function(){return B(_1mu(_1mx));}));case 1:return new T2(1,new T2(0,_1mA,_IT),new T(function(){return B(_1mu(_1mx));}));case 2:return new T2(1,new T2(0,_1mA,_Iu),new T(function(){return B(_1mu(_1mx));}));case 3:return new T2(1,new T2(0,_1mA,_IA),new T(function(){return B(_1mu(_1mx));}));case 4:return new T2(1,new T2(0,_1mA,_IG),new T(function(){return B(_1mu(_1mx));}));case 5:return new T2(1,new T2(0,_1mA,_J7),new T(function(){return B(_1mu(_1mx));}));case 6:return new T2(1,new T2(0,_1mA,_J0),new T(function(){return B(_1mu(_1mx));}));case 7:return new T2(1,new T2(0,_1mA,_IT),new T(function(){return B(_1mu(_1mx));}));default:return new T2(1,new T2(0,_1mA,_IM),new T(function(){return B(_1mu(_1mx));}));}}};if(E(_1mA)==32){return new F(function(){return _1mB(_);});}else{switch(E(_1mz)){case 0:return new T2(1,new T2(0,_1mA,_IM),new T(function(){return B(_1mu(_1mx));}));case 1:return new F(function(){return _1mB(_);});break;case 2:return new F(function(){return _1mB(_);});break;case 3:return new F(function(){return _1mB(_);});break;case 4:return new F(function(){return _1mB(_);});break;case 5:return new F(function(){return _1mB(_);});break;case 6:return new F(function(){return _1mB(_);});break;case 7:return new F(function(){return _1mB(_);});break;default:return new F(function(){return _1mB(_);});}}}},_1mD=function(_1mE){var _1mF=E(_1mE);return (_1mF._==0)?__Z:new T2(1,new T(function(){return B(_1mu(_1mF.a));}),new T(function(){return B(_1mD(_1mF.b));}));},_1mG=function(_1mH){var _1mI=E(_1mH);if(!_1mI._){return __Z;}else{var _1mJ=_1mI.b,_1mK=E(_1mI.a),_1mL=_1mK.b,_1mM=E(_1mK.a),_1mN=function(_1mO){if(E(_1mM)==32){return new T2(1,_1mK,new T(function(){return B(_1mG(_1mJ));}));}else{switch(E(_1mL)){case 0:return new T2(1,new T2(0,_1mM,_Ii),new T(function(){return B(_1mG(_1mJ));}));case 1:return new T2(1,new T2(0,_1mM,_Io),new T(function(){return B(_1mG(_1mJ));}));case 2:return new T2(1,new T2(0,_1mM,_Iu),new T(function(){return B(_1mG(_1mJ));}));case 3:return new T2(1,new T2(0,_1mM,_IA),new T(function(){return B(_1mG(_1mJ));}));case 4:return new T2(1,new T2(0,_1mM,_IG),new T(function(){return B(_1mG(_1mJ));}));case 5:return new T2(1,new T2(0,_1mM,_J7),new T(function(){return B(_1mG(_1mJ));}));case 6:return new T2(1,new T2(0,_1mM,_J0),new T(function(){return B(_1mG(_1mJ));}));case 7:return new T2(1,new T2(0,_1mM,_Io),new T(function(){return B(_1mG(_1mJ));}));default:return new T2(1,new T2(0,_1mM,_IM),new T(function(){return B(_1mG(_1mJ));}));}}};if(E(_1mM)==32){return new F(function(){return _1mN(_);});}else{if(E(_1mL)==8){return new T2(1,new T2(0,_1mM,_Ii),new T(function(){return B(_1mG(_1mJ));}));}else{return new F(function(){return _1mN(_);});}}}},_1mP=function(_1mQ){var _1mR=E(_1mQ);return (_1mR._==0)?__Z:new T2(1,new T(function(){return B(_1mG(_1mR.a));}),new T(function(){return B(_1mP(_1mR.b));}));},_1mS=function(_1mT,_1mU,_1mV,_1mW,_1mX,_1mY,_1mZ,_1n0,_1n1,_1n2,_1n3,_1n4,_1n5,_1n6,_1n7,_1n8,_1n9,_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx){var _1ny=E(_1mU);if(!_1ny._){return E(_1lj);}else{var _1nz=_1ny.b,_1nA=E(_1ny.a),_1nB=new T(function(){var _1nC=function(_){var _1nD=B(_qy(_1na,0))-1|0,_1nE=function(_1nF){if(_1nF>=0){var _1nG=newArr(_1nF,_1c9),_1nH=_1nG,_1nI=E(_1nF);if(!_1nI){return new T4(0,E(_1ev),E(_1nD),0,_1nH);}else{var _1nJ=function(_1nK,_1nL,_){while(1){var _1nM=E(_1nK);if(!_1nM._){return E(_);}else{var _=_1nH[_1nL]=_1nM.a;if(_1nL!=(_1nI-1|0)){var _1nN=_1nL+1|0;_1nK=_1nM.b;_1nL=_1nN;continue;}else{return E(_);}}}},_=B(_1nJ(_1na,0,_));return new T4(0,E(_1ev),E(_1nD),_1nI,_1nH);}}else{return E(_1d3);}};if(0>_1nD){return new F(function(){return _1nE(0);});}else{return new F(function(){return _1nE(_1nD+1|0);});}},_1nO=B(_1d4(_1nC)),_1nP=E(_1nO.a),_1nQ=E(_1nO.b),_1nR=E(_1mT);if(_1nP>_1nR){return B(_1kB(_1nR,_1nP,_1nQ));}else{if(_1nR>_1nQ){return B(_1kB(_1nR,_1nP,_1nQ));}else{return E(_1nO.d[_1nR-_1nP|0]);}}});switch(E(_1nA)){case 97:var _1nS=new T(function(){var _1nT=E(_1nz);if(!_1nT._){return E(_1li);}else{return new T2(0,_1nT.a,_1nT.b);}}),_1nU=new T(function(){var _1nV=B(_1gs(E(_1nS).b));return new T2(0,_1nV.a,_1nV.b);}),_1nW=B(_Kk(B(_wH(_1eu,new T(function(){return E(E(_1nU).b);})))));if(!_1nW._){return E(_1es);}else{if(!E(_1nW.b)._){var _1nX=new T(function(){var _1nY=B(_Kk(B(_wH(_1eu,new T(function(){return E(E(_1nU).a);})))));if(!_1nY._){return E(_1es);}else{if(!E(_1nY.b)._){return E(_1nY.a);}else{return E(_1et);}}},1);return {_:0,a:E({_:0,a:E(_1mV),b:E(B(_P3(_1nX,E(_1nW.a),new T(function(){return E(E(_1nS).a);}),_Ii,_1mW))),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};}else{return E(_1et);}}break;case 104:return {_:0,a:E({_:0,a:E(_1mV),b:E(B(_1mD(_1mW))),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};case 106:var _1nZ=E(_1nz);if(!_1nZ._){return {_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l: -1,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};}else{if(E(_1nZ.a)==108){var _1o0=E(_1mT),_1o1=B(_Kk(B(_wH(_1eu,_1nZ.b))));return (_1o1._==0)?E(_1es):(E(_1o1.b)._==0)?{_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(B(_1e5(_1o0,_1n9))),f:E(B(_1e5(_1o0,_1na))),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:E(_1o1.a),m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_AD),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)}:E(_1et);}else{var _1o2=B(_Kk(B(_wH(_1eu,_1nZ))));return (_1o2._==0)?E(_1es):(E(_1o2.b)._==0)?{_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:E(_1o2.a),m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)}:E(_1et);}}break;case 108:var _1o3=E(_1mT);return {_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(B(_1e5(_1o3,_1n9))),f:E(B(_1e5(_1o3,_1na))),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_AD),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};case 109:var _1o4=B(_1ex(E(_1nB),_1nz)),_1o5=_1o4.c,_1o6=B(_uV(_1o5,_Z));if(!E(_1o6)){var _1o7=E(_1mT),_1o8=new T(function(){var _1o9=function(_){var _1oa=B(_qy(_1n9,0))-1|0,_1ob=function(_1oc){if(_1oc>=0){var _1od=newArr(_1oc,_1c9),_1oe=_1od,_1of=E(_1oc);if(!_1of){return new T4(0,E(_1ev),E(_1oa),0,_1oe);}else{var _1og=function(_1oh,_1oi,_){while(1){var _1oj=E(_1oh);if(!_1oj._){return E(_);}else{var _=_1oe[_1oi]=_1oj.a;if(_1oi!=(_1of-1|0)){var _1ok=_1oi+1|0;_1oh=_1oj.b;_1oi=_1ok;continue;}else{return E(_);}}}},_=B(_1og(_1n9,0,_));return new T4(0,E(_1ev),E(_1oa),_1of,_1oe);}}else{return E(_1d3);}};if(0>_1oa){return new F(function(){return _1ob(0);});}else{return new F(function(){return _1ob(_1oa+1|0);});}},_1ol=B(_1d4(_1o9)),_1om=E(_1ol.a),_1on=E(_1ol.b);if(_1om>_1o7){return B(_1kB(_1o7,_1om,_1on));}else{if(_1o7>_1on){return B(_1kB(_1o7,_1om,_1on));}else{return E(E(_1ol.d[_1o7-_1om|0]).a);}}}),_1oo=B(_1eW(_1o7,new T2(0,_1o8,new T2(1,_1nA,_1o5)),_1n9));}else{var _1oo=B(_1gE(_1mT,_1n9));}if(!E(_1o6)){var _1op=B(_1eW(E(_1mT),_1o4.a,_1na));}else{var _1op=B(_1gE(_1mT,_1na));}return {_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(B(_1jT(_1n8,_1o4.b))),d:E(_1n8),e:E(_1oo),f:E(_1op),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_AD),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};case 114:var _1oq=B(_aW(_1ko,_1n0));return {_:0,a:E({_:0,a:E(B(_aW(_1kz,_1n0))),b:E(B(_1fC(_1oq.a,E(_1oq.b),new T(function(){return B(_aW(_1mt,_1n0));})))),c:E(_1mX),d:B(_aW(_1kM,_1n0)),e:32,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1oq),c:E(_1kG),d:E(_1n8),e:E(_1n9),f:E(B(_aj(_1kJ,_1na))),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_AD),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};case 115:return {_:0,a:E({_:0,a:E(_1mV),b:E(B(_1mP(_1mW))),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};case 116:var _1or=E(_1nB),_1os=B(_1ex(_1or,_1nz)),_1ot=E(_1os.a);if(!E(_1ot)){var _1ou=true;}else{var _1ou=false;}if(!E(_1ou)){var _1ov=B(_1eW(E(_1mT),_1ot,_1na));}else{var _1ov=B(_1eW(E(_1mT),_1or+1|0,_1na));}if(!E(_1ou)){var _1ow=__Z;}else{var _1ow=E(_1os.b);}if(!B(_uV(_1ow,_Z))){var _1ox=B(_1mS(_1mT,_1ow,_1mV,_1mW,_1mX,_1mY,_1mZ,_1n0,_1n1,_1n2,_1n3,_1n4,_1n5,_1n6,_1n7,_1n8,_1n9,_1ov,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx)),_1oy=E(_1ox.a);return {_:0,a:E({_:0,a:E(_1oy.a),b:E(_1oy.b),c:E(_1oy.c),d:_1oy.d,e:_1oy.e,f:_1oy.f,g:E(_1oy.g),h:_1oy.h,i:E(B(_x(_1n3,_1ny))),j:E(_1oy.j),k:E(_1oy.k)}),b:E(_1ox.b),c:E(_1ox.c),d:E(_1ox.d),e:E(_1ox.e),f:E(_1ox.f),g:E(_1ox.g),h:E(_1ox.h),i:_1ox.i,j:_1ox.j,k:_1ox.k,l:_1ox.l,m:E(_1ox.m),n:_1ox.n,o:E(_1ox.o),p:E(_1ox.p),q:_1ox.q,r:E(_1ox.r),s:E(_1ox.s),t:_1ox.t,u:E(_1ox.u),v:E(_1ox.v)};}else{return {_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1ov),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};}break;case 119:return {_:0,a:E({_:0,a:E(_1kq),b:E(_1lh),c:E(_1mX),d:E(_1kN),e:32,f:0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1kb),c:E(_1kI),d:E(_1n8),e:E(_1n9),f:E(B(_aj(_1kJ,_1na))),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_AD),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};default:return {_:0,a:E({_:0,a:E(_1mV),b:E(_1mW),c:E(_1mX),d:_1mY,e:_1mZ,f:_1n0,g:E(_1n1),h:_1n2,i:E(B(_x(_1n3,_1ny))),j:E(_1n4),k:E(_1n5)}),b:E(_1n6),c:E(_1n7),d:E(_1n8),e:E(_1n9),f:E(_1na),g:E(_1nb),h:E(_1nc),i:_1nd,j:_1ne,k:_1nf,l:_1ng,m:E(_1nh),n:_1ni,o:E(_1nj),p:E(_1nk),q:_1nl,r:E(_1nm),s:E(_1nn),t:_1no,u:E({_:0,a:E(_1np),b:E(_1nq),c:E(_1nr),d:E(_1ns),e:E(_1nt),f:E(_1nu),g:E(_1nv),h:E(_1nw)}),v:E(_1nx)};}}},_1oz=function(_1oA,_1oB){while(1){var _1oC=E(_1oB);if(!_1oC._){return __Z;}else{var _1oD=_1oC.b,_1oE=E(_1oA);if(_1oE==1){return E(_1oD);}else{_1oA=_1oE-1|0;_1oB=_1oD;continue;}}}},_1oF=new T(function(){return B(unCStr("X"));}),_1oG=new T(function(){return B(_ic("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1oH=38,_1oI=function(_1oJ,_1oK,_1oL,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7){var _1p8=E(_1oL);if(!_1p8._){return {_:0,a:_1oM,b:_1oN,c:_1oO,d:_1oP,e:_1oQ,f:_1oR,g:_1oS,h:_1oT,i:_1oU,j:_1oV,k:_1oW,l:_1oX,m:_1oY,n:_1oZ,o:_1p0,p:_1p1,q:_1p2,r:_1p3,s:_1p4,t:_1p5,u:_1p6,v:_1p7};}else{var _1p9=_1p8.b,_1pa=E(_1p8.a),_1pb=_1pa.a,_1pc=_1pa.b,_1pd=function(_1pe,_1pf,_1pg){var _1ph=function(_1pi,_1pj){if(!B(_uV(_1pi,_Z))){var _1pk=E(_1oM),_1pl=E(_1p6),_1pm=B(_1mS(_1pj,_1pi,_1pk.a,_1pk.b,_1pk.c,_1pk.d,_1pk.e,_1pk.f,_1pk.g,_1pk.h,_1pk.i,_1pk.j,_1pk.k,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1pl.a,_1pl.b,_1pl.c,_1pl.d,_1pl.e,_1pl.f,_1pl.g,_1pl.h,_1p7)),_1pn=_1pm.a,_1po=_1pm.b,_1pp=_1pm.c,_1pq=_1pm.d,_1pr=_1pm.e,_1ps=_1pm.f,_1pt=_1pm.g,_1pu=_1pm.h,_1pv=_1pm.i,_1pw=_1pm.j,_1px=_1pm.k,_1py=_1pm.l,_1pz=_1pm.m,_1pA=_1pm.n,_1pB=_1pm.o,_1pC=_1pm.p,_1pD=_1pm.q,_1pE=_1pm.r,_1pF=_1pm.s,_1pG=_1pm.t,_1pH=_1pm.u,_1pI=_1pm.v;if(B(_qy(_1ps,0))!=B(_qy(_1oR,0))){return {_:0,a:_1pn,b:_1po,c:_1pp,d:_1pq,e:_1pr,f:_1ps,g:_1pt,h:_1pu,i:_1pv,j:_1pw,k:_1px,l:_1py,m:_1pz,n:_1pA,o:_1pB,p:_1pC,q:_1pD,r:_1pE,s:_1pF,t:_1pG,u:_1pH,v:_1pI};}else{return new F(function(){return _1oI(new T(function(){return E(_1oJ)+1|0;}),_1oK,_1p9,_1pn,_1po,_1pp,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv,_1pw,_1px,_1py,_1pz,_1pA,_1pB,_1pC,_1pD,_1pE,_1pF,_1pG,_1pH,_1pI);});}}else{return new F(function(){return _1oI(new T(function(){return E(_1oJ)+1|0;}),_1oK,_1p9,_1oM,_1oN,_1oO,_1oP,_1oQ,_1oR,_1oS,_1oT,_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7);});}},_1pJ=B(_qy(_1oK,0))-B(_qy(new T2(1,_1pe,_1pf),0))|0;if(_1pJ>0){var _1pK=B(_1oz(_1pJ,_1oK));}else{var _1pK=E(_1oK);}if(E(B(_1dN(_1pe,_1pf,_Zw)))==63){var _1pL=B(_XN(_1pe,_1pf));}else{var _1pL=new T2(1,_1pe,_1pf);}var _1pM=function(_1pN){if(!B(_4H(_lc,_1oH,_1pb))){return new T2(0,_1pc,_1oJ);}else{var _1pO=function(_1pP){while(1){var _1pQ=B((function(_1pR){var _1pS=E(_1pR);if(!_1pS._){return true;}else{var _1pT=_1pS.b,_1pU=E(_1pS.a);if(!_1pU._){return E(_1oG);}else{switch(E(_1pU.a)){case 99:var _1pV=E(_1oM);if(!E(_1pV.k)){return false;}else{var _1pW=function(_1pX){while(1){var _1pY=E(_1pX);if(!_1pY._){return true;}else{var _1pZ=_1pY.b,_1q0=E(_1pY.a);if(!_1q0._){return E(_1oG);}else{if(E(_1q0.a)==115){var _1q1=B(_Kk(B(_wH(_1eu,_1q0.b))));if(!_1q1._){return E(_1es);}else{if(!E(_1q1.b)._){if(_1pV.f!=E(_1q1.a)){return false;}else{_1pX=_1pZ;continue;}}else{return E(_1et);}}}else{_1pX=_1pZ;continue;}}}}};return new F(function(){return _1pW(_1pT);});}break;case 115:var _1q2=E(_1oM),_1q3=_1q2.f,_1q4=B(_Kk(B(_wH(_1eu,_1pU.b))));if(!_1q4._){return E(_1es);}else{if(!E(_1q4.b)._){if(_1q3!=E(_1q4.a)){return false;}else{var _1q5=function(_1q6){while(1){var _1q7=E(_1q6);if(!_1q7._){return true;}else{var _1q8=_1q7.b,_1q9=E(_1q7.a);if(!_1q9._){return E(_1oG);}else{switch(E(_1q9.a)){case 99:if(!E(_1q2.k)){return false;}else{_1q6=_1q8;continue;}break;case 115:var _1qa=B(_Kk(B(_wH(_1eu,_1q9.b))));if(!_1qa._){return E(_1es);}else{if(!E(_1qa.b)._){if(_1q3!=E(_1qa.a)){return false;}else{_1q6=_1q8;continue;}}else{return E(_1et);}}break;default:_1q6=_1q8;continue;}}}}};return new F(function(){return _1q5(_1pT);});}}else{return E(_1et);}}break;default:_1pP=_1pT;return __continue;}}}})(_1pP));if(_1pQ!=__continue){return _1pQ;}}};return (!B(_1pO(_1pg)))?(!B(_uV(_1pL,_1oF)))?new T2(0,_Z,_1oJ):new T2(0,_1pc,_1oJ):new T2(0,_1pc,_1oJ);}};if(E(B(_1dV(_1pe,_1pf,_Zw)))==63){if(!B(_ae(_1pK,_Z))){var _1qb=E(_1pK);if(!_1qb._){return E(_XS);}else{if(!B(_uV(_1pL,B(_XN(_1qb.a,_1qb.b))))){if(!B(_uV(_1pL,_1oF))){return new F(function(){return _1ph(_Z,_1oJ);});}else{return new F(function(){return _1ph(_1pc,_1oJ);});}}else{var _1qc=B(_1pM(_));return new F(function(){return _1ph(_1qc.a,_1qc.b);});}}}else{if(!B(_uV(_1pL,_1pK))){if(!B(_uV(_1pL,_1oF))){return new F(function(){return _1ph(_Z,_1oJ);});}else{return new F(function(){return _1ph(_1pc,_1oJ);});}}else{var _1qd=B(_1pM(_));return new F(function(){return _1ph(_1qd.a,_1qd.b);});}}}else{if(!B(_uV(_1pL,_1pK))){if(!B(_uV(_1pL,_1oF))){return new F(function(){return _1ph(_Z,_1oJ);});}else{return new F(function(){return _1ph(_1pc,_1oJ);});}}else{var _1qe=B(_1pM(_));return new F(function(){return _1ph(_1qe.a,_1qe.b);});}}},_1qf=E(_1pb);if(!_1qf._){return E(_Zw);}else{var _1qg=_1qf.a,_1qh=E(_1qf.b);if(!_1qh._){return new F(function(){return _1pd(_1qg,_Z,_Z);});}else{var _1qi=E(_1qg),_1qj=new T(function(){var _1qk=B(_Lc(38,_1qh.a,_1qh.b));return new T2(0,_1qk.a,_1qk.b);});if(E(_1qi)==38){return E(_Zw);}else{return new F(function(){return _1pd(_1qi,new T(function(){return E(E(_1qj).a);}),new T(function(){return E(E(_1qj).b);}));});}}}}},_1ql="]",_1qm="}",_1qn=":",_1qo=",",_1qp=new T(function(){return eval("JSON.stringify");}),_1qq="false",_1qr="null",_1qs="[",_1qt="{",_1qu="\"",_1qv="true",_1qw=function(_1qx,_1qy){var _1qz=E(_1qy);switch(_1qz._){case 0:return new T2(0,new T(function(){return jsShow(_1qz.a);}),_1qx);case 1:return new T2(0,new T(function(){var _1qA=__app1(E(_1qp),_1qz.a);return String(_1qA);}),_1qx);case 2:return (!E(_1qz.a))?new T2(0,_1qq,_1qx):new T2(0,_1qv,_1qx);case 3:var _1qB=E(_1qz.a);if(!_1qB._){return new T2(0,_1qs,new T2(1,_1ql,_1qx));}else{var _1qC=new T(function(){var _1qD=new T(function(){var _1qE=function(_1qF){var _1qG=E(_1qF);if(!_1qG._){return E(new T2(1,_1ql,_1qx));}else{var _1qH=new T(function(){var _1qI=B(_1qw(new T(function(){return B(_1qE(_1qG.b));}),_1qG.a));return new T2(1,_1qI.a,_1qI.b);});return new T2(1,_1qo,_1qH);}};return B(_1qE(_1qB.b));}),_1qJ=B(_1qw(_1qD,_1qB.a));return new T2(1,_1qJ.a,_1qJ.b);});return new T2(0,_1qs,_1qC);}break;case 4:var _1qK=E(_1qz.a);if(!_1qK._){return new T2(0,_1qt,new T2(1,_1qm,_1qx));}else{var _1qL=E(_1qK.a),_1qM=new T(function(){var _1qN=new T(function(){var _1qO=function(_1qP){var _1qQ=E(_1qP);if(!_1qQ._){return E(new T2(1,_1qm,_1qx));}else{var _1qR=E(_1qQ.a),_1qS=new T(function(){var _1qT=B(_1qw(new T(function(){return B(_1qO(_1qQ.b));}),_1qR.b));return new T2(1,_1qT.a,_1qT.b);});return new T2(1,_1qo,new T2(1,_1qu,new T2(1,_1qR.a,new T2(1,_1qu,new T2(1,_1qn,_1qS)))));}};return B(_1qO(_1qK.b));}),_1qU=B(_1qw(_1qN,_1qL.b));return new T2(1,_1qU.a,_1qU.b);});return new T2(0,_1qt,new T2(1,new T(function(){var _1qV=__app1(E(_1qp),E(_1qL.a));return String(_1qV);}),new T2(1,_1qn,_1qM)));}break;default:return new T2(0,_1qr,_1qx);}},_1qW=new T(function(){return toJSStr(_Z);}),_1qX=function(_1qY){var _1qZ=B(_1qw(_Z,_1qY)),_1r0=jsCat(new T2(1,_1qZ.a,_1qZ.b),E(_1qW));return E(_1r0);},_1r1=function(_1r2){var _1r3=E(_1r2);if(!_1r3._){return new T2(0,_Z,_Z);}else{var _1r4=E(_1r3.a),_1r5=new T(function(){var _1r6=B(_1r1(_1r3.b));return new T2(0,_1r6.a,_1r6.b);});return new T2(0,new T2(1,_1r4.a,new T(function(){return E(E(_1r5).a);})),new T2(1,_1r4.b,new T(function(){return E(E(_1r5).b);})));}},_1r7=new T(function(){return B(unCStr("Rk"));}),_1r8=function(_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri,_1rj,_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr,_1rs,_1rt,_1ru,_1rv){while(1){var _1rw=B((function(_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP,_1rQ,_1rR,_1rS,_1rT){var _1rU=E(_1rx);if(!_1rU._){return {_:0,a:_1ry,b:_1rz,c:_1rA,d:_1rB,e:_1rC,f:_1rD,g:_1rE,h:_1rF,i:_1rG,j:_1rH,k:_1rI,l:_1rJ,m:_1rK,n:_1rL,o:_1rM,p:_1rN,q:_1rO,r:_1rP,s:_1rQ,t:_1rR,u:_1rS,v:_1rT};}else{var _1rV=_1rU.a,_1rW=B(_Yd(B(unAppCStr("e.e",new T2(1,_1rV,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1rV,_1r7)));})))),_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP,_1rQ,_1rR,_1rS,_1rT));_1r9=_1rU.b;_1ra=_1rW.a;_1rb=_1rW.b;_1rc=_1rW.c;_1rd=_1rW.d;_1re=_1rW.e;_1rf=_1rW.f;_1rg=_1rW.g;_1rh=_1rW.h;_1ri=_1rW.i;_1rj=_1rW.j;_1rk=_1rW.k;_1rl=_1rW.l;_1rm=_1rW.m;_1rn=_1rW.n;_1ro=_1rW.o;_1rp=_1rW.p;_1rq=_1rW.q;_1rr=_1rW.r;_1rs=_1rW.s;_1rt=_1rW.t;_1ru=_1rW.u;_1rv=_1rW.v;return __continue;}})(_1r9,_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri,_1rj,_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr,_1rs,_1rt,_1ru,_1rv));if(_1rw!=__continue){return _1rw;}}},_1rX=function(_1rY){var _1rZ=E(_1rY);switch(_1rZ){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1rZ>>>0>1114111){return new F(function(){return _AN(_1rZ);});}else{return _1rZ;}}},_1s0=function(_1s1,_1s2,_1s3){while(1){var _1s4=E(_1s2);if(!_1s4._){return (E(_1s3)._==0)?true:false;}else{var _1s5=E(_1s3);if(!_1s5._){return false;}else{if(!B(A3(_4F,_1s1,_1s4.a,_1s5.a))){return false;}else{_1s2=_1s4.b;_1s3=_1s5.b;continue;}}}}},_1s6=function(_1s7,_1s8){return (!B(_1s0(_vs,_1s7,_1s8)))?true:false;},_1s9=function(_1sa,_1sb){return new F(function(){return _1s0(_vs,_1sa,_1sb);});},_1sc=new T2(0,_1s9,_1s6),_1sd=function(_1se){var _1sf=E(_1se);if(!_1sf._){return new T2(0,_Z,_Z);}else{var _1sg=E(_1sf.a),_1sh=new T(function(){var _1si=B(_1sd(_1sf.b));return new T2(0,_1si.a,_1si.b);});return new T2(0,new T2(1,_1sg.a,new T(function(){return E(E(_1sh).a);})),new T2(1,_1sg.b,new T(function(){return E(E(_1sh).b);})));}},_1sj=function(_1sk,_1sl){while(1){var _1sm=E(_1sl);if(!_1sm._){return __Z;}else{var _1sn=_1sm.b,_1so=E(_1sk);if(_1so==1){return E(_1sn);}else{_1sk=_1so-1|0;_1sl=_1sn;continue;}}}},_1sp=function(_1sq,_1sr){while(1){var _1ss=E(_1sr);if(!_1ss._){return __Z;}else{var _1st=_1ss.b,_1su=E(_1sq);if(_1su==1){return E(_1st);}else{_1sq=_1su-1|0;_1sr=_1st;continue;}}}},_1sv=function(_1sw){return new F(function(){return _Kr(_1sw,_Z);});},_1sx=function(_1sy,_1sz,_1sA,_1sB){var _1sC=new T(function(){return B(_QT(_lc,_1sz,_1sA));}),_1sD=new T(function(){var _1sE=E(_1sC),_1sF=new T(function(){var _1sG=_1sE+1|0;if(_1sG>0){return B(_1sp(_1sG,_1sA));}else{return E(_1sA);}});if(0>=_1sE){return E(_1sF);}else{var _1sH=function(_1sI,_1sJ){var _1sK=E(_1sI);if(!_1sK._){return E(_1sF);}else{var _1sL=_1sK.a,_1sM=E(_1sJ);return (_1sM==1)?new T2(1,_1sL,_1sF):new T2(1,_1sL,new T(function(){return B(_1sH(_1sK.b,_1sM-1|0));}));}};return B(_1sH(_1sA,_1sE));}}),_1sN=new T(function(){var _1sO=E(_1sC),_1sP=new T(function(){if(E(_1sz)==94){return B(A2(_1sy,new T(function(){return B(_aW(_1sB,_1sO+1|0));}),new T(function(){return B(_aW(_1sB,_1sO));})));}else{return B(A2(_1sy,new T(function(){return B(_aW(_1sB,_1sO));}),new T(function(){return B(_aW(_1sB,_1sO+1|0));})));}}),_1sQ=new T2(1,_1sP,new T(function(){var _1sR=_1sO+2|0;if(_1sR>0){return B(_1sj(_1sR,_1sB));}else{return E(_1sB);}}));if(0>=_1sO){return E(_1sQ);}else{var _1sS=function(_1sT,_1sU){var _1sV=E(_1sT);if(!_1sV._){return E(_1sQ);}else{var _1sW=_1sV.a,_1sX=E(_1sU);return (_1sX==1)?new T2(1,_1sW,_1sQ):new T2(1,_1sW,new T(function(){return B(_1sS(_1sV.b,_1sX-1|0));}));}};return B(_1sS(_1sB,_1sO));}});return (E(_1sz)==94)?new T2(0,new T(function(){return B(_1sv(_1sD));}),new T(function(){return B(_1sv(_1sN));})):new T2(0,_1sD,_1sN);},_1sY=new T(function(){return B(_gs(_sR,_sQ));}),_1sZ=function(_1t0,_1t1,_1t2){while(1){if(!E(_1sY)){if(!B(_gs(B(_180(_1t1,_sR)),_sQ))){if(!B(_gs(_1t1,_f0))){var _1t3=B(_sk(_1t0,_1t0)),_1t4=B(_17L(B(_iT(_1t1,_f0)),_sR)),_1t5=B(_sk(_1t0,_1t2));_1t0=_1t3;_1t1=_1t4;_1t2=_1t5;continue;}else{return new F(function(){return _sk(_1t0,_1t2);});}}else{var _1t3=B(_sk(_1t0,_1t0)),_1t4=B(_17L(_1t1,_sR));_1t0=_1t3;_1t1=_1t4;continue;}}else{return E(_dZ);}}},_1t6=function(_1t7,_1t8){while(1){if(!E(_1sY)){if(!B(_gs(B(_180(_1t8,_sR)),_sQ))){if(!B(_gs(_1t8,_f0))){return new F(function(){return _1sZ(B(_sk(_1t7,_1t7)),B(_17L(B(_iT(_1t8,_f0)),_sR)),_1t7);});}else{return E(_1t7);}}else{var _1t9=B(_sk(_1t7,_1t7)),_1ta=B(_17L(_1t8,_sR));_1t7=_1t9;_1t8=_1ta;continue;}}else{return E(_dZ);}}},_1tb=function(_1tc,_1td){if(!B(_hc(_1td,_sQ))){if(!B(_gs(_1td,_sQ))){return new F(function(){return _1t6(_1tc,_1td);});}else{return E(_f0);}}else{return E(_tw);}},_1te=94,_1tf=45,_1tg=43,_1th=42,_1ti=function(_1tj,_1tk){while(1){var _1tl=B((function(_1tm,_1tn){var _1to=E(_1tn);if(!_1to._){return __Z;}else{if((B(_qy(_1tm,0))+1|0)==B(_qy(_1to,0))){if(!B(_4H(_lc,_1te,_1tm))){if(!B(_4H(_lc,_1th,_1tm))){if(!B(_4H(_lc,_1tg,_1tm))){if(!B(_4H(_lc,_1tf,_1tm))){return E(_1to);}else{var _1tp=B(_1sx(_iT,45,_1tm,_1to));_1tj=_1tp.a;_1tk=_1tp.b;return __continue;}}else{var _1tq=B(_1sx(_gA,43,_1tm,_1to));_1tj=_1tq.a;_1tk=_1tq.b;return __continue;}}else{var _1tr=B(_1sx(_sk,42,_1tm,_1to));_1tj=_1tr.a;_1tk=_1tr.b;return __continue;}}else{var _1ts=B(_1sx(_1tb,94,new T(function(){return B(_1sv(_1tm));}),new T(function(){return B(_Kr(_1to,_Z));})));_1tj=_1ts.a;_1tk=_1ts.b;return __continue;}}else{return __Z;}}})(_1tj,_1tk));if(_1tl!=__continue){return _1tl;}}},_1tt=function(_1tu){var _1tv=E(_1tu);if(!_1tv._){return new T2(0,_Z,_Z);}else{var _1tw=E(_1tv.a),_1tx=new T(function(){var _1ty=B(_1tt(_1tv.b));return new T2(0,_1ty.a,_1ty.b);});return new T2(0,new T2(1,_1tw.a,new T(function(){return E(E(_1tx).a);})),new T2(1,_1tw.b,new T(function(){return E(E(_1tx).b);})));}},_1tz=new T(function(){return B(unCStr("0123456789+-"));}),_1tA=function(_1tB){while(1){var _1tC=E(_1tB);if(!_1tC._){return true;}else{if(!B(_4H(_lc,_1tC.a,_1tz))){return false;}else{_1tB=_1tC.b;continue;}}}},_1tD=new T(function(){return B(err(_wy));}),_1tE=new T(function(){return B(err(_wC));}),_1tF=function(_1tG,_1tH){var _1tI=function(_1tJ,_1tK){var _1tL=function(_1tM){return new F(function(){return A1(_1tK,new T(function(){return B(_jy(_1tM));}));});},_1tN=new T(function(){return B(_Hg(function(_1tO){return new F(function(){return A3(_1tG,_1tO,_1tJ,_1tL);});}));}),_1tP=function(_1tQ){return E(_1tN);},_1tR=function(_1tS){return new F(function(){return A2(_FX,_1tS,_1tP);});},_1tT=new T(function(){return B(_Hg(function(_1tU){var _1tV=E(_1tU);if(_1tV._==4){var _1tW=E(_1tV.a);if(!_1tW._){return new F(function(){return A3(_1tG,_1tV,_1tJ,_1tK);});}else{if(E(_1tW.a)==45){if(!E(_1tW.b)._){return E(new T1(1,_1tR));}else{return new F(function(){return A3(_1tG,_1tV,_1tJ,_1tK);});}}else{return new F(function(){return A3(_1tG,_1tV,_1tJ,_1tK);});}}}else{return new F(function(){return A3(_1tG,_1tV,_1tJ,_1tK);});}}));}),_1tX=function(_1tY){return E(_1tT);};return new T1(1,function(_1tZ){return new F(function(){return A2(_FX,_1tZ,_1tX);});});};return new F(function(){return _I7(_1tI,_1tH);});},_1u0=function(_1u1){var _1u2=E(_1u1);if(_1u2._==5){var _1u3=B(_K3(_1u2.a));return (_1u3._==0)?E(_K8):function(_1u4,_1u5){return new F(function(){return A1(_1u5,_1u3.a);});};}else{return E(_K8);}},_1u6=new T(function(){return B(A3(_1tF,_1u0,_HN,_JA));}),_1u7=function(_1u8,_1u9){var _1ua=E(_1u9);if(!_1ua._){return __Z;}else{var _1ub=_1ua.a,_1uc=_1ua.b,_1ud=function(_1ue){var _1uf=B(_1tt(_1u8)),_1ug=_1uf.a;return (!B(_4H(_uj,_1ub,_1ug)))?__Z:new T2(1,new T(function(){return B(_aW(_1uf.b,B(_QT(_uj,_1ub,_1ug))));}),new T(function(){return B(_1u7(_1u8,_1uc));}));};if(!B(_ae(_1ub,_Z))){if(!B(_1tA(_1ub))){return new F(function(){return _1ud(_);});}else{return new T2(1,new T(function(){var _1uh=B(_Kk(B(_wH(_1u6,_1ub))));if(!_1uh._){return E(_1tD);}else{if(!E(_1uh.b)._){return E(_1uh.a);}else{return E(_1tE);}}}),new T(function(){return B(_1u7(_1u8,_1uc));}));}}else{return new F(function(){return _1ud(_);});}}},_1ui=new T(function(){return B(unCStr("+-*^"));}),_1uj=new T(function(){return B(unCStr("0123456789"));}),_1uk=new T(function(){return B(_Pu("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1ul=new T2(1,_Z,_Z),_1um=function(_1un){var _1uo=E(_1un);if(!_1uo._){return new T2(0,_1ul,_Z);}else{var _1up=_1uo.a,_1uq=new T(function(){var _1ur=B(_1um(_1uo.b)),_1us=E(_1ur.a);if(!_1us._){return E(_1uk);}else{return new T3(0,_1us.a,_1us.b,_1ur.b);}});return (!B(_4H(_lc,_1up,_1uj)))?(!B(_4H(_lc,_1up,_1ui)))?new T2(0,new T2(1,new T2(1,_1up,new T(function(){return E(E(_1uq).a);})),new T(function(){return E(E(_1uq).b);})),new T(function(){return E(E(_1uq).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1uq).a);}),new T(function(){return E(E(_1uq).b);}))),new T2(1,_1up,new T(function(){return E(E(_1uq).c);}))):new T2(0,new T2(1,new T2(1,_1up,new T(function(){return E(E(_1uq).a);})),new T(function(){return E(E(_1uq).b);})),new T(function(){return E(E(_1uq).c);}));}},_1ut=function(_1uu,_1uv){var _1uw=new T(function(){var _1ux=B(_1um(_1uv)),_1uy=E(_1ux.a);if(!_1uy._){return E(_1uk);}else{return new T3(0,_1uy.a,_1uy.b,_1ux.b);}});return (!B(_4H(_lc,_1uu,_1uj)))?(!B(_4H(_lc,_1uu,_1ui)))?new T2(0,new T2(1,new T2(1,_1uu,new T(function(){return E(E(_1uw).a);})),new T(function(){return E(E(_1uw).b);})),new T(function(){return E(E(_1uw).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1uw).a);}),new T(function(){return E(E(_1uw).b);}))),new T2(1,_1uu,new T(function(){return E(E(_1uw).c);}))):new T2(0,new T2(1,new T2(1,_1uu,new T(function(){return E(E(_1uw).a);})),new T(function(){return E(E(_1uw).b);})),new T(function(){return E(E(_1uw).c);}));},_1uz=function(_1uA,_1uB){while(1){var _1uC=E(_1uA);if(!_1uC._){return E(_1uB);}else{_1uA=_1uC.b;_1uB=_1uC.a;continue;}}},_1uD=function(_1uE,_1uF,_1uG){return new F(function(){return _1uz(_1uF,_1uE);});},_1uH=function(_1uI,_1uJ){var _1uK=E(_1uJ);if(!_1uK._){return __Z;}else{var _1uL=B(_1ut(_1uK.a,_1uK.b)),_1uM=B(_1ti(_1uL.b,B(_1u7(_1uI,_1uL.a))));if(!_1uM._){return E(_1uK);}else{return new F(function(){return _1a4(0,B(_1uD(_1uM.a,_1uM.b,_Zw)),_Z);});}}},_1uN=function(_1uO,_1uP){var _1uQ=function(_1uR,_1uS){while(1){var _1uT=B((function(_1uU,_1uV){var _1uW=E(_1uV);if(!_1uW._){return (!B(_uV(_1uU,_Z)))?new T2(0,_AD,_1uU):new T2(0,_AC,_Z);}else{var _1uX=_1uW.b,_1uY=B(_1sd(_1uW.a)).a;if(!B(_4H(_lc,_1fW,_1uY))){var _1uZ=_1uU;_1uR=_1uZ;_1uS=_1uX;return __continue;}else{var _1v0=B(_1gs(_1uY)),_1v1=_1v0.a,_1v2=_1v0.b;if(!B(_ae(_1v2,_Z))){if(!B(_uV(B(_1uH(_1uO,_1v1)),B(_1uH(_1uO,_1v2))))){return new T2(0,_AC,_Z);}else{var _1v3=new T(function(){if(!B(_uV(_1uU,_Z))){return B(_x(_1uU,new T(function(){return B(unAppCStr(" ",_1v1));},1)));}else{return E(_1v1);}});_1uR=_1v3;_1uS=_1uX;return __continue;}}else{return new T2(0,_AC,_Z);}}}})(_1uR,_1uS));if(_1uT!=__continue){return _1uT;}}};return new F(function(){return _1uQ(_Z,_1uP);});},_1v4=function(_1v5,_1v6){var _1v7=new T(function(){var _1v8=B(_Kk(B(_wH(_19U,new T(function(){return B(_tT(3,B(_H(0,imul(E(_1v6),E(_1v5)-1|0)|0,_Z))));})))));if(!_1v8._){return E(_19T);}else{if(!E(_1v8.b)._){return E(_1v8.a);}else{return E(_19S);}}});return new T2(0,new T(function(){return B(_eA(_1v7,_1v5));}),_1v7);},_1v9=function(_1va,_1vb){while(1){var _1vc=E(_1vb);if(!_1vc._){return __Z;}else{var _1vd=_1vc.b,_1ve=E(_1va);if(_1ve==1){return E(_1vd);}else{_1va=_1ve-1|0;_1vb=_1vd;continue;}}}},_1vf=function(_1vg,_1vh){while(1){var _1vi=E(_1vh);if(!_1vi._){return __Z;}else{var _1vj=_1vi.b,_1vk=E(_1vg);if(_1vk==1){return E(_1vj);}else{_1vg=_1vk-1|0;_1vh=_1vj;continue;}}}},_1vl=64,_1vm=new T2(1,_1vl,_Z),_1vn=function(_1vo,_1vp,_1vq,_1vr){return (!B(_uV(_1vo,_1vq)))?true:(!B(_gs(_1vp,_1vr)))?true:false;},_1vs=function(_1vt,_1vu){var _1vv=E(_1vt),_1vw=E(_1vu);return new F(function(){return _1vn(_1vv.a,_1vv.b,_1vw.a,_1vw.b);});},_1vx=function(_1vy,_1vz,_1vA,_1vB){if(!B(_uV(_1vy,_1vA))){return false;}else{return new F(function(){return _gs(_1vz,_1vB);});}},_1vC=function(_1vD,_1vE){var _1vF=E(_1vD),_1vG=E(_1vE);return new F(function(){return _1vx(_1vF.a,_1vF.b,_1vG.a,_1vG.b);});},_1vH=new T2(0,_1vC,_1vs),_1vI=function(_1vJ){var _1vK=E(_1vJ);if(!_1vK._){return new T2(0,_Z,_Z);}else{var _1vL=E(_1vK.a),_1vM=new T(function(){var _1vN=B(_1vI(_1vK.b));return new T2(0,_1vN.a,_1vN.b);});return new T2(0,new T2(1,_1vL.a,new T(function(){return E(E(_1vM).a);})),new T2(1,_1vL.b,new T(function(){return E(E(_1vM).b);})));}},_1vO=function(_1vP){var _1vQ=E(_1vP);if(!_1vQ._){return new T2(0,_Z,_Z);}else{var _1vR=E(_1vQ.a),_1vS=new T(function(){var _1vT=B(_1vO(_1vQ.b));return new T2(0,_1vT.a,_1vT.b);});return new T2(0,new T2(1,_1vR.a,new T(function(){return E(E(_1vS).a);})),new T2(1,_1vR.b,new T(function(){return E(E(_1vS).b);})));}},_1vU=function(_1vV){var _1vW=E(_1vV);if(!_1vW._){return new T2(0,_Z,_Z);}else{var _1vX=E(_1vW.a),_1vY=new T(function(){var _1vZ=B(_1vU(_1vW.b));return new T2(0,_1vZ.a,_1vZ.b);});return new T2(0,new T2(1,_1vX.a,new T(function(){return E(E(_1vY).a);})),new T2(1,_1vX.b,new T(function(){return E(E(_1vY).b);})));}},_1w0=function(_1w1,_1w2){return (_1w1<=_1w2)?new T2(1,_1w1,new T(function(){return B(_1w0(_1w1+1|0,_1w2));})):__Z;},_1w3=new T(function(){return B(_1w0(65,90));}),_1w4=function(_1w5){return (_1w5<=122)?new T2(1,_1w5,new T(function(){return B(_1w4(_1w5+1|0));})):E(_1w3);},_1w6=new T(function(){return B(_1w4(97));}),_1w7=function(_1w8){while(1){var _1w9=E(_1w8);if(!_1w9._){return true;}else{if(!B(_4H(_lc,_1w9.a,_1w6))){return false;}else{_1w8=_1w9.b;continue;}}}},_1wa=new T2(0,_Z,_Z),_1wb=new T(function(){return B(err(_wy));}),_1wc=new T(function(){return B(err(_wC));}),_1wd=new T(function(){return B(A3(_1tF,_1u0,_HN,_JA));}),_1we=function(_1wf,_1wg,_1wh){while(1){var _1wi=B((function(_1wj,_1wk,_1wl){var _1wm=E(_1wl);if(!_1wm._){return __Z;}else{var _1wn=_1wm.b,_1wo=B(_1vO(_1wk)),_1wp=_1wo.a,_1wq=B(_1vI(_1wp)),_1wr=_1wq.a,_1ws=new T(function(){return E(B(_1vU(_1wm.a)).a);}),_1wt=new T(function(){return B(_4H(_lc,_1fW,_1ws));}),_1wu=new T(function(){if(!E(_1wt)){return E(_1wa);}else{var _1wv=B(_1gs(_1ws));return new T2(0,_1wv.a,_1wv.b);}}),_1ww=new T(function(){return E(E(_1wu).a);}),_1wx=new T(function(){return B(_QT(_uj,_1ww,_1wr));}),_1wy=new T(function(){var _1wz=function(_){var _1wA=B(_qy(_1wk,0))-1|0,_1wB=function(_1wC){if(_1wC>=0){var _1wD=newArr(_1wC,_1c9),_1wE=_1wD,_1wF=E(_1wC);if(!_1wF){return new T4(0,E(_1ev),E(_1wA),0,_1wE);}else{var _1wG=function(_1wH,_1wI,_){while(1){var _1wJ=E(_1wH);if(!_1wJ._){return E(_);}else{var _=_1wE[_1wI]=_1wJ.a;if(_1wI!=(_1wF-1|0)){var _1wK=_1wI+1|0;_1wH=_1wJ.b;_1wI=_1wK;continue;}else{return E(_);}}}},_=B(_1wG(_1wo.b,0,_));return new T4(0,E(_1ev),E(_1wA),_1wF,_1wE);}}else{return E(_1d3);}};if(0>_1wA){return new F(function(){return _1wB(0);});}else{return new F(function(){return _1wB(_1wA+1|0);});}};return B(_1d4(_1wz));});if(!B(_4H(_uj,_1ww,_1wr))){var _1wL=false;}else{var _1wM=E(_1wy),_1wN=E(_1wM.a),_1wO=E(_1wM.b),_1wP=E(_1wx);if(_1wN>_1wP){var _1wQ=B(_1kB(_1wP,_1wN,_1wO));}else{if(_1wP>_1wO){var _1wR=B(_1kB(_1wP,_1wN,_1wO));}else{var _1wR=E(_1wM.d[_1wP-_1wN|0])==E(_1wj);}var _1wQ=_1wR;}var _1wL=_1wQ;}var _1wS=new T(function(){return E(E(_1wu).b);}),_1wT=new T(function(){return B(_QT(_uj,_1wS,_1wr));}),_1wU=new T(function(){if(!B(_4H(_uj,_1wS,_1wr))){return false;}else{var _1wV=E(_1wy),_1wW=E(_1wV.a),_1wX=E(_1wV.b),_1wY=E(_1wT);if(_1wW>_1wY){return B(_1kB(_1wY,_1wW,_1wX));}else{if(_1wY>_1wX){return B(_1kB(_1wY,_1wW,_1wX));}else{return E(_1wV.d[_1wY-_1wW|0])==E(_1wj);}}}}),_1wZ=new T(function(){var _1x0=function(_){var _1x1=B(_qy(_1wp,0))-1|0,_1x2=function(_1x3){if(_1x3>=0){var _1x4=newArr(_1x3,_1c9),_1x5=_1x4,_1x6=E(_1x3);if(!_1x6){return new T4(0,E(_1ev),E(_1x1),0,_1x5);}else{var _1x7=function(_1x8,_1x9,_){while(1){var _1xa=E(_1x8);if(!_1xa._){return E(_);}else{var _=_1x5[_1x9]=_1xa.a;if(_1x9!=(_1x6-1|0)){var _1xb=_1x9+1|0;_1x8=_1xa.b;_1x9=_1xb;continue;}else{return E(_);}}}},_=B(_1x7(_1wq.b,0,_));return new T4(0,E(_1ev),E(_1x1),_1x6,_1x5);}}else{return E(_1d3);}};if(0>_1x1){return new F(function(){return _1x2(0);});}else{return new F(function(){return _1x2(_1x1+1|0);});}};return B(_1d4(_1x0));}),_1xc=function(_1xd){var _1xe=function(_1xf){return (!E(_1wL))?__Z:(!E(_1wU))?__Z:new T2(1,new T2(0,_1ww,new T(function(){var _1xg=E(_1wZ),_1xh=E(_1xg.a),_1xi=E(_1xg.b),_1xj=E(_1wx);if(_1xh>_1xj){return B(_1kB(_1xj,_1xh,_1xi));}else{if(_1xj>_1xi){return B(_1kB(_1xj,_1xh,_1xi));}else{return E(_1xg.d[_1xj-_1xh|0]);}}})),new T2(1,new T2(0,_1wS,new T(function(){var _1xk=E(_1wZ),_1xl=E(_1xk.a),_1xm=E(_1xk.b),_1xn=E(_1wT);if(_1xl>_1xn){return B(_1kB(_1xn,_1xl,_1xm));}else{if(_1xn>_1xm){return B(_1kB(_1xn,_1xl,_1xm));}else{return E(_1xk.d[_1xn-_1xl|0]);}}})),_Z));};if(!E(_1wL)){if(!E(_1wU)){return new F(function(){return _1xe(_);});}else{return new T2(1,new T2(0,_1wS,new T(function(){var _1xo=E(_1wZ),_1xp=E(_1xo.a),_1xq=E(_1xo.b),_1xr=E(_1wT);if(_1xp>_1xr){return B(_1kB(_1xr,_1xp,_1xq));}else{if(_1xr>_1xq){return B(_1kB(_1xr,_1xp,_1xq));}else{return E(_1xo.d[_1xr-_1xp|0]);}}})),_Z);}}else{return new F(function(){return _1xe(_);});}};if(!E(_1wL)){var _1xs=B(_1xc(_));}else{if(!E(_1wU)){var _1xt=new T2(1,new T2(0,_1ww,new T(function(){var _1xu=E(_1wZ),_1xv=E(_1xu.a),_1xw=E(_1xu.b),_1xx=E(_1wx);if(_1xv>_1xx){return B(_1kB(_1xx,_1xv,_1xw));}else{if(_1xx>_1xw){return B(_1kB(_1xx,_1xv,_1xw));}else{return E(_1xu.d[_1xx-_1xv|0]);}}})),_Z);}else{var _1xt=B(_1xc(_));}var _1xs=_1xt;}if(!B(_1s0(_1vH,_1xs,_Z))){return new F(function(){return _x(_1xs,new T(function(){return B(_1we(_1wj,_1wk,_1wn));},1));});}else{if(!E(_1wt)){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{if(!B(_1w7(_1ww))){if(!B(_1w7(_1wS))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{if(!E(_1wL)){if(!E(_1wU)){if(!B(_ae(_1ww,_Z))){if(!B(_1tA(_1ww))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{return new T2(1,new T2(0,_1wS,new T(function(){var _1xA=B(_Kk(B(_wH(_1wd,_1ww))));if(!_1xA._){return E(_1wb);}else{if(!E(_1xA.b)._){return E(_1xA.a);}else{return E(_1wc);}}})),new T(function(){return B(_1we(_1wj,_1wk,_1wn));}));}}else{var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}else{var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}else{var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}}else{if(!E(_1wL)){if(!E(_1wU)){if(!B(_ae(_1wS,_Z))){if(!B(_1tA(_1wS))){if(!B(_1w7(_1wS))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{if(!B(_ae(_1ww,_Z))){if(!B(_1tA(_1ww))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{return new T2(1,new T2(0,_1wS,new T(function(){var _1xB=B(_Kk(B(_wH(_1wd,_1ww))));if(!_1xB._){return E(_1wb);}else{if(!E(_1xB.b)._){return E(_1xB.a);}else{return E(_1wc);}}})),new T(function(){return B(_1we(_1wj,_1wk,_1wn));}));}}else{var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}}else{return new T2(1,new T2(0,_1ww,new T(function(){var _1xC=B(_Kk(B(_wH(_1wd,_1wS))));if(!_1xC._){return E(_1wb);}else{if(!E(_1xC.b)._){return E(_1xC.a);}else{return E(_1wc);}}})),new T(function(){return B(_1we(_1wj,_1wk,_1wn));}));}}else{if(!B(_1w7(_1wS))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{if(!B(_ae(_1ww,_Z))){if(!B(_1tA(_1ww))){var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}else{return new T2(1,new T2(0,_1wS,new T(function(){var _1xD=B(_Kk(B(_wH(_1wd,_1ww))));if(!_1xD._){return E(_1wb);}else{if(!E(_1xD.b)._){return E(_1xD.a);}else{return E(_1wc);}}})),new T(function(){return B(_1we(_1wj,_1wk,_1wn));}));}}else{var _1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}}}else{var _1xE=B(_1w7(_1wS)),_1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}else{var _1xF=B(_1w7(_1wS)),_1xy=_1wj,_1xz=_1wk;_1wf=_1xy;_1wg=_1xz;_1wh=_1wn;return __continue;}}}}}})(_1wf,_1wg,_1wh));if(_1wi!=__continue){return _1wi;}}},_1xG=102,_1xH=101,_1xI=new T(function(){return B(unCStr("=="));}),_1xJ=new T(function(){return B(_ic("Action.hs:(103,17)-(107,70)|case"));}),_1xK=new T(function(){return B(_ic("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1xL=5,_1xM=117,_1xN=98,_1xO=110,_1xP=118,_1xQ=function(_1xR,_1xS,_1xT,_1xU,_1xV,_1xW,_1xX,_1xY,_1xZ,_1y0,_1y1,_1y2,_1y3,_1y4){var _1y5=B(_aW(B(_aW(_1xV,_1xS)),_1xR)),_1y6=_1y5.a,_1y7=_1y5.b;if(E(_1xY)==32){if(!B(_4H(_lc,_1y6,_1vm))){var _1y8=false;}else{switch(E(_1y7)){case 0:var _1y9=true;break;case 1:var _1y9=false;break;case 2:var _1y9=false;break;case 3:var _1y9=false;break;case 4:var _1y9=false;break;case 5:var _1y9=false;break;case 6:var _1y9=false;break;case 7:var _1y9=false;break;default:var _1y9=false;}var _1y8=_1y9;}var _1ya=_1y8;}else{var _1ya=false;}if(E(_1xY)==32){if(E(_1y6)==32){var _1yb=false;}else{switch(E(_1y7)){case 0:if(!E(_1ya)){var _1yc=true;}else{var _1yc=false;}var _1yd=_1yc;break;case 1:var _1yd=false;break;case 2:var _1yd=false;break;case 3:var _1yd=false;break;case 4:var _1yd=false;break;case 5:var _1yd=false;break;case 6:var _1yd=false;break;case 7:var _1yd=false;break;default:if(!E(_1ya)){var _1ye=true;}else{var _1ye=false;}var _1yd=_1ye;}var _1yb=_1yd;}var _1yf=_1yb;}else{var _1yf=false;}var _1yg=new T(function(){return B(_P3(_1xR,_1xS,new T(function(){if(!E(_1yf)){if(!E(_1ya)){return E(_1y6);}else{return _1xX;}}else{return E(_11r);}}),_1y7,_1xV));});switch(E(_1y7)){case 3:var _1yh=true;break;case 4:if(E(_1xY)==32){var _1yi=true;}else{var _1yi=false;}var _1yh=_1yi;break;default:var _1yh=false;}if(!E(_1yh)){var _1yj=E(_1yg);}else{var _1yk=E(_1xT),_1yl=new T(function(){return B(_aW(_1yg,_1xS));}),_1ym=function(_1yn,_1yo){var _1yp=E(_1yn);if(_1yp==( -1)){return E(_1yg);}else{var _1yq=new T(function(){return B(_P3(_1xR,_1xS,_11r,_Ii,_1yg));}),_1yr=E(_1yo);if(_1yr==( -1)){var _1ys=__Z;}else{var _1ys=B(_aW(_1yq,_1yr));}if(E(B(_aW(_1ys,_1yp)).a)==32){var _1yt=new T(function(){var _1yu=new T(function(){return B(_aW(_1yl,_1xR));}),_1yv=new T2(1,new T2(0,new T(function(){return E(E(_1yu).a);}),new T(function(){return E(E(_1yu).b);})),new T(function(){var _1yw=_1yp+1|0;if(_1yw>0){return B(_1vf(_1yw,_1ys));}else{return E(_1ys);}}));if(0>=_1yp){return E(_1yv);}else{var _1yx=function(_1yy,_1yz){var _1yA=E(_1yy);if(!_1yA._){return E(_1yv);}else{var _1yB=_1yA.a,_1yC=E(_1yz);return (_1yC==1)?new T2(1,_1yB,_1yv):new T2(1,_1yB,new T(function(){return B(_1yx(_1yA.b,_1yC-1|0));}));}};return B(_1yx(_1ys,_1yp));}}),_1yD=new T2(1,_1yt,new T(function(){var _1yE=_1yo+1|0;if(_1yE>0){return B(_1v9(_1yE,_1yq));}else{return E(_1yq);}}));if(0>=_1yo){return E(_1yD);}else{var _1yF=function(_1yG,_1yH){var _1yI=E(_1yG);if(!_1yI._){return E(_1yD);}else{var _1yJ=_1yI.a,_1yK=E(_1yH);return (_1yK==1)?new T2(1,_1yJ,_1yD):new T2(1,_1yJ,new T(function(){return B(_1yF(_1yI.b,_1yK-1|0));}));}};return new F(function(){return _1yF(_1yq,_1yo);});}}else{return E(_1yg);}}};if(_1xR<=_1yk){if(_1yk<=_1xR){var _1yL=E(_1xU);if(_1xS<=_1yL){if(_1yL<=_1xS){var _1yM=E(_1xJ);}else{var _1yN=E(_1xS);if(!_1yN){var _1yO=B(_1ym( -1, -1));}else{var _1yO=B(_1ym(_1xR,_1yN-1|0));}var _1yM=_1yO;}var _1yP=_1yM;}else{if(_1xS!=(B(_qy(_1yg,0))-1|0)){var _1yQ=B(_1ym(_1xR,_1xS+1|0));}else{var _1yQ=B(_1ym( -1, -1));}var _1yP=_1yQ;}var _1yR=_1yP;}else{var _1yS=E(_1xR);if(!_1yS){var _1yT=B(_1ym( -1, -1));}else{var _1yT=B(_1ym(_1yS-1|0,_1xS));}var _1yR=_1yT;}var _1yU=_1yR;}else{if(_1xR!=(B(_qy(_1yl,0))-1|0)){var _1yV=B(_1ym(_1xR+1|0,_1xS));}else{var _1yV=B(_1ym( -1, -1));}var _1yU=_1yV;}var _1yj=_1yU;}if(!E(_1y3)){var _1yW=E(_1yj);}else{var _1yX=new T(function(){var _1yY=E(_1yj);if(!_1yY._){return E(_rm);}else{return B(_qy(_1yY.a,0));}}),_1yZ=new T(function(){return B(_qy(_1yj,0));}),_1z0=function(_1z1,_1z2,_1z3,_1z4,_1z5,_1z6,_1z7){while(1){var _1z8=B((function(_1z9,_1za,_1zb,_1zc,_1zd,_1ze,_1zf){var _1zg=E(_1zf);if(!_1zg._){return E(_1zc);}else{var _1zh=_1zg.b,_1zi=E(_1zg.a);if(!_1zi._){return E(_1xK);}else{var _1zj=_1zi.b,_1zk=E(_1zi.a);if(E(_1zk.b)==5){var _1zl=new T(function(){var _1zm=B(_1v4(_1xL,_1z9));return new T2(0,_1zm.a,_1zm.b);}),_1zn=new T(function(){var _1zo=function(_1zp,_1zq){var _1zr=function(_1zs){return new F(function(){return _P3(_1za,_1zb,_11r,_Ii,new T(function(){return B(_P3(_1zp,_1zq,_1zk.a,_J7,_1zc));}));});};if(_1zp!=_1za){return new F(function(){return _1zr(_);});}else{if(_1zq!=_1zb){return new F(function(){return _1zr(_);});}else{return E(_1zc);}}};switch(E(E(_1zl).a)){case 1:var _1zt=_1za-1|0;if(_1zt<0){return B(_1zo(_1za,_1zb));}else{if(_1zt>=E(_1yX)){return B(_1zo(_1za,_1zb));}else{if(_1zb<0){return B(_1zo(_1za,_1zb));}else{if(_1zb>=E(_1yZ)){return B(_1zo(_1za,_1zb));}else{if(_1zt!=_1zd){if(E(B(_aW(B(_aW(_1zc,_1zb)),_1zt)).a)==32){return B(_1zo(_1zt,_1zb));}else{return B(_1zo(_1za,_1zb));}}else{if(_1zb!=_1ze){if(E(B(_aW(B(_aW(_1zc,_1zb)),_1zt)).a)==32){return B(_1zo(_1zt,_1zb));}else{return B(_1zo(_1za,_1zb));}}else{return B(_1zo(_1za,_1zb));}}}}}}break;case 2:if(_1za<0){return B(_1zo(_1za,_1zb));}else{if(_1za>=E(_1yX)){return B(_1zo(_1za,_1zb));}else{var _1zu=_1zb-1|0;if(_1zu<0){return B(_1zo(_1za,_1zb));}else{if(_1zu>=E(_1yZ)){return B(_1zo(_1za,_1zb));}else{if(_1za!=_1zd){if(E(B(_aW(B(_aW(_1zc,_1zu)),_1za)).a)==32){return B(_1zo(_1za,_1zu));}else{return B(_1zo(_1za,_1zb));}}else{if(_1zu!=_1ze){if(E(B(_aW(B(_aW(_1zc,_1zu)),_1za)).a)==32){return B(_1zo(_1za,_1zu));}else{return B(_1zo(_1za,_1zb));}}else{return B(_1zo(_1za,_1zb));}}}}}}break;case 3:var _1zv=_1za+1|0;if(_1zv<0){return B(_1zo(_1za,_1zb));}else{if(_1zv>=E(_1yX)){return B(_1zo(_1za,_1zb));}else{if(_1zb<0){return B(_1zo(_1za,_1zb));}else{if(_1zb>=E(_1yZ)){return B(_1zo(_1za,_1zb));}else{if(_1zv!=_1zd){if(E(B(_aW(B(_aW(_1zc,_1zb)),_1zv)).a)==32){return B(_1zo(_1zv,_1zb));}else{return B(_1zo(_1za,_1zb));}}else{if(_1zb!=_1ze){if(E(B(_aW(B(_aW(_1zc,_1zb)),_1zv)).a)==32){return B(_1zo(_1zv,_1zb));}else{return B(_1zo(_1za,_1zb));}}else{return B(_1zo(_1za,_1zb));}}}}}}break;case 4:if(_1za<0){return B(_1zo(_1za,_1zb));}else{if(_1za>=E(_1yX)){return B(_1zo(_1za,_1zb));}else{var _1zw=_1zb+1|0;if(_1zw<0){return B(_1zo(_1za,_1zb));}else{if(_1zw>=E(_1yZ)){return B(_1zo(_1za,_1zb));}else{if(_1za!=_1zd){if(E(B(_aW(B(_aW(_1zc,_1zw)),_1za)).a)==32){return B(_1zo(_1za,_1zw));}else{return B(_1zo(_1za,_1zb));}}else{if(_1zw!=_1ze){if(E(B(_aW(B(_aW(_1zc,_1zw)),_1za)).a)==32){return B(_1zo(_1za,_1zw));}else{return B(_1zo(_1za,_1zb));}}else{return B(_1zo(_1za,_1zb));}}}}}}break;default:if(_1za<0){return B(_1zo(_1za,_1zb));}else{if(_1za>=E(_1yX)){return B(_1zo(_1za,_1zb));}else{if(_1zb<0){return B(_1zo(_1za,_1zb));}else{if(_1zb>=E(_1yZ)){return B(_1zo(_1za,_1zb));}else{if(_1za!=_1zd){var _1zx=E(B(_aW(B(_aW(_1zc,_1zb)),_1za)).a);return B(_1zo(_1za,_1zb));}else{if(_1zb!=_1ze){var _1zy=E(B(_aW(B(_aW(_1zc,_1zb)),_1za)).a);return B(_1zo(_1za,_1zb));}else{return B(_1zo(_1za,_1zb));}}}}}}}}),_1zz=E(_1zj);if(!_1zz._){var _1zA=_1zb+1|0,_1zB=_1zd,_1zC=_1ze;_1z1=new T(function(){return E(E(_1zl).b);},1);_1z2=0;_1z3=_1zA;_1z4=_1zn;_1z5=_1zB;_1z6=_1zC;_1z7=_1zh;return __continue;}else{return new F(function(){return _1zD(new T(function(){return E(E(_1zl).b);},1),_1za+1|0,_1zb,_1zn,_1zd,_1ze,_1zz.a,_1zz.b,_1zh);});}}else{var _1zE=E(_1zj);if(!_1zE._){var _1zF=_1z9,_1zA=_1zb+1|0,_1zG=_1zc,_1zB=_1zd,_1zC=_1ze;_1z1=_1zF;_1z2=0;_1z3=_1zA;_1z4=_1zG;_1z5=_1zB;_1z6=_1zC;_1z7=_1zh;return __continue;}else{return new F(function(){return _1zD(_1z9,_1za+1|0,_1zb,_1zc,_1zd,_1ze,_1zE.a,_1zE.b,_1zh);});}}}}})(_1z1,_1z2,_1z3,_1z4,_1z5,_1z6,_1z7));if(_1z8!=__continue){return _1z8;}}},_1zD=function(_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zN,_1zO,_1zP){while(1){var _1zQ=B((function(_1zR,_1zS,_1zT,_1zU,_1zV,_1zW,_1zX,_1zY,_1zZ){var _1A0=E(_1zX);if(E(_1A0.b)==5){var _1A1=new T(function(){var _1A2=B(_1v4(_1xL,_1zR));return new T2(0,_1A2.a,_1A2.b);}),_1A3=new T(function(){var _1A4=function(_1A5,_1A6){var _1A7=function(_1A8){return new F(function(){return _P3(_1zS,_1zT,_11r,_Ii,new T(function(){return B(_P3(_1A5,_1A6,_1A0.a,_J7,_1zU));}));});};if(_1A5!=_1zS){return new F(function(){return _1A7(_);});}else{if(_1A6!=_1zT){return new F(function(){return _1A7(_);});}else{return E(_1zU);}}};switch(E(E(_1A1).a)){case 1:var _1A9=_1zS-1|0;if(_1A9<0){return B(_1A4(_1zS,_1zT));}else{if(_1A9>=E(_1yX)){return B(_1A4(_1zS,_1zT));}else{if(_1zT<0){return B(_1A4(_1zS,_1zT));}else{if(_1zT>=E(_1yZ)){return B(_1A4(_1zS,_1zT));}else{if(_1A9!=_1zV){if(E(B(_aW(B(_aW(_1zU,_1zT)),_1A9)).a)==32){return B(_1A4(_1A9,_1zT));}else{return B(_1A4(_1zS,_1zT));}}else{if(_1zT!=_1zW){if(E(B(_aW(B(_aW(_1zU,_1zT)),_1A9)).a)==32){return B(_1A4(_1A9,_1zT));}else{return B(_1A4(_1zS,_1zT));}}else{return B(_1A4(_1zS,_1zT));}}}}}}break;case 2:if(_1zS<0){return B(_1A4(_1zS,_1zT));}else{if(_1zS>=E(_1yX)){return B(_1A4(_1zS,_1zT));}else{var _1Aa=_1zT-1|0;if(_1Aa<0){return B(_1A4(_1zS,_1zT));}else{if(_1Aa>=E(_1yZ)){return B(_1A4(_1zS,_1zT));}else{if(_1zS!=_1zV){if(E(B(_aW(B(_aW(_1zU,_1Aa)),_1zS)).a)==32){return B(_1A4(_1zS,_1Aa));}else{return B(_1A4(_1zS,_1zT));}}else{if(_1Aa!=_1zW){if(E(B(_aW(B(_aW(_1zU,_1Aa)),_1zS)).a)==32){return B(_1A4(_1zS,_1Aa));}else{return B(_1A4(_1zS,_1zT));}}else{return B(_1A4(_1zS,_1zT));}}}}}}break;case 3:var _1Ab=_1zS+1|0;if(_1Ab<0){return B(_1A4(_1zS,_1zT));}else{if(_1Ab>=E(_1yX)){return B(_1A4(_1zS,_1zT));}else{if(_1zT<0){return B(_1A4(_1zS,_1zT));}else{if(_1zT>=E(_1yZ)){return B(_1A4(_1zS,_1zT));}else{if(_1Ab!=_1zV){if(E(B(_aW(B(_aW(_1zU,_1zT)),_1Ab)).a)==32){return B(_1A4(_1Ab,_1zT));}else{return B(_1A4(_1zS,_1zT));}}else{if(_1zT!=_1zW){if(E(B(_aW(B(_aW(_1zU,_1zT)),_1Ab)).a)==32){return B(_1A4(_1Ab,_1zT));}else{return B(_1A4(_1zS,_1zT));}}else{return B(_1A4(_1zS,_1zT));}}}}}}break;case 4:if(_1zS<0){return B(_1A4(_1zS,_1zT));}else{if(_1zS>=E(_1yX)){return B(_1A4(_1zS,_1zT));}else{var _1Ac=_1zT+1|0;if(_1Ac<0){return B(_1A4(_1zS,_1zT));}else{if(_1Ac>=E(_1yZ)){return B(_1A4(_1zS,_1zT));}else{if(_1zS!=_1zV){if(E(B(_aW(B(_aW(_1zU,_1Ac)),_1zS)).a)==32){return B(_1A4(_1zS,_1Ac));}else{return B(_1A4(_1zS,_1zT));}}else{if(_1Ac!=_1zW){if(E(B(_aW(B(_aW(_1zU,_1Ac)),_1zS)).a)==32){return B(_1A4(_1zS,_1Ac));}else{return B(_1A4(_1zS,_1zT));}}else{return B(_1A4(_1zS,_1zT));}}}}}}break;default:if(_1zS<0){return B(_1A4(_1zS,_1zT));}else{if(_1zS>=E(_1yX)){return B(_1A4(_1zS,_1zT));}else{if(_1zT<0){return B(_1A4(_1zS,_1zT));}else{if(_1zT>=E(_1yZ)){return B(_1A4(_1zS,_1zT));}else{if(_1zS!=_1zV){var _1Ad=E(B(_aW(B(_aW(_1zU,_1zT)),_1zS)).a);return B(_1A4(_1zS,_1zT));}else{if(_1zT!=_1zW){var _1Ae=E(B(_aW(B(_aW(_1zU,_1zT)),_1zS)).a);return B(_1A4(_1zS,_1zT));}else{return B(_1A4(_1zS,_1zT));}}}}}}}}),_1Af=E(_1zY);if(!_1Af._){return new F(function(){return _1z0(new T(function(){return E(E(_1A1).b);},1),0,_1zT+1|0,_1A3,_1zV,_1zW,_1zZ);});}else{var _1Ag=_1zS+1|0,_1Ah=_1zT,_1Ai=_1zV,_1Aj=_1zW,_1Ak=_1zZ;_1zH=new T(function(){return E(E(_1A1).b);},1);_1zI=_1Ag;_1zJ=_1Ah;_1zK=_1A3;_1zL=_1Ai;_1zM=_1Aj;_1zN=_1Af.a;_1zO=_1Af.b;_1zP=_1Ak;return __continue;}}else{var _1Al=E(_1zY);if(!_1Al._){return new F(function(){return _1z0(_1zR,0,_1zT+1|0,_1zU,_1zV,_1zW,_1zZ);});}else{var _1Am=_1zR,_1Ag=_1zS+1|0,_1Ah=_1zT,_1An=_1zU,_1Ai=_1zV,_1Aj=_1zW,_1Ak=_1zZ;_1zH=_1Am;_1zI=_1Ag;_1zJ=_1Ah;_1zK=_1An;_1zL=_1Ai;_1zM=_1Aj;_1zN=_1Al.a;_1zO=_1Al.b;_1zP=_1Ak;return __continue;}}})(_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zN,_1zO,_1zP));if(_1zQ!=__continue){return _1zQ;}}},_1yW=B(_1z0(_1y1,0,0,_1yj,_1xR,_1xS,_1yj));}var _1Ao=function(_1Ap){var _1Aq=function(_1Ar){var _1As=new T(function(){switch(E(_1y7)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1At=new T(function(){if(!E(_1yh)){if(!E(_1As)){return new T2(0,_1xR,_1xS);}else{return new T2(0,_1xT,_1xU);}}else{if(!B(_1s0(_1sc,_1yW,_1yg))){if(!E(_1As)){return new T2(0,_1xR,_1xS);}else{return new T2(0,_1xT,_1xU);}}else{return new T2(0,_1xT,_1xU);}}}),_1Au=new T(function(){return E(E(_1At).b);}),_1Av=new T(function(){return E(E(_1At).a);});if(!E(_1yh)){var _1Aw=E(_1y4);}else{var _1Aw=E(B(_1uN(new T(function(){return B(_1we(_1xZ,_1y0,_1yW));}),_1yW)).a);}var _1Ax=new T(function(){if(!E(_1yf)){if(!E(_1ya)){var _1Ay=function(_1Az){var _1AA=function(_1AB){var _1AC=E(_1y7);if(_1AC==4){return new T2(1,_1xO,new T2(1,_1y6,_Z));}else{if(!E(_1As)){return (E(_1AC)==2)?new T2(1,_1xM,new T2(1,_1y6,_Z)):__Z;}else{var _1AD=E(_1y6);return (E(_1AD)==61)?new T2(1,_1xN,new T2(1,_1AD,new T(function(){return B(_H(0,_1xS,_Z));}))):new T2(1,_1xN,new T2(1,_1AD,_Z));}}};if(!E(_1yh)){return new F(function(){return _1AA(_);});}else{if(E(_1xT)!=E(_1Av)){return new T2(1,_1xP,new T2(1,_1y6,_Z));}else{if(E(_1xU)!=E(_1Au)){return new T2(1,_1xP,new T2(1,_1y6,_Z));}else{return new F(function(){return _1AA(_);});}}}};if(!E(_1yh)){return B(_1Ay(_));}else{if(!E(_1Aw)){return B(_1Ay(_));}else{return E(_1xI);}}}else{return new T2(1,_1xG,new T2(1,_1y6,_Z));}}else{return new T2(1,_1xH,new T2(1,_1y6,_Z));}},1);return {_:0,a:E(new T2(0,_1Av,_1Au)),b:E(_1yW),c:E(_1xW),d:_1Ap,e:_1Ar,f:_1xZ,g:E(_1y0),h:_1y1,i:E(B(_x(_1y2,_1Ax))),j:E(_1y3),k:E(_1Aw)};};if(!E(_1yf)){return new F(function(){return _1Aq(_1xY);});}else{return new F(function(){return _1Aq(E(_1y6));});}};if(!E(_1ya)){return new F(function(){return _1Ao(_1xX);});}else{return new F(function(){return _1Ao(E(_1y6));});}},_1AE=new T2(1,_61,_Z),_1AF=5,_1AG=new T2(1,_1AF,_Z),_1AH=function(_1AI,_1AJ){while(1){var _1AK=E(_1AI);if(!_1AK._){return E(_1AJ);}else{_1AI=_1AK.b;_1AJ=_1AK.a;continue;}}},_1AL=57,_1AM=48,_1AN=new T2(1,_1vl,_Z),_1AO=new T(function(){return B(err(_wC));}),_1AP=new T(function(){return B(err(_wy));}),_1AQ=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_1AR=function(_1AS,_1AT){if((_1AT-48|0)>>>0>9){var _1AU=_1AT+_1AS|0,_1AV=function(_1AW){if(!B(_4H(_lc,_1AW,_1AN))){return E(_1AW);}else{return new F(function(){return _1AR(_1AS,_1AW);});}};if(_1AU<=122){if(_1AU>=97){if(_1AU>>>0>1114111){return new F(function(){return _AN(_1AU);});}else{return new F(function(){return _1AV(_1AU);});}}else{if(_1AU<=90){if(_1AU>>>0>1114111){return new F(function(){return _AN(_1AU);});}else{return new F(function(){return _1AV(_1AU);});}}else{var _1AX=65+(_1AU-90|0)|0;if(_1AX>>>0>1114111){return new F(function(){return _AN(_1AX);});}else{return new F(function(){return _1AV(_1AX);});}}}}else{var _1AY=97+(_1AU-122|0)|0;if(_1AY>>>0>1114111){return new F(function(){return _AN(_1AY);});}else{return new F(function(){return _1AV(_1AY);});}}}else{var _1AZ=B(_Kk(B(_wH(_1AQ,new T2(1,_1AT,_Z)))));if(!_1AZ._){return E(_1AP);}else{if(!E(_1AZ.b)._){var _1B0=E(_1AZ.a)+_1AS|0;switch(_1B0){case  -1:return E(_1AM);case 10:return E(_1AL);default:return new F(function(){return _1AH(B(_H(0,_1B0,_Z)),_Zw);});}}else{return E(_1AO);}}}},_1B1=function(_1B2,_1B3){if((_1B2-48|0)>>>0>9){return _1B3;}else{var _1B4=B(_Kk(B(_wH(_1AQ,new T2(1,_1B2,_Z)))));if(!_1B4._){return E(_1AP);}else{if(!E(_1B4.b)._){return new F(function(){return _1AR(E(_1B4.a),_1B3);});}else{return E(_1AO);}}}},_1B5=function(_1B6,_1B7){return new F(function(){return _1B1(E(_1B6),E(_1B7));});},_1B8=new T2(1,_1B5,_Z),_1B9=112,_1Ba=111,_1Bb=function(_1Bc,_1Bd,_1Be,_1Bf,_1Bg,_1Bh,_1Bi,_1Bj,_1Bk,_1Bl,_1Bm,_1Bn){var _1Bo=new T(function(){return B(_aW(B(_aW(_1Be,_1Bd)),E(_1Bc)));}),_1Bp=new T(function(){return E(E(_1Bo).b);}),_1Bq=new T(function(){if(E(_1Bp)==4){return true;}else{return false;}}),_1Br=new T(function(){return E(E(_1Bo).a);});if(E(_1Bh)==32){var _1Bs=false;}else{if(E(_1Br)==32){var _1Bt=true;}else{var _1Bt=false;}var _1Bs=_1Bt;}var _1Bu=new T(function(){var _1Bv=new T(function(){return B(A3(_aW,_1AE,B(_QT(_lc,_1Bg,_1vm)),_1Bh));});if(!E(_1Bs)){if(!E(_1Bq)){return E(_1Br);}else{if(!B(_4H(_3S,_1Bi,_1AG))){return E(_1Br);}else{return B(A(_aW,[_1B8,B(_QT(_3S,_1Bi,_1AG)),_1Bv,_1Br]));}}}else{return E(_1Bv);}}),_1Bw=B(_P3(_1Bc,_1Bd,_1Bu,_1Bp,_1Be)),_1Bx=function(_1By){var _1Bz=B(_1uN(new T(function(){return B(_1we(_1Bi,_1Bj,_1Bw));}),_1Bw)).a;return {_:0,a:E(new T2(0,_1Bc,_1Bd)),b:E(_1Bw),c:E(_1Bf),d:_1Bg,e:_1By,f:_1Bi,g:E(_1Bj),h:_1Bk,i:E(B(_x(_1Bl,new T(function(){if(!E(_1Bz)){if(!E(_1Bs)){if(!E(_1Bq)){return __Z;}else{return new T2(1,_1B9,new T2(1,_1Bu,_Z));}}else{return new T2(1,_1Ba,new T2(1,_1Bu,_Z));}}else{return E(_1xI);}},1)))),j:E(_1Bm),k:E(_1Bz)};};if(!E(_1Bs)){return new F(function(){return _1Bx(_1Bh);});}else{return new F(function(){return _1Bx(32);});}},_1BA=function(_1BB,_1BC){while(1){var _1BD=E(_1BC);if(!_1BD._){return __Z;}else{var _1BE=_1BD.b,_1BF=E(_1BB);if(_1BF==1){return E(_1BE);}else{_1BB=_1BF-1|0;_1BC=_1BE;continue;}}}},_1BG=4,_1BH=new T(function(){return B(unCStr("\u5e74 "));}),_1BI=function(_1BJ,_1BK,_1BL,_1BM,_1BN){var _1BO=new T(function(){var _1BP=new T(function(){var _1BQ=new T(function(){var _1BR=new T(function(){var _1BS=new T(function(){return B(_x(_1BL,new T(function(){return B(unAppCStr(" >>",_1BM));},1)));});return B(unAppCStr(" >>",_1BS));},1);return B(_x(_1BK,_1BR));},1);return B(_x(_1BH,_1BQ));},1);return B(_x(B(_H(0,_1BJ,_Z)),_1BP));});return new T2(0,new T2(1,_1BN,_1r7),_1BO);},_1BT=function(_1BU){var _1BV=E(_1BU),_1BW=E(_1BV.a),_1BX=B(_1BI(_1BW.a,_1BW.b,_1BW.c,_1BW.d,_1BV.b));return new T2(0,_1BX.a,_1BX.b);},_1BY=function(_1BZ){var _1C0=E(_1BZ);return new T2(0,new T2(1,_1C0.b,_1r7),E(_1C0.a).b);},_1C1=new T(function(){return B(_ic("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1C2=function(_1C3,_1C4){while(1){var _1C5=E(_1C4);if(!_1C5._){return false;}else{var _1C6=_1C5.b,_1C7=E(_1C3),_1C8=_1C7.a,_1C9=_1C7.b,_1Ca=E(_1C5.a);if(!_1Ca._){return E(_1C1);}else{var _1Cb=E(_1Ca.a),_1Cc=_1Cb.a,_1Cd=_1Cb.b,_1Ce=E(_1Ca.b);if(!_1Ce._){var _1Cf=E(_1C8),_1Cg=E(_1Cf);if(_1Cg==32){switch(E(_1C9)){case 0:if(!E(_1Cd)){return true;}else{_1C3=new T2(0,_1Cf,_Ii);_1C4=_1C6;continue;}break;case 1:if(E(_1Cd)==1){return true;}else{_1C3=new T2(0,_1Cf,_Io);_1C4=_1C6;continue;}break;case 2:if(E(_1Cd)==2){return true;}else{_1C3=new T2(0,_1Cf,_Iu);_1C4=_1C6;continue;}break;case 3:if(E(_1Cd)==3){return true;}else{_1C3=new T2(0,_1Cf,_IA);_1C4=_1C6;continue;}break;case 4:if(E(_1Cd)==4){return true;}else{_1C3=new T2(0,_1Cf,_IG);_1C4=_1C6;continue;}break;case 5:if(E(_1Cd)==5){return true;}else{_1C3=new T2(0,_1Cf,_J7);_1C4=_1C6;continue;}break;case 6:if(E(_1Cd)==6){return true;}else{_1C3=new T2(0,_1Cf,_J0);_1C4=_1C6;continue;}break;case 7:if(E(_1Cd)==7){return true;}else{_1C3=new T2(0,_1Cf,_IT);_1C4=_1C6;continue;}break;default:if(E(_1Cd)==8){return true;}else{_1C3=new T2(0,_1Cf,_IM);_1C4=_1C6;continue;}}}else{if(_1Cg!=E(_1Cc)){_1C3=_1C7;_1C4=_1C6;continue;}else{switch(E(_1C9)){case 0:if(!E(_1Cd)){return true;}else{_1C3=new T2(0,_1Cf,_Ii);_1C4=_1C6;continue;}break;case 1:if(E(_1Cd)==1){return true;}else{_1C3=new T2(0,_1Cf,_Io);_1C4=_1C6;continue;}break;case 2:if(E(_1Cd)==2){return true;}else{_1C3=new T2(0,_1Cf,_Iu);_1C4=_1C6;continue;}break;case 3:if(E(_1Cd)==3){return true;}else{_1C3=new T2(0,_1Cf,_IA);_1C4=_1C6;continue;}break;case 4:if(E(_1Cd)==4){return true;}else{_1C3=new T2(0,_1Cf,_IG);_1C4=_1C6;continue;}break;case 5:if(E(_1Cd)==5){return true;}else{_1C3=new T2(0,_1Cf,_J7);_1C4=_1C6;continue;}break;case 6:if(E(_1Cd)==6){return true;}else{_1C3=new T2(0,_1Cf,_J0);_1C4=_1C6;continue;}break;case 7:if(E(_1Cd)==7){return true;}else{_1C3=new T2(0,_1Cf,_IT);_1C4=_1C6;continue;}break;default:if(E(_1Cd)==8){return true;}else{_1C3=new T2(0,_1Cf,_IM);_1C4=_1C6;continue;}}}}}else{var _1Ch=E(_1C8),_1Ci=E(_1Ch);if(_1Ci==32){switch(E(_1C9)){case 0:if(!E(_1Cd)){return true;}else{_1C3=new T2(0,_1Ch,_Ii);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 1:if(E(_1Cd)==1){return true;}else{_1C3=new T2(0,_1Ch,_Io);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 2:if(E(_1Cd)==2){return true;}else{_1C3=new T2(0,_1Ch,_Iu);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 3:if(E(_1Cd)==3){return true;}else{_1C3=new T2(0,_1Ch,_IA);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 4:if(E(_1Cd)==4){return true;}else{_1C3=new T2(0,_1Ch,_IG);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 5:if(E(_1Cd)==5){return true;}else{_1C3=new T2(0,_1Ch,_J7);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 6:if(E(_1Cd)==6){return true;}else{_1C3=new T2(0,_1Ch,_J0);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 7:if(E(_1Cd)==7){return true;}else{_1C3=new T2(0,_1Ch,_IT);_1C4=new T2(1,_1Ce,_1C6);continue;}break;default:if(E(_1Cd)==8){return true;}else{_1C3=new T2(0,_1Ch,_IM);_1C4=new T2(1,_1Ce,_1C6);continue;}}}else{if(_1Ci!=E(_1Cc)){_1C3=_1C7;_1C4=new T2(1,_1Ce,_1C6);continue;}else{switch(E(_1C9)){case 0:if(!E(_1Cd)){return true;}else{_1C3=new T2(0,_1Ch,_Ii);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 1:if(E(_1Cd)==1){return true;}else{_1C3=new T2(0,_1Ch,_Io);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 2:if(E(_1Cd)==2){return true;}else{_1C3=new T2(0,_1Ch,_Iu);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 3:if(E(_1Cd)==3){return true;}else{_1C3=new T2(0,_1Ch,_IA);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 4:if(E(_1Cd)==4){return true;}else{_1C3=new T2(0,_1Ch,_IG);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 5:if(E(_1Cd)==5){return true;}else{_1C3=new T2(0,_1Ch,_J7);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 6:if(E(_1Cd)==6){return true;}else{_1C3=new T2(0,_1Ch,_J0);_1C4=new T2(1,_1Ce,_1C6);continue;}break;case 7:if(E(_1Cd)==7){return true;}else{_1C3=new T2(0,_1Ch,_IT);_1C4=new T2(1,_1Ce,_1C6);continue;}break;default:if(E(_1Cd)==8){return true;}else{_1C3=new T2(0,_1Ch,_IM);_1C4=new T2(1,_1Ce,_1C6);continue;}}}}}}}}},_1Cj=new T(function(){return B(unCStr("\n"));}),_1Ck=function(_1Cl,_1Cm,_){var _1Cn=jsWriteHandle(E(_1Cl),toJSStr(E(_1Cm)));return _kJ;},_1Co=function(_1Cp,_1Cq,_){var _1Cr=E(_1Cp),_1Cs=jsWriteHandle(_1Cr,toJSStr(E(_1Cq)));return new F(function(){return _1Ck(_1Cr,_1Cj,_);});},_1Ct=function(_1Cu){var _1Cv=E(_1Cu);if(!_1Cv._){return __Z;}else{return new F(function(){return _x(_1Cv.a,new T(function(){return B(_1Ct(_1Cv.b));},1));});}},_1Cw=new T(function(){return B(unCStr("removed"));}),_1Cx=new T(function(){return B(unCStr("loadError"));}),_1Cy=new T(function(){return B(unCStr("saved"));}),_1Cz=new T(function(){return B(err(_wy));}),_1CA=new T(function(){return B(err(_wC));}),_1CB=12,_1CC=3,_1CD=new T(function(){return B(unCStr("Coding : yokoP"));}),_1CE=8,_1CF=32,_1CG=new T2(0,_1CF,_J7),_1CH=99,_1CI=64,_1CJ=new T(function(){return B(_qy(_1mt,0));}),_1CK=new T(function(){return B(unCStr("loadError"));}),_1CL=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_1CM=new T(function(){return B(unCStr(","));}),_1CN=new T(function(){return B(unCStr("~"));}),_1CO=new T(function(){return B(unCStr("savedata"));}),_1CP=new T(function(){return B(unCStr("---"));}),_1CQ=new T(function(){return B(unCStr("=="));}),_1CR=4,_1CS=6,_1CT=5,_1CU=new T1(0,333),_1CV=new T(function(){return B(_cx(1,2147483647));}),_1CW=function(_1CX){var _1CY=B(_Kk(B(_wH(_1CL,_1CX))));return (_1CY._==0)?E(_1Cz):(E(_1CY.b)._==0)?E(_1CY.a):E(_1CA);},_1CZ=new T(function(){var _1D0=E(_1kM);if(!_1D0._){return E(_rm);}else{return E(_1D0.a);}}),_1D1=new T(function(){return B(unAppCStr("[]",_Z));}),_1D2=new T(function(){return B(unCStr("\""));}),_1D3=new T2(1,_Z,_Z),_1D4=new T(function(){return B(_aj(_1CW,_1D3));}),_1D5=function(_1D6,_1D7){return new T2(1,_aI,new T(function(){return B(_cp(_1D6,new T2(1,_aI,_1D7)));}));},_1D8=function(_1D9,_1Da){var _1Db=E(_1D9),_1Dc=new T(function(){var _1Dd=function(_1De){var _1Df=E(_1Db.a),_1Dg=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1Dh){return new F(function(){return _1D5(_1Df.a,_1Dh);});},new T2(1,function(_1Di){return new F(function(){return _1a4(0,_1Df.b,_1Di);});},_Z)),new T2(1,_F,_1De)));});return new T2(1,_G,_1Dg);};return B(A3(_wk,_aC,new T2(1,_1Dd,new T2(1,function(_1Dj){return new F(function(){return _H(0,E(_1Db.b),_1Dj);});},_Z)),new T2(1,_F,_1Da)));});return new T2(1,_G,_1Dc);},_1Dk=new T2(1,_aI,_Z),_1Dl=new T(function(){return B(_1fC(_1ka,5,_1lg));}),_1Dm=new T(function(){return B(unCStr("Thank you!"));}),_1Dn=17,_1Do=2,_1Dp=new T(function(){return B(unCStr("First Up : 2024 12 24"));}),_1Dq=function(_1Dr,_1Ds){var _1Dt=E(_1Ds);return (_1Dt._==0)?__Z:new T2(1,_1Dr,new T2(1,_1Dt.a,new T(function(){return B(_1Dq(_1Dr,_1Dt.b));})));},_1Du=new T(function(){return B(unCStr("noContent"));}),_1Dv=new T(function(){return B(unCStr("noHint"));}),_1Dw=new T(function(){return B(err(_wC));}),_1Dx=new T(function(){return B(err(_wy));}),_1Dy=new T(function(){return B(A3(_JI,_Kb,_HN,_JA));}),_1Dz=function(_1DA,_1DB){var _1DC=E(_1DB);if(!_1DC._){var _1DD=B(_Kk(B(_wH(_1Dy,_1DA))));return (_1DD._==0)?E(_1Dx):(E(_1DD.b)._==0)?new T4(0,E(_1DD.a),_Z,_Z,_Z):E(_1Dw);}else{var _1DE=_1DC.a,_1DF=E(_1DC.b);if(!_1DF._){var _1DG=B(_Kk(B(_wH(_1Dy,_1DA))));return (_1DG._==0)?E(_1Dx):(E(_1DG.b)._==0)?new T4(0,E(_1DG.a),E(_1DE),E(_1Dv),E(_1Du)):E(_1Dw);}else{var _1DH=_1DF.a,_1DI=E(_1DF.b);if(!_1DI._){var _1DJ=B(_Kk(B(_wH(_1Dy,_1DA))));return (_1DJ._==0)?E(_1Dx):(E(_1DJ.b)._==0)?new T4(0,E(_1DJ.a),E(_1DE),E(_1DH),E(_1Du)):E(_1Dw);}else{if(!E(_1DI.b)._){var _1DK=B(_Kk(B(_wH(_1Dy,_1DA))));return (_1DK._==0)?E(_1Dx):(E(_1DK.b)._==0)?new T4(0,E(_1DK.a),E(_1DE),E(_1DH),E(_1DI.a)):E(_1Dw);}else{return new T4(0,0,_Z,_Z,_Z);}}}}},_1DL=function(_1DM){var _1DN=E(_1DM);if(!_1DN._){return new F(function(){return _1Dz(_Z,_Z);});}else{var _1DO=_1DN.a,_1DP=E(_1DN.b);if(!_1DP._){return new F(function(){return _1Dz(new T2(1,_1DO,_Z),_Z);});}else{var _1DQ=E(_1DO),_1DR=new T(function(){var _1DS=B(_Lc(44,_1DP.a,_1DP.b));return new T2(0,_1DS.a,_1DS.b);});if(E(_1DQ)==44){return new F(function(){return _1Dz(_Z,new T2(1,new T(function(){return E(E(_1DR).a);}),new T(function(){return E(E(_1DR).b);})));});}else{var _1DT=E(_1DR);return new F(function(){return _1Dz(new T2(1,_1DQ,_1DT.a),_1DT.b);});}}}},_1DU=function(_1DV){var _1DW=B(_1DL(_1DV));return new T4(0,_1DW.a,E(_1DW.b),E(_1DW.c),E(_1DW.d));},_1DX=function(_1DY){return (E(_1DY)==10)?true:false;},_1DZ=function(_1E0){var _1E1=E(_1E0);if(!_1E1._){return __Z;}else{var _1E2=new T(function(){var _1E3=B(_1g5(_1DX,_1E1));return new T2(0,_1E3.a,new T(function(){var _1E4=E(_1E3.b);if(!_1E4._){return __Z;}else{return B(_1DZ(_1E4.b));}}));});return new T2(1,new T(function(){return E(E(_1E2).a);}),new T(function(){return E(E(_1E2).b);}));}},_1E5=new T(function(){return B(unCStr("57,\u5974\uff1a\u306a\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304c\u5f8c\uff1a\u3053\u3046\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u304b\u3089\u91d1\uff1a\u304d\u3093\uff1a\u5370\uff1a\u3044\u3093\uff1a,<\u5f8c\uff1a\u3054\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308a \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u671f\uff1a\u304d\uff1a\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\uff1a\u3075\u304f\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a\u5fd7\uff1a\u3057\uff1a\u8cc0\uff1a\u304b\u306e\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u3066<\u6f22\uff1a\u304b\u3093\u306e\uff1a\u59d4\uff1a\u308f\u306e\uff1a\u5974\uff1a\u306a\u306e\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a>\u3068\u523b\uff1a\u304d\u3056\uff1a\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\uff1a\u306f\u3063\uff1a\u898b\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b >>\u5927\uff1a\u3084\uff1a\u548c\uff1a\u307e\u3068\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u3068\u306e\u95dc\uff1a\u304b\u3093\uff1a\u4fc2\uff1a\u3051\u3044\uff1a\u4e0d\uff1a\u3075\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f\n239,<\u5351\uff1a\u3072\uff1a\u5f25\uff1a\u307f\uff1a\u547c\uff1a\u3053\uff1a>\u304c\u9b4f\uff1a\u304e\uff1a\u306b\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u66f8\uff1a\u3057\u3087\uff1a<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u3055\u308c\u3066\u3090\u308b\u5deb\uff1a\u307f\uff1a\u5973\uff1a\u3053\uff1a,<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u502d\uff1a\u308f\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u4f1d\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u3057\u308b\uff1a\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\uff1a\u306e\u3053\uff1a\u308b\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3044\uff1a\u3067\u306f\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3067\u304d\u306a\u3044\n316,\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687 \u7a0e\uff1a\u305c\u3044\uff1a\u3092\u514d\uff1a\u3081\u3093\uff1a\u9664\uff1a\u3058\u3087\uff1a,<\u53e4\uff1a\u3053\uff1a\u4e8b\uff1a\u3058\uff1a\u8a18\uff1a\u304d\uff1a><\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a\u7d00\uff1a\u304d\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b,16\u4ee3\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c<\u6c11\uff1a\u305f\u307f\uff1a\u306e\u304b\u307e\u3069\u3088\u308a\u7159\uff1a\u3051\u3080\u308a\uff1a\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\uff1a\u307e\u3065\uff1a\u3057\u304f\u3066\u708a\uff1a\u305f\uff1a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\uff1a\u304d\u3085\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306e\u4fee\uff1a\u3057\u3085\u3046\uff1a\u7e55\uff1a\u305c\u3093\uff1a\u3092\u5f8c\uff1a\u3042\u3068\uff1a\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\uff1a\u3086\u305f\uff1a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d\uff1a\u308f\uff1a>\u306e\u6b66\uff1a\u3076\uff1a\u738b\uff1a\u304a\u3046\uff1a \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5b8b\uff1a\u305d\u3046\uff1a\u3078\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u96c4\uff1a\u3086\u3046\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\uff1a\u3066\u3044\uff1a\u8aac\uff1a\u305b\u3064\uff1a,<\u5b8b\uff1a\u305d\u3046\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u502d\uff1a\u308f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u50b3\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b >> \u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\uff1a\u3076\u3063\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f1d\uff1a\u3067\u3093\uff1a,\u6b3d\uff1a\u304d\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u5fa1\uff1a\u307f\uff1a\u4ee3\uff1a\u3088\uff1a\u306b\u767e\uff1a\u304f\uff1a\u6e08\uff1a\u3060\u3089\uff1a\u306e\u8056\uff1a\u305b\u3044\uff1a\u660e\uff1a\u3081\u3044\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304b\u3089\u50b3\uff1a\u3067\u3093\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3057\u305f\u3068\u306e\u6587\uff1a\u3076\u3093\uff1a\u732e\uff1a\u3051\u3093\uff1a\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\n604,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e03\uff1a\u3057\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u61b2\uff1a\u3051\u3093\uff1a\u6cd5\uff1a\u307d\u3046\uff1a\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u304c\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\uff1a\u308f\uff1a\u3092\u4ee5\uff1a\u3082\u3063\uff1a\u3066\u8cb4\uff1a\u305f\u3075\u3068\uff1a\u3057\u3068\u70ba\uff1a\u306a\uff1a\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\uff1a\u306a\uff1a\u304d\u3092\u5b97\uff1a\u3080\u306d\uff1a\u3068\u305b\u3088>\n607,\u6cd5\uff1a\u307b\u3046\uff1a\u9686\uff1a\u308a\u3085\u3046\uff1a\u5bfa\uff1a\u3058\uff1a\u304c\u5275\uff1a\u305d\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u3086\u304b\u308a\u306e\u5bfa\uff1a\u3058\uff1a\u9662\uff1a\u3044\u3093\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u9662\uff1a\u3044\u3093\uff1a\u4f3d\uff1a\u304c\uff1a\u85cd\uff1a\u3089\u3093\uff1a\u306f\u73fe\uff1a\u3052\u3093\uff1a\u5b58\uff1a\u305e\u3093\uff1a\u3059\u308b\u4e16\u754c\u6700\uff1a\u3055\u3044\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u6728\uff1a\u3082\u304f\uff1a\u9020\uff1a\u305e\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u7bc9\uff1a\u3061\u304f\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\uff1a\u3044\u3063\uff1a\u5df3\uff1a\u3057\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u3053\u306e\u5f8c\u3059\u3050\u5927\uff1a\u305f\u3044\uff1a\u5316\uff1a\u304b\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306a\u308b,\u4e2d\uff1a\u306a\u304b\u306e\uff1a\u5927\uff1a\u304a\u304a\uff1a\u5144\uff1a\u3048\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a(\u5f8c\u306e38\u4ee3\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687)\u304c\u8607\uff1a\u305d\uff1a\u6211\uff1a\u304c\uff1a\u6c0f\uff1a\u3057\uff1a\u3092\u4ea1\uff1a\u307b\u308d\uff1a\u307c\u3059\n663,\u767d\uff1a\u306f\u304f\uff1a\u6751\uff1a\u3059\u304d\u306e\uff1a\u6c5f\uff1a\u3048\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u3068\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u306b\u6ec5\uff1a\u307b\u308d\uff1a\u307c\u3055\u308c\u305f\u767e\uff1a\u304f\u3060\uff1a\u6e08\uff1a\u3089\uff1a\u3092\u518d\uff1a\u3055\u3044\uff1a\u8208\uff1a\u3053\u3046\uff1a\u3059\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u30fb\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u3054\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u308b\n672,\u58ec\uff1a\u3058\u3093\uff1a\u7533\uff1a\u3057\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u4e89\uff1a\u3042\u3089\u305d\uff1a\u3072,\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u3067\u3042\u3063\u305f\u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u306b\u53d4\uff1a\u304a\uff1a\u7236\uff1a\u3058\uff1a\u306e\u5927\uff1a\u304a\u304a\uff1a\u6d77\uff1a\u3042\uff1a\u4eba\uff1a\u307e\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u304c\u53cd\uff1a\u306f\u3093\uff1a\u65d7\uff1a\u304d\uff1a\u3092\u7ffb\uff1a\u3072\u308b\u304c\u3078\uff1a\u3057 \u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u3066\u5929\uff1a\u3066\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\uff1a\u3078\u3044\uff1a\u57ce\uff1a\u3058\u3087\u3046\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\uff1a\u3088\uff1a\u3080,\u548c\uff1a\u308f\uff1a\u9285\uff1a\u3069\u3046\uff1a3\u5e74 \u7b2c43\u4ee3\u5143\uff1a\u3052\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306b\u3088\u308b \u5148\uff1a\u305b\u3093\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u6587\uff1a\u3082\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u304c\u75ab\uff1a\u3048\u304d\uff1a\u75c5\uff1a\u3073\u3087\u3046\uff1a\u3067\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a13\u5e74 \u7b2c50\u4ee3\u6853\uff1a\u304b\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687 \u9577\uff1a\u306a\u304c\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u306b\u3088\u308b\u798f\uff1a\u3075\u304f\uff1a\u539f\uff1a\u306f\u3089\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\u90fd\u3084\u5357\uff1a\u306a\u3093\uff1a\u5317\uff1a\u307c\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u6642\u4ee3\u306e\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306a\u3069\u306e\u4f8b\uff1a\u308c\u3044\uff1a\u5916\uff1a\u304c\u3044\uff1a\u306f\u3042\u308b\u3082\u306e\u306e \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u7dad\uff1a\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\uff1a\u3064\u3065\uff1a\u304f\n806,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u304c\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u304c\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u671f\uff1a\u304d\uff1a \u3069\u3061\u3089\u3082\u5510\uff1a\u3068\u3046\uff1a\u3067\u4fee\uff1a\u3057\u3085\uff1a\u884c\uff1a\u304e\u3087\u3046\uff1a\u3057\u5e30\uff1a\u304d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u5f8c\uff1a\u3054\uff1a \u4ecf\uff1a\u3076\u3064\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u306f\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u6bd4\uff1a\u3072\uff1a\u53e1\uff1a\u3048\u3044\uff1a\u5c71\uff1a\u3056\u3093\uff1a\u306b\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a\u5bfa\uff1a\u3058\uff1a\u3092 \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u306f\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\u304d \u9ad8\uff1a\u3053\u3046\uff1a\u91ce\uff1a\u3084\uff1a\u5c71\uff1a\u3055\u3093\uff1a\u306b\u91d1\uff1a\u3053\u3093\uff1a\u525b\uff1a\u3054\u3046\uff1a\u5cf0\uff1a\u3076\uff1a\u5bfa\uff1a\u3058\uff1a\u3092\u5efa\uff1a\u3053\u3093\uff1a\u7acb\uff1a\u308a\u3085\u3046\uff1a\n857,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u826f\uff1a\u3088\u3057\uff1a\u623f\uff1a\u3075\u3055\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,56\u4ee3\u6e05\uff1a\u305b\u3044\uff1a\u548c\uff1a\u308f\uff1a\u5929\u7687\u306e\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a,\u81e3\uff1a\u3057\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u306e\u8eab\uff1a\u307f\uff1a\u5206\uff1a\u3076\u3093\uff1a\u3067\u521d\u3081\u3066\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b\u306a\u3063\u305f\n894,\u9063\uff1a\u3051\u3093\uff1a\u5510\uff1a\u3068\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u304c\u5ec3\uff1a\u306f\u3044\uff1a\u6b62\uff1a\u3057\uff1a\u3055\u308c\u308b,\u83c5\uff1a\u3059\u304c\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u771f\uff1a\u3056\u306d\uff1a\u306e\u5efa\uff1a\u3051\u3093\uff1a\u8b70\uff1a\u304e\uff1a\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\uff1a\u3068\u3046\uff1a\u306f\u6ec5\uff1a\u307b\u308d\uff1a\u3073\u5c0f\uff1a\u3057\u3087\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5206\uff1a\u3076\u3093\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3057\u305f\u5f8c \u5b8b\uff1a\u305d\u3046\uff1a(\u5317\uff1a\u307b\u304f\uff1a\u5b8b\uff1a\u305d\u3046\uff1a)\u304c\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5927\uff1a\u305f\u3044\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3092\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3059\u308b\n935,\u627f\uff1a\u3057\u3087\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5929\uff1a\u3066\u3093\uff1a\u6176\uff1a\u304e\u3087\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u5c06\uff1a\u306e\u307e\u3055\uff1a\u9580\uff1a\u304b\u3069\uff1a\u3084\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u7d14\uff1a\u3059\u307f\uff1a\u53cb\uff1a\u3068\u3082\uff1a\u3068\u3044\u3064\u305f\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u95a2\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u3078\u306e\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u5e95\uff1a\u3066\u3044\uff1a\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\uff1a\u6c0f\uff1a\u3057\uff1a\u5168\uff1a\u305c\u3093\uff1a\u76db\uff1a\u305b\u3044\uff1a\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u9577\uff1a\u3061\u3087\u3046\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(66\u4ee3)\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b \u6b21\uff1a\u3058\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e09\uff1a\u3055\u3093\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\uff1a\u3055\u3093\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u5f8c\uff1a\u3054\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\uff1a\u3044\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u958b\uff1a\u304b\u3044\uff1a\u59cb\uff1a\u3057\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u3084\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3092\u6291\uff1a\u304a\u3055\uff1a\u3078\u308b,72\u4ee3\u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u5929\u7687\u304c\u8b72\uff1a\u3058\u3087\u3046\uff1a\u4f4d\uff1a\u3044\uff1a\u5f8c \u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u3068\u306a\u308a \u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u306e\u5b9f\uff1a\u3058\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u63e1\uff1a\u306b\u304e\uff1a\u308b\n1167,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,\u5a18\uff1a\u3080\u3059\u3081\uff1a\u3092\u5929\u7687\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b\u3057 81\u4ee3\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c\u8a95\uff1a\u305f\u3093\uff1a\u751f\uff1a\u3058\u3087\u3046\uff1a,\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u3068\u3057\u3066\u521d\uff1a\u306f\u3058\uff1a\u3081\u3066\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c\u308b\n1185,\u5e73\uff1a\u3078\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u307c\u3046\uff1a,\u58c7\uff1a\u3060\u3093\uff1a\u30ce\uff1a\u306e\uff1a\u6d66\uff1a\u3046\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u306e\u547d\uff1a\u3081\u3044\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u305f \u5f1f\uff1a\u304a\u3068\u3046\u3068\uff1a\u306e\u7fa9\uff1a\u3088\u3057\uff1a\u7d4c\uff1a\u3064\u306d\uff1a\u3089\u306e\u6d3b\uff1a\u304b\u3064\uff1a\u8e8d\uff1a\u3084\u304f\uff1a\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u306f\u6578\uff1a\u304b\u305e\uff1a\u3078\u5e74\u4e03\u6b73\uff1a\u3055\u3044\uff1a\u3067\u5165\uff1a\u306b\u3085\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u3057\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u308b\n1192,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u304c\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b,\u6b66\uff1a\u3076\uff1a\u5bb6\uff1a\u3051\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u672c\uff1a\u307b\u3093\uff1a\u683c\uff1a\u304b\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u306b\u59cb\uff1a\u306f\u3058\uff1a\u307e\u308b\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a\n1221,\u627f\uff1a\u3058\u3087\u3046\uff1a\u4e45\uff1a\u304d\u3085\u3046\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u5168\uff1a\u305c\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306b \u57f7\uff1a\u3057\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6642\uff1a\u3068\u304d\uff1a\u306e\u8a0e\uff1a\u3068\u3046\uff1a\u4f10\uff1a\u3070\u3064\uff1a\u3092\u547d\uff1a\u3081\u3044\uff1a\u305a\u308b\u5f8c\uff1a\u3054\uff1a\u9ce5\uff1a\u3068\uff1a\u7fbd\uff1a\u3070\uff1a\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u306e\u9662\uff1a\u3044\u3093\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u304c\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c\u308b,\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306f\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3055\u308c\u5931\uff1a\u3057\u3063\uff1a\u6557\uff1a\u3071\u3044\uff1a \n1274,\u6587\uff1a\u3076\u3093\uff1a\u6c38\uff1a\u3048\u3044\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,1281\u5e74\u306e\u5f18\uff1a\u3053\u3046\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3068\u5408\uff1a\u3042\uff1a\u306f\u305b\u3066 \u5143\uff1a\u3052\u3093\uff1a\u5bc7\uff1a\u3053\u3046\uff1a\u3068\u547c\uff1a\u3088\uff1a\u3076,\u7d04\u4e09\u4e07\u306e\u5143\uff1a\u3052\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u304c\u7d04\uff1a\u3084\u304f\uff1a900\u96bb\uff1a\u305b\u304d\uff1a\u306e\u8ecd\uff1a\u3050\u3093\uff1a\u8239\uff1a\u305b\u3093\uff1a\u3067\u5317\uff1a\u304d\u305f\uff1a\u4e5d\uff1a\u304d\u3085\u3046\uff1a\u5dde\uff1a\u3057\u3085\u3046\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u653b\uff1a\u3053\u3046\uff1a\u3059\u308b\u3082\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6483\uff1a\u3052\u304d\uff1a\u9000\uff1a\u305f\u3044\uff1a\u3055\u308c\u308b\n1334,\u5efa\uff1a\u3051\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u306e\u65b0\uff1a\u3057\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a,\u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u304c\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u3092\u5fd7\uff1a\u3053\u3053\u308d\u3056\uff1a\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\uff1a\u308a\uff1a\u53cd\uff1a\u306f\u3093\uff1a\u3057 \u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u306f\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306b\u9003\uff1a\u306e\u304c\uff1a\u308c \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u306f\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3092\u64c1\uff1a\u3088\u3046\uff1a\u3057\u305f\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\u304f\n1338,\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u304c\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6e80\uff1a\u307f\u3064\uff1a(3\u4ee3)\u304c\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u306b<\u82b1\uff1a\u306f\u306a\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u6240\uff1a\u3057\u3087\uff1a>\u3092\u69cb\uff1a\u304b\u307e\uff1a\u3078\u653f\u6cbb\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\uff1a\u3057\u3087\u3046\uff1a\u3055\u308c\u308b\n1429,\u7409\uff1a\u308a\u3085\u3046\uff1a\u7403\uff1a\u304d\u3085\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,\u4e09\u3064\u306e\u52e2\uff1a\u305b\u3044\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u304c\u5341\u4e94\u4e16\uff1a\u305b\u3044\uff1a\u7d00\uff1a\u304d\uff1a\u306b\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3055\u308c\u308b,\u660e\uff1a\u307f\u3093\uff1a\u306e\u518a\uff1a\u3055\u304f\uff1a\u5c01\uff1a\u307b\u3046\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3061\u3087\u3046\uff1a\u8ca2\uff1a\u3053\u3046\uff1a\u8cbf\uff1a\u307c\u3046\uff1a\u6613\uff1a\u3048\u304d\uff1a\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3075\n1467,\u61c9\uff1a\u304a\u3046\uff1a\u4ec1\uff1a\u306b\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u5e55\uff1a\u307e\u304f\uff1a\u958b\uff1a\u3042\uff1a\u3051,\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u5bb6\uff1a\u3051\uff1a\u3068\u7ba1\uff1a\u304b\u3093\uff1a\u9818\uff1a\u308c\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u306e\u8de1\uff1a\u3042\u3068\uff1a\u7d99\uff1a\u3064\u304e\uff1a\u304e\u722d\uff1a\u3042\u3089\u305d\uff1a\u3072\u304c11\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u304d\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u753a\uff1a\u307e\u3061\uff1a\u306f\u7126\uff1a\u3057\u3087\u3046\uff1a\u571f\uff1a\u3069\uff1a\u3068\u5316\uff1a\u304b\uff1a\u3059\n1495,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u304c\u5c0f\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u539f\uff1a\u306f\u3089\uff1a\u5165\uff1a\u306b\u3075\uff1a\u57ce\uff1a\u3058\u3083\u3046\uff1a,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u306f\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u306e\u5148\uff1a\u3055\u304d\uff1a\u99c6\uff1a\u304c\uff1a\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\uff1a\u304b\uff1a\u7a0b\uff1a\u3066\u3044\uff1a\u306f \u5bb6\uff1a\u304b\uff1a\u81e3\uff1a\u3057\u3093\uff1a\u304c\u4e3b\uff1a\u3057\u3085\uff1a\u541b\uff1a\u304f\u3093\uff1a\u304b\u3089\u6a29\uff1a\u3051\u3093\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3063\u3066\u306e\u3057\u4e0a\uff1a\u3042\u304c\uff1a\u308b\u3068\u3044\u3075<\u4e0b\uff1a\u3052\uff1a\u524b\uff1a\u3053\u304f\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6230\u570b\u5927\u540d\u306e\u5686\uff1a\u304b\u3046\uff1a\u77e2\uff1a\u3057\uff1a\u3068\u3044\u3078\u308b\n1542,\u658e\uff1a\u3055\u3044\uff1a\u85e4\uff1a\u3068\u3046\uff1a\u9053\uff1a\u3069\u3046\uff1a\u4e09\uff1a\u3056\u3093\uff1a\u304c\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3046,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6b66\uff1a\u3076\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u306e\u4e00\uff1a\u3044\u3061\uff1a,\u4ed6\uff1a\u307b\u304b\uff1a\u306b\u3082\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3057\u305f\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u5eb7\uff1a\u3084\u3059\uff1a \u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a \u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3048\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a \u51fa\uff1a\u3067\uff1a\u7fbd\uff1a\u306f\uff1a\u3068\u9678\uff1a\u3080\uff1a\u5965\uff1a\u3064\uff1a\u306e\u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u6b63\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a \u5b89\uff1a\u3042\uff1a\u82b8\uff1a\u304d\uff1a\u306e\u6bdb\uff1a\u3082\u3046\uff1a\u5229\uff1a\u308a\uff1a\u5143\uff1a\u3082\u3068\uff1a\u5c31\uff1a\u306a\u308a\uff1a \u571f\uff1a\u3068\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u9577\uff1a\u3061\u3083\u3046\uff1a\u5b97\uff1a\u305d\uff1a\u6211\uff1a\u304b\uff1a\u90e8\uff1a\u3079\uff1a\u5143\uff1a\u3082\u3068\uff1a\u89aa\uff1a\u3061\u304b\uff1a \u85a9\uff1a\u3055\u3064\uff1a\u6469\uff1a\u307e\uff1a\u306e\u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u8cb4\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\uff1a\u304b\u306f\uff1a\u4e2d\uff1a\u306a\u304b\uff1a\u5cf6\uff1a\u3058\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a\u3068\u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3078\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u6709\uff1a\u3044\u3046\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306a\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3067\u52dd\uff1a\u3057\u3087\u3046\uff1a\u6557\uff1a\u306f\u3044\uff1a\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\u3082\u5b9a\uff1a\u3055\u3060\uff1a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\uff1a\u304a\u3051\uff1a\u72ed\uff1a\u306f\u3056\uff1a\u9593\uff1a\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u306e\u7e54\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u99ff\uff1a\u3059\u308b\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u4eca\uff1a\u3044\u307e\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u5143\uff1a\u3082\u3068\uff1a\u3092\u7834\uff1a\u3084\u3076\uff1a\u308b,\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u3068\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u4e0b\uff1a\u304b\uff1a\u306b\u304a\u304d <\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5e03\uff1a\u3075\uff1a\u6b66\uff1a\u3076\uff1a>\u3092\u304b\u304b\u3052 \u5f8c\uff1a\u306e\u3061\uff1a\u306b\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u662d\uff1a\u3042\u304d\uff1a\u3092\u4eac\uff1a\u304d\u3083\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u304b\u3089\u8ffd\uff1a\u3064\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3057\u3066\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u3070\u3046\uff1a\u3055\u305b\u308b\n1590,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,106\u4ee3\u6b63\uff1a\u304a\u307b\uff1a\u89aa\uff1a\u304e\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5929\u7687\u304b\u3089\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u4f4d\uff1a\u304f\u3089\u3090\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u3051\u3089\u308c \u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3078\u306e\u5f8c\uff1a\u3042\u3068\uff1a\u62bc\uff1a\u304a\uff1a\u3057\u3092\u3082\u3089\u3075,\u60e3\uff1a\u3055\u3046\uff1a\u7121\uff1a\u3076\uff1a\u4e8b\uff1a\u3058\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u3092\u51fa\uff1a\u3060\uff1a\u3057\u3066\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u79c1\uff1a\u3057\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u3058 \u5929\uff1a\u3066\u3093\uff1a\u7687\uff1a\u308f\u3046\uff1a\u3088\u308a\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u306e\u59d3\uff1a\u305b\u3044\uff1a\u3092\u8cdc\uff1a\u305f\u307e\u306f\uff1a\u308a \u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3083\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a \u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u653f\uff1a\u307e\u3055\uff1a \u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u653f\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a\u3089\u8af8\uff1a\u3057\u3087\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3083\u3046\uff1a\u3092\u5e73\uff1a\u3078\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\uff1a\u3076\u3093\uff1a\u7984\uff1a\u308d\u304f\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3063\uff1a\u5175\uff1a\u307a\u3044\uff1a,\u4e8c\uff1a\u306b\uff1a\u5ea6\uff1a\u3069\uff1a\u76ee\uff1a\u3081\uff1a\u306e\u6176\uff1a\u3051\u3044\uff1a\u9577\uff1a\u3061\u3083\u3046\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3067\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u304c\u6ca1\uff1a\u307c\u3063\uff1a\u3057 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u304b\u3089\u64a4\uff1a\u3066\u3063\uff1a\u9000\uff1a\u305f\u3044\uff1a\n1600,\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u3053\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u5f8c\uff1a\u3054\uff1a\u967d\uff1a\u3084\u3046\uff1a\u6210\uff1a\u305c\u3044\uff1a\u5929\u7687\u306b\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\u304c\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306b\u304a\u3051\u308b\u4e94\uff1a\u3054\uff1a\u5927\uff1a\u305f\u3044\uff1a\u8001\uff1a\u3089\u3046\uff1a\u306e\u7b46\uff1a\u3072\u3063\uff1a\u982d\uff1a\u3068\u3046\uff1a\u3067\u3042\u3063\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u6c0f\uff1a\u3057\uff1a\u306e\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u7dad\uff1a\u3090\uff1a\u6301\uff1a\u3062\uff1a\u3057\u3084\u3046\u3068\u3059\u308b\u77f3\uff1a\u3044\u3057\uff1a\u7530\uff1a\u3060\uff1a\u4e09\uff1a\u307f\u3064\uff1a\u6210\uff1a\u306a\u308a\uff1a\u3068\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u3067\u5c0d\uff1a\u305f\u3044\uff1a\u6c7a\uff1a\u3051\u3064\uff1a\u30fc\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5206\uff1a\u308f\uff1a\u3051\u76ee\uff1a\u3081\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3068\u3044\u306f\u308c \u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3067\u3042\u308b\u5fb3\u5ddd\u5bb6\u5eb7\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\n1637,\u5cf6\uff1a\u3057\u307e\uff1a\u539f\uff1a\u3070\u3089\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u3044\u306f\u3086\u308b<\u9396\uff1a\u3055\uff1a\u570b\uff1a\u3053\u304f\uff1a>\u653f\uff1a\u305b\u3044\uff1a\u7b56\uff1a\u3055\u304f\uff1a\u306e\u5f15\uff1a\u3072\uff1a\u304d\u91d1\uff1a\u304c\u306d\uff1a\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u3089\u304c\u5bfa\uff1a\u3058\uff1a\u793e\uff1a\u3057\u3083\uff1a\u306b\u653e\uff1a\u306f\u3046\uff1a\u706b\uff1a\u304f\u308f\uff1a\u3057\u50e7\uff1a\u305d\u3046\uff1a\u4fb6\uff1a\u308a\u3087\uff1a\u3092\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306f\u5927\uff1a\u305f\u3044\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u9001\uff1a\u304a\u304f\uff1a\u308a\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3059\u308b\n1685,\u751f\uff1a\u3057\u3083\u3046\uff1a\u985e\uff1a\u308b\uff1a\u6190\uff1a\u3042\u306f\u308c\uff1a\u307f\u306e\u4ee4\uff1a\u308c\u3044\uff1a,\u4e94\uff1a\u3054\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7db1\uff1a\u3064\u306a\uff1a\u5409\uff1a\u3088\u3057\uff1a,\u75c5\uff1a\u3073\u3083\u3046\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u907a\uff1a\u3090\uff1a\u68c4\uff1a\u304d\uff1a\u3084\u6368\uff1a\u3059\uff1a\u3066\u5b50\uff1a\u3054\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u6b62\uff1a\u3057\uff1a \u4eba\uff1a\u306b\u3093\uff1a\u9593\uff1a\u3052\u3093\uff1a\u4ee5\uff1a\u3044\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u3042\u3089\u3086\u308b\u751f\uff1a\u305b\u3044\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3078\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3084\u6bba\uff1a\u305b\u3063\uff1a\u751f\uff1a\u3057\u3083\u3046\uff1a\u3092\u3082\u7f70\uff1a\u3070\u3064\uff1a\u3059\u308b\u3053\u3068\u3067 \u9053\uff1a\u3060\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u559a\uff1a\u304b\u3093\uff1a\u8d77\uff1a\u304d\uff1a\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\uff1a\u304d\u3084\u3046\uff1a\u4fdd\uff1a\u307b\u3046\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u516b\uff1a\u306f\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5409\uff1a\u3088\u3057\uff1a\u5b97\uff1a\u3080\u306d\uff1a,\u8cea\uff1a\u3057\u3063\uff1a\u7d20\uff1a\u305d\uff1a\u5039\uff1a\u3051\u3093\uff1a\u7d04\uff1a\u3084\u304f\uff1a \u7c73\uff1a\u3053\u3081\uff1a\u306e\u5897\uff1a\u305e\u3046\uff1a\u53ce\uff1a\u3057\u3046\uff1a \u516c\uff1a\u304f\uff1a\u4e8b\uff1a\u3058\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u5fa1\uff1a\u304a\uff1a\u5b9a\uff1a\u3055\u3060\u3081\uff1a\u66f8\uff1a\u304c\u304d\uff1a \u5be6\uff1a\u3058\u3064\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u306e\u5968\uff1a\u3057\u3084\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u76ee\uff1a\u3081\uff1a\u5b89\uff1a\u3084\u3059\uff1a\u7bb1\uff1a\u3070\u3053\uff1a\u306a\u3069\n1767,\u7530\uff1a\u305f\uff1a\u6cbc\uff1a\u306c\u307e\uff1a\u610f\uff1a\u304a\u304d\uff1a\u6b21\uff1a\u3064\u3050\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6cbb\uff1a\u306f\u308b\uff1a\u306e\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a,\u682a\uff1a\u304b\u3076\uff1a\u4ef2\uff1a\u306a\u304b\uff1a\u9593\uff1a\u307e\uff1a\u3092\u516c\uff1a\u3053\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a \u7a0e\uff1a\u305c\u3044\uff1a\u5236\uff1a\u305b\u3044\uff1a\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a \u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u3092\u6d3b\uff1a\u304b\u3063\uff1a\u6027\uff1a\u305b\u3044\uff1a\u5316\uff1a\u304b\uff1a\u3055\u305b\u308b\n1787,\u5bdb\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6589\uff1a\u306a\u308a\uff1a\u304c \u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u4e3b\uff1a\u3057\u3085\uff1a \u677e\uff1a\u307e\u3064\uff1a\u5e73\uff1a\u3060\u3044\u3089\uff1a\u5b9a\uff1a\u3055\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u3092\u767b\uff1a\u3068\u3046\uff1a\u7528\uff1a\u3088\u3046\uff1a,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\uff1a\u3057\u3083\u3063\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u306e\u5e33\uff1a\u3061\u3083\u3046\uff1a\u6d88\uff1a\u3051\uff1a\u3057 \u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u306e\u5e30\uff1a\u304d\uff1a\u90f7\uff1a\u304d\u3083\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059 \u6e6f\uff1a\u3086\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u660c\uff1a\u3057\u3083\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5742\uff1a\u3056\u304b\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u6240\uff1a\u3058\u3087\uff1a\u3092\u3064\u304f\u308a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u30fb\u6b66\uff1a\u3076\uff1a\u8853\uff1a\u3058\u3085\u3064\uff1a\u3092\u5968\uff1a\u3057\u3083\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u53b3\uff1a\u304d\u3073\uff1a\u3057\u3044\u7dca\uff1a\u304d\u3093\uff1a\u7e2e\uff1a\u3057\u3085\u304f\uff1a\u8ca1\uff1a\u3056\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u3067\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u306f\u505c\uff1a\u3066\u3044\uff1a\u6ede\uff1a\u305f\u3044\uff1a\n1837,\u5927\uff1a\u304a\u307b\uff1a\u5869\uff1a\u3057\u307b\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u516b\uff1a\u306f\u3061\uff1a\u90ce\uff1a\u3089\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u4fdd\uff1a\u307d\u3046\uff1a\u306e\u98e2\uff1a\u304d\uff1a\u9949\uff1a\u304d\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u672c\uff1a\u307d\u3093\uff1a\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064,\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306e\u5143\uff1a\u3082\u3068\uff1a\u5f79\uff1a\u3084\u304f\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u5e55\u5e9c\u306b\u885d\uff1a\u3057\u3087\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1854,\u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u548c\uff1a\u308f\uff1a\u89aa\uff1a\u3057\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\uff1a\u3046\u3089\uff1a\u8cc0\uff1a\u304c\uff1a\u306b\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u56db\uff1a\u3088\u3093\uff1a\u96bb\uff1a\u305b\u304d\uff1a\u3067\u4f86\uff1a\u3089\u3044\uff1a\u822a\uff1a\u304b\u3046\uff1a,\u4e0b\uff1a\u3057\u3082\uff1a\u7530\uff1a\u3060\uff1a(\u9759\uff1a\u3057\u3065\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a)\u30fb\u7bb1\uff1a\u306f\u3053\uff1a\u9928\uff1a\u3060\u3066\uff1a(\u5317\uff1a\u307b\u3063\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u9053\uff1a\u3060\u3046\uff1a)\u306e\u4e8c\uff1a\u306b\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304f\n1860,\u685c\uff1a\u3055\u304f\u3089\uff1a\u7530\uff1a\u3060\uff1a\u9580\uff1a\u3082\u3093\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,121\u4ee3\uff1a\u3060\u3044\uff1a\u5b5d\uff1a\u304b\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306e\u52c5\uff1a\u3061\u3087\u304f\uff1a\u8a31\uff1a\u304d\u3087\uff1a\u3092\u5f97\u305a \u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3093\u3060 \u3068\u3044\u3075\u6279\uff1a\u3072\uff1a\u5224\uff1a\u306f\u3093\uff1a\u306b \u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c \u5b89\uff1a\u3042\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u7344\uff1a\u3054\u304f\uff1a\u3067\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u5fd7\uff1a\u3057\uff1a\u58eb\uff1a\u3057\uff1a\u3092\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u3057\u305f\u3053\u3068\u304c\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u3068\u3055\u308c\u308b,\u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c\u6c34\uff1a\u307f\uff1a\u6238\uff1a\u3068\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u306e\u6d6a\uff1a\u3089\u3046\uff1a\u58eb\uff1a\u3057\uff1a\u3089\u306b\u6697\uff1a\u3042\u3093\uff1a\u6bba\uff1a\u3055\u3064\uff1a\u3055\u308c\u308b\n1868,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a,\u524d\uff1a\u305c\u3093\uff1a\u5e74\uff1a\u306d\u3093\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5949\uff1a\u307b\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3066\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u304c<\u738b\uff1a\u308f\u3046\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5fa9\uff1a\u3075\u3063\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u5927\uff1a\u3060\u3044\uff1a\u53f7\uff1a\u304c\u3046\uff1a\u4ee4\uff1a\u308c\u3044\uff1a>\u3092\u51fa\uff1a\u3060\uff1a\u3059,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u5929\u7687\u304c \u4e94\uff1a\u3054\uff1a\u7b87\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u8a93\uff1a\u305b\u3044\uff1a\u6587\uff1a\u3082\u3093\uff1a\u3092\u767c\uff1a\u306f\u3063\uff1a\u5e03\uff1a\u3077\uff1a\u3055\u308c\u308b\n1875,\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a,\u3053\u306e\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u306e\u7d50\uff1a\u3051\u3064\uff1a\u679c\uff1a\u304b\uff1a \u65e5\uff1a\u306b\u3063\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u898f\uff1a\u304d\uff1a(\u4e0d\uff1a\u3075\uff1a\u5e73\uff1a\u3073\u3084\u3046\uff1a\u7b49\uff1a\u3069\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3068\u3055\u308c\u308b)\u3092\u7de0\uff1a\u3066\u3044\uff1a\u7d50\uff1a\u3051\u3064\uff1a,\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u53f7\uff1a\u3054\u3046\uff1a\u304c\u98f2\uff1a\u3044\u3093\uff1a\u6599\uff1a\u308c\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u4fdd\uff1a\u307b\uff1a\u306e\u305f\u3081\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u306b\u63a5\uff1a\u305b\u3063\uff1a\u8fd1\uff1a\u304d\u3093\uff1a\u3057\u305f\u969b\uff1a\u3055\u3044\uff1a \u7a81\uff1a\u3068\u3064\uff1a\u5982\uff1a\u3058\u3087\uff1a\u540c\uff1a\u3069\u3046\uff1a\u5cf6\uff1a\u3068\u3046\uff1a\u306e\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3088\u308a\u5f37\uff1a\u304d\u3083\u3046\uff1a\u70c8\uff1a\u308c\u3064\uff1a\u306a\u7832\uff1a\u306f\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b >>\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3057\u9678\uff1a\u308a\u304f\uff1a\u6230\uff1a\u305b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3055\u305b\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u62e0\uff1a\u304d\u3087\uff1a \u6b66\uff1a\u3076\uff1a\u5668\uff1a\u304d\uff1a\u3092\u6355\uff1a\u307b\uff1a\u7372\uff1a\u304b\u304f\uff1a\u3057\u3066\u9577\uff1a\u306a\u304c\uff1a\u5d0e\uff1a\u3055\u304d\uff1a\u3078\u5e30\uff1a\u304d\uff1a\u7740\uff1a\u3061\u3083\u304f\uff1a\n1877,\u897f\uff1a\u305b\u3044\uff1a\u5357\uff1a\u306a\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092\u6230\uff1a\u305f\u305f\u304b\uff1a\u3063\u305f\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u305f\u3061\u304c \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306b\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u3092\u62b1\uff1a\u3044\u3060\uff1a\u304d \u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u62c5\uff1a\u304b\u3064\uff1a\u3044\u3067\u8702\uff1a\u307b\u3046\uff1a\u8d77\uff1a\u304d\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u7dcf\uff1a\u305d\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u3068\u3059\u308b\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3055\u308c \u897f\u90f7\u306f\u81ea\uff1a\u3058\uff1a\u6c7a\uff1a\u3051\u3064\uff1a \u4ee5\uff1a\u3044\uff1a\u5f8c\uff1a\u3054\uff1a\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u306e\u53cd\u4e82\u306f\u9014\uff1a\u3068\uff1a\u7d76\uff1a\u3060\uff1a\u3078 \u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u304b\u3089\u5341\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u3044\u3066\u3090\u305f\u52d5\uff1a\u3069\u3046\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u53ce\uff1a\u3057\u3046\uff1a\u675f\uff1a\u305d\u304f\uff1a\u3057\u305f\n1894,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u3067\u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u4e00\uff1a\u3044\u3063\uff1a\u63c6\uff1a\u304d\uff1a\u304c\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u66b4\uff1a\u307c\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u5316\uff1a\u304b\uff1a(\u6771\uff1a\u3068\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u9ee8\uff1a\u305f\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a) \u304c\u8d77\uff1a\u304d\uff1a\u7206\uff1a\u3070\u304f\uff1a\u5264\uff1a\u3056\u3044\uff1a\u3068\u306a\u308b,\u8c4a\uff1a\u3068\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306f \u6211\uff1a\u308f\uff1a\u304c\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u904a\uff1a\u3044\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u968a\uff1a\u305f\u3044\uff1a\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u304c\u793c\uff1a\u308c\u3044\uff1a\u7832\uff1a\u306f\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u63db\uff1a\u304f\u308f\u3093\uff1a\u306e\u7528\uff1a\u3088\u3046\uff1a\u610f\uff1a\u3044\uff1a\u3092\u3057\u3066\u8fd1\uff1a\u304d\u3093\uff1a\u63a5\uff1a\u305b\u3064\uff1a\u3057\u305f\u306e\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u6e08\uff1a\u305b\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304a\u3088\u3073\u767c\uff1a\u306f\u3063\uff1a\u7832\uff1a\u3071\u3046\uff1a\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\uff1a\u3057\u3082\u306e\uff1a\u95a2\uff1a\u305b\u304d\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306b\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u3066\u7d50\uff1a\u3080\u3059\uff1a\u3070\u308c\u305f\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a >> \u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5e72\uff1a\u304b\u3093\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b,\u4e00 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5b8c\uff1a\u304b\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u7121\uff1a\u3080\uff1a\u6b20\uff1a\u3051\u3064\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u81ea\uff1a\u3058\uff1a\u4e3b\uff1a\u3057\u3085\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u3067\u3042\u308b\u3053\u3068\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u4e8c \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u907c\uff1a\u308a\u3087\u3046\uff1a\u6771\uff1a\u3068\u3046\uff1a\u534a\uff1a\u306f\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a \u53f0\uff1a\u305f\u3044\uff1a\u6e7e\uff1a\u308f\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u53ca\uff1a\u304a\u3088\uff1a\u3073\u6f8e\uff1a\u307b\u3046\uff1a\u6e56\uff1a\u3053\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u6c38\uff1a\u3048\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306b\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306b\u5272\uff1a\u304b\u3064\uff1a\u8b72\uff1a\u3058\u3083\u3046\uff1a\u3059\u308b \u4e09 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u8ecd\uff1a\u3050\u3093\uff1a\u8cbb\uff1a\u3074\uff1a\u8ce0\uff1a\u3070\u3044\uff1a\u511f\uff1a\u3057\u3083\u3046\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u4e8c\uff1a\u306b\uff1a\u5104\uff1a\u304a\u304f\uff1a\u4e21\uff1a\u30c6\u30fc\u30eb\uff1a\u3092\u652f\uff1a\u3057\uff1a\u6255\uff1a\u306f\u3089\uff1a\u3075 \u56db \u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u306f\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u305f\u3081\u6d88\uff1a\u3057\u3087\u3046\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u305f\u306e\u3067\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u822a\uff1a\u304b\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3076 \u4e94 \u672c\uff1a\u307b\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u76f4\uff1a\u305f\u3060\uff1a\u3061\u306b\u4fd8\uff1a\u3075\uff1a\u865c\uff1a\u308a\u3087\uff1a\u3092\u8fd4\uff1a\u3078\u3093\uff1a\u9084\uff1a\u304b\u3093\uff1a\u3059\u308b \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u9001\uff1a\u305d\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3042\u308b\u3044\u306f\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u305b\u306c\u3053\u3068\n1899,\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3068\u8a00\uff1a\u3044\uff1a\u3078\u308b,\u5b97\uff1a\u3057\u3085\u3046\uff1a\u6559\uff1a\u3051\u3046\uff1a\u7684\uff1a\u3066\u304d\uff1a\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u7d50\uff1a\u3051\u3063\uff1a\u793e\uff1a\u3057\u3083\uff1a\u3067\u3042\u308b\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u304c<\u6276\uff1a\u3075\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u6d0b\uff1a\u3084\u3046\uff1a>\u3092\u304b\u304b\u3052 \u5c71\uff1a\u3055\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u7701\uff1a\u3057\u3083\u3046\uff1a\u3067 \u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u306e\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a \u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u306a\u3069\u3092\u884c\uff1a\u304a\u3053\uff1a\u306a\u3044 \u6e05\uff1a\u3057\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u7d50\uff1a\u3051\u3063\uff1a\u8a17\uff1a\u305f\u304f\uff1a\u3057\u3066 \u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u306e\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a \u6e05\uff1a\u3057\u3093\uff1a\u5e1d\uff1a\u3066\u3044\uff1a\u306f\u5217\uff1a\u308c\u3063\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u5ba3\uff1a\u305b\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u8aed\uff1a\u3086\uff1a\u3092\u767c\uff1a\u306f\u3064\uff1a\u3059\u308b\u3082 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3092\u4e3b\uff1a\u3057\u3085\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3068\u3059\u308b\u516b\uff1a\u306f\u3061\uff1a\u30f6\uff1a\u304b\uff1a\u570b\uff1a\u3053\u304f\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u30fb\u6e05\uff1a\u3057\u3093\uff1a\u5175\uff1a\u307a\u3044\uff1a\u306e\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u304b\u3089\u6551\uff1a\u304d\u3046\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1902,\u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u52dd\uff1a\u3057\u3083\u3046\uff1a\u5229\uff1a\u308a\uff1a\u306b\u852d\uff1a\u304b\u3052\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3068\u306a\u308b,\u4e00 \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u3057\u304b\u3057\u82f1\uff1a\u3048\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u30fb\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u683c\uff1a\u304b\u304f\uff1a\u6bb5\uff1a\u3060\u3093\uff1a\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u6709\uff1a\u3044\u3046\uff1a\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u304c\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u306e\u4fb5\uff1a\u3057\u3093\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u3084\u5185\uff1a\u306a\u3044\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3067\u4fb5\uff1a\u3057\u3093\uff1a\u8feb\uff1a\u3071\u304f\uff1a\u3055\u308c\u305f\u6642\uff1a\u3068\u304d\uff1a\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306a\u63aa\uff1a\u305d\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u3068\u308b \u4e8c \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u304c\u3053\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u8b77\uff1a\u307e\u3082\uff1a\u308b\u305f\u3081\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u3068\u6230\uff1a\u305f\u305f\u304b\uff1a\u3075\u6642\uff1a\u3068\u304d\uff1a\u306f\u4ed6\uff1a\u305f\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u306f\u53b3\uff1a\u3052\u3093\uff1a\u6b63\uff1a\u305b\u3044\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u5b88\uff1a\u307e\u3082\uff1a\u308a \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u6575\uff1a\u3066\u304d\uff1a\u5074\uff1a\u304c\u306f\uff1a\u306b\u53c2\uff1a\u3055\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u3059\u308b\u306e\u3092\u9632\uff1a\u3075\u305b\uff1a\u3050 \u4e09 \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308b\u6642\uff1a\u3068\u304d\uff1a\u306f \u4ed6\uff1a\u305f\uff1a\u306e\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f \u63f4\uff1a\u3048\u3093\uff1a\u52a9\uff1a\u3058\u3087\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1904,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6975\uff1a\u304d\u3087\u304f\uff1a\u6771\uff1a\u3068\u3046\uff1a\u306e\u30ed\u30b7\u30a2\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u52d5\uff1a\u3069\u3046\uff1a\u54e1\uff1a\u3090\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u306b\u306f\u6212\uff1a\u304b\u3044\uff1a\u53b3\uff1a\u3052\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c\u4e0b\uff1a\u304f\u3060\uff1a\u3055\u308c \u5bfe\uff1a\u305f\u3044\uff1a\u9732\uff1a\u308d\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u306f\u6c7a\uff1a\u3051\u3064\uff1a\u88c2\uff1a\u308c\u3064\uff1a \u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f\u570b\uff1a\u3053\u3063\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u65ad\uff1a\u3060\u3093\uff1a\u7d76\uff1a\u305c\u3064\uff1a\u3092\u9732\uff1a\u308d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u901a\uff1a\u3064\u3046\uff1a\u544a\uff1a\u3053\u304f\uff1a,\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u806f\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u306b\u3088\u308b \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u653b\uff1a\u3053\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a \u4ec1\uff1a\u3058\u3093\uff1a\u5ddd\uff1a\u305b\u3093\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u306b\u3066\u6575\uff1a\u3066\u304d\uff1a\u8266\uff1a\u304b\u3093\uff1a\u306e\u6483\uff1a\u3052\u304d\uff1a\u6c88\uff1a\u3061\u3093\uff1a\u304c\u3042\u308a \u6b21\uff1a\u3064\u304e\uff1a\u306e\u65e5\uff1a\u3072\uff1a\u306b\u5ba3\u6226 >> \u907c\uff1a\u308a\u3083\u3046\uff1a\u967d\uff1a\u3084\u3046\uff1a\u30fb\u6c99\uff1a\u3057\u3083\uff1a\u6cb3\uff1a\u304b\uff1a\u306e\u6703\uff1a\u304f\u308f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a \u6d77\uff1a\u304b\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306e\u7372\uff1a\u304b\u304f\uff1a\u5f97\uff1a\u3068\u304f\uff1a \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u9665\uff1a\u304b\u3093\uff1a\u843d\uff1a\u3089\u304f\uff1a \u5949\uff1a\u307b\u3046\uff1a\u5929\uff1a\u3066\u3093\uff1a\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3092\u7d4c\uff1a\u3078\uff1a\u3066 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u5168\uff1a\u305c\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3055\u305b \u6a3a\uff1a\u304b\u3089\uff1a\u592a\uff1a\u3075\u3068\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\n1931,\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u30bd\u9023\uff1a\u308c\u3093\uff1a\u306e\u5916\uff1a\u304c\u3044\uff1a\u8499\uff1a\u3082\u3046\uff1a\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a \u4e8b\uff1a\u3058\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u4e09\u3064\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6301\uff1a\u3082\uff1a\u3064\u4e0d\uff1a\u3075\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u306a\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u6bba\uff1a\u3055\u3064\uff1a \u5f35\uff1a\u3061\u3087\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u9716\uff1a\u308a\u3093\uff1a\u30fb\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u79d5\uff1a\u3072\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306b\u3088\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u7aae\uff1a\u304d\u3085\u3046\uff1a\u4e4f\uff1a\u307c\u3075\uff1a \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u904b\uff1a\u3046\u3093\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u306a\u3069 \u6e80\u6d32\u306b\u306f\u3044\u3064\u7206\uff1a\u3070\u304f\uff1a\u767c\uff1a\u306f\u3064\uff1a\u3057\u3066\u3082\u304a\u304b\u3057\u304f\u306a\u3044 \u7dca\uff1a\u304d\u3093\uff1a\u5f35\uff1a\u3061\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u304c\u3042\u3063\u305f,\u77f3\uff1a\u3044\u3057\uff1a\u539f\uff1a\u306f\u3089\uff1a\u839e\uff1a\u304b\u3093\uff1a\u723e\uff1a\u3058\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u7dbf\uff1a\u3081\u3093\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306a\u8a08\uff1a\u3051\u3044\uff1a\u753b\uff1a\u304b\u304f\uff1a\u306b\u3088\u308a \u67f3\uff1a\u308a\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u306b\u304a\u3051\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u306e\u7dda\uff1a\u305b\u3093\uff1a\u8def\uff1a\u308d\uff1a\u304c\u5c0f\uff1a\u305b\u3046\uff1a\u898f\uff1a\u304d\uff1a\u6a21\uff1a\u307c\uff1a\u306b\u7206\uff1a\u3070\u304f\uff1a\u7834\uff1a\u306f\uff1a\u3055\u308c \u305d\u308c\u3092\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304b\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u4ed5\uff1a\u3057\uff1a\u696d\uff1a\u308f\u3056\uff1a\u3068\u3057\u305f\u95a2\uff1a\u304b\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f \u5317\uff1a\u307b\u304f\uff1a\u5927\uff1a\u305f\u3044\uff1a\u55b6\uff1a\u3048\u3044\uff1a\u306e\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u6557\uff1a\u306f\u3044\uff1a\u8d70\uff1a\u305d\u3046\uff1a\u305b\u3057\u3081 \u3053\u308c\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u3057\u305f\n1937,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u76e7\uff1a\u308d\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u6a4b\uff1a\u3051\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u3092\u5951\uff1a\u3051\u3044\uff1a\u6a5f\uff1a\u304d\uff1a\u3068\u3057 \u4e0a\uff1a\u3057\u3083\u3093\uff1a\u6d77\uff1a\u306f\u3044\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u306f\u3093\uff1a\u3078 \u305d\u3057\u3066\u65e5\uff1a\u306b\u3063\uff1a\u652f\uff1a\u3057\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5168\uff1a\u305c\u3093\uff1a\u9762\uff1a\u3081\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6bb5\uff1a\u3060\u3093\uff1a\u968e\uff1a\u304b\u3044\uff1a\u306b\u7a81\uff1a\u3068\u3064\uff1a\u5165\uff1a\u306b\u3075\uff1a\u3057\u305f,\u8ecd\uff1a\u3050\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u6f14\uff1a\u3048\u3093\uff1a\u7fd2\uff1a\u3057\u3075\uff1a\u3092\u7d42\uff1a\u3057\u3085\u3046\uff1a\u4e86\uff1a\u308c\u3046\uff1a\u3057\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u99d0\uff1a\u3061\u3085\u3046\uff1a\u5c6f\uff1a\u3068\u3093\uff1a\u6b69\uff1a\u307b\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057\u9283\uff1a\u3058\u3085\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u304c\u6d74\uff1a\u3042\uff1a\u3073\u305b\u3089\u308c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u61c9\uff1a\u304a\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u305b\u305a\u306b\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u306e\u628a\uff1a\u306f\uff1a\u63e1\uff1a\u3042\u304f\uff1a \u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u9032\uff1a\u3059\u3059\uff1a\u3081\u305f\u304c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u3068\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u307f\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306f\u731b\uff1a\u307e\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u3057 \u4e03\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u81ea\uff1a\u3058\uff1a\u91cd\uff1a\u3061\u3087\u3046\uff1a\u3082\u865a\uff1a\u3080\u306a\uff1a\u3057\u304f\u6211\u8ecd\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a \u7adc\uff1a\u308a\u3085\u3046\uff1a\u738b\uff1a\u308f\u3046\uff1a\u5ef3\uff1a\u3061\u3087\u3046\uff1a\u306e\u6575\uff1a\u3066\u304d\uff1a\u3092\u6483\uff1a\u3052\u304d\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u6c38\uff1a\u3048\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u53f3\uff1a\u3046\uff1a\u5cb8\uff1a\u304c\u3093\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1941,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f \u3053\u306e\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092<\u592a\uff1a\u305f\u3044\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u6d0b\uff1a\u3084\u3046\uff1a\u6230\u722d>\u3068\u547c\uff1a\u3053\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u3057\u3066\u3090\u308b,\u3053\u306e\u6230\u722d\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u305f\u6211\u570b\u306f\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c \u52dd\uff1a\u3057\u3087\u3046\uff1a\u8005\uff1a\u3057\u3083\uff1a\u306b\u90fd\uff1a\u3064\uff1a\u5408\uff1a\u304c\u3075\uff1a\u306e\u60e1\uff1a\u308f\u308b\uff1a\u3044\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u306e\u6559\uff1a\u3051\u3046\uff1a\u80b2\uff1a\u3044\u304f\uff1a\u3092\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u6392\uff1a\u306f\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u4eca\uff1a\u3044\u307e\uff1a\u306b\u81f3\uff1a\u3044\u305f\uff1a\u308b\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3078\u306e\u964d\uff1a\u304b\u3046\uff1a\u4f0f\uff1a\u3075\u304f\uff1a\u8981\uff1a\u3048\u3046\uff1a\u6c42\uff1a\u304d\u3046\uff1a\u306e\u6700\uff1a\u3055\u3044\uff1a\u7d42\uff1a\u3057\u3085\u3046\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a>,\u5168\uff1a\u305c\u3093\uff1a13\u30f6\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u304b\u3089\u306a\u308a \u30a4\u30ae\u30ea\u30b9\u30fb\u30a2\u30e1\u30ea\u30ab\u5408\uff1a\u304c\u3063\uff1a\u8846\uff1a\u3057\u3085\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u30fb\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u9996\uff1a\u3057\u3085\uff1a\u8133\uff1a\u306e\u3046\uff1a\u306e\u9023\uff1a\u308c\u3093\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306b\u304a\u3044\u3066\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c \u30bd\u30d3\u30a8\u30c8\u9023\uff1a\u308c\u3093\uff1a\u90a6\uff1a\u3071\u3046\uff1a\u306f \u5f8c\uff1a\u3042\u3068\uff1a\u304b\u3089\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308a\u8ffd\uff1a\u3064\u3044\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3057\u305f\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a>,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u3042\u308a \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c\u3066\u3090\u305f\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c \u3053\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u3057\u305f\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u3088\u308a\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3055\u308c \u570b\uff1a\u3053\u304f\uff1a\u969b\uff1a\u3055\u3044\uff1a\u6cd5\uff1a\u306f\u3046\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a \u6211\u570b\u3068\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u9023\u5408\u570b\u3068\u306e\u9593\uff1a\u3042\u3072\u3060\uff1a\u306e<\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a>\u304c\u7d42\uff1a\u3057\u3085\u3046\uff1a\u7d50\uff1a\u3051\u3064\uff1a\u3057\u305f \u3053\u306e\u6761\u7d04\u3067\u6211\u570b\u306f1875\u5e74\u306b\u5168\uff1a\u305c\u3093\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u9818\uff1a\u308a\u3083\u3046\uff1a\u6709\uff1a\u3044\u3046\uff1a\u3057\u305f\u5343\uff1a\u3061\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u653e\uff1a\u306f\u3046\uff1a\u68c4\uff1a\u304d\uff1a\u3057\u3066\u3090\u308b \u306a\u307b \u3053\u306e\u6761\u7d04\u306e\u767c\uff1a\u306f\u3063\uff1a\u52b9\uff1a\u304b\u3046\uff1a\u65e5\uff1a\u3073\uff1a\u306f1952\u5e74<\u662d\u548c27\u5e74>4\u670828\u65e5\u3067\u3042\u308a \u6211\u570b\u306e\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u56de\uff1a\u304b\u3044\uff1a\u5fa9\uff1a\u3075\u304f\uff1a\u3057 \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u3082\u89e3\uff1a\u304b\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u305f"));}),_1E6=new T(function(){return B(_1DZ(_1E5));}),_1E7=new T(function(){return B(_aj(_1DU,_1E6));}),_1E8=new T(function(){return B(_cU(1,2));}),_1E9=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b<\u4e0d\u5e73\u7b49>\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1882,\u58ec\u5348\u306e\u5909,\u4ff8\u7d66\u306e\u9045\u914d\u3092\u304d\u3063\u304b\u3051\u3068\u3057\u305f\u65e7\u5175\u306e\u66b4\u52d5\u3092\u5927\u9662\u541b\u304c\u717d\u52d5(\u5927\u9662\u541b\u306f\u65e7\u5b88\u6d3e \u9594\u5983\u4e00\u65cf\u306f\u958b\u5316\u6d3e),\u65e5\u97d3\u4fee\u4ea4\u4ee5\u964d \u9594\u5983\u4e00\u65cf\u306e\u958b\u5316\u6d3e\u304c\u529b\u3092\u306e\u3070\u3057 \u65e5\u672c\u306e\u8fd1\u4ee3\u5316\u306b\u5023\u306f\u3093\u3068 \u5927\u898f\u6a21\u306a\u8996\u5bdf\u56e3\u3092\u6d3e\u9063\u3057\u305f\u308a \u65e5\u672c\u304b\u3089\u5800\u672c\u793c\u9020\u3092\u62db\u3044\u3066\u65b0\u5f0f\u8ecd\u968a\u3092\u7de8\u6210\u3059\u308b\u306a\u3069\u8ecd\u653f\u6539\u9769\u3092\u65ad\u884c\u3057\u3066\u3090\u305f\u304c \u65e7\u5175\u3068\u5927\u9662\u541b\u306e\u53cd\u4e71\u306b\u3088\u308a \u591a\u6570\u306e\u65e5\u672c\u4eba\u304c\u8650\u6bba\u3055\u308c\u65e5\u672c\u516c\u4f7f\u9928\u304c\u8972\u6483\u3055\u308c\u305f(\u5800\u672c\u793c\u9020\u3082\u6bba\u3055\u308c\u308b) \u6e05\u570b\u306f\u7d04\u4e94\u5343\u306e\u5175\u3092\u304a\u304f\u308a\u4e71\u306e\u93ae\u5727\u306b\u5f53\u308b\u3068\u3068\u3082\u306b \u9996\u9b41\u3067\u3042\u308b\u5927\u9662\u541b\u3092\u6e05\u570b\u306b\u62c9\u81f4\u3057\u6291\u7559**\u3053\u306e\u4e8b\u5909\u306e\u5584\u5f8c\u7d04\u5b9a\u3068\u3057\u3066 \u65e5\u672c\u30fb\u671d\u9bae\u9593\u306b\u6e08\u7269\u6d66\u6761\u7d04\u304c\u7d50\u3070\u308c \u671d\u9bae\u5074\u306f\u72af\u4eba\u306e\u53b3\u7f70 \u8ce0\u511f\u91d1 \u516c\u4f7f\u9928\u8b66\u5099\u306e\u305f\u3081\u4eac\u57ce\u306b\u65e5\u672c\u8ecd\u82e5\u5e72\u3092\u7f6e\u304f \u65e5\u672c\u306b\u8b1d\u7f6a\u4f7f\u3092\u6d3e\u9063\u3059\u308b\u3053\u3068\u3092\u7d04\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,<\u6276\u6e05\u6ec5\u6d0b>\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***<\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287>\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b<\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42>,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059>\u30fc\u30fc\u5f8c\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059>"));}),_1Ea=new T(function(){return B(_1DZ(_1E9));}),_1Eb=new T(function(){return B(_aj(_1DU,_1Ea));}),_1Ec=function(_1Ed,_1Ee){var _1Ef=E(_1Ed);if(!_1Ef._){return __Z;}else{var _1Eg=E(_1Ee);return (_1Eg._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1Ef.a).a;}),_1Eg.a),new T(function(){return B(_1Ec(_1Ef.b,_1Eg.b));}));}},_1Eh=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1Ei=new T(function(){return B(unCStr("tail"));}),_1Ej=new T(function(){return B(_rj(_1Ei));}),_1Ek=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1El=new T2(1,_2A,_Z),_1Em=function(_1En){var _1Eo=E(_1En);if(!_1Eo._){return E(_1El);}else{var _1Ep=new T(function(){return B(_H(0,E(_1Eo.a),new T(function(){return B(_1Em(_1Eo.b));})));});return new T2(1,_2z,_1Ep);}},_1Eq=function(_1Er){var _1Es=E(_1Er);if(!_1Es._){return E(_1El);}else{var _1Et=new T(function(){var _1Eu=E(_1Es.a),_1Ev=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1Ew){return new F(function(){return _1D5(_1Eu.a,_1Ew);});},new T2(1,function(_1Ex){return new F(function(){return _1D5(_1Eu.b,_1Ex);});},_Z)),new T2(1,_F,new T(function(){return B(_1Eq(_1Es.b));}))));});return new T2(1,_G,_1Ev);});return new T2(1,_2z,_1Et);}},_1Ey=function(_1Ez){var _1EA=E(_1Ez);if(!_1EA._){return E(_1El);}else{var _1EB=new T(function(){return B(_H(0,E(_1EA.a),new T(function(){return B(_1Ey(_1EA.b));})));});return new T2(1,_2z,_1EB);}},_1EC=function(_1ED){var _1EE=E(_1ED);if(!_1EE._){return E(_1El);}else{var _1EF=new T(function(){var _1EG=E(_1EE.a),_1EH=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1EI){return new F(function(){return _1D5(_1EG.a,_1EI);});},new T2(1,function(_1EJ){return new F(function(){return _1D5(_1EG.b,_1EJ);});},_Z)),new T2(1,_F,new T(function(){return B(_1EC(_1EE.b));}))));});return new T2(1,_G,_1EH);});return new T2(1,_2z,_1EF);}},_1EK=new T(function(){return B(unCStr("True"));}),_1EL=new T(function(){return B(unCStr("False"));}),_1EM=function(_1EN){return E(E(_1EN).b);},_1EO=function(_1EP,_1EQ,_1ER){var _1ES=new T(function(){var _1ET=E(_1ER);if(!_1ET._){return __Z;}else{var _1EU=_1ET.b,_1EV=E(_1ET.a),_1EW=E(_1EV.a);if(_1EW<_1EP){var _1EX=function(_1EY){while(1){var _1EZ=B((function(_1F0){var _1F1=E(_1F0);if(!_1F1._){return __Z;}else{var _1F2=_1F1.b,_1F3=E(_1F1.a);if(E(_1F3.a)<_1EP){_1EY=_1F2;return __continue;}else{return new T2(1,_1F3,new T(function(){return B(_1EX(_1F2));}));}}})(_1EY));if(_1EZ!=__continue){return _1EZ;}}};return B(_1F4(B(_1EX(_1EU))));}else{var _1F5=new T(function(){var _1F6=function(_1F7){while(1){var _1F8=B((function(_1F9){var _1Fa=E(_1F9);if(!_1Fa._){return __Z;}else{var _1Fb=_1Fa.b,_1Fc=E(_1Fa.a);if(E(_1Fc.a)<_1EP){_1F7=_1Fb;return __continue;}else{return new T2(1,_1Fc,new T(function(){return B(_1F6(_1Fb));}));}}})(_1F7));if(_1F8!=__continue){return _1F8;}}};return B(_1F6(_1EU));});return B(_1EO(_1EW,_1EV.b,_1F5));}}}),_1Fd=E(_1ER);if(!_1Fd._){return new F(function(){return _x(_Z,new T2(1,new T2(0,_1EP,_1EQ),_1ES));});}else{var _1Fe=_1Fd.b,_1Ff=E(_1Fd.a),_1Fg=E(_1Ff.a);if(_1Fg>=_1EP){var _1Fh=function(_1Fi){while(1){var _1Fj=B((function(_1Fk){var _1Fl=E(_1Fk);if(!_1Fl._){return __Z;}else{var _1Fm=_1Fl.b,_1Fn=E(_1Fl.a);if(E(_1Fn.a)>=_1EP){_1Fi=_1Fm;return __continue;}else{return new T2(1,_1Fn,new T(function(){return B(_1Fh(_1Fm));}));}}})(_1Fi));if(_1Fj!=__continue){return _1Fj;}}};return new F(function(){return _x(B(_1F4(B(_1Fh(_1Fe)))),new T2(1,new T2(0,_1EP,_1EQ),_1ES));});}else{var _1Fo=new T(function(){var _1Fp=function(_1Fq){while(1){var _1Fr=B((function(_1Fs){var _1Ft=E(_1Fs);if(!_1Ft._){return __Z;}else{var _1Fu=_1Ft.b,_1Fv=E(_1Ft.a);if(E(_1Fv.a)>=_1EP){_1Fq=_1Fu;return __continue;}else{return new T2(1,_1Fv,new T(function(){return B(_1Fp(_1Fu));}));}}})(_1Fq));if(_1Fr!=__continue){return _1Fr;}}};return B(_1Fp(_1Fe));});return new F(function(){return _x(B(_1EO(_1Fg,_1Ff.b,_1Fo)),new T2(1,new T2(0,_1EP,_1EQ),_1ES));});}}},_1F4=function(_1Fw){var _1Fx=E(_1Fw);if(!_1Fx._){return __Z;}else{var _1Fy=_1Fx.b,_1Fz=E(_1Fx.a),_1FA=_1Fz.a,_1FB=new T(function(){var _1FC=E(_1Fy);if(!_1FC._){return __Z;}else{var _1FD=_1FC.b,_1FE=E(_1FC.a),_1FF=E(_1FE.a),_1FG=E(_1FA);if(_1FF<_1FG){var _1FH=function(_1FI){while(1){var _1FJ=B((function(_1FK){var _1FL=E(_1FK);if(!_1FL._){return __Z;}else{var _1FM=_1FL.b,_1FN=E(_1FL.a);if(E(_1FN.a)<_1FG){_1FI=_1FM;return __continue;}else{return new T2(1,_1FN,new T(function(){return B(_1FH(_1FM));}));}}})(_1FI));if(_1FJ!=__continue){return _1FJ;}}};return B(_1F4(B(_1FH(_1FD))));}else{var _1FO=new T(function(){var _1FP=function(_1FQ){while(1){var _1FR=B((function(_1FS){var _1FT=E(_1FS);if(!_1FT._){return __Z;}else{var _1FU=_1FT.b,_1FV=E(_1FT.a);if(E(_1FV.a)<_1FG){_1FQ=_1FU;return __continue;}else{return new T2(1,_1FV,new T(function(){return B(_1FP(_1FU));}));}}})(_1FQ));if(_1FR!=__continue){return _1FR;}}};return B(_1FP(_1FD));});return B(_1EO(_1FF,_1FE.b,_1FO));}}}),_1FW=E(_1Fy);if(!_1FW._){return new F(function(){return _x(_Z,new T2(1,_1Fz,_1FB));});}else{var _1FX=_1FW.b,_1FY=E(_1FW.a),_1FZ=E(_1FY.a),_1G0=E(_1FA);if(_1FZ>=_1G0){var _1G1=function(_1G2){while(1){var _1G3=B((function(_1G4){var _1G5=E(_1G4);if(!_1G5._){return __Z;}else{var _1G6=_1G5.b,_1G7=E(_1G5.a);if(E(_1G7.a)>=_1G0){_1G2=_1G6;return __continue;}else{return new T2(1,_1G7,new T(function(){return B(_1G1(_1G6));}));}}})(_1G2));if(_1G3!=__continue){return _1G3;}}};return new F(function(){return _x(B(_1F4(B(_1G1(_1FX)))),new T2(1,_1Fz,_1FB));});}else{var _1G8=new T(function(){var _1G9=function(_1Ga){while(1){var _1Gb=B((function(_1Gc){var _1Gd=E(_1Gc);if(!_1Gd._){return __Z;}else{var _1Ge=_1Gd.b,_1Gf=E(_1Gd.a);if(E(_1Gf.a)>=_1G0){_1Ga=_1Ge;return __continue;}else{return new T2(1,_1Gf,new T(function(){return B(_1G9(_1Ge));}));}}})(_1Ga));if(_1Gb!=__continue){return _1Gb;}}};return B(_1G9(_1FX));});return new F(function(){return _x(B(_1EO(_1FZ,_1FY.b,_1G8)),new T2(1,_1Fz,_1FB));});}}}},_1Gg=function(_){return new F(function(){return jsMkStdout();});},_1Gh=new T(function(){return B(_3d(_1Gg));}),_1Gi=new T(function(){return B(_Pu("Browser.hs:82:24-56|(Right j)"));}),_1Gj=function(_1Gk){var _1Gl=jsParseJSON(toJSStr(E(_1Gk)));return (_1Gl._==0)?E(_1Gi):E(_1Gl.a);},_1Gm=0,_1Gn=function(_1Go,_1Gp,_1Gq,_1Gr,_1Gs){var _1Gt=E(_1Gs);if(!_1Gt._){var _1Gu=new T(function(){var _1Gv=B(_1Gn(_1Gt.a,_1Gt.b,_1Gt.c,_1Gt.d,_1Gt.e));return new T2(0,_1Gv.a,_1Gv.b);});return new T2(0,new T(function(){return E(E(_1Gu).a);}),new T(function(){return B(_78(_1Gp,_1Gq,_1Gr,E(_1Gu).b));}));}else{return new T2(0,new T2(0,_1Gp,_1Gq),_1Gr);}},_1Gw=function(_1Gx,_1Gy,_1Gz,_1GA,_1GB){var _1GC=E(_1GA);if(!_1GC._){var _1GD=new T(function(){var _1GE=B(_1Gw(_1GC.a,_1GC.b,_1GC.c,_1GC.d,_1GC.e));return new T2(0,_1GE.a,_1GE.b);});return new T2(0,new T(function(){return E(E(_1GD).a);}),new T(function(){return B(_6h(_1Gy,_1Gz,E(_1GD).b,_1GB));}));}else{return new T2(0,new T2(0,_1Gy,_1Gz),_1GB);}},_1GF=function(_1GG,_1GH){var _1GI=E(_1GG);if(!_1GI._){var _1GJ=_1GI.a,_1GK=E(_1GH);if(!_1GK._){var _1GL=_1GK.a;if(_1GJ<=_1GL){var _1GM=B(_1Gw(_1GL,_1GK.b,_1GK.c,_1GK.d,_1GK.e)),_1GN=E(_1GM.a);return new F(function(){return _78(_1GN.a,_1GN.b,_1GI,_1GM.b);});}else{var _1GO=B(_1Gn(_1GJ,_1GI.b,_1GI.c,_1GI.d,_1GI.e)),_1GP=E(_1GO.a);return new F(function(){return _6h(_1GP.a,_1GP.b,_1GO.b,_1GK);});}}else{return E(_1GI);}}else{return E(_1GH);}},_1GQ=function(_1GR,_1GS){var _1GT=E(_1GR),_1GU=E(_1GS);if(!_1GU._){var _1GV=_1GU.b,_1GW=_1GU.c,_1GX=_1GU.d,_1GY=_1GU.e;switch(B(_65(_1GT,_1GV))){case 0:return new F(function(){return _6h(_1GV,_1GW,B(_1GQ(_1GT,_1GX)),_1GY);});break;case 1:return new F(function(){return _1GF(_1GX,_1GY);});break;default:return new F(function(){return _78(_1GV,_1GW,_1GX,B(_1GQ(_1GT,_1GY)));});}}else{return new T0(1);}},_1GZ=function(_1H0,_1H1){while(1){var _1H2=E(_1H0);if(!_1H2._){return E(_1H1);}else{var _1H3=B(_1GQ(new T2(1,_1H2.a,_1r7),_1H1));_1H0=_1H2.b;_1H1=_1H3;continue;}}},_1H4=function(_1H5,_1H6,_1H7,_1H8,_1H9,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_1HL,_1HM,_1HN,_1HO,_1HP,_){var _1HQ={_:0,a:E(_1HH),b:E(_1HI),c:E(_1HJ),d:E(_1HK),e:E(_1HL),f:E(_1HM),g:E(_1HN),h:E(_1HO)},_1HR=new T2(0,_1HE,_1HF),_1HS=new T2(0,_1Hs,_1Ht),_1HT=new T2(0,_1Hl,_1Hm),_1HU={_:0,a:E(_1Ha),b:E(_1Hb),c:E(_1Hc),d:_1Hd,e:_1He,f:_1Hf,g:E(_1Hg),h:_1Hh,i:E(_1Hi),j:E(_1Hj),k:E(_1Hk)},_1HV={_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:_1Hz,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};if(!E(_1HM)){if(!E(_1HI)){var _1HW=function(_1HX){if(!E(_1HK)){if(!E(_1HO)){return _1HV;}else{var _1HY=function(_,_1HZ,_1I0,_1I1,_1I2,_1I3,_1I4,_1I5,_1I6,_1I7,_1I8,_1I9,_1Ia,_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In,_1Io,_1Ip,_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv){var _1Iw=function(_){var _1Ix=function(_){var _1Iy=function(_){var _1Iz=B(_1Co(_1Gh,new T2(1,_aI,new T(function(){return B(_cp(_1I7,_1Dk));})),_)),_1IA=function(_){var _1IB=B(_1Co(_1Gh,B(_H(0,_1Hx,_Z)),_)),_1IC=B(_1Co(_1Gh,B(_2C(_1D8,_1I5,_Z)),_)),_1ID=function(_){var _1IE=B(_1aE(_1CT,_1I6,_)),_1IF=_1IE,_1IG=E(_1H5),_1IH=_1IG.a,_1II=_1IG.b,_1IJ=new T(function(){return B(_1rX(E(_1H9)));}),_1IK=new T(function(){var _1IL=E(_1IJ),_1IM=E(_1HZ),_1IN=_1IM.a,_1IO=_1IM.b,_1IP=function(_1IQ,_1IR){var _1IS=E(_1IQ),_1IT=E(_1IR),_1IU=E(_1IN);if(_1IS<=_1IU){if(_1IU<=_1IS){var _1IV=E(_1IO);if(_1IT<=_1IV){if(_1IV<=_1IT){var _1IW=4;}else{var _1IW=0;}var _1IX=_1IW;}else{var _1IX=1;}var _1IY=_1IX;}else{var _1IY=2;}var _1IZ=_1IY;}else{var _1IZ=3;}var _1J0=function(_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja){switch(E(_1IZ)){case 0:if(!E(_1I1)){var _1Jb=new T2(0,_1Ir,_1Is);}else{var _1Jb=new T2(0,_1Ir,_1Do);}var _1Jc=_1Jb;break;case 1:if(E(_1I1)==1){var _1Jd=new T2(0,_1Ir,_1Is);}else{var _1Jd=new T2(0,_1Ir,_1Gm);}var _1Jc=_1Jd;break;case 2:if(E(_1I1)==2){var _1Je=new T2(0,_1Ir,_1Is);}else{var _1Je=new T2(0,_1Ir,_1CS);}var _1Jc=_1Je;break;case 3:if(E(_1I1)==3){var _1Jf=new T2(0,_1Ir,_1Is);}else{var _1Jf=new T2(0,_1Ir,_1CR);}var _1Jc=_1Jf;break;default:if(E(_1I1)==4){var _1Jg=new T2(0,_1Ir,_1Is);}else{var _1Jg=new T2(0,_1Ir,_1Gm);}var _1Jc=_1Jg;}var _1Jh=B(_1oI(_1Gm,_1J8,_1Id,{_:0,a:E(_1J1),b:E(_1J2),c:E(_1J3),d:_1J4,e:_1J5,f:_1J6,g:E(_1J7),h:E(E(_1IF).b),i:E(_1J8),j:E(_1J9),k:E(_1Ja)},_1Ia,_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In,_1Io,_1Ip,_1Iq,_1Jc,_1It,_1Iu,_1Iv)),_1Ji=_1Jh.a,_1Jj=_1Jh.b,_1Jk=_1Jh.c,_1Jl=_1Jh.d,_1Jm=_1Jh.e,_1Jn=_1Jh.f,_1Jo=_1Jh.g,_1Jp=_1Jh.h,_1Jq=_1Jh.i,_1Jr=_1Jh.j,_1Js=_1Jh.k,_1Jt=_1Jh.l,_1Ju=_1Jh.m,_1Jv=_1Jh.n,_1Jw=_1Jh.o,_1Jx=_1Jh.q,_1Jy=_1Jh.r,_1Jz=_1Jh.s,_1JA=_1Jh.t,_1JB=_1Jh.u,_1JC=_1Jh.v,_1JD=E(_1Jh.p);if(!_1JD._){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_Z),q:_1Jx,r:E(_1Jy),s:E(_1Jz),t:_1JA,u:E(_1JB),v:E(_1JC)};}else{var _1JE=B(_qy(_1J8,0))-2|0,_1JF=function(_1JG){var _1JH=E(_1Ji);return {_:0,a:E({_:0,a:E(_1JH.a),b:E(_1JH.b),c:E(_1JH.c),d:_1JH.d,e:_1JH.e,f:_1JH.f,g:E(_Z),h:_1JH.h,i:E(_1JH.i),j:E(_1JH.j),k:E(_1JH.k)}),b:E(_1Jj),c:E(_1Jk),d:E(B(_x(B(_0(_Z,B(_1GZ(B(_aj(_1EM,_1JD)),B(_9T(_1Jl)))))),new T(function(){return B(_aj(_1BT,_1JD));},1)))),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_Z),q:_1Jx,r:E(B(_x(_1Jy,new T2(1,_1Jx,_Z)))),s:E(_1Jz),t:_1JA,u:E(_1JB),v:E(_1JC)};};if(_1JE>0){if(!B(_uV(B(_1BA(_1JE,_1J8)),_1CQ))){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_1JD),q:_1Jx,r:E(_1Jy),s:E(_1Jz),t:_1JA,u:E(_1JB),v:E(_1JC)};}else{return new F(function(){return _1JF(_);});}}else{if(!B(_uV(_1J8,_1CQ))){return {_:0,a:E(_1Ji),b:E(_1Jj),c:E(_1Jk),d:E(_1Jl),e:E(_1Jm),f:E(_1Jn),g:E(_1Jo),h:E(_1Jp),i:_1Jq,j:_1Jr,k:_1Js,l:_1Jt,m:E(_1Ju),n:_1Jv,o:E(_1Jw),p:E(_1JD),q:_1Jx,r:E(_1Jy),s:E(_1Jz),t:_1JA,u:E(_1JB),v:E(_1JC)};}else{return new F(function(){return _1JF(_);});}}}};if(E(_1IL)==32){var _1JI=B(_1xQ(_1IS,_1IT,_1IU,_1IO,_1I0,_1IZ,_1I2,_1I3,_1I4,_1I5,_1I6,_1I7,_1I8,_1I9)),_1JJ=E(_1JI.a),_1JK=B(_1Bb(_1JJ.a,E(_1JJ.b),_1JI.b,_1JI.c,_1JI.d,_1JI.e,_1JI.f,_1JI.g,_1JI.h,_1JI.i,_1JI.j,_1JI.k));return new F(function(){return _1J0(_1JK.a,_1JK.b,_1JK.c,_1JK.d,_1JK.e,_1JK.f,_1JK.g,_1JK.i,_1JK.j,_1JK.k);});}else{var _1JL=B(_1xQ(_1IS,_1IT,_1IU,_1IO,_1I0,_1IZ,_1I2,_1I3,_1I4,_1I5,_1I6,_1I7,_1I8,_1I9));return new F(function(){return _1J0(_1JL.a,_1JL.b,_1JL.c,_1JL.d,_1JL.e,_1JL.f,_1JL.g,_1JL.i,_1JL.j,_1JL.k);});}};switch(E(_1IL)){case 72:var _1JM=E(_1IO);if(0<=(_1JM-1|0)){return B(_1IP(_1IN,_1JM-1|0));}else{return B(_1IP(_1IN,_1JM));}break;case 75:var _1JN=E(_1IN);if(0<=(_1JN-1|0)){return B(_1IP(_1JN-1|0,_1IO));}else{return B(_1IP(_1JN,_1IO));}break;case 77:var _1JO=E(_1IN);if(E(_1Hl)!=(_1JO+1|0)){return B(_1IP(_1JO+1|0,_1IO));}else{return B(_1IP(_1JO,_1IO));}break;case 80:var _1JP=E(_1IO);if(E(_1Hm)!=(_1JP+1|0)){return B(_1IP(_1IN,_1JP+1|0));}else{return B(_1IP(_1IN,_1JP));}break;case 104:var _1JQ=E(_1IN);if(0<=(_1JQ-1|0)){return B(_1IP(_1JQ-1|0,_1IO));}else{return B(_1IP(_1JQ,_1IO));}break;case 106:var _1JR=E(_1IO);if(E(_1Hm)!=(_1JR+1|0)){return B(_1IP(_1IN,_1JR+1|0));}else{return B(_1IP(_1IN,_1JR));}break;case 107:var _1JS=E(_1IO);if(0<=(_1JS-1|0)){return B(_1IP(_1IN,_1JS-1|0));}else{return B(_1IP(_1IN,_1JS));}break;case 108:var _1JT=E(_1IN);if(E(_1Hl)!=(_1JT+1|0)){return B(_1IP(_1JT+1|0,_1IO));}else{return B(_1IP(_1JT,_1IO));}break;default:return B(_1IP(_1IN,_1IO));}}),_1JU=B(_1bq(_1IH,_1II,_1H6,_1H7,_1H8,_1IK,_)),_1JV=_1JU,_1JW=E(_1IJ),_1JX=function(_,_1JY){var _1JZ=function(_1K0){var _1K1=B(_1Co(_1Gh,B(_cv(_1JY)),_)),_1K2=E(_1JV),_1K3=_1K2.d,_1K4=_1K2.e,_1K5=_1K2.f,_1K6=_1K2.g,_1K7=_1K2.i,_1K8=_1K2.j,_1K9=_1K2.k,_1Ka=_1K2.l,_1Kb=_1K2.m,_1Kc=_1K2.n,_1Kd=_1K2.o,_1Ke=_1K2.p,_1Kf=_1K2.q,_1Kg=_1K2.r,_1Kh=_1K2.t,_1Ki=_1K2.v,_1Kj=E(_1K2.u),_1Kk=_1Kj.a,_1Kl=_1Kj.d,_1Km=_1Kj.e,_1Kn=_1Kj.f,_1Ko=_1Kj.g,_1Kp=_1Kj.h,_1Kq=E(_1K2.a),_1Kr=_1Kq.c,_1Ks=_1Kq.f,_1Kt=_1Kq.g,_1Ku=_1Kq.h,_1Kv=E(_1K2.h),_1Kw=E(_1K2.s),_1Kx=function(_1Ky){var _1Kz=function(_1KA){if(_1KA!=E(_1CJ)){var _1KB=B(_aW(_1ko,_1KA)),_1KC=_1KB.a,_1KD=E(_1KB.b),_1KE=B(_1fC(_1KC,_1KD,new T(function(){return B(_aW(_1mt,_1KA));})));return new F(function(){return _1H4(_1IG,_1H6,_1H7,_1H8,_1CI,B(_aW(_1kz,_1KA)),_1KE,_1Kr,B(_aW(_1kM,_1KA)),32,_1KA,_1Kt,_1Ku,B(_x(_1Kq.i,new T2(1,_1CH,new T(function(){return B(_H(0,_1Ks,_Z));})))),B(_1C2(_1CG,_1KE)),_AC,_1KC,_1KD,_Z,_1K3,_1K4,_1K5,_1K6,_1Kv.a,_1Kv.b,_1K7,_1K8,_1K9, -1,_1Kb,_1Kc,_1Kd,_1Ke,_1Kf,_1Kg,_1Kw.a,_1Kw.b,_1Kh,_AC,_AC,_AC,_1Kl,_1Km,_1Kn,_1Ko,_1Kp,_1Ki,_);});}else{var _1KF=__app1(E(_rn),_1II),_1KG=B(A2(_ro,_1IH,_)),_1KH=B(A(_qT,[_1IH,_n8,_1CC,_1CE,_1CD,_])),_1KI=B(A(_qT,[_1IH,_n8,_1CC,_1CB,_1Dp,_])),_1KJ=B(A(_qT,[_1IH,_n8,_1Do,_1Dn,_1Dm,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1kq),b:E(_1Dl),c:E(_1Kr),d:E(_1CZ),e:32,f:0,g:E(_1Kt),h:_1Ku,i:E(_Z),j:E(_1Kq.j),k:E(_AC)}),b:E(_1kb),c:E(_1K2.c),d:E(_1K3),e:E(_1K4),f:E(_1K5),g:E(_1K6),h:E(_1Kv),i:_1K7,j:_1K8,k:_1K9,l:_1Ka,m:E(_1Kb),n:_1Kc,o:E(_1Kd),p:E(_1Ke),q:_1Kf,r:E(_1Kg),s:E(_1Kw),t:_1Kh,u:E({_:0,a:E(_1Kk),b:E(_AD),c:E(_AC),d:E(_1Kl),e:E(_1Km),f:E(_1Kn),g:E(_1Ko),h:E(_1Kp)}),v:E(_1Ki)};});}};if(_1Ka>=0){return new F(function(){return _1Kz(_1Ka);});}else{return new F(function(){return _1Kz(_1Ks+1|0);});}};if(!E(_1Kk)){if(E(_1JW)==110){return new F(function(){return _1Kx(_);});}else{return _1K2;}}else{return new F(function(){return _1Kx(_);});}};if(E(_1JW)==114){if(!B(_ae(_1JY,_1CK))){var _1KK=E(_1JY);if(!_1KK._){return _1JV;}else{var _1KL=_1KK.b;return new T(function(){var _1KM=E(_1JV),_1KN=E(_1KM.a),_1KO=E(_1KK.a),_1KP=E(_1KO);if(_1KP==34){var _1KQ=B(_XN(_1KO,_1KL));if(!_1KQ._){var _1KR=E(_1Ej);}else{var _1KS=E(_1KQ.b);if(!_1KS._){var _1KT=E(_1D3);}else{var _1KU=_1KS.a,_1KV=E(_1KS.b);if(!_1KV._){var _1KW=new T2(1,new T2(1,_1KU,_Z),_Z);}else{var _1KX=E(_1KU),_1KY=new T(function(){var _1KZ=B(_Lc(126,_1KV.a,_1KV.b));return new T2(0,_1KZ.a,_1KZ.b);});if(E(_1KX)==126){var _1L0=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1KY).a);}),new T(function(){return E(E(_1KY).b);})));}else{var _1L0=new T2(1,new T2(1,_1KX,new T(function(){return E(E(_1KY).a);})),new T(function(){return E(E(_1KY).b);}));}var _1KW=_1L0;}var _1KT=_1KW;}var _1KR=_1KT;}var _1L1=_1KR;}else{var _1L2=E(_1KL);if(!_1L2._){var _1L3=new T2(1,new T2(1,_1KO,_Z),_Z);}else{var _1L4=new T(function(){var _1L5=B(_Lc(126,_1L2.a,_1L2.b));return new T2(0,_1L5.a,_1L5.b);});if(E(_1KP)==126){var _1L6=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1L4).a);}),new T(function(){return E(E(_1L4).b);})));}else{var _1L6=new T2(1,new T2(1,_1KO,new T(function(){return E(E(_1L4).a);})),new T(function(){return E(E(_1L4).b);}));}var _1L3=_1L6;}var _1L1=_1L3;}var _1L7=B(_Kk(B(_wH(_1CL,new T(function(){return B(_Nr(_1L1));})))));if(!_1L7._){return E(_1Cz);}else{if(!E(_1L7.b)._){var _1L8=E(_1L7.a),_1L9=B(_aW(_1ko,_1L8)),_1La=B(_aW(_1L1,1));if(!_1La._){var _1Lb=__Z;}else{var _1Lc=E(_1La.b);if(!_1Lc._){var _1Ld=__Z;}else{var _1Le=E(_1La.a),_1Lf=new T(function(){var _1Lg=B(_Lc(44,_1Lc.a,_1Lc.b));return new T2(0,_1Lg.a,_1Lg.b);});if(E(_1Le)==44){var _1Lh=B(_15B(_Z,new T(function(){return E(E(_1Lf).a);}),new T(function(){return E(E(_1Lf).b);})));}else{var _1Lh=B(_15F(new T2(1,_1Le,new T(function(){return E(E(_1Lf).a);})),new T(function(){return E(E(_1Lf).b);})));}var _1Ld=_1Lh;}var _1Lb=_1Ld;}var _1Li=B(_aW(_1L1,2));if(!_1Li._){var _1Lj=E(_1D4);}else{var _1Lk=_1Li.a,_1Ll=E(_1Li.b);if(!_1Ll._){var _1Lm=B(_aj(_1CW,new T2(1,new T2(1,_1Lk,_Z),_Z)));}else{var _1Ln=E(_1Lk),_1Lo=new T(function(){var _1Lp=B(_Lc(44,_1Ll.a,_1Ll.b));return new T2(0,_1Lp.a,_1Lp.b);});if(E(_1Ln)==44){var _1Lq=B(_aj(_1CW,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Lo).a);}),new T(function(){return E(E(_1Lo).b);})))));}else{var _1Lq=B(_aj(_1CW,new T2(1,new T2(1,_1Ln,new T(function(){return E(E(_1Lo).a);})),new T(function(){return E(E(_1Lo).b);}))));}var _1Lm=_1Lq;}var _1Lj=_1Lm;}return {_:0,a:E({_:0,a:E(B(_aW(_1kz,_1L8))),b:E(B(_1fC(_1L9.a,E(_1L9.b),new T(function(){return B(_aW(_1mt,_1L8));})))),c:E(_1KN.c),d:B(_aW(_1kM,_1L8)),e:32,f:_1L8,g:E(_1KN.g),h:_1KN.h,i:E(_1KN.i),j:E(_1KN.j),k:E(_1KN.k)}),b:E(_1L9),c:E(_1KM.c),d:E(_1KM.d),e:E(_1Lb),f:E(_1Lj),g:E(_1KM.g),h:E(_1KM.h),i:_1KM.i,j:_1KM.j,k:_1KM.k,l:_1KM.l,m:E(_1KM.m),n:_1KM.n,o:E(_1KM.o),p:E(_1KM.p),q:_1KM.q,r:E(_1KM.r),s:E(_1KM.s),t:_1KM.t,u:E(_1KM.u),v:E(_1KM.v)};}else{return E(_1CA);}}});}}else{return new F(function(){return _1JZ(_);});}}else{return new F(function(){return _1JZ(_);});}};switch(E(_1JW)){case 100:var _1Lr=__app1(E(_1Eh),toJSStr(E(_1CO)));return new F(function(){return _1JX(_,_1Cw);});break;case 114:var _1Ls=B(_15Q(_aB,toJSStr(E(_1CO)),_));return new F(function(){return _1JX(_,new T(function(){var _1Lt=E(_1Ls);if(!_1Lt._){return E(_1Cx);}else{return fromJSStr(B(_1qX(_1Lt.a)));}}));});break;case 115:var _1Lu=new T(function(){var _1Lv=new T(function(){var _1Lw=new T(function(){var _1Lx=B(_aj(_aG,_1Hq));if(!_1Lx._){return __Z;}else{return B(_1Ct(new T2(1,_1Lx.a,new T(function(){return B(_1Dq(_1CM,_1Lx.b));}))));}}),_1Ly=new T(function(){var _1Lz=function(_1LA){var _1LB=E(_1LA);if(!_1LB._){return __Z;}else{var _1LC=E(_1LB.a);return new T2(1,_1LC.a,new T2(1,_1LC.b,new T(function(){return B(_1Lz(_1LB.b));})));}},_1LD=B(_1Lz(_1Hp));if(!_1LD._){return __Z;}else{return B(_1Ct(new T2(1,_1LD.a,new T(function(){return B(_1Dq(_1CM,_1LD.b));}))));}});return B(_1Dq(_1CN,new T2(1,_1Ly,new T2(1,_1Lw,_Z))));});return B(_x(B(_1Ct(new T2(1,new T(function(){return B(_H(0,_1Hf,_Z));}),_1Lv))),_1D2));}),_1LE=__app2(E(_1Ek),toJSStr(E(_1CO)),B(_1qX(B(_1Gj(B(unAppCStr("\"",_1Lu)))))));return new F(function(){return _1JX(_,_1Cy);});break;default:return new F(function(){return _1JX(_,_1CP);});}},_1LF=E(_1HD);if(!_1LF._){var _1LG=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1ID(_);});}else{var _1LH=new T(function(){return B(_H(0,E(_1LF.a),new T(function(){return B(_1Em(_1LF.b));})));}),_1LI=B(_1Co(_1Gh,new T2(1,_2B,_1LH),_));return new F(function(){return _1ID(_);});}};if(!E(_1I9)){var _1LJ=B(_1Co(_1Gh,_1EL,_));return new F(function(){return _1IA(_);});}else{var _1LK=B(_1Co(_1Gh,_1EK,_));return new F(function(){return _1IA(_);});}},_1LL=E(_1Hr);if(!_1LL._){var _1LM=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Iy(_);});}else{var _1LN=new T(function(){var _1LO=E(_1LL.a),_1LP=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1LQ){return new F(function(){return _1D5(_1LO.a,_1LQ);});},new T2(1,function(_1LR){return new F(function(){return _1D5(_1LO.b,_1LR);});},_Z)),new T2(1,_F,new T(function(){return B(_1Eq(_1LL.b));}))));});return new T2(1,_G,_1LP);}),_1LS=B(_1Co(_1Gh,new T2(1,_2B,_1LN),_));return new F(function(){return _1Iy(_);});}},_1LT=E(_1Hq);if(!_1LT._){var _1LU=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Ix(_);});}else{var _1LV=new T(function(){return B(_H(0,E(_1LT.a),new T(function(){return B(_1Ey(_1LT.b));})));}),_1LW=B(_1Co(_1Gh,new T2(1,_2B,_1LV),_));return new F(function(){return _1Ix(_);});}},_1LX=E(_1Hp);if(!_1LX._){var _1LY=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Iw(_);});}else{var _1LZ=new T(function(){var _1M0=E(_1LX.a),_1M1=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1M2){return new F(function(){return _1D5(_1M0.a,_1M2);});},new T2(1,function(_1M3){return new F(function(){return _1D5(_1M0.b,_1M3);});},_Z)),new T2(1,_F,new T(function(){return B(_1EC(_1LX.b));}))));});return new T2(1,_G,_1M1);}),_1M4=B(_1Co(_1Gh,new T2(1,_2B,_1LZ),_));return new F(function(){return _1Iw(_);});}},_1M5=E(_1HA);if(!_1M5._){return new F(function(){return _1HY(_,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HT,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HQ,_1HP);});}else{var _1M6=E(_1M5.b);if(!_1M6._){return new F(function(){return _1HY(_,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HT,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HQ,_1HP);});}else{var _1M7=E(_1M6.b);if(!_1M7._){return new F(function(){return _1HY(_,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HT,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HQ,_1HP);});}else{var _1M8=_1M7.a,_1M9=E(_1M7.b);if(!_1M9._){return new F(function(){return _1HY(_,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HT,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HQ,_1HP);});}else{if(!E(_1M9.b)._){var _1Ma=B(_1d7(B(_qy(_1M8,0)),_1Hh,new T(function(){var _1Mb=B(_Kk(B(_wH(_1CL,_1M5.a))));if(!_1Mb._){return E(_1E7);}else{if(!E(_1Mb.b)._){if(E(_1Mb.a)==2){return E(_1Eb);}else{return E(_1E7);}}else{return E(_1E7);}}}),_)),_1Mc=E(_1Ma),_1Md=_1Mc.a,_1Me=new T(function(){var _1Mf=new T(function(){return B(_aj(function(_1Mg){var _1Mh=B(_ws(_3S,_1Mg,B(_Kw(_1CV,_1M8))));return (_1Mh._==0)?E(_1CF):E(_1Mh.a);},B(_aj(_1EM,B(_1F4(B(_1Ec(_1Md,_1E8))))))));}),_1Mi=B(_Kw(_1Md,_1M8)),_1Mj=B(_Yd(B(unAppCStr("e.==.m1:",_1M9.a)),{_:0,a:E(_1Ha),b:E(_1Hb),c:E(_1Hc),d:_1Hd,e:_1He,f:_1Hf,g:E(B(_x(_1Hg,new T2(1,new T2(0,new T2(0,_1M6.a,_1CU),_1Hf),new T2(1,new T2(0,new T2(0,_1Mf,_1CU),_1Hf),_Z))))),h:E(_1Mc.b),i:E(_1Hi),j:E(_1Hj),k:E(_1Hk)},_1HT,_1Hn,B(_x(B(_0(_Z,B(_1GZ(_1M8,B(_9T(_1Ho)))))),new T(function(){return B(_aj(_1BY,_1Mi));},1))),_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,E(_1Mi),0,_1HD,_1HR,_1HG,_1HQ,_1HP)),_1Mk=B(_1r8(_1M8,_1Mj.a,_1Mj.b,_1Mj.c,_1Mj.d,_1Mj.e,_1Mj.f,_1Mj.g,_1Mj.h,_1Mj.i,_1Mj.j,_1Mj.k,_1Mj.l,_1Mj.m,_1Mj.n,_1Mj.o,_1Mj.p,_1Mj.q,_1Mj.r,_1Mj.s,_1Mj.t,_1Mj.u,_1Mj.v));return {_:0,a:E(_1Mk.a),b:E(_1Mk.b),c:E(_1Mk.c),d:E(_1Mk.d),e:E(_1Mk.e),f:E(_1Mk.f),g:E(_1Mk.g),h:E(_1Mk.h),i:_1Mk.i,j:_1Mk.j,k:_1Mk.k,l:_1Mk.l,m:E(_1Mk.m),n:_1Mk.n,o:E(_1Mk.o),p:E(_1Mk.p),q:_1Mk.q,r:E(_1Mk.r),s:E(_1Mk.s),t:_1Mk.t,u:E(_1Mk.u),v:E(_1Mk.v)};}),_1Ml=function(_){var _1Mm=function(_){var _1Mn=function(_){var _1Mo=new T(function(){var _1Mp=E(E(_1Me).a);return new T6(0,_1Mp,_1Mp.a,_1Mp.g,_1Mp.h,_1Mp.i,_1Mp.k);}),_1Mq=B(_1Co(_1Gh,new T2(1,_aI,new T(function(){return B(_cp(E(_1Mo).e,_1Dk));})),_)),_1Mr=E(_1Mo),_1Ms=_1Mr.a,_1Mt=function(_){var _1Mu=B(_1Co(_1Gh,B(_H(0,_1Hx,_Z)),_)),_1Mv=B(_1Co(_1Gh,B(_2C(_1D8,_1Mr.c,_Z)),_)),_1Mw=function(_){var _1Mx=B(_1aE(_1CT,_1Mr.d,_)),_1My=E(_1Mx).b,_1Mz=E(_1H5),_1MA=_1Mz.a,_1MB=_1Mz.b,_1MC=new T(function(){return B(_1rX(E(_1H9)));}),_1MD=new T(function(){var _1ME=E(_1Me),_1MF=_1ME.b,_1MG=_1ME.c,_1MH=_1ME.d,_1MI=_1ME.e,_1MJ=_1ME.f,_1MK=_1ME.g,_1ML=_1ME.h,_1MM=_1ME.i,_1MN=_1ME.j,_1MO=_1ME.k,_1MP=_1ME.l,_1MQ=_1ME.m,_1MR=_1ME.n,_1MS=_1ME.o,_1MT=_1ME.p,_1MU=_1ME.q,_1MV=_1ME.r,_1MW=_1ME.t,_1MX=_1ME.u,_1MY=_1ME.v,_1MZ=E(_1ME.s),_1N0=_1MZ.a,_1N1=_1MZ.b,_1N2=E(_1MC),_1N3=E(_1Mr.b),_1N4=_1N3.a,_1N5=_1N3.b,_1N6=function(_1N7,_1N8){var _1N9=E(_1N7),_1Na=E(_1N4);if(_1N9<=_1Na){if(_1Na<=_1N9){var _1Nb=E(_1N5);if(_1N8<=_1Nb){if(_1Nb<=_1N8){var _1Nc=4;}else{var _1Nc=0;}var _1Nd=_1Nc;}else{var _1Nd=1;}var _1Ne=_1Nd;}else{var _1Ne=2;}var _1Nf=_1Ne;}else{var _1Nf=3;}var _1Ng=function(_1Nh,_1Ni,_1Nj,_1Nk,_1Nl,_1Nm,_1Nn,_1No,_1Np,_1Nq){switch(E(_1Nf)){case 0:if(!E(E(_1Ms).c)){var _1Nr=new T2(0,_1N0,_1N1);}else{var _1Nr=new T2(0,_1N0,_1Do);}var _1Ns=_1Nr;break;case 1:if(E(E(_1Ms).c)==1){var _1Nt=new T2(0,_1N0,_1N1);}else{var _1Nt=new T2(0,_1N0,_1Gm);}var _1Ns=_1Nt;break;case 2:if(E(E(_1Ms).c)==2){var _1Nu=new T2(0,_1N0,_1N1);}else{var _1Nu=new T2(0,_1N0,_1CS);}var _1Ns=_1Nu;break;case 3:if(E(E(_1Ms).c)==3){var _1Nv=new T2(0,_1N0,_1N1);}else{var _1Nv=new T2(0,_1N0,_1CR);}var _1Ns=_1Nv;break;default:if(E(E(_1Ms).c)==4){var _1Nw=new T2(0,_1N0,_1N1);}else{var _1Nw=new T2(0,_1N0,_1Gm);}var _1Ns=_1Nw;}var _1Nx=B(_1oI(_1Gm,_1No,_1MI,{_:0,a:E(_1Nh),b:E(_1Ni),c:E(_1Nj),d:_1Nk,e:_1Nl,f:_1Nm,g:E(_1Nn),h:E(_1My),i:E(_1No),j:E(_1Np),k:E(_1Nq)},_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1MP,_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1Ns,_1MW,_1MX,_1MY)),_1Ny=_1Nx.a,_1Nz=_1Nx.b,_1NA=_1Nx.c,_1NB=_1Nx.d,_1NC=_1Nx.e,_1ND=_1Nx.f,_1NE=_1Nx.g,_1NF=_1Nx.h,_1NG=_1Nx.i,_1NH=_1Nx.j,_1NI=_1Nx.k,_1NJ=_1Nx.l,_1NK=_1Nx.m,_1NL=_1Nx.n,_1NM=_1Nx.o,_1NN=_1Nx.q,_1NO=_1Nx.r,_1NP=_1Nx.s,_1NQ=_1Nx.t,_1NR=_1Nx.u,_1NS=_1Nx.v,_1NT=E(_1Nx.p);if(!_1NT._){return {_:0,a:E(_1Ny),b:E(_1Nz),c:E(_1NA),d:E(_1NB),e:E(_1NC),f:E(_1ND),g:E(_1NE),h:E(_1NF),i:_1NG,j:_1NH,k:_1NI,l:_1NJ,m:E(_1NK),n:_1NL,o:E(_1NM),p:E(_Z),q:_1NN,r:E(_1NO),s:E(_1NP),t:_1NQ,u:E(_1NR),v:E(_1NS)};}else{var _1NU=B(_qy(_1No,0))-2|0,_1NV=function(_1NW){var _1NX=E(_1Ny);return {_:0,a:E({_:0,a:E(_1NX.a),b:E(_1NX.b),c:E(_1NX.c),d:_1NX.d,e:_1NX.e,f:_1NX.f,g:E(_Z),h:_1NX.h,i:E(_1NX.i),j:E(_1NX.j),k:E(_1NX.k)}),b:E(_1Nz),c:E(_1NA),d:E(B(_x(B(_0(_Z,B(_1GZ(B(_aj(_1EM,_1NT)),B(_9T(_1NB)))))),new T(function(){return B(_aj(_1BT,_1NT));},1)))),e:E(_1NC),f:E(_1ND),g:E(_1NE),h:E(_1NF),i:_1NG,j:_1NH,k:_1NI,l:_1NJ,m:E(_1NK),n:_1NL,o:E(_1NM),p:E(_Z),q:_1NN,r:E(B(_x(_1NO,new T2(1,_1NN,_Z)))),s:E(_1NP),t:_1NQ,u:E(_1NR),v:E(_1NS)};};if(_1NU>0){if(!B(_uV(B(_1BA(_1NU,_1No)),_1CQ))){return {_:0,a:E(_1Ny),b:E(_1Nz),c:E(_1NA),d:E(_1NB),e:E(_1NC),f:E(_1ND),g:E(_1NE),h:E(_1NF),i:_1NG,j:_1NH,k:_1NI,l:_1NJ,m:E(_1NK),n:_1NL,o:E(_1NM),p:E(_1NT),q:_1NN,r:E(_1NO),s:E(_1NP),t:_1NQ,u:E(_1NR),v:E(_1NS)};}else{return new F(function(){return _1NV(_);});}}else{if(!B(_uV(_1No,_1CQ))){return {_:0,a:E(_1Ny),b:E(_1Nz),c:E(_1NA),d:E(_1NB),e:E(_1NC),f:E(_1ND),g:E(_1NE),h:E(_1NF),i:_1NG,j:_1NH,k:_1NI,l:_1NJ,m:E(_1NK),n:_1NL,o:E(_1NM),p:E(_1NT),q:_1NN,r:E(_1NO),s:E(_1NP),t:_1NQ,u:E(_1NR),v:E(_1NS)};}else{return new F(function(){return _1NV(_);});}}}};if(E(_1N2)==32){var _1NY=E(_1Ms),_1NZ=E(_1NY.a),_1O0=B(_1xQ(_1N9,_1N8,_1NZ.a,_1NZ.b,_1NY.b,_1Nf,_1NY.d,_1NY.e,_1NY.f,_1NY.g,_1NY.h,_1NY.i,_1NY.j,_1NY.k)),_1O1=E(_1O0.a),_1O2=B(_1Bb(_1O1.a,E(_1O1.b),_1O0.b,_1O0.c,_1O0.d,_1O0.e,_1O0.f,_1O0.g,_1O0.h,_1O0.i,_1O0.j,_1O0.k));return new F(function(){return _1Ng(_1O2.a,_1O2.b,_1O2.c,_1O2.d,_1O2.e,_1O2.f,_1O2.g,_1O2.i,_1O2.j,_1O2.k);});}else{var _1O3=E(_1Ms),_1O4=E(_1O3.a),_1O5=B(_1xQ(_1N9,_1N8,_1O4.a,_1O4.b,_1O3.b,_1Nf,_1O3.d,_1O3.e,_1O3.f,_1O3.g,_1O3.h,_1O3.i,_1O3.j,_1O3.k));return new F(function(){return _1Ng(_1O5.a,_1O5.b,_1O5.c,_1O5.d,_1O5.e,_1O5.f,_1O5.g,_1O5.i,_1O5.j,_1O5.k);});}},_1O6=function(_1O7,_1O8){var _1O9=E(_1O8),_1Oa=E(_1N4);if(_1O7<=_1Oa){if(_1Oa<=_1O7){var _1Ob=E(_1N5);if(_1O9<=_1Ob){if(_1Ob<=_1O9){var _1Oc=4;}else{var _1Oc=0;}var _1Od=_1Oc;}else{var _1Od=1;}var _1Oe=_1Od;}else{var _1Oe=2;}var _1Of=_1Oe;}else{var _1Of=3;}var _1Og=function(_1Oh,_1Oi,_1Oj,_1Ok,_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq){switch(E(_1Of)){case 0:if(!E(E(_1Ms).c)){var _1Or=new T2(0,_1N0,_1N1);}else{var _1Or=new T2(0,_1N0,_1Do);}var _1Os=_1Or;break;case 1:if(E(E(_1Ms).c)==1){var _1Ot=new T2(0,_1N0,_1N1);}else{var _1Ot=new T2(0,_1N0,_1Gm);}var _1Os=_1Ot;break;case 2:if(E(E(_1Ms).c)==2){var _1Ou=new T2(0,_1N0,_1N1);}else{var _1Ou=new T2(0,_1N0,_1CS);}var _1Os=_1Ou;break;case 3:if(E(E(_1Ms).c)==3){var _1Ov=new T2(0,_1N0,_1N1);}else{var _1Ov=new T2(0,_1N0,_1CR);}var _1Os=_1Ov;break;default:if(E(E(_1Ms).c)==4){var _1Ow=new T2(0,_1N0,_1N1);}else{var _1Ow=new T2(0,_1N0,_1Gm);}var _1Os=_1Ow;}var _1Ox=B(_1oI(_1Gm,_1Oo,_1MI,{_:0,a:E(_1Oh),b:E(_1Oi),c:E(_1Oj),d:_1Ok,e:_1Ol,f:_1Om,g:E(_1On),h:E(_1My),i:E(_1Oo),j:E(_1Op),k:E(_1Oq)},_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1MP,_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1Os,_1MW,_1MX,_1MY)),_1Oy=_1Ox.a,_1Oz=_1Ox.b,_1OA=_1Ox.c,_1OB=_1Ox.d,_1OC=_1Ox.e,_1OD=_1Ox.f,_1OE=_1Ox.g,_1OF=_1Ox.h,_1OG=_1Ox.i,_1OH=_1Ox.j,_1OI=_1Ox.k,_1OJ=_1Ox.l,_1OK=_1Ox.m,_1OL=_1Ox.n,_1OM=_1Ox.o,_1ON=_1Ox.q,_1OO=_1Ox.r,_1OP=_1Ox.s,_1OQ=_1Ox.t,_1OR=_1Ox.u,_1OS=_1Ox.v,_1OT=E(_1Ox.p);if(!_1OT._){return {_:0,a:E(_1Oy),b:E(_1Oz),c:E(_1OA),d:E(_1OB),e:E(_1OC),f:E(_1OD),g:E(_1OE),h:E(_1OF),i:_1OG,j:_1OH,k:_1OI,l:_1OJ,m:E(_1OK),n:_1OL,o:E(_1OM),p:E(_Z),q:_1ON,r:E(_1OO),s:E(_1OP),t:_1OQ,u:E(_1OR),v:E(_1OS)};}else{var _1OU=B(_qy(_1Oo,0))-2|0,_1OV=function(_1OW){var _1OX=E(_1Oy);return {_:0,a:E({_:0,a:E(_1OX.a),b:E(_1OX.b),c:E(_1OX.c),d:_1OX.d,e:_1OX.e,f:_1OX.f,g:E(_Z),h:_1OX.h,i:E(_1OX.i),j:E(_1OX.j),k:E(_1OX.k)}),b:E(_1Oz),c:E(_1OA),d:E(B(_x(B(_0(_Z,B(_1GZ(B(_aj(_1EM,_1OT)),B(_9T(_1OB)))))),new T(function(){return B(_aj(_1BT,_1OT));},1)))),e:E(_1OC),f:E(_1OD),g:E(_1OE),h:E(_1OF),i:_1OG,j:_1OH,k:_1OI,l:_1OJ,m:E(_1OK),n:_1OL,o:E(_1OM),p:E(_Z),q:_1ON,r:E(B(_x(_1OO,new T2(1,_1ON,_Z)))),s:E(_1OP),t:_1OQ,u:E(_1OR),v:E(_1OS)};};if(_1OU>0){if(!B(_uV(B(_1BA(_1OU,_1Oo)),_1CQ))){return {_:0,a:E(_1Oy),b:E(_1Oz),c:E(_1OA),d:E(_1OB),e:E(_1OC),f:E(_1OD),g:E(_1OE),h:E(_1OF),i:_1OG,j:_1OH,k:_1OI,l:_1OJ,m:E(_1OK),n:_1OL,o:E(_1OM),p:E(_1OT),q:_1ON,r:E(_1OO),s:E(_1OP),t:_1OQ,u:E(_1OR),v:E(_1OS)};}else{return new F(function(){return _1OV(_);});}}else{if(!B(_uV(_1Oo,_1CQ))){return {_:0,a:E(_1Oy),b:E(_1Oz),c:E(_1OA),d:E(_1OB),e:E(_1OC),f:E(_1OD),g:E(_1OE),h:E(_1OF),i:_1OG,j:_1OH,k:_1OI,l:_1OJ,m:E(_1OK),n:_1OL,o:E(_1OM),p:E(_1OT),q:_1ON,r:E(_1OO),s:E(_1OP),t:_1OQ,u:E(_1OR),v:E(_1OS)};}else{return new F(function(){return _1OV(_);});}}}};if(E(_1N2)==32){var _1OY=E(_1Ms),_1OZ=E(_1OY.a),_1P0=B(_1xQ(_1O7,_1O9,_1OZ.a,_1OZ.b,_1OY.b,_1Of,_1OY.d,_1OY.e,_1OY.f,_1OY.g,_1OY.h,_1OY.i,_1OY.j,_1OY.k)),_1P1=E(_1P0.a),_1P2=B(_1Bb(_1P1.a,E(_1P1.b),_1P0.b,_1P0.c,_1P0.d,_1P0.e,_1P0.f,_1P0.g,_1P0.h,_1P0.i,_1P0.j,_1P0.k));return new F(function(){return _1Og(_1P2.a,_1P2.b,_1P2.c,_1P2.d,_1P2.e,_1P2.f,_1P2.g,_1P2.i,_1P2.j,_1P2.k);});}else{var _1P3=E(_1Ms),_1P4=E(_1P3.a),_1P5=B(_1xQ(_1O7,_1O9,_1P4.a,_1P4.b,_1P3.b,_1Of,_1P3.d,_1P3.e,_1P3.f,_1P3.g,_1P3.h,_1P3.i,_1P3.j,_1P3.k));return new F(function(){return _1Og(_1P5.a,_1P5.b,_1P5.c,_1P5.d,_1P5.e,_1P5.f,_1P5.g,_1P5.i,_1P5.j,_1P5.k);});}},_1P6=E(_1N2);switch(_1P6){case 72:var _1P7=E(_1N5);if(0<=(_1P7-1|0)){return B(_1N6(_1N4,_1P7-1|0));}else{return B(_1N6(_1N4,_1P7));}break;case 75:var _1P8=E(_1N4);if(0<=(_1P8-1|0)){return B(_1O6(_1P8-1|0,_1N5));}else{return B(_1O6(_1P8,_1N5));}break;case 77:var _1P9=E(_1N4);if(E(_1Hl)!=(_1P9+1|0)){return B(_1O6(_1P9+1|0,_1N5));}else{return B(_1O6(_1P9,_1N5));}break;case 80:var _1Pa=E(_1N5);if(E(_1Hm)!=(_1Pa+1|0)){return B(_1N6(_1N4,_1Pa+1|0));}else{return B(_1N6(_1N4,_1Pa));}break;case 104:var _1Pb=E(_1N4);if(0<=(_1Pb-1|0)){return B(_1O6(_1Pb-1|0,_1N5));}else{return B(_1O6(_1Pb,_1N5));}break;case 106:var _1Pc=E(_1N5);if(E(_1Hm)!=(_1Pc+1|0)){return B(_1N6(_1N4,_1Pc+1|0));}else{return B(_1N6(_1N4,_1Pc));}break;case 107:var _1Pd=E(_1N5);if(0<=(_1Pd-1|0)){return B(_1N6(_1N4,_1Pd-1|0));}else{return B(_1N6(_1N4,_1Pd));}break;case 108:var _1Pe=E(_1N4);if(E(_1Hl)!=(_1Pe+1|0)){return B(_1O6(_1Pe+1|0,_1N5));}else{return B(_1O6(_1Pe,_1N5));}break;default:var _1Pf=E(_1N4),_1Pg=E(_1N5),_1Ph=function(_1Pi,_1Pj,_1Pk,_1Pl,_1Pm,_1Pn,_1Po,_1Pp,_1Pq,_1Pr){if(E(E(_1Ms).c)==4){var _1Ps=new T2(0,_1N0,_1N1);}else{var _1Ps=new T2(0,_1N0,_1Gm);}var _1Pt=B(_1oI(_1Gm,_1Pp,_1MI,{_:0,a:E(_1Pi),b:E(_1Pj),c:E(_1Pk),d:_1Pl,e:_1Pm,f:_1Pn,g:E(_1Po),h:E(_1My),i:E(_1Pp),j:E(_1Pq),k:E(_1Pr)},_1MF,_1MG,_1MH,_1MI,_1MJ,_1MK,_1ML,_1MM,_1MN,_1MO,_1MP,_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1Ps,_1MW,_1MX,_1MY)),_1Pu=_1Pt.a,_1Pv=_1Pt.b,_1Pw=_1Pt.c,_1Px=_1Pt.d,_1Py=_1Pt.e,_1Pz=_1Pt.f,_1PA=_1Pt.g,_1PB=_1Pt.h,_1PC=_1Pt.i,_1PD=_1Pt.j,_1PE=_1Pt.k,_1PF=_1Pt.l,_1PG=_1Pt.m,_1PH=_1Pt.n,_1PI=_1Pt.o,_1PJ=_1Pt.q,_1PK=_1Pt.r,_1PL=_1Pt.s,_1PM=_1Pt.t,_1PN=_1Pt.u,_1PO=_1Pt.v,_1PP=E(_1Pt.p);if(!_1PP._){return {_:0,a:E(_1Pu),b:E(_1Pv),c:E(_1Pw),d:E(_1Px),e:E(_1Py),f:E(_1Pz),g:E(_1PA),h:E(_1PB),i:_1PC,j:_1PD,k:_1PE,l:_1PF,m:E(_1PG),n:_1PH,o:E(_1PI),p:E(_Z),q:_1PJ,r:E(_1PK),s:E(_1PL),t:_1PM,u:E(_1PN),v:E(_1PO)};}else{var _1PQ=B(_qy(_1Pp,0))-2|0,_1PR=function(_1PS){var _1PT=E(_1Pu);return {_:0,a:E({_:0,a:E(_1PT.a),b:E(_1PT.b),c:E(_1PT.c),d:_1PT.d,e:_1PT.e,f:_1PT.f,g:E(_Z),h:_1PT.h,i:E(_1PT.i),j:E(_1PT.j),k:E(_1PT.k)}),b:E(_1Pv),c:E(_1Pw),d:E(B(_x(B(_0(_Z,B(_1GZ(B(_aj(_1EM,_1PP)),B(_9T(_1Px)))))),new T(function(){return B(_aj(_1BT,_1PP));},1)))),e:E(_1Py),f:E(_1Pz),g:E(_1PA),h:E(_1PB),i:_1PC,j:_1PD,k:_1PE,l:_1PF,m:E(_1PG),n:_1PH,o:E(_1PI),p:E(_Z),q:_1PJ,r:E(B(_x(_1PK,new T2(1,_1PJ,_Z)))),s:E(_1PL),t:_1PM,u:E(_1PN),v:E(_1PO)};};if(_1PQ>0){if(!B(_uV(B(_1BA(_1PQ,_1Pp)),_1CQ))){return {_:0,a:E(_1Pu),b:E(_1Pv),c:E(_1Pw),d:E(_1Px),e:E(_1Py),f:E(_1Pz),g:E(_1PA),h:E(_1PB),i:_1PC,j:_1PD,k:_1PE,l:_1PF,m:E(_1PG),n:_1PH,o:E(_1PI),p:E(_1PP),q:_1PJ,r:E(_1PK),s:E(_1PL),t:_1PM,u:E(_1PN),v:E(_1PO)};}else{return new F(function(){return _1PR(_);});}}else{if(!B(_uV(_1Pp,_1CQ))){return {_:0,a:E(_1Pu),b:E(_1Pv),c:E(_1Pw),d:E(_1Px),e:E(_1Py),f:E(_1Pz),g:E(_1PA),h:E(_1PB),i:_1PC,j:_1PD,k:_1PE,l:_1PF,m:E(_1PG),n:_1PH,o:E(_1PI),p:E(_1PP),q:_1PJ,r:E(_1PK),s:E(_1PL),t:_1PM,u:E(_1PN),v:E(_1PO)};}else{return new F(function(){return _1PR(_);});}}}};if(E(_1P6)==32){var _1PU=E(_1Ms),_1PV=E(_1PU.a),_1PW=B(_1xQ(_1Pf,_1Pg,_1PV.a,_1PV.b,_1PU.b,_1BG,_1PU.d,_1PU.e,_1PU.f,_1PU.g,_1PU.h,_1PU.i,_1PU.j,_1PU.k)),_1PX=E(_1PW.a),_1PY=B(_1Bb(_1PX.a,E(_1PX.b),_1PW.b,_1PW.c,_1PW.d,_1PW.e,_1PW.f,_1PW.g,_1PW.h,_1PW.i,_1PW.j,_1PW.k));return B(_1Ph(_1PY.a,_1PY.b,_1PY.c,_1PY.d,_1PY.e,_1PY.f,_1PY.g,_1PY.i,_1PY.j,_1PY.k));}else{var _1PZ=E(_1Ms),_1Q0=E(_1PZ.a),_1Q1=B(_1xQ(_1Pf,_1Pg,_1Q0.a,_1Q0.b,_1PZ.b,_1BG,_1PZ.d,_1PZ.e,_1PZ.f,_1PZ.g,_1PZ.h,_1PZ.i,_1PZ.j,_1PZ.k));return B(_1Ph(_1Q1.a,_1Q1.b,_1Q1.c,_1Q1.d,_1Q1.e,_1Q1.f,_1Q1.g,_1Q1.i,_1Q1.j,_1Q1.k));}}}),_1Q2=B(_1bq(_1MA,_1MB,_1H6,_1H7,_1H8,_1MD,_)),_1Q3=_1Q2,_1Q4=E(_1MC),_1Q5=function(_,_1Q6){var _1Q7=function(_1Q8){var _1Q9=B(_1Co(_1Gh,B(_cv(_1Q6)),_)),_1Qa=E(_1Q3),_1Qb=_1Qa.d,_1Qc=_1Qa.e,_1Qd=_1Qa.f,_1Qe=_1Qa.g,_1Qf=_1Qa.i,_1Qg=_1Qa.j,_1Qh=_1Qa.k,_1Qi=_1Qa.l,_1Qj=_1Qa.m,_1Qk=_1Qa.n,_1Ql=_1Qa.o,_1Qm=_1Qa.p,_1Qn=_1Qa.q,_1Qo=_1Qa.r,_1Qp=_1Qa.t,_1Qq=_1Qa.v,_1Qr=E(_1Qa.u),_1Qs=_1Qr.a,_1Qt=_1Qr.d,_1Qu=_1Qr.e,_1Qv=_1Qr.f,_1Qw=_1Qr.g,_1Qx=_1Qr.h,_1Qy=E(_1Qa.a),_1Qz=_1Qy.c,_1QA=_1Qy.f,_1QB=_1Qy.g,_1QC=_1Qy.h,_1QD=E(_1Qa.h),_1QE=E(_1Qa.s),_1QF=function(_1QG){var _1QH=function(_1QI){if(_1QI!=E(_1CJ)){var _1QJ=B(_aW(_1ko,_1QI)),_1QK=_1QJ.a,_1QL=E(_1QJ.b),_1QM=B(_1fC(_1QK,_1QL,new T(function(){return B(_aW(_1mt,_1QI));})));return new F(function(){return _1H4(_1Mz,_1H6,_1H7,_1H8,_1CI,B(_aW(_1kz,_1QI)),_1QM,_1Qz,B(_aW(_1kM,_1QI)),32,_1QI,_1QB,_1QC,B(_x(_1Qy.i,new T2(1,_1CH,new T(function(){return B(_H(0,_1QA,_Z));})))),B(_1C2(_1CG,_1QM)),_AC,_1QK,_1QL,_Z,_1Qb,_1Qc,_1Qd,_1Qe,_1QD.a,_1QD.b,_1Qf,_1Qg,_1Qh, -1,_1Qj,_1Qk,_1Ql,_1Qm,_1Qn,_1Qo,_1QE.a,_1QE.b,_1Qp,_AC,_AC,_AC,_1Qt,_1Qu,_1Qv,_1Qw,_1Qx,_1Qq,_);});}else{var _1QN=__app1(E(_rn),_1MB),_1QO=B(A2(_ro,_1MA,_)),_1QP=B(A(_qT,[_1MA,_n8,_1CC,_1CE,_1CD,_])),_1QQ=B(A(_qT,[_1MA,_n8,_1CC,_1CB,_1Dp,_])),_1QR=B(A(_qT,[_1MA,_n8,_1Do,_1Dn,_1Dm,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1kq),b:E(_1Dl),c:E(_1Qz),d:E(_1CZ),e:32,f:0,g:E(_1QB),h:_1QC,i:E(_Z),j:E(_1Qy.j),k:E(_AC)}),b:E(_1kb),c:E(_1Qa.c),d:E(_1Qb),e:E(_1Qc),f:E(_1Qd),g:E(_1Qe),h:E(_1QD),i:_1Qf,j:_1Qg,k:_1Qh,l:_1Qi,m:E(_1Qj),n:_1Qk,o:E(_1Ql),p:E(_1Qm),q:_1Qn,r:E(_1Qo),s:E(_1QE),t:_1Qp,u:E({_:0,a:E(_1Qs),b:E(_AD),c:E(_AC),d:E(_1Qt),e:E(_1Qu),f:E(_1Qv),g:E(_1Qw),h:E(_1Qx)}),v:E(_1Qq)};});}};if(_1Qi>=0){return new F(function(){return _1QH(_1Qi);});}else{return new F(function(){return _1QH(_1QA+1|0);});}};if(!E(_1Qs)){if(E(_1Q4)==110){return new F(function(){return _1QF(_);});}else{return _1Qa;}}else{return new F(function(){return _1QF(_);});}};if(E(_1Q4)==114){if(!B(_ae(_1Q6,_1CK))){var _1QS=E(_1Q6);if(!_1QS._){return _1Q3;}else{var _1QT=_1QS.b;return new T(function(){var _1QU=E(_1Q3),_1QV=E(_1QU.a),_1QW=E(_1QS.a),_1QX=E(_1QW);if(_1QX==34){var _1QY=B(_XN(_1QW,_1QT));if(!_1QY._){var _1QZ=E(_1Ej);}else{var _1R0=E(_1QY.b);if(!_1R0._){var _1R1=E(_1D3);}else{var _1R2=_1R0.a,_1R3=E(_1R0.b);if(!_1R3._){var _1R4=new T2(1,new T2(1,_1R2,_Z),_Z);}else{var _1R5=E(_1R2),_1R6=new T(function(){var _1R7=B(_Lc(126,_1R3.a,_1R3.b));return new T2(0,_1R7.a,_1R7.b);});if(E(_1R5)==126){var _1R8=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1R6).a);}),new T(function(){return E(E(_1R6).b);})));}else{var _1R8=new T2(1,new T2(1,_1R5,new T(function(){return E(E(_1R6).a);})),new T(function(){return E(E(_1R6).b);}));}var _1R4=_1R8;}var _1R1=_1R4;}var _1QZ=_1R1;}var _1R9=_1QZ;}else{var _1Ra=E(_1QT);if(!_1Ra._){var _1Rb=new T2(1,new T2(1,_1QW,_Z),_Z);}else{var _1Rc=new T(function(){var _1Rd=B(_Lc(126,_1Ra.a,_1Ra.b));return new T2(0,_1Rd.a,_1Rd.b);});if(E(_1QX)==126){var _1Re=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Rc).a);}),new T(function(){return E(E(_1Rc).b);})));}else{var _1Re=new T2(1,new T2(1,_1QW,new T(function(){return E(E(_1Rc).a);})),new T(function(){return E(E(_1Rc).b);}));}var _1Rb=_1Re;}var _1R9=_1Rb;}var _1Rf=B(_Kk(B(_wH(_1CL,new T(function(){return B(_Nr(_1R9));})))));if(!_1Rf._){return E(_1Cz);}else{if(!E(_1Rf.b)._){var _1Rg=E(_1Rf.a),_1Rh=B(_aW(_1ko,_1Rg)),_1Ri=B(_aW(_1R9,1));if(!_1Ri._){var _1Rj=__Z;}else{var _1Rk=E(_1Ri.b);if(!_1Rk._){var _1Rl=__Z;}else{var _1Rm=E(_1Ri.a),_1Rn=new T(function(){var _1Ro=B(_Lc(44,_1Rk.a,_1Rk.b));return new T2(0,_1Ro.a,_1Ro.b);});if(E(_1Rm)==44){var _1Rp=B(_15B(_Z,new T(function(){return E(E(_1Rn).a);}),new T(function(){return E(E(_1Rn).b);})));}else{var _1Rp=B(_15F(new T2(1,_1Rm,new T(function(){return E(E(_1Rn).a);})),new T(function(){return E(E(_1Rn).b);})));}var _1Rl=_1Rp;}var _1Rj=_1Rl;}var _1Rq=B(_aW(_1R9,2));if(!_1Rq._){var _1Rr=E(_1D4);}else{var _1Rs=_1Rq.a,_1Rt=E(_1Rq.b);if(!_1Rt._){var _1Ru=B(_aj(_1CW,new T2(1,new T2(1,_1Rs,_Z),_Z)));}else{var _1Rv=E(_1Rs),_1Rw=new T(function(){var _1Rx=B(_Lc(44,_1Rt.a,_1Rt.b));return new T2(0,_1Rx.a,_1Rx.b);});if(E(_1Rv)==44){var _1Ry=B(_aj(_1CW,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Rw).a);}),new T(function(){return E(E(_1Rw).b);})))));}else{var _1Ry=B(_aj(_1CW,new T2(1,new T2(1,_1Rv,new T(function(){return E(E(_1Rw).a);})),new T(function(){return E(E(_1Rw).b);}))));}var _1Ru=_1Ry;}var _1Rr=_1Ru;}return {_:0,a:E({_:0,a:E(B(_aW(_1kz,_1Rg))),b:E(B(_1fC(_1Rh.a,E(_1Rh.b),new T(function(){return B(_aW(_1mt,_1Rg));})))),c:E(_1QV.c),d:B(_aW(_1kM,_1Rg)),e:32,f:_1Rg,g:E(_1QV.g),h:_1QV.h,i:E(_1QV.i),j:E(_1QV.j),k:E(_1QV.k)}),b:E(_1Rh),c:E(_1QU.c),d:E(_1QU.d),e:E(_1Rj),f:E(_1Rr),g:E(_1QU.g),h:E(_1QU.h),i:_1QU.i,j:_1QU.j,k:_1QU.k,l:_1QU.l,m:E(_1QU.m),n:_1QU.n,o:E(_1QU.o),p:E(_1QU.p),q:_1QU.q,r:E(_1QU.r),s:E(_1QU.s),t:_1QU.t,u:E(_1QU.u),v:E(_1QU.v)};}else{return E(_1CA);}}});}}else{return new F(function(){return _1Q7(_);});}}else{return new F(function(){return _1Q7(_);});}};switch(E(_1Q4)){case 100:var _1Rz=__app1(E(_1Eh),toJSStr(E(_1CO)));return new F(function(){return _1Q5(_,_1Cw);});break;case 114:var _1RA=B(_15Q(_aB,toJSStr(E(_1CO)),_));return new F(function(){return _1Q5(_,new T(function(){var _1RB=E(_1RA);if(!_1RB._){return E(_1Cx);}else{return fromJSStr(B(_1qX(_1RB.a)));}}));});break;case 115:var _1RC=new T(function(){var _1RD=new T(function(){var _1RE=new T(function(){var _1RF=B(_aj(_aG,_1Hq));if(!_1RF._){return __Z;}else{return B(_1Ct(new T2(1,_1RF.a,new T(function(){return B(_1Dq(_1CM,_1RF.b));}))));}}),_1RG=new T(function(){var _1RH=function(_1RI){var _1RJ=E(_1RI);if(!_1RJ._){return __Z;}else{var _1RK=E(_1RJ.a);return new T2(1,_1RK.a,new T2(1,_1RK.b,new T(function(){return B(_1RH(_1RJ.b));})));}},_1RL=B(_1RH(_1Hp));if(!_1RL._){return __Z;}else{return B(_1Ct(new T2(1,_1RL.a,new T(function(){return B(_1Dq(_1CM,_1RL.b));}))));}});return B(_1Dq(_1CN,new T2(1,_1RG,new T2(1,_1RE,_Z))));});return B(_x(B(_1Ct(new T2(1,new T(function(){return B(_H(0,_1Hf,_Z));}),_1RD))),_1D2));}),_1RM=__app2(E(_1Ek),toJSStr(E(_1CO)),B(_1qX(B(_1Gj(B(unAppCStr("\"",_1RC)))))));return new F(function(){return _1Q5(_,_1Cy);});break;default:return new F(function(){return _1Q5(_,_1CP);});}},_1RN=E(_1HD);if(!_1RN._){var _1RO=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Mw(_);});}else{var _1RP=new T(function(){return B(_H(0,E(_1RN.a),new T(function(){return B(_1Em(_1RN.b));})));}),_1RQ=B(_1Co(_1Gh,new T2(1,_2B,_1RP),_));return new F(function(){return _1Mw(_);});}};if(!E(_1Mr.f)){var _1RR=B(_1Co(_1Gh,_1EL,_));return new F(function(){return _1Mt(_);});}else{var _1RS=B(_1Co(_1Gh,_1EK,_));return new F(function(){return _1Mt(_);});}},_1RT=E(_1Hr);if(!_1RT._){var _1RU=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Mn(_);});}else{var _1RV=new T(function(){var _1RW=E(_1RT.a),_1RX=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1RY){return new F(function(){return _1D5(_1RW.a,_1RY);});},new T2(1,function(_1RZ){return new F(function(){return _1D5(_1RW.b,_1RZ);});},_Z)),new T2(1,_F,new T(function(){return B(_1Eq(_1RT.b));}))));});return new T2(1,_G,_1RX);}),_1S0=B(_1Co(_1Gh,new T2(1,_2B,_1RV),_));return new F(function(){return _1Mn(_);});}},_1S1=E(_1Hq);if(!_1S1._){var _1S2=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Mm(_);});}else{var _1S3=new T(function(){return B(_H(0,E(_1S1.a),new T(function(){return B(_1Ey(_1S1.b));})));}),_1S4=B(_1Co(_1Gh,new T2(1,_2B,_1S3),_));return new F(function(){return _1Mm(_);});}},_1S5=E(_1Hp);if(!_1S5._){var _1S6=B(_1Co(_1Gh,_1D1,_));return new F(function(){return _1Ml(_);});}else{var _1S7=new T(function(){var _1S8=E(_1S5.a),_1S9=new T(function(){return B(A3(_wk,_aC,new T2(1,function(_1Sa){return new F(function(){return _1D5(_1S8.a,_1Sa);});},new T2(1,function(_1Sb){return new F(function(){return _1D5(_1S8.b,_1Sb);});},_Z)),new T2(1,_F,new T(function(){return B(_1EC(_1S5.b));}))));});return new T2(1,_G,_1S9);}),_1Sc=B(_1Co(_1Gh,new T2(1,_2B,_1S7),_));return new F(function(){return _1Ml(_);});}}else{return new F(function(){return _1HY(_,_1Ha,_1Hb,_1Hc,_1Hd,_1He,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1HT,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1HS,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_Z,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HQ,_1HP);});}}}}}}}else{if(!E(_1HN)){return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:_1Hz,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E({_:0,a:E(_1HH),b:E(_AC),c:E(_1HJ),d:E(_AC),e:E(_1HL),f:E(_AC),g:E(_AC),h:E(_1HO)}),v:E(_1HP)};}else{var _1Sd=E(_1H5),_1Se=new T(function(){var _1Sf=new T(function(){var _1Sg=B(_1r1(_1Hy));return new T2(0,_1Sg.a,_1Sg.b);}),_1Sh=new T(function(){return B(_qy(E(_1Sf).a,0))-1|0;}),_1Si=function(_1Sj){var _1Sk=E(_1Sj);switch(_1Sk){case  -2:return E(_1HV);case  -1:return {_:0,a:E(_1HU),b:E(_1HT),c:E(B(_1jT(_Z,new T(function(){return B(_aW(E(_1Sf).b,_1Hz));})))),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:_1Hz,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E({_:0,a:E(_1HH),b:E(_AC),c:E(_AD),d:E(_AC),e:E(_1HL),f:E(_AC),g:E(_AC),h:E(_1HO)}),v:E(_1HP)};default:return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:_1Sk,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};}};switch(E(B(_1rX(E(_1H9))))){case 32:return {_:0,a:E(_1HU),b:E(_1HT),c:E(B(_1jT(_Z,new T(function(){return B(_aW(E(_1Sf).b,_1Hz));})))),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:_1Hz,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E({_:0,a:E(_1HH),b:E(_AC),c:E(_AD),d:E(_AC),e:E(_1HL),f:E(_AC),g:E(_AC),h:E(_1HO)}),v:E(_1HP)};break;case 72:var _1Sl=E(_1Hz);if(!_1Sl){return B(_1Si(E(_1Sh)));}else{return B(_1Si(_1Sl-1|0));}break;case 75:if(_1Hz!=E(_1Sh)){return B(_1Si(_1Hz+1|0));}else{return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:0,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};}break;case 77:var _1Sm=E(_1Hz);if(!_1Sm){return B(_1Si(E(_1Sh)));}else{return B(_1Si(_1Sm-1|0));}break;case 80:if(_1Hz!=E(_1Sh)){return B(_1Si(_1Hz+1|0));}else{return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:0,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};}break;case 104:if(_1Hz!=E(_1Sh)){return B(_1Si(_1Hz+1|0));}else{return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:0,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};}break;case 106:if(_1Hz!=E(_1Sh)){return B(_1Si(_1Hz+1|0));}else{return {_:0,a:E(_1HU),b:E(_1HT),c:E(_1Hn),d:E(_1Ho),e:E(_1Hp),f:E(_1Hq),g:E(_1Hr),h:E(_1HS),i:_1Hu,j:_1Hv,k:_1Hw,l:_1Hx,m:E(_1Hy),n:0,o:E(_1HA),p:E(_1HB),q:_1HC,r:E(_1HD),s:E(_1HR),t:_1HG,u:E(_1HQ),v:E(_1HP)};}break;case 107:var _1Sn=E(_1Hz);if(!_1Sn){return B(_1Si(E(_1Sh)));}else{return B(_1Si(_1Sn-1|0));}break;case 108:var _1So=E(_1Hz);if(!_1So){return B(_1Si(E(_1Sh)));}else{return B(_1Si(_1So-1|0));}break;default:return E(_1HV);}});return new F(function(){return _1bq(_1Sd.a,_1Sd.b,_1H6,_1H7,_1H8,_1Se,_);});}}};if(!E(_1HJ)){return new F(function(){return _1HW(_);});}else{if(!E(_1HK)){return new F(function(){return _14v(_1H5,_1H6,_1H7,_1HU,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HR,_1HG,_1HH,_AC,_AC,_1HL,_AD,_1HN,_1HO,_1HP,_);});}else{return new F(function(){return _1HW(_);});}}}else{return _1HV;}}else{return _1HV;}},_1Sp=function(_1Sq,_1Sr,_1Ss){var _1St=E(_1Ss);if(!_1St._){return 0;}else{var _1Su=_1St.b,_1Sv=E(_1St.a),_1Sw=_1Sv.a,_1Sx=_1Sv.b;return (_1Sq<=_1Sw)?1+B(_1Sp(_1Sq,_1Sr,_1Su))|0:(_1Sq>=_1Sw+_1Sv.c)?1+B(_1Sp(_1Sq,_1Sr,_1Su))|0:(_1Sr<=_1Sx)?1+B(_1Sp(_1Sq,_1Sr,_1Su))|0:(_1Sr>=_1Sx+_1Sv.d)?1+B(_1Sp(_1Sq,_1Sr,_1Su))|0:1;}},_1Sy=function(_1Sz,_1SA,_1SB){var _1SC=E(_1SB);if(!_1SC._){return 0;}else{var _1SD=_1SC.b,_1SE=E(_1SC.a),_1SF=_1SE.a,_1SG=_1SE.b;if(_1Sz<=_1SF){return 1+B(_1Sy(_1Sz,_1SA,_1SD))|0;}else{if(_1Sz>=_1SF+_1SE.c){return 1+B(_1Sy(_1Sz,_1SA,_1SD))|0;}else{var _1SH=E(_1SA);return (_1SH<=_1SG)?1+B(_1Sp(_1Sz,_1SH,_1SD))|0:(_1SH>=_1SG+_1SE.d)?1+B(_1Sp(_1Sz,_1SH,_1SD))|0:1;}}}},_1SI=function(_1SJ,_1SK,_1SL){var _1SM=E(_1SL);if(!_1SM._){return 0;}else{var _1SN=_1SM.b,_1SO=E(_1SM.a),_1SP=_1SO.a,_1SQ=_1SO.b,_1SR=E(_1SJ);if(_1SR<=_1SP){return 1+B(_1Sy(_1SR,_1SK,_1SN))|0;}else{if(_1SR>=_1SP+_1SO.c){return 1+B(_1Sy(_1SR,_1SK,_1SN))|0;}else{var _1SS=E(_1SK);return (_1SS<=_1SQ)?1+B(_1Sp(_1SR,_1SS,_1SN))|0:(_1SS>=_1SQ+_1SO.d)?1+B(_1Sp(_1SR,_1SS,_1SN))|0:1;}}}},_1ST=function(_1SU,_1SV){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1SV)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1SV)-100,E(_1SU),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1SU),100);}),new T2(1,new T(function(){return new T4(0,E(_1SU)-100,100,100,E(_1SV)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1SU)-200,E(_1SV)-200);}),_Z)))));},_1SW=32,_1SX=76,_1SY=75,_1SZ=74,_1T0=72,_1T1=64,_1T2=function(_1T3,_1T4,_1T5,_1T6,_1T7){var _1T8=new T(function(){var _1T9=E(_1T4),_1Ta=E(_1T9.a),_1Tb=_1Ta.a,_1Tc=_1Ta.b,_1Td=B(_1ST(_1Tb,_1Tc)),_1Te=new T(function(){var _1Tf=E(_1T9.b);return new T2(0,new T(function(){return B(_kd(_1Tb,_1Tf.a));}),new T(function(){return B(_kd(_1Tc,_1Tf.b));}));});switch(B(_1SI(new T(function(){return E(_1T6)*E(E(_1Te).a);},1),new T(function(){return E(_1T7)*E(E(_1Te).b);},1),new T2(1,_1Td.a,_1Td.b)))){case 1:return E(_1T0);break;case 2:return E(_1SZ);break;case 3:return E(_1SY);break;case 4:return E(_1SX);break;case 5:return E(_1SW);break;default:return E(_1T1);}});return function(_1Tg,_){var _1Th=E(E(_1T4).a),_1Ti=E(_1Tg),_1Tj=E(_1Ti.a),_1Tk=E(_1Ti.b),_1Tl=E(_1Ti.h),_1Tm=E(_1Ti.s),_1Tn=E(_1Ti.u);return new F(function(){return _1H4(_1T3,_1Th.a,_1Th.b,_1T5,_1T8,_1Tj.a,_1Tj.b,_1Tj.c,_1Tj.d,_1Tj.e,_1Tj.f,_1Tj.g,_1Tj.h,_1Tj.i,_1Tj.j,_1Tj.k,_1Tk.a,_1Tk.b,_1Ti.c,_1Ti.d,_1Ti.e,_1Ti.f,_1Ti.g,_1Tl.a,_1Tl.b,_1Ti.i,_1Ti.j,_1Ti.k,_1Ti.l,_1Ti.m,_1Ti.n,_1Ti.o,_1Ti.p,_1Ti.q,_1Ti.r,_1Tm.a,_1Tm.b,_1Ti.t,_1Tn.a,_1Tn.b,_1Tn.c,_1Tn.d,_1Tn.e,_1Tn.f,_1Tn.g,_1Tn.h,_1Ti.v,_);});};},_1To=0,_1Tp=2,_1Tq=2,_1Tr=0,_1Ts=new T(function(){return eval("document");}),_1Tt=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Tu=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1Tv=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1Tw=function(_1Tx){return E(E(_1Tx).b);},_1Ty=function(_1Tz,_1TA){return new F(function(){return A2(_1Tw,_1Tz,function(_){var _1TB=E(_1TA),_1TC=__app1(E(_1Tv),_1TB);if(!_1TC){return _2U;}else{var _1TD=__app1(E(_1Tu),_1TB);return new T1(1,new T2(0,_1TD,_1TB));}});});},_1TE=1,_1TF=new T(function(){var _1TG=E(_1kM);if(!_1TG._){return E(_rm);}else{return {_:0,a:E(_1kq),b:E(B(_1fC(_1ka,5,_1lg))),c:E(_1TE),d:E(_1TG.a),e:32,f:0,g:E(_Z),h:0,i:E(_Z),j:E(_AC),k:E(_AC)};}}),_1TH=0,_1TI=4,_1TJ=new T2(0,_1TI,_1TH),_1TK=new T2(0,_1TH,_1TH),_1TL={_:0,a:E(_AC),b:E(_AC),c:E(_AD),d:E(_AC),e:E(_AC),f:E(_AC),g:E(_AC),h:E(_AC)},_1TM=new T(function(){return {_:0,a:E(_1TF),b:E(_1kb),c:E(_1gN),d:E(_Z),e:E(_Z),f:E(_Z),g:E(_Z),h:E(_1TK),i:0,j:0,k:0,l: -1,m:E(_Z),n:0,o:E(_Z),p:E(_Z),q:0,r:E(_Z),s:E(_1TJ),t:0,u:E(_1TL),v:E(_Z)};}),_1TN=new T1(0,100),_1TO=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1TP=new T6(0,_2U,_2V,_Z,_1TO,_2U,_2U),_1TQ=new T(function(){return B(_2S(_1TP));}),_1TR=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-8"));}),_1TS=new T6(0,_2U,_2V,_Z,_1TR,_2U,_2U),_1TT=new T(function(){return B(_2S(_1TS));}),_1TU=new T1(1,50),_1TV=function(_1TW){return E(E(_1TW).a);},_1TX=function(_1TY){return E(E(_1TY).a);},_1TZ=function(_1U0){return E(E(_1U0).b);},_1U1=function(_1U2){return E(E(_1U2).b);},_1U3=function(_1U4){return E(E(_1U4).a);},_1U5=function(_){return new F(function(){return nMV(_2U);});},_1U6=new T(function(){return B(_3d(_1U5));}),_1U7=function(_1U8){return E(E(_1U8).b);},_1U9=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1Ua=function(_1Ub){return E(E(_1Ub).d);},_1Uc=function(_1Ud,_1Ue,_1Uf,_1Ug,_1Uh,_1Ui){var _1Uj=B(_1TV(_1Ud)),_1Uk=B(_1TX(_1Uj)),_1Ul=new T(function(){return B(_1Tw(_1Uj));}),_1Um=new T(function(){return B(_1Ua(_1Uk));}),_1Un=new T(function(){return B(A1(_1Ue,_1Ug));}),_1Uo=new T(function(){return B(A2(_1U3,_1Uf,_1Uh));}),_1Up=function(_1Uq){return new F(function(){return A1(_1Um,new T3(0,_1Uo,_1Un,_1Uq));});},_1Ur=function(_1Us){var _1Ut=new T(function(){var _1Uu=new T(function(){var _1Uv=__createJSFunc(2,function(_1Uw,_){var _1Ux=B(A2(E(_1Us),_1Uw,_));return _3h;}),_1Uy=_1Uv;return function(_){return new F(function(){return __app3(E(_1U9),E(_1Un),E(_1Uo),_1Uy);});};});return B(A1(_1Ul,_1Uu));});return new F(function(){return A3(_1TZ,_1Uk,_1Ut,_1Up);});},_1Uz=new T(function(){var _1UA=new T(function(){return B(_1Tw(_1Uj));}),_1UB=function(_1UC){var _1UD=new T(function(){return B(A1(_1UA,function(_){var _=wMV(E(_1U6),new T1(1,_1UC));return new F(function(){return A(_1U1,[_1Uf,_1Uh,_1UC,_]);});}));});return new F(function(){return A3(_1TZ,_1Uk,_1UD,_1Ui);});};return B(A2(_1U7,_1Ud,_1UB));});return new F(function(){return A3(_1TZ,_1Uk,_1Uz,_1Ur);});},_1UE=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1UF=function(_){var _1UG=rMV(E(_1U6)),_1UH=E(_1UG);if(!_1UH._){var _1UI=__app1(E(_1UE),E(_3h));return new F(function(){return _kK(_);});}else{var _1UJ=__app1(E(_1UE),E(_1UH.a));return new F(function(){return _kK(_);});}},_1UK="src",_1UL=new T(function(){return B(unCStr("img"));}),_1UM=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1UN=function(_1UO,_1UP){return new F(function(){return A2(_1Tw,_1UO,function(_){var _1UQ=__app1(E(_1UM),toJSStr(E(_1UL))),_1UR=__app3(E(_m6),_1UQ,E(_1UK),E(_1UP));return _1UQ;});});},_1US=new T(function(){return B(unCStr(".png"));}),_1UT=function(_1UU,_1UV){var _1UW=E(_1UU);if(_1UW==( -1)){return __Z;}else{var _1UX=new T(function(){var _1UY=new T(function(){return toJSStr(B(_x(_1UV,new T(function(){return B(_x(B(_H(0,_1UW,_Z)),_1US));},1))));});return B(_1UN(_63,_1UY));});return new F(function(){return _x(B(_1UT(_1UW-1|0,_1UV)),new T2(1,_1UX,_Z));});}},_1UZ=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1V0=new T(function(){return B(_1UT(120,_1UZ));}),_1V1=function(_1V2,_){var _1V3=E(_1V2);if(!_1V3._){return _Z;}else{var _1V4=B(A1(_1V3.a,_)),_1V5=B(_1V1(_1V3.b,_));return new T2(1,_1V4,_1V5);}},_1V6=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1V7=new T(function(){return B(_1UT(56,_1V6));}),_1V8=function(_1V9,_){var _1Va=E(_1V9);if(!_1Va._){return _Z;}else{var _1Vb=B(A1(_1Va.a,_)),_1Vc=B(_1V8(_1Va.b,_));return new T2(1,_1Vb,_1Vc);}},_1Vd=new T(function(){return B(unCStr("Images/img"));}),_1Ve=new T(function(){return B(_1UT(5,_1Vd));}),_1Vf=function(_1Vg,_){var _1Vh=E(_1Vg);if(!_1Vh._){return _Z;}else{var _1Vi=B(A1(_1Vh.a,_)),_1Vj=B(_1Vf(_1Vh.b,_));return new T2(1,_1Vi,_1Vj);}},_1Vk=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1Vl=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1Vm=function(_1Vn,_1Vo,_1Vp){var _1Vq=B(_1TV(_1Vn)),_1Vr=new T(function(){return B(_1Tw(_1Vq));}),_1Vs=function(_1Vt){var _1Vu=function(_){var _1Vv=E(_1Vo);if(!_1Vv._){var _1Vw=B(A1(_1Vt,_kJ)),_1Vx=__createJSFunc(0,function(_){var _1Vy=B(A1(_1Vw,_));return _3h;}),_1Vz=__app2(E(_1Vl),_1Vv.a,_1Vx);return new T(function(){var _1VA=Number(_1Vz),_1VB=jsTrunc(_1VA);return new T2(0,_1VB,E(_1Vv));});}else{var _1VC=B(A1(_1Vt,_kJ)),_1VD=__createJSFunc(0,function(_){var _1VE=B(A1(_1VC,_));return _3h;}),_1VF=__app2(E(_1Vk),_1Vv.a,_1VD);return new T(function(){var _1VG=Number(_1VF),_1VH=jsTrunc(_1VG);return new T2(0,_1VH,E(_1Vv));});}};return new F(function(){return A1(_1Vr,_1Vu);});},_1VI=new T(function(){return B(A2(_1U7,_1Vn,function(_1VJ){return E(_1Vp);}));});return new F(function(){return A3(_1TZ,B(_1TX(_1Vq)),_1VI,_1Vs);});},_1VK=function(_1VL){var _1VM=E(_1VL),_1VN=E(_1VM.a),_1VO=new T(function(){return B(_x(_1VN.b,new T(function(){return B(unAppCStr(" >>",_1VN.c));},1)));});return new T2(0,new T2(1,_1VM.b,_1r7),_1VO);},_1VP=function(_){var _1VQ=B(_1Vf(_1Ve,_)),_1VR=B(_1V8(_1V7,_)),_1VS=B(_1V1(_1V0,_)),_1VT=__app1(E(_1Tt),"canvas"),_1VU=__eq(_1VT,E(_3h));if(!E(_1VU)){var _1VV=__isUndef(_1VT);if(!E(_1VV)){var _1VW=B(A3(_1Ty,_63,_1VT,_)),_1VX=E(_1VW);if(!_1VX._){return new F(function(){return die(_1TT);});}else{var _1VY=E(_1VX.a),_1VZ=_1VY.b,_1W0=B(_a8(_1VZ,_)),_1W1=_1W0,_1W2=nMV(_1TM),_1W3=_1W2,_1W4=new T3(0,_1VQ,_1VR,_1VS),_1W5=B(A(_1Uc,[_64,_3K,_t,_1Ts,_1Tp,function(_1W6,_){var _1W7=B(_1UF(_)),_1W8=rMV(_1W3),_1W9=E(E(_1W1).a),_1Wa=E(_1W8),_1Wb=E(_1Wa.a),_1Wc=E(_1Wa.b),_1Wd=E(_1Wa.h),_1We=E(_1Wa.s),_1Wf=E(_1Wa.u),_1Wg=B(_1H4(_1VY,_1W9.a,_1W9.b,_1W4,E(_1W6).a,_1Wb.a,_1Wb.b,_1Wb.c,_1Wb.d,_1Wb.e,_1Wb.f,_1Wb.g,_1Wb.h,_1Wb.i,_1Wb.j,_1Wb.k,_1Wc.a,_1Wc.b,_1Wa.c,_1Wa.d,_1Wa.e,_1Wa.f,_1Wa.g,_1Wd.a,_1Wd.b,_1Wa.i,_1Wa.j,_1Wa.k,_1Wa.l,_1Wa.m,_1Wa.n,_1Wa.o,_1Wa.p,_1Wa.q,_1Wa.r,_1We.a,_1We.b,_1Wa.t,_1Wf.a,_1Wf.b,_1Wf.c,_1Wf.d,_1Wf.e,_1Wf.f,_1Wf.g,_1Wf.h,_1Wa.v,_)),_=wMV(_1W3,_1Wg);return _kJ;},_])),_1Wh=B(A(_1Uc,[_64,_3K,_3J,_1VT,_1To,function(_1Wi,_){var _1Wj=E(E(_1Wi).a),_1Wk=rMV(_1W3),_1Wl=B(A(_1T2,[_1VY,_1W1,_1W4,_1Wj.a,_1Wj.b,_1Wk,_])),_=wMV(_1W3,_1Wl);return _kJ;},_])),_1Wm=B(A(_1Uc,[_64,_3K,_5j,_1VT,_1Tr,function(_1Wn,_){var _1Wo=E(_1Wn),_1Wp=rMV(_1W3),_1Wq=E(_1Wp);if(!E(E(_1Wq.u).e)){var _=wMV(_1W3,_1Wq);return _kJ;}else{var _1Wr=B(_1UF(_)),_=wMV(_1W3,_1Wq);return _kJ;}},_])),_1Ws=function(_){var _1Wt=rMV(_1W3),_=wMV(_1W3,new T(function(){var _1Wu=E(_1Wt),_1Wv=E(_1Wu.u);return {_:0,a:E(_1Wu.a),b:E(_1Wu.b),c:E(_1Wu.c),d:E(_1Wu.d),e:E(_1Wu.e),f:E(_1Wu.f),g:E(_1Wu.g),h:E(_1Wu.h),i:_1Wu.i,j:_1Wu.j,k:_1Wu.k,l:_1Wu.l,m:E(_1Wu.m),n:_1Wu.n,o:E(_1Wu.o),p:E(_1Wu.p),q:_1Wu.q,r:E(_1Wu.r),s:E(_1Wu.s),t:_1Wu.t,u:E({_:0,a:E(_1Wv.a),b:E(_1Wv.b),c:E(_1Wv.c),d:E(_1Wv.d),e:E(_AC),f:E(_1Wv.f),g:E(_1Wv.g),h:E(_1Wv.h)}),v:E(_1Wu.v)};}));return _kJ;},_1Ww=function(_1Wx,_){var _1Wy=E(_1Wx),_1Wz=rMV(_1W3),_=wMV(_1W3,new T(function(){var _1WA=E(_1Wz),_1WB=E(_1WA.u);return {_:0,a:E(_1WA.a),b:E(_1WA.b),c:E(_1WA.c),d:E(_1WA.d),e:E(_1WA.e),f:E(_1WA.f),g:E(_1WA.g),h:E(_1WA.h),i:_1WA.i,j:_1WA.j,k:_1WA.k,l:_1WA.l,m:E(_1WA.m),n:_1WA.n,o:E(_1WA.o),p:E(_1WA.p),q:_1WA.q,r:E(_1WA.r),s:E(_1WA.s),t:_1WA.t,u:E({_:0,a:E(_1WB.a),b:E(_1WB.b),c:E(_1WB.c),d:E(_1WB.d),e:E(_AD),f:E(_1WB.f),g:E(_1WB.g),h:E(_1WB.h)}),v:E(_1WA.v)};})),_1WC=B(A(_1Vm,[_64,_1TN,_1Ws,_]));return _kJ;},_1WD=B(A(_1Uc,[_64,_3K,_5j,_1VT,_1Tq,_1Ww,_])),_1WE=function(_){var _1WF=rMV(_1W3),_1WG=E(_1WF),_1WH=_1WG.a,_1WI=_1WG.b,_1WJ=_1WG.c,_1WK=_1WG.d,_1WL=_1WG.e,_1WM=_1WG.f,_1WN=_1WG.g,_1WO=_1WG.h,_1WP=_1WG.i,_1WQ=_1WG.j,_1WR=_1WG.k,_1WS=_1WG.l,_1WT=_1WG.m,_1WU=_1WG.n,_1WV=_1WG.o,_1WW=_1WG.p,_1WX=_1WG.q,_1WY=_1WG.r,_1WZ=_1WG.s,_1X0=_1WG.t,_1X1=_1WG.v,_1X2=E(_1WG.u),_1X3=new T(function(){if(_1X0<=298){return _1X0+1|0;}else{return E(_1Gm);}}),_1X4=new T(function(){var _1X5=function(_1X6){var _1X7=E(_1X6);return (_1X7==30)?{_:0,a:E(_1WH),b:E(_1WI),c:E(_1WJ),d:E(B(_x(B(_0(_Z,B(_1GZ(B(_aj(_1EM,_1WW)),B(_9T(_1WK)))))),new T(function(){return B(_aj(_1VK,_1WW));},1)))),e:E(_1WL),f:E(_1WM),g:E(_1WN),h:E(_1WO),i:_1WP,j:_1WQ,k:_1WR,l:_1WS,m:E(_1WT),n:_1WU,o:E(_1WV),p:E(_1WW),q:30,r:E(_1WY),s:E(_1WZ),t:E(_1X3),u:E(_1X2),v:E(_1X1)}:{_:0,a:E(_1WH),b:E(_1WI),c:E(_1WJ),d:E(_1WK),e:E(_1WL),f:E(_1WM),g:E(_1WN),h:E(_1WO),i:_1WP,j:_1WQ,k:_1WR,l:_1WS,m:E(_1WT),n:_1WU,o:E(_1WV),p:E(_1WW),q:_1X7,r:E(_1WY),s:E(_1WZ),t:E(_1X3),u:E(_1X2),v:E(_1X1)};};if(!E(_1WW)._){return B(_1X5(_1WX));}else{if(!B(_et(E(_1X3),20))){return B(_1X5(_1WX+1|0));}else{return B(_1X5(_1WX));}}});if(!E(_1X2.b)){if(!E(_1X2.h)){var _1X8=E(E(_1W1).a),_1X9=E(_1X4),_1Xa=E(_1X9.b),_1Xb=E(_1X9.h),_1Xc=E(_1X9.u),_1Xd=B(_12l(_1VY,_1X8.a,_1X8.b,_1X9.a,_1Xa.a,_1Xa.b,_1X9.c,_1X9.d,_1X9.e,_1X9.f,_1X9.g,_1Xb.a,_1Xb.b,_1X9.i,_1X9.j,_1X9.k,_1X9.l,_1X9.m,_1X9.n,_1X9.o,_1X9.p,_1X9.q,_1X9.r,_1X9.s,_1X9.t,_1Xc.a,_1Xc.b,_1Xc.c,_1Xc.d,_1Xc.e,_1Xc.f,_1Xc.g,_1Xc.h,_1X9.v,_)),_=wMV(_1W3,_1Xd);return _kJ;}else{if(!B(_et(E(_1X3),10))){if(!E(_1X2.c)){var _1Xe=E(E(_1W1).a),_1Xf=B(_1bq(_1VY.a,_1VZ,_1Xe.a,_1Xe.b,_1W4,_1X4,_)),_=wMV(_1W3,_1Xf);return _kJ;}else{var _1Xg=E(E(_1W1).a),_1Xh=E(_1X4),_1Xi=E(_1Xh.b),_1Xj=E(_1Xh.h),_1Xk=E(_1Xh.u),_1Xl=B(_12l(_1VY,_1Xg.a,_1Xg.b,_1Xh.a,_1Xi.a,_1Xi.b,_1Xh.c,_1Xh.d,_1Xh.e,_1Xh.f,_1Xh.g,_1Xj.a,_1Xj.b,_1Xh.i,_1Xh.j,_1Xh.k,_1Xh.l,_1Xh.m,_1Xh.n,_1Xh.o,_1Xh.p,_1Xh.q,_1Xh.r,_1Xh.s,_1Xh.t,_1Xk.a,_1Xk.b,_1Xk.c,_1Xk.d,_1Xk.e,_1Xk.f,_1Xk.g,_1Xk.h,_1Xh.v,_)),_=wMV(_1W3,_1Xl);return _kJ;}}else{var _1Xm=E(E(_1W1).a),_1Xn=E(_1X4),_1Xo=E(_1Xn.b),_1Xp=E(_1Xn.h),_1Xq=E(_1Xn.u),_1Xr=B(_12l(_1VY,_1Xm.a,_1Xm.b,_1Xn.a,_1Xo.a,_1Xo.b,_1Xn.c,_1Xn.d,_1Xn.e,_1Xn.f,_1Xn.g,_1Xp.a,_1Xp.b,_1Xn.i,_1Xn.j,_1Xn.k,_1Xn.l,_1Xn.m,_1Xn.n,_1Xn.o,_1Xn.p,_1Xn.q,_1Xn.r,_1Xn.s,_1Xn.t,_1Xq.a,_1Xq.b,_1Xq.c,_1Xq.d,_1Xq.e,_1Xq.f,_1Xq.g,_1Xq.h,_1Xn.v,_)),_=wMV(_1W3,_1Xr);return _kJ;}}}else{var _=wMV(_1W3,_1X4);return _kJ;}},_1Xs=B(A(_1Vm,[_64,_1TU,_1WE,_]));return _kJ;}}else{return new F(function(){return die(_1TQ);});}}else{return new F(function(){return die(_1TQ);});}},_1Xt=function(_){return new F(function(){return _1VP(_);});};
var hasteMain = function() {B(A(_1Xt, [0]));};window.onload = hasteMain;