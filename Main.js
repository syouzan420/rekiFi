"use strict";
var __haste_prog_id = '523e517cf45a412e230a04bbe72813767f9d2ccd2bdb1674712fc48142eaf751';
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

var _0=function(_1,_2){while(1){var _3=B((function(_4,_5){var _6=E(_5);if(!_6._){_1=new T2(1,new T2(0,_6.b,_6.c),new T(function(){return B(_0(_4,_6.e));}));_2=_6.d;return __continue;}else{return E(_4);}})(_1,_2));if(_3!=__continue){return _3;}}},_7="metaKey",_8="shiftKey",_9="altKey",_a="ctrlKey",_b="keyCode",_c=function(_d,_){var _e=__get(_d,E(_b)),_f=__get(_d,E(_a)),_g=__get(_d,E(_9)),_h=__get(_d,E(_8)),_i=__get(_d,E(_7));return new T(function(){var _j=Number(_e),_k=jsTrunc(_j);return new T5(0,_k,E(_f),E(_g),E(_h),E(_i));});},_l=function(_m,_n,_){return new F(function(){return _c(E(_n),_);});},_o="keydown",_p="keyup",_q="keypress",_r=function(_s){switch(E(_s)){case 0:return E(_q);case 1:return E(_p);default:return E(_o);}},_t=new T2(0,_r,_l),_u="deltaZ",_v="deltaY",_w="deltaX",_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return B(_x(_A.b,_z));}));},_B=function(_C,_D){var _E=jsShowI(_C);return new F(function(){return _x(fromJSStr(_E),_D);});},_F=41,_G=40,_H=function(_I,_J,_K){if(_J>=0){return new F(function(){return _B(_J,_K);});}else{if(_I<=6){return new F(function(){return _B(_J,_K);});}else{return new T2(1,_G,new T(function(){var _L=jsShowI(_J);return B(_x(fromJSStr(_L),new T2(1,_F,_K)));}));}}},_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(_H(0,2,_M));}),_O=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_N));}),_P=function(_Q){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_H(0,_Q,_O));}))));});},_R=function(_S,_){return new T(function(){var _T=Number(E(_S)),_U=jsTrunc(_T);if(_U<0){return B(_P(_U));}else{if(_U>2){return B(_P(_U));}else{return _U;}}});},_V=0,_W=new T3(0,_V,_V,_V),_X="button",_Y=new T(function(){return eval("jsGetMouseCoords");}),_Z=__Z,_10=function(_11,_){var _12=E(_11);if(!_12._){return _Z;}else{var _13=B(_10(_12.b,_));return new T2(1,new T(function(){var _14=Number(E(_12.a));return jsTrunc(_14);}),_13);}},_15=function(_16,_){var _17=__arr2lst(0,_16);return new F(function(){return _10(_17,_);});},_18=function(_19,_){return new F(function(){return _15(E(_19),_);});},_1a=function(_1b,_){return new T(function(){var _1c=Number(E(_1b));return jsTrunc(_1c);});},_1d=new T2(0,_1a,_18),_1e=function(_1f,_){var _1g=E(_1f);if(!_1g._){return _Z;}else{var _1h=B(_1e(_1g.b,_));return new T2(1,_1g.a,_1h);}},_1i=new T(function(){return B(unCStr("base"));}),_1j=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1k=new T(function(){return B(unCStr("IOException"));}),_1l=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1i,_1j,_1k),_1m=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1l,_Z,_Z),_1n=function(_1o){return E(_1m);},_1p=function(_1q){return E(E(_1q).a);},_1r=function(_1s,_1t,_1u){var _1v=B(A1(_1s,_)),_1w=B(A1(_1t,_)),_1x=hs_eqWord64(_1v.a,_1w.a);if(!_1x){return __Z;}else{var _1y=hs_eqWord64(_1v.b,_1w.b);return (!_1y)?__Z:new T1(1,_1u);}},_1z=function(_1A){var _1B=E(_1A);return new F(function(){return _1r(B(_1p(_1B.a)),_1n,_1B.b);});},_1C=new T(function(){return B(unCStr(": "));}),_1D=new T(function(){return B(unCStr(")"));}),_1E=new T(function(){return B(unCStr(" ("));}),_1F=new T(function(){return B(unCStr("interrupted"));}),_1G=new T(function(){return B(unCStr("system error"));}),_1H=new T(function(){return B(unCStr("unsatisified constraints"));}),_1I=new T(function(){return B(unCStr("user error"));}),_1J=new T(function(){return B(unCStr("permission denied"));}),_1K=new T(function(){return B(unCStr("illegal operation"));}),_1L=new T(function(){return B(unCStr("end of file"));}),_1M=new T(function(){return B(unCStr("resource exhausted"));}),_1N=new T(function(){return B(unCStr("resource busy"));}),_1O=new T(function(){return B(unCStr("does not exist"));}),_1P=new T(function(){return B(unCStr("already exists"));}),_1Q=new T(function(){return B(unCStr("resource vanished"));}),_1R=new T(function(){return B(unCStr("timeout"));}),_1S=new T(function(){return B(unCStr("unsupported operation"));}),_1T=new T(function(){return B(unCStr("hardware fault"));}),_1U=new T(function(){return B(unCStr("inappropriate type"));}),_1V=new T(function(){return B(unCStr("invalid argument"));}),_1W=new T(function(){return B(unCStr("failed"));}),_1X=new T(function(){return B(unCStr("protocol error"));}),_1Y=function(_1Z,_20){switch(E(_1Z)){case 0:return new F(function(){return _x(_1P,_20);});break;case 1:return new F(function(){return _x(_1O,_20);});break;case 2:return new F(function(){return _x(_1N,_20);});break;case 3:return new F(function(){return _x(_1M,_20);});break;case 4:return new F(function(){return _x(_1L,_20);});break;case 5:return new F(function(){return _x(_1K,_20);});break;case 6:return new F(function(){return _x(_1J,_20);});break;case 7:return new F(function(){return _x(_1I,_20);});break;case 8:return new F(function(){return _x(_1H,_20);});break;case 9:return new F(function(){return _x(_1G,_20);});break;case 10:return new F(function(){return _x(_1X,_20);});break;case 11:return new F(function(){return _x(_1W,_20);});break;case 12:return new F(function(){return _x(_1V,_20);});break;case 13:return new F(function(){return _x(_1U,_20);});break;case 14:return new F(function(){return _x(_1T,_20);});break;case 15:return new F(function(){return _x(_1S,_20);});break;case 16:return new F(function(){return _x(_1R,_20);});break;case 17:return new F(function(){return _x(_1Q,_20);});break;default:return new F(function(){return _x(_1F,_20);});}},_21=new T(function(){return B(unCStr("}"));}),_22=new T(function(){return B(unCStr("{handle: "));}),_23=function(_24,_25,_26,_27,_28,_29){var _2a=new T(function(){var _2b=new T(function(){var _2c=new T(function(){var _2d=E(_27);if(!_2d._){return E(_29);}else{var _2e=new T(function(){return B(_x(_2d,new T(function(){return B(_x(_1D,_29));},1)));},1);return B(_x(_1E,_2e));}},1);return B(_1Y(_25,_2c));}),_2f=E(_26);if(!_2f._){return E(_2b);}else{return B(_x(_2f,new T(function(){return B(_x(_1C,_2b));},1)));}}),_2g=E(_28);if(!_2g._){var _2h=E(_24);if(!_2h._){return E(_2a);}else{var _2i=E(_2h.a);if(!_2i._){var _2j=new T(function(){var _2k=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2k));},1);return new F(function(){return _x(_22,_2j);});}else{var _2l=new T(function(){var _2m=new T(function(){return B(_x(_21,new T(function(){return B(_x(_1C,_2a));},1)));},1);return B(_x(_2i.a,_2m));},1);return new F(function(){return _x(_22,_2l);});}}}else{return new F(function(){return _x(_2g.a,new T(function(){return B(_x(_1C,_2a));},1));});}},_2n=function(_2o){var _2p=E(_2o);return new F(function(){return _23(_2p.a,_2p.b,_2p.c,_2p.d,_2p.f,_Z);});},_2q=function(_2r,_2s,_2t){var _2u=E(_2s);return new F(function(){return _23(_2u.a,_2u.b,_2u.c,_2u.d,_2u.f,_2t);});},_2v=function(_2w,_2x){var _2y=E(_2w);return new F(function(){return _23(_2y.a,_2y.b,_2y.c,_2y.d,_2y.f,_2x);});},_2z=44,_2A=93,_2B=91,_2C=function(_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){return new F(function(){return unAppCStr("[]",_2F);});}else{var _2H=new T(function(){var _2I=new T(function(){var _2J=function(_2K){var _2L=E(_2K);if(!_2L._){return E(new T2(1,_2A,_2F));}else{var _2M=new T(function(){return B(A2(_2D,_2L.a,new T(function(){return B(_2J(_2L.b));})));});return new T2(1,_2z,_2M);}};return B(_2J(_2G.b));});return B(A2(_2D,_2G.a,_2I));});return new T2(1,_2B,_2H);}},_2N=function(_2O,_2P){return new F(function(){return _2C(_2v,_2O,_2P);});},_2Q=new T3(0,_2q,_2n,_2N),_2R=new T(function(){return new T5(0,_1n,_2Q,_2S,_1z,_2n);}),_2S=function(_2T){return new T2(0,_2R,_2T);},_2U=__Z,_2V=7,_2W=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_2X=new T6(0,_2U,_2V,_Z,_2W,_2U,_2U),_2Y=new T(function(){return B(_2S(_2X));}),_2Z=function(_){return new F(function(){return die(_2Y);});},_30=function(_31){return E(E(_31).a);},_32=function(_33,_34,_35,_){var _36=__arr2lst(0,_35),_37=B(_1e(_36,_)),_38=E(_37);if(!_38._){return new F(function(){return _2Z(_);});}else{var _39=E(_38.b);if(!_39._){return new F(function(){return _2Z(_);});}else{if(!E(_39.b)._){var _3a=B(A3(_30,_33,_38.a,_)),_3b=B(A3(_30,_34,_39.a,_));return new T2(0,_3a,_3b);}else{return new F(function(){return _2Z(_);});}}}},_3c=function(_){return new F(function(){return __jsNull();});},_3d=function(_3e){var _3f=B(A1(_3e,_));return E(_3f);},_3g=new T(function(){return B(_3d(_3c));}),_3h=new T(function(){return E(_3g);}),_3i=function(_3j,_3k,_){if(E(_3j)==7){var _3l=__app1(E(_Y),_3k),_3m=B(_32(_1d,_1d,_3l,_)),_3n=__get(_3k,E(_w)),_3o=__get(_3k,E(_v)),_3p=__get(_3k,E(_u));return new T(function(){return new T3(0,E(_3m),E(_2U),E(new T3(0,_3n,_3o,_3p)));});}else{var _3q=__app1(E(_Y),_3k),_3r=B(_32(_1d,_1d,_3q,_)),_3s=__get(_3k,E(_X)),_3t=__eq(_3s,E(_3h));if(!E(_3t)){var _3u=__isUndef(_3s);if(!E(_3u)){var _3v=B(_R(_3s,_));return new T(function(){return new T3(0,E(_3r),E(new T1(1,_3v)),E(_W));});}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}else{return new T(function(){return new T3(0,E(_3r),E(_2U),E(_W));});}}},_3w=function(_3x,_3y,_){return new F(function(){return _3i(_3x,E(_3y),_);});},_3z="mouseout",_3A="mouseover",_3B="mousemove",_3C="mouseup",_3D="mousedown",_3E="dblclick",_3F="click",_3G="wheel",_3H=function(_3I){switch(E(_3I)){case 0:return E(_3F);case 1:return E(_3E);case 2:return E(_3D);case 3:return E(_3C);case 4:return E(_3B);case 5:return E(_3A);case 6:return E(_3z);default:return E(_3G);}},_3J=new T2(0,_3H,_3w),_3K=function(_3L){return E(_3L);},_3M=function(_3N,_3O){return E(_3N)==E(_3O);},_3P=function(_3Q,_3R){return E(_3Q)!=E(_3R);},_3S=new T2(0,_3M,_3P),_3T="screenY",_3U="screenX",_3V="clientY",_3W="clientX",_3X="pageY",_3Y="pageX",_3Z="target",_40="identifier",_41=function(_42,_){var _43=__get(_42,E(_40)),_44=__get(_42,E(_3Z)),_45=__get(_42,E(_3Y)),_46=__get(_42,E(_3X)),_47=__get(_42,E(_3W)),_48=__get(_42,E(_3V)),_49=__get(_42,E(_3U)),_4a=__get(_42,E(_3T));return new T(function(){var _4b=Number(_43),_4c=jsTrunc(_4b);return new T5(0,_4c,_44,E(new T2(0,new T(function(){var _4d=Number(_45);return jsTrunc(_4d);}),new T(function(){var _4e=Number(_46);return jsTrunc(_4e);}))),E(new T2(0,new T(function(){var _4f=Number(_47);return jsTrunc(_4f);}),new T(function(){var _4g=Number(_48);return jsTrunc(_4g);}))),E(new T2(0,new T(function(){var _4h=Number(_49);return jsTrunc(_4h);}),new T(function(){var _4i=Number(_4a);return jsTrunc(_4i);}))));});},_4j=function(_4k,_){var _4l=E(_4k);if(!_4l._){return _Z;}else{var _4m=B(_41(E(_4l.a),_)),_4n=B(_4j(_4l.b,_));return new T2(1,_4m,_4n);}},_4o="touches",_4p=function(_4q){return E(E(_4q).b);},_4r=function(_4s,_4t,_){var _4u=__arr2lst(0,_4t),_4v=new T(function(){return B(_4p(_4s));}),_4w=function(_4x,_){var _4y=E(_4x);if(!_4y._){return _Z;}else{var _4z=B(A2(_4v,_4y.a,_)),_4A=B(_4w(_4y.b,_));return new T2(1,_4z,_4A);}};return new F(function(){return _4w(_4u,_);});},_4B=function(_4C,_){return new F(function(){return _4r(_1d,E(_4C),_);});},_4D=new T2(0,_18,_4B),_4E=new T(function(){return eval("(function(e) {  var len = e.changedTouches.length;  var chts = new Array(len);  for(var i = 0; i < len; ++i) {chts[i] = e.changedTouches[i].identifier;}  var len = e.targetTouches.length;  var tts = new Array(len);  for(var i = 0; i < len; ++i) {tts[i] = e.targetTouches[i].identifier;}  return [chts, tts];})");}),_4F=function(_4G){return E(E(_4G).a);},_4H=function(_4I,_4J,_4K){while(1){var _4L=E(_4K);if(!_4L._){return false;}else{if(!B(A3(_4F,_4I,_4J,_4L.a))){_4K=_4L.b;continue;}else{return true;}}}},_4M=function(_4N,_4O){while(1){var _4P=B((function(_4Q,_4R){var _4S=E(_4R);if(!_4S._){return __Z;}else{var _4T=_4S.a,_4U=_4S.b;if(!B(A1(_4Q,_4T))){var _4V=_4Q;_4N=_4V;_4O=_4U;return __continue;}else{return new T2(1,_4T,new T(function(){return B(_4M(_4Q,_4U));}));}}})(_4N,_4O));if(_4P!=__continue){return _4P;}}},_4W=function(_4X,_){var _4Y=__get(_4X,E(_4o)),_4Z=__arr2lst(0,_4Y),_50=B(_4j(_4Z,_)),_51=__app1(E(_4E),_4X),_52=B(_32(_4D,_4D,_51,_)),_53=E(_52),_54=new T(function(){var _55=function(_56){return new F(function(){return _4H(_3S,new T(function(){return E(_56).a;}),_53.a);});};return B(_4M(_55,_50));}),_57=new T(function(){var _58=function(_59){return new F(function(){return _4H(_3S,new T(function(){return E(_59).a;}),_53.b);});};return B(_4M(_58,_50));});return new T3(0,_50,_57,_54);},_5a=function(_5b,_5c,_){return new F(function(){return _4W(E(_5c),_);});},_5d="touchcancel",_5e="touchend",_5f="touchmove",_5g="touchstart",_5h=function(_5i){switch(E(_5i)){case 0:return E(_5g);case 1:return E(_5f);case 2:return E(_5e);default:return E(_5d);}},_5j=new T2(0,_5h,_5a),_5k=function(_5l,_5m,_){var _5n=B(A1(_5l,_)),_5o=B(A1(_5m,_));return _5n;},_5p=function(_5q,_5r,_){var _5s=B(A1(_5q,_)),_5t=B(A1(_5r,_));return new T(function(){return B(A1(_5s,_5t));});},_5u=function(_5v,_5w,_){var _5x=B(A1(_5w,_));return _5v;},_5y=function(_5z,_5A,_){var _5B=B(A1(_5A,_));return new T(function(){return B(A1(_5z,_5B));});},_5C=new T2(0,_5y,_5u),_5D=function(_5E,_){return _5E;},_5F=function(_5G,_5H,_){var _5I=B(A1(_5G,_));return new F(function(){return A1(_5H,_);});},_5J=new T5(0,_5C,_5D,_5p,_5F,_5k),_5K=new T(function(){return E(_2R);}),_5L=function(_5M){return E(E(_5M).c);},_5N=function(_5O){return new T6(0,_2U,_2V,_Z,_5O,_2U,_2U);},_5P=function(_5Q,_){var _5R=new T(function(){return B(A2(_5L,_5K,new T(function(){return B(A1(_5N,_5Q));})));});return new F(function(){return die(_5R);});},_5S=function(_5T,_){return new F(function(){return _5P(_5T,_);});},_5U=function(_5V){return new F(function(){return A1(_5S,_5V);});},_5W=function(_5X,_5Y,_){var _5Z=B(A1(_5X,_));return new F(function(){return A2(_5Y,_5Z,_);});},_60=new T5(0,_5J,_5W,_5F,_5D,_5U),_61=function(_62){return E(_62);},_63=new T2(0,_60,_61),_64=new T2(0,_63,_5D),_65=function(_66,_67){while(1){var _68=E(_66);if(!_68._){return (E(_67)._==0)?1:0;}else{var _69=E(_67);if(!_69._){return 2;}else{var _6a=E(_68.a),_6b=E(_69.a);if(_6a!=_6b){return (_6a>_6b)?2:0;}else{_66=_68.b;_67=_69.b;continue;}}}}},_6c=new T0(1),_6d=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_6e=function(_6f){return new F(function(){return err(_6d);});},_6g=new T(function(){return B(_6e(_));}),_6h=function(_6i,_6j,_6k,_6l){var _6m=E(_6k);if(!_6m._){var _6n=_6m.a,_6o=E(_6l);if(!_6o._){var _6p=_6o.a,_6q=_6o.b,_6r=_6o.c;if(_6p<=(imul(3,_6n)|0)){return new T5(0,(1+_6n|0)+_6p|0,E(_6i),_6j,E(_6m),E(_6o));}else{var _6s=E(_6o.d);if(!_6s._){var _6t=_6s.a,_6u=_6s.b,_6v=_6s.c,_6w=_6s.d,_6x=E(_6o.e);if(!_6x._){var _6y=_6x.a;if(_6t>=(imul(2,_6y)|0)){var _6z=function(_6A){var _6B=E(_6i),_6C=E(_6s.e);return (_6C._==0)?new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,(1+_6y|0)+_6C.a|0,E(_6q),_6r,E(_6C),E(_6x)))):new T5(0,(1+_6n|0)+_6p|0,E(_6u),_6v,E(new T5(0,(1+_6n|0)+_6A|0,E(_6B),_6j,E(_6m),E(_6w))),E(new T5(0,1+_6y|0,E(_6q),_6r,E(_6c),E(_6x))));},_6D=E(_6w);if(!_6D._){return new F(function(){return _6z(_6D.a);});}else{return new F(function(){return _6z(0);});}}else{return new T5(0,(1+_6n|0)+_6p|0,E(_6q),_6r,E(new T5(0,(1+_6n|0)+_6t|0,E(_6i),_6j,E(_6m),E(_6s))),E(_6x));}}else{return E(_6g);}}else{return E(_6g);}}}else{return new T5(0,1+_6n|0,E(_6i),_6j,E(_6m),E(_6c));}}else{var _6E=E(_6l);if(!_6E._){var _6F=_6E.a,_6G=_6E.b,_6H=_6E.c,_6I=_6E.e,_6J=E(_6E.d);if(!_6J._){var _6K=_6J.a,_6L=_6J.b,_6M=_6J.c,_6N=_6J.d,_6O=E(_6I);if(!_6O._){var _6P=_6O.a;if(_6K>=(imul(2,_6P)|0)){var _6Q=function(_6R){var _6S=E(_6i),_6T=E(_6J.e);return (_6T._==0)?new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,(1+_6P|0)+_6T.a|0,E(_6G),_6H,E(_6T),E(_6O)))):new T5(0,1+_6F|0,E(_6L),_6M,E(new T5(0,1+_6R|0,E(_6S),_6j,E(_6c),E(_6N))),E(new T5(0,1+_6P|0,E(_6G),_6H,E(_6c),E(_6O))));},_6U=E(_6N);if(!_6U._){return new F(function(){return _6Q(_6U.a);});}else{return new F(function(){return _6Q(0);});}}else{return new T5(0,1+_6F|0,E(_6G),_6H,E(new T5(0,1+_6K|0,E(_6i),_6j,E(_6c),E(_6J))),E(_6O));}}else{return new T5(0,3,E(_6L),_6M,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(new T5(0,1,E(_6G),_6H,E(_6c),E(_6c))));}}else{var _6V=E(_6I);return (_6V._==0)?new T5(0,3,E(_6G),_6H,E(new T5(0,1,E(_6i),_6j,E(_6c),E(_6c))),E(_6V)):new T5(0,2,E(_6i),_6j,E(_6c),E(_6E));}}else{return new T5(0,1,E(_6i),_6j,E(_6c),E(_6c));}}},_6W=function(_6X,_6Y){return new T5(0,1,E(_6X),_6Y,E(_6c),E(_6c));},_6Z=function(_70,_71,_72){var _73=E(_72);if(!_73._){return new F(function(){return _6h(_73.b,_73.c,_73.d,B(_6Z(_70,_71,_73.e)));});}else{return new F(function(){return _6W(_70,_71);});}},_74=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_75=function(_76){return new F(function(){return err(_74);});},_77=new T(function(){return B(_75(_));}),_78=function(_79,_7a,_7b,_7c){var _7d=E(_7c);if(!_7d._){var _7e=_7d.a,_7f=E(_7b);if(!_7f._){var _7g=_7f.a,_7h=_7f.b,_7i=_7f.c;if(_7g<=(imul(3,_7e)|0)){return new T5(0,(1+_7g|0)+_7e|0,E(_79),_7a,E(_7f),E(_7d));}else{var _7j=E(_7f.d);if(!_7j._){var _7k=_7j.a,_7l=E(_7f.e);if(!_7l._){var _7m=_7l.a,_7n=_7l.b,_7o=_7l.c,_7p=_7l.d;if(_7m>=(imul(2,_7k)|0)){var _7q=function(_7r){var _7s=E(_7l.e);return (_7s._==0)?new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,(1+_7e|0)+_7s.a|0,E(_79),_7a,E(_7s),E(_7d)))):new T5(0,(1+_7g|0)+_7e|0,E(_7n),_7o,E(new T5(0,(1+_7k|0)+_7r|0,E(_7h),_7i,E(_7j),E(_7p))),E(new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d))));},_7t=E(_7p);if(!_7t._){return new F(function(){return _7q(_7t.a);});}else{return new F(function(){return _7q(0);});}}else{return new T5(0,(1+_7g|0)+_7e|0,E(_7h),_7i,E(_7j),E(new T5(0,(1+_7e|0)+_7m|0,E(_79),_7a,E(_7l),E(_7d))));}}else{return E(_77);}}else{return E(_77);}}}else{return new T5(0,1+_7e|0,E(_79),_7a,E(_6c),E(_7d));}}else{var _7u=E(_7b);if(!_7u._){var _7v=_7u.a,_7w=_7u.b,_7x=_7u.c,_7y=_7u.e,_7z=E(_7u.d);if(!_7z._){var _7A=_7z.a,_7B=E(_7y);if(!_7B._){var _7C=_7B.a,_7D=_7B.b,_7E=_7B.c,_7F=_7B.d;if(_7C>=(imul(2,_7A)|0)){var _7G=function(_7H){var _7I=E(_7B.e);return (_7I._==0)?new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1+_7I.a|0,E(_79),_7a,E(_7I),E(_6c)))):new T5(0,1+_7v|0,E(_7D),_7E,E(new T5(0,(1+_7A|0)+_7H|0,E(_7w),_7x,E(_7z),E(_7F))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));},_7J=E(_7F);if(!_7J._){return new F(function(){return _7G(_7J.a);});}else{return new F(function(){return _7G(0);});}}else{return new T5(0,1+_7v|0,E(_7w),_7x,E(_7z),E(new T5(0,1+_7C|0,E(_79),_7a,E(_7B),E(_6c))));}}else{return new T5(0,3,E(_7w),_7x,E(_7z),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c))));}}else{var _7K=E(_7y);return (_7K._==0)?new T5(0,3,E(_7K.b),_7K.c,E(new T5(0,1,E(_7w),_7x,E(_6c),E(_6c))),E(new T5(0,1,E(_79),_7a,E(_6c),E(_6c)))):new T5(0,2,E(_79),_7a,E(_7u),E(_6c));}}else{return new T5(0,1,E(_79),_7a,E(_6c),E(_6c));}}},_7L=function(_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _78(_7P.b,_7P.c,B(_7L(_7M,_7N,_7P.d)),_7P.e);});}else{return new F(function(){return _6W(_7M,_7N);});}},_7Q=function(_7R,_7S,_7T,_7U,_7V,_7W,_7X){return new F(function(){return _78(_7U,_7V,B(_7L(_7R,_7S,_7W)),_7X);});},_7Y=function(_7Z,_80,_81,_82,_83,_84,_85,_86){var _87=E(_81);if(!_87._){var _88=_87.a,_89=_87.b,_8a=_87.c,_8b=_87.d,_8c=_87.e;if((imul(3,_88)|0)>=_82){if((imul(3,_82)|0)>=_88){return new T5(0,(_88+_82|0)+1|0,E(_7Z),_80,E(_87),E(new T5(0,_82,E(_83),_84,E(_85),E(_86))));}else{return new F(function(){return _6h(_89,_8a,_8b,B(_7Y(_7Z,_80,_8c,_82,_83,_84,_85,_86)));});}}else{return new F(function(){return _78(_83,_84,B(_8d(_7Z,_80,_88,_89,_8a,_8b,_8c,_85)),_86);});}}else{return new F(function(){return _7Q(_7Z,_80,_82,_83,_84,_85,_86);});}},_8d=function(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l){var _8m=E(_8l);if(!_8m._){var _8n=_8m.a,_8o=_8m.b,_8p=_8m.c,_8q=_8m.d,_8r=_8m.e;if((imul(3,_8g)|0)>=_8n){if((imul(3,_8n)|0)>=_8g){return new T5(0,(_8g+_8n|0)+1|0,E(_8e),_8f,E(new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k))),E(_8m));}else{return new F(function(){return _6h(_8h,_8i,_8j,B(_7Y(_8e,_8f,_8k,_8n,_8o,_8p,_8q,_8r)));});}}else{return new F(function(){return _78(_8o,_8p,B(_8d(_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8q)),_8r);});}}else{return new F(function(){return _6Z(_8e,_8f,new T5(0,_8g,E(_8h),_8i,E(_8j),E(_8k)));});}},_8s=function(_8t,_8u,_8v,_8w){var _8x=E(_8v);if(!_8x._){var _8y=_8x.a,_8z=_8x.b,_8A=_8x.c,_8B=_8x.d,_8C=_8x.e,_8D=E(_8w);if(!_8D._){var _8E=_8D.a,_8F=_8D.b,_8G=_8D.c,_8H=_8D.d,_8I=_8D.e;if((imul(3,_8y)|0)>=_8E){if((imul(3,_8E)|0)>=_8y){return new T5(0,(_8y+_8E|0)+1|0,E(_8t),_8u,E(_8x),E(_8D));}else{return new F(function(){return _6h(_8z,_8A,_8B,B(_7Y(_8t,_8u,_8C,_8E,_8F,_8G,_8H,_8I)));});}}else{return new F(function(){return _78(_8F,_8G,B(_8d(_8t,_8u,_8y,_8z,_8A,_8B,_8C,_8H)),_8I);});}}else{return new F(function(){return _6Z(_8t,_8u,_8x);});}}else{return new F(function(){return _7L(_8t,_8u,_8w);});}},_8J=function(_8K,_8L,_8M,_8N){var _8O=E(_8K);if(_8O==1){var _8P=E(_8N);return (_8P._==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_Z):(B(_65(_8L,E(_8P.a).a))==0)?new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_8P,_Z):new T3(0,new T(function(){return new T5(0,1,E(_8L),_8M,E(_6c),E(_6c));}),_Z,_8P);}else{var _8Q=B(_8J(_8O>>1,_8L,_8M,_8N)),_8R=_8Q.a,_8S=_8Q.c,_8T=E(_8Q.b);if(!_8T._){return new T3(0,_8R,_Z,_8S);}else{var _8U=E(_8T.a),_8V=_8U.a,_8W=_8U.b,_8X=E(_8T.b);if(!_8X._){return new T3(0,new T(function(){return B(_6Z(_8V,_8W,_8R));}),_Z,_8S);}else{var _8Y=E(_8X.a),_8Z=_8Y.a;if(!B(_65(_8V,_8Z))){var _90=B(_8J(_8O>>1,_8Z,_8Y.b,_8X.b));return new T3(0,new T(function(){return B(_8s(_8V,_8W,_8R,_90.a));}),_90.b,_90.c);}else{return new T3(0,_8R,_Z,_8T);}}}}},_91=function(_92,_93,_94){var _95=E(_92),_96=E(_94);if(!_96._){var _97=_96.b,_98=_96.c,_99=_96.d,_9a=_96.e;switch(B(_65(_95,_97))){case 0:return new F(function(){return _78(_97,_98,B(_91(_95,_93,_99)),_9a);});break;case 1:return new T5(0,_96.a,E(_95),_93,E(_99),E(_9a));default:return new F(function(){return _6h(_97,_98,_99,B(_91(_95,_93,_9a)));});}}else{return new T5(0,1,E(_95),_93,E(_6c),E(_6c));}},_9b=function(_9c,_9d){while(1){var _9e=E(_9d);if(!_9e._){return E(_9c);}else{var _9f=E(_9e.a),_9g=B(_91(_9f.a,_9f.b,_9c));_9c=_9g;_9d=_9e.b;continue;}}},_9h=function(_9i,_9j,_9k,_9l){return new F(function(){return _9b(B(_91(_9j,_9k,_9i)),_9l);});},_9m=function(_9n,_9o,_9p){var _9q=E(_9o);return new F(function(){return _9b(B(_91(_9q.a,_9q.b,_9n)),_9p);});},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v._){return E(_9t);}else{var _9w=E(_9v.a),_9x=_9w.a,_9y=_9w.b,_9z=E(_9v.b);if(!_9z._){return new F(function(){return _6Z(_9x,_9y,_9t);});}else{var _9A=E(_9z.a),_9B=_9A.a;if(!B(_65(_9x,_9B))){var _9C=B(_8J(_9s,_9B,_9A.b,_9z.b)),_9D=_9C.a,_9E=E(_9C.c);if(!_9E._){var _9F=_9s<<1,_9G=B(_8s(_9x,_9y,_9t,_9D));_9s=_9F;_9t=_9G;_9u=_9C.b;continue;}else{return new F(function(){return _9m(B(_8s(_9x,_9y,_9t,_9D)),_9E.a,_9E.b);});}}else{return new F(function(){return _9h(_9t,_9x,_9y,_9z);});}}}}},_9H=function(_9I,_9J,_9K,_9L,_9M){var _9N=E(_9M);if(!_9N._){return new F(function(){return _6Z(_9K,_9L,_9J);});}else{var _9O=E(_9N.a),_9P=_9O.a;if(!B(_65(_9K,_9P))){var _9Q=B(_8J(_9I,_9P,_9O.b,_9N.b)),_9R=_9Q.a,_9S=E(_9Q.c);if(!_9S._){return new F(function(){return _9r(_9I<<1,B(_8s(_9K,_9L,_9J,_9R)),_9Q.b);});}else{return new F(function(){return _9m(B(_8s(_9K,_9L,_9J,_9R)),_9S.a,_9S.b);});}}else{return new F(function(){return _9h(_9J,_9K,_9L,_9N);});}}},_9T=function(_9U){var _9V=E(_9U);if(!_9V._){return new T0(1);}else{var _9W=E(_9V.a),_9X=_9W.a,_9Y=_9W.b,_9Z=E(_9V.b);if(!_9Z._){return new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c));}else{var _a0=_9Z.b,_a1=E(_9Z.a),_a2=_a1.a,_a3=_a1.b;if(!B(_65(_9X,_a2))){return new F(function(){return _9H(1,new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}else{return new F(function(){return _9h(new T5(0,1,E(_9X),_9Y,E(_6c),E(_6c)),_a2,_a3,_a0);});}}}},_a4=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().height})");}),_a5=new T(function(){return eval("(function(cv){return cv.getBoundingClientRect().width})");}),_a6=new T(function(){return eval("(function(cv){return cv.height})");}),_a7=new T(function(){return eval("(function(cv){return cv.width})");}),_a8=function(_a9,_){var _aa=__app1(E(_a7),_a9),_ab=__app1(E(_a6),_a9),_ac=__app1(E(_a5),_a9),_ad=__app1(E(_a4),_a9);return new T2(0,new T2(0,_aa,_ab),new T2(0,_ac,_ad));},_ae=function(_af,_ag){while(1){var _ah=E(_af);if(!_ah._){return (E(_ag)._==0)?true:false;}else{var _ai=E(_ag);if(!_ai._){return false;}else{if(E(_ah.a)!=E(_ai.a)){return false;}else{_af=_ah.b;_ag=_ai.b;continue;}}}}},_aj=function(_ak,_al){var _am=E(_al);return (_am._==0)?__Z:new T2(1,new T(function(){return B(A1(_ak,_am.a));}),new T(function(){return B(_aj(_ak,_am.b));}));},_an=function(_ao){return new T1(3,E(B(_aj(_61,_ao))));},_ap="Tried to deserialie a non-array to a list!",_aq=new T1(0,_ap),_ar=new T1(1,_Z),_as=function(_at){var _au=E(_at);if(!_au._){return E(_ar);}else{var _av=B(_as(_au.b));return (_av._==0)?new T1(0,_av.a):new T1(1,new T2(1,_au.a,_av.a));}},_aw=function(_ax){var _ay=E(_ax);if(_ay._==3){return new F(function(){return _as(_ay.a);});}else{return E(_aq);}},_az=function(_aA){return new T1(1,_aA);},_aB=new T4(0,_61,_an,_az,_aw),_aC=function(_aD,_aE,_aF){return new F(function(){return A1(_aD,new T2(1,_2z,new T(function(){return B(A1(_aE,_aF));})));});},_aG=function(_aH){return new F(function(){return _H(0,E(_aH),_Z);});},_aI=34,_aJ=new T2(1,_aI,_Z),_aK=new T(function(){return B(unCStr("!!: negative index"));}),_aL=new T(function(){return B(unCStr("Prelude."));}),_aM=new T(function(){return B(_x(_aL,_aK));}),_aN=new T(function(){return B(err(_aM));}),_aO=new T(function(){return B(unCStr("!!: index too large"));}),_aP=new T(function(){return B(_x(_aL,_aO));}),_aQ=new T(function(){return B(err(_aP));}),_aR=function(_aS,_aT){while(1){var _aU=E(_aS);if(!_aU._){return E(_aQ);}else{var _aV=E(_aT);if(!_aV){return E(_aU.a);}else{_aS=_aU.b;_aT=_aV-1|0;continue;}}}},_aW=function(_aX,_aY){if(_aY>=0){return new F(function(){return _aR(_aX,_aY);});}else{return E(_aN);}},_aZ=new T(function(){return B(unCStr("ACK"));}),_b0=new T(function(){return B(unCStr("BEL"));}),_b1=new T(function(){return B(unCStr("BS"));}),_b2=new T(function(){return B(unCStr("SP"));}),_b3=new T2(1,_b2,_Z),_b4=new T(function(){return B(unCStr("US"));}),_b5=new T2(1,_b4,_b3),_b6=new T(function(){return B(unCStr("RS"));}),_b7=new T2(1,_b6,_b5),_b8=new T(function(){return B(unCStr("GS"));}),_b9=new T2(1,_b8,_b7),_ba=new T(function(){return B(unCStr("FS"));}),_bb=new T2(1,_ba,_b9),_bc=new T(function(){return B(unCStr("ESC"));}),_bd=new T2(1,_bc,_bb),_be=new T(function(){return B(unCStr("SUB"));}),_bf=new T2(1,_be,_bd),_bg=new T(function(){return B(unCStr("EM"));}),_bh=new T2(1,_bg,_bf),_bi=new T(function(){return B(unCStr("CAN"));}),_bj=new T2(1,_bi,_bh),_bk=new T(function(){return B(unCStr("ETB"));}),_bl=new T2(1,_bk,_bj),_bm=new T(function(){return B(unCStr("SYN"));}),_bn=new T2(1,_bm,_bl),_bo=new T(function(){return B(unCStr("NAK"));}),_bp=new T2(1,_bo,_bn),_bq=new T(function(){return B(unCStr("DC4"));}),_br=new T2(1,_bq,_bp),_bs=new T(function(){return B(unCStr("DC3"));}),_bt=new T2(1,_bs,_br),_bu=new T(function(){return B(unCStr("DC2"));}),_bv=new T2(1,_bu,_bt),_bw=new T(function(){return B(unCStr("DC1"));}),_bx=new T2(1,_bw,_bv),_by=new T(function(){return B(unCStr("DLE"));}),_bz=new T2(1,_by,_bx),_bA=new T(function(){return B(unCStr("SI"));}),_bB=new T2(1,_bA,_bz),_bC=new T(function(){return B(unCStr("SO"));}),_bD=new T2(1,_bC,_bB),_bE=new T(function(){return B(unCStr("CR"));}),_bF=new T2(1,_bE,_bD),_bG=new T(function(){return B(unCStr("FF"));}),_bH=new T2(1,_bG,_bF),_bI=new T(function(){return B(unCStr("VT"));}),_bJ=new T2(1,_bI,_bH),_bK=new T(function(){return B(unCStr("LF"));}),_bL=new T2(1,_bK,_bJ),_bM=new T(function(){return B(unCStr("HT"));}),_bN=new T2(1,_bM,_bL),_bO=new T2(1,_b1,_bN),_bP=new T2(1,_b0,_bO),_bQ=new T2(1,_aZ,_bP),_bR=new T(function(){return B(unCStr("ENQ"));}),_bS=new T2(1,_bR,_bQ),_bT=new T(function(){return B(unCStr("EOT"));}),_bU=new T2(1,_bT,_bS),_bV=new T(function(){return B(unCStr("ETX"));}),_bW=new T2(1,_bV,_bU),_bX=new T(function(){return B(unCStr("STX"));}),_bY=new T2(1,_bX,_bW),_bZ=new T(function(){return B(unCStr("SOH"));}),_c0=new T2(1,_bZ,_bY),_c1=new T(function(){return B(unCStr("NUL"));}),_c2=new T2(1,_c1,_c0),_c3=92,_c4=new T(function(){return B(unCStr("\\DEL"));}),_c5=new T(function(){return B(unCStr("\\a"));}),_c6=new T(function(){return B(unCStr("\\\\"));}),_c7=new T(function(){return B(unCStr("\\SO"));}),_c8=new T(function(){return B(unCStr("\\r"));}),_c9=new T(function(){return B(unCStr("\\f"));}),_ca=new T(function(){return B(unCStr("\\v"));}),_cb=new T(function(){return B(unCStr("\\n"));}),_cc=new T(function(){return B(unCStr("\\t"));}),_cd=new T(function(){return B(unCStr("\\b"));}),_ce=function(_cf,_cg){if(_cf<=127){var _ch=E(_cf);switch(_ch){case 92:return new F(function(){return _x(_c6,_cg);});break;case 127:return new F(function(){return _x(_c4,_cg);});break;default:if(_ch<32){var _ci=E(_ch);switch(_ci){case 7:return new F(function(){return _x(_c5,_cg);});break;case 8:return new F(function(){return _x(_cd,_cg);});break;case 9:return new F(function(){return _x(_cc,_cg);});break;case 10:return new F(function(){return _x(_cb,_cg);});break;case 11:return new F(function(){return _x(_ca,_cg);});break;case 12:return new F(function(){return _x(_c9,_cg);});break;case 13:return new F(function(){return _x(_c8,_cg);});break;case 14:return new F(function(){return _x(_c7,new T(function(){var _cj=E(_cg);if(!_cj._){return __Z;}else{if(E(_cj.a)==72){return B(unAppCStr("\\&",_cj));}else{return E(_cj);}}},1));});break;default:return new F(function(){return _x(new T2(1,_c3,new T(function(){return B(_aW(_c2,_ci));})),_cg);});}}else{return new T2(1,_ch,_cg);}}}else{var _ck=new T(function(){var _cl=jsShowI(_cf);return B(_x(fromJSStr(_cl),new T(function(){var _cm=E(_cg);if(!_cm._){return __Z;}else{var _cn=E(_cm.a);if(_cn<48){return E(_cm);}else{if(_cn>57){return E(_cm);}else{return B(unAppCStr("\\&",_cm));}}}},1)));});return new T2(1,_c3,_ck);}},_co=new T(function(){return B(unCStr("\\\""));}),_cp=function(_cq,_cr){var _cs=E(_cq);if(!_cs._){return E(_cr);}else{var _ct=_cs.b,_cu=E(_cs.a);if(_cu==34){return new F(function(){return _x(_co,new T(function(){return B(_cp(_ct,_cr));},1));});}else{return new F(function(){return _ce(_cu,new T(function(){return B(_cp(_ct,_cr));}));});}}},_cv=function(_cw){return new T2(1,_aI,new T(function(){return B(_cp(_cw,_aJ));}));},_cx=function(_cy,_cz){if(_cy<=_cz){var _cA=function(_cB){return new T2(1,_cB,new T(function(){if(_cB!=_cz){return B(_cA(_cB+1|0));}else{return __Z;}}));};return new F(function(){return _cA(_cy);});}else{return __Z;}},_cC=function(_cD){return new F(function(){return _cx(E(_cD),2147483647);});},_cE=function(_cF,_cG,_cH){if(_cH<=_cG){var _cI=new T(function(){var _cJ=_cG-_cF|0,_cK=function(_cL){return (_cL>=(_cH-_cJ|0))?new T2(1,_cL,new T(function(){return B(_cK(_cL+_cJ|0));})):new T2(1,_cL,_Z);};return B(_cK(_cG));});return new T2(1,_cF,_cI);}else{return (_cH<=_cF)?new T2(1,_cF,_Z):__Z;}},_cM=function(_cN,_cO,_cP){if(_cP>=_cO){var _cQ=new T(function(){var _cR=_cO-_cN|0,_cS=function(_cT){return (_cT<=(_cP-_cR|0))?new T2(1,_cT,new T(function(){return B(_cS(_cT+_cR|0));})):new T2(1,_cT,_Z);};return B(_cS(_cO));});return new T2(1,_cN,_cQ);}else{return (_cP>=_cN)?new T2(1,_cN,_Z):__Z;}},_cU=function(_cV,_cW){if(_cW<_cV){return new F(function(){return _cE(_cV,_cW, -2147483648);});}else{return new F(function(){return _cM(_cV,_cW,2147483647);});}},_cX=function(_cY,_cZ){return new F(function(){return _cU(E(_cY),E(_cZ));});},_d0=function(_d1,_d2,_d3){if(_d2<_d1){return new F(function(){return _cE(_d1,_d2,_d3);});}else{return new F(function(){return _cM(_d1,_d2,_d3);});}},_d4=function(_d5,_d6,_d7){return new F(function(){return _d0(E(_d5),E(_d6),E(_d7));});},_d8=function(_d9,_da){return new F(function(){return _cx(E(_d9),E(_da));});},_db=function(_dc){return E(_dc);},_dd=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_de=new T(function(){return B(err(_dd));}),_df=function(_dg){var _dh=E(_dg);return (_dh==( -2147483648))?E(_de):_dh-1|0;},_di=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_dj=new T(function(){return B(err(_di));}),_dk=function(_dl){var _dm=E(_dl);return (_dm==2147483647)?E(_dj):_dm+1|0;},_dn={_:0,a:_dk,b:_df,c:_db,d:_db,e:_cC,f:_cX,g:_d8,h:_d4},_do=function(_dp,_dq){if(_dp<=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{if(_dq>=0){if(_dp>=0){return new F(function(){return quot(_dp,_dq);});}else{if(_dq<=0){return new F(function(){return quot(_dp,_dq);});}else{return quot(_dp+1|0,_dq)-1|0;}}}else{return quot(_dp-1|0,_dq)-1|0;}}},_dr=new T(function(){return B(unCStr("base"));}),_ds=new T(function(){return B(unCStr("GHC.Exception"));}),_dt=new T(function(){return B(unCStr("ArithException"));}),_du=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_dr,_ds,_dt),_dv=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_du,_Z,_Z),_dw=function(_dx){return E(_dv);},_dy=function(_dz){var _dA=E(_dz);return new F(function(){return _1r(B(_1p(_dA.a)),_dw,_dA.b);});},_dB=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_dC=new T(function(){return B(unCStr("denormal"));}),_dD=new T(function(){return B(unCStr("divide by zero"));}),_dE=new T(function(){return B(unCStr("loss of precision"));}),_dF=new T(function(){return B(unCStr("arithmetic underflow"));}),_dG=new T(function(){return B(unCStr("arithmetic overflow"));}),_dH=function(_dI,_dJ){switch(E(_dI)){case 0:return new F(function(){return _x(_dG,_dJ);});break;case 1:return new F(function(){return _x(_dF,_dJ);});break;case 2:return new F(function(){return _x(_dE,_dJ);});break;case 3:return new F(function(){return _x(_dD,_dJ);});break;case 4:return new F(function(){return _x(_dC,_dJ);});break;default:return new F(function(){return _x(_dB,_dJ);});}},_dK=function(_dL){return new F(function(){return _dH(_dL,_Z);});},_dM=function(_dN,_dO,_dP){return new F(function(){return _dH(_dO,_dP);});},_dQ=function(_dR,_dS){return new F(function(){return _2C(_dH,_dR,_dS);});},_dT=new T3(0,_dM,_dK,_dQ),_dU=new T(function(){return new T5(0,_dw,_dT,_dV,_dy,_dK);}),_dV=function(_dW){return new T2(0,_dU,_dW);},_dX=3,_dY=new T(function(){return B(_dV(_dX));}),_dZ=new T(function(){return die(_dY);}),_e0=0,_e1=new T(function(){return B(_dV(_e0));}),_e2=new T(function(){return die(_e1);}),_e3=function(_e4,_e5){var _e6=E(_e5);switch(_e6){case  -1:var _e7=E(_e4);if(_e7==( -2147483648)){return E(_e2);}else{return new F(function(){return _do(_e7, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return _do(_e4,_e6);});}},_e8=function(_e9,_ea){return new F(function(){return _e3(E(_e9),E(_ea));});},_eb=0,_ec=new T2(0,_e2,_eb),_ed=function(_ee,_ef){var _eg=E(_ee),_eh=E(_ef);switch(_eh){case  -1:var _ei=E(_eg);if(_ei==( -2147483648)){return E(_ec);}else{if(_ei<=0){if(_ei>=0){var _ej=quotRemI(_ei, -1);return new T2(0,_ej.a,_ej.b);}else{var _ek=quotRemI(_ei, -1);return new T2(0,_ek.a,_ek.b);}}else{var _el=quotRemI(_ei-1|0, -1);return new T2(0,_el.a-1|0,(_el.b+( -1)|0)+1|0);}}break;case 0:return E(_dZ);default:if(_eg<=0){if(_eg>=0){var _em=quotRemI(_eg,_eh);return new T2(0,_em.a,_em.b);}else{if(_eh<=0){var _en=quotRemI(_eg,_eh);return new T2(0,_en.a,_en.b);}else{var _eo=quotRemI(_eg+1|0,_eh);return new T2(0,_eo.a-1|0,(_eo.b+_eh|0)-1|0);}}}else{if(_eh>=0){if(_eg>=0){var _ep=quotRemI(_eg,_eh);return new T2(0,_ep.a,_ep.b);}else{if(_eh<=0){var _eq=quotRemI(_eg,_eh);return new T2(0,_eq.a,_eq.b);}else{var _er=quotRemI(_eg+1|0,_eh);return new T2(0,_er.a-1|0,(_er.b+_eh|0)-1|0);}}}else{var _es=quotRemI(_eg-1|0,_eh);return new T2(0,_es.a-1|0,(_es.b+_eh|0)+1|0);}}}},_et=function(_eu,_ev){var _ew=_eu%_ev;if(_eu<=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ex=E(_ew);return (_ex==0)?0:_ex+_ev|0;}}}else{if(_ev>=0){if(_eu>=0){return E(_ew);}else{if(_ev<=0){return E(_ew);}else{var _ey=E(_ew);return (_ey==0)?0:_ey+_ev|0;}}}else{var _ez=E(_ew);return (_ez==0)?0:_ez+_ev|0;}}},_eA=function(_eB,_eC){var _eD=E(_eC);switch(_eD){case  -1:return E(_eb);case 0:return E(_dZ);default:return new F(function(){return _et(E(_eB),_eD);});}},_eE=function(_eF,_eG){var _eH=E(_eF),_eI=E(_eG);switch(_eI){case  -1:var _eJ=E(_eH);if(_eJ==( -2147483648)){return E(_e2);}else{return new F(function(){return quot(_eJ, -1);});}break;case 0:return E(_dZ);default:return new F(function(){return quot(_eH,_eI);});}},_eK=function(_eL,_eM){var _eN=E(_eL),_eO=E(_eM);switch(_eO){case  -1:var _eP=E(_eN);if(_eP==( -2147483648)){return E(_ec);}else{var _eQ=quotRemI(_eP, -1);return new T2(0,_eQ.a,_eQ.b);}break;case 0:return E(_dZ);default:var _eR=quotRemI(_eN,_eO);return new T2(0,_eR.a,_eR.b);}},_eS=function(_eT,_eU){var _eV=E(_eU);switch(_eV){case  -1:return E(_eb);case 0:return E(_dZ);default:return E(_eT)%_eV;}},_eW=function(_eX){return new T1(0,_eX);},_eY=function(_eZ){return new F(function(){return _eW(E(_eZ));});},_f0=new T1(0,1),_f1=function(_f2){return new T2(0,E(B(_eW(E(_f2)))),E(_f0));},_f3=function(_f4,_f5){return imul(E(_f4),E(_f5))|0;},_f6=function(_f7,_f8){return E(_f7)+E(_f8)|0;},_f9=function(_fa,_fb){return E(_fa)-E(_fb)|0;},_fc=function(_fd){var _fe=E(_fd);return (_fe<0)? -_fe:E(_fe);},_ff=function(_fg){var _fh=E(_fg);if(!_fh._){return E(_fh.a);}else{return new F(function(){return I_toInt(_fh.a);});}},_fi=function(_fj){return new F(function(){return _ff(_fj);});},_fk=function(_fl){return  -E(_fl);},_fm= -1,_fn=0,_fo=1,_fp=function(_fq){var _fr=E(_fq);return (_fr>=0)?(E(_fr)==0)?E(_fn):E(_fo):E(_fm);},_fs={_:0,a:_f6,b:_f9,c:_f3,d:_fk,e:_fc,f:_fp,g:_fi},_ft=function(_fu,_fv){var _fw=E(_fu),_fx=E(_fv);return (_fw>_fx)?E(_fw):E(_fx);},_fy=function(_fz,_fA){var _fB=E(_fz),_fC=E(_fA);return (_fB>_fC)?E(_fC):E(_fB);},_fD=function(_fE,_fF){return (_fE>=_fF)?(_fE!=_fF)?2:1:0;},_fG=function(_fH,_fI){return new F(function(){return _fD(E(_fH),E(_fI));});},_fJ=function(_fK,_fL){return E(_fK)>=E(_fL);},_fM=function(_fN,_fO){return E(_fN)>E(_fO);},_fP=function(_fQ,_fR){return E(_fQ)<=E(_fR);},_fS=function(_fT,_fU){return E(_fT)<E(_fU);},_fV={_:0,a:_3S,b:_fG,c:_fS,d:_fP,e:_fM,f:_fJ,g:_ft,h:_fy},_fW=new T3(0,_fs,_fV,_f1),_fX={_:0,a:_fW,b:_dn,c:_eE,d:_eS,e:_e8,f:_eA,g:_eK,h:_ed,i:_eY},_fY=function(_fZ){var _g0=E(_fZ);return new F(function(){return Math.log(_g0+(_g0+1)*Math.sqrt((_g0-1)/(_g0+1)));});},_g1=function(_g2){var _g3=E(_g2);return new F(function(){return Math.log(_g3+Math.sqrt(1+_g3*_g3));});},_g4=function(_g5){var _g6=E(_g5);return 0.5*Math.log((1+_g6)/(1-_g6));},_g7=function(_g8,_g9){return Math.log(E(_g9))/Math.log(E(_g8));},_ga=3.141592653589793,_gb=new T1(0,1),_gc=function(_gd,_ge){var _gf=E(_gd);if(!_gf._){var _gg=_gf.a,_gh=E(_ge);if(!_gh._){var _gi=_gh.a;return (_gg!=_gi)?(_gg>_gi)?2:0:1;}else{var _gj=I_compareInt(_gh.a,_gg);return (_gj<=0)?(_gj>=0)?1:2:0;}}else{var _gk=_gf.a,_gl=E(_ge);if(!_gl._){var _gm=I_compareInt(_gk,_gl.a);return (_gm>=0)?(_gm<=0)?1:2:0;}else{var _gn=I_compare(_gk,_gl.a);return (_gn>=0)?(_gn<=0)?1:2:0;}}},_go=function(_gp,_gq){var _gr=E(_gp);return (_gr._==0)?_gr.a*Math.pow(2,_gq):I_toNumber(_gr.a)*Math.pow(2,_gq);},_gs=function(_gt,_gu){var _gv=E(_gt);if(!_gv._){var _gw=_gv.a,_gx=E(_gu);return (_gx._==0)?_gw==_gx.a:(I_compareInt(_gx.a,_gw)==0)?true:false;}else{var _gy=_gv.a,_gz=E(_gu);return (_gz._==0)?(I_compareInt(_gy,_gz.a)==0)?true:false:(I_compare(_gy,_gz.a)==0)?true:false;}},_gA=function(_gB,_gC){while(1){var _gD=E(_gB);if(!_gD._){var _gE=_gD.a,_gF=E(_gC);if(!_gF._){var _gG=_gF.a,_gH=addC(_gE,_gG);if(!E(_gH.b)){return new T1(0,_gH.a);}else{_gB=new T1(1,I_fromInt(_gE));_gC=new T1(1,I_fromInt(_gG));continue;}}else{_gB=new T1(1,I_fromInt(_gE));_gC=_gF;continue;}}else{var _gI=E(_gC);if(!_gI._){_gB=_gD;_gC=new T1(1,I_fromInt(_gI.a));continue;}else{return new T1(1,I_add(_gD.a,_gI.a));}}}},_gJ=function(_gK,_gL){while(1){var _gM=E(_gK);if(!_gM._){var _gN=E(_gM.a);if(_gN==( -2147483648)){_gK=new T1(1,I_fromInt( -2147483648));continue;}else{var _gO=E(_gL);if(!_gO._){var _gP=_gO.a;return new T2(0,new T1(0,quot(_gN,_gP)),new T1(0,_gN%_gP));}else{_gK=new T1(1,I_fromInt(_gN));_gL=_gO;continue;}}}else{var _gQ=E(_gL);if(!_gQ._){_gK=_gM;_gL=new T1(1,I_fromInt(_gQ.a));continue;}else{var _gR=I_quotRem(_gM.a,_gQ.a);return new T2(0,new T1(1,_gR.a),new T1(1,_gR.b));}}}},_gS=new T1(0,0),_gT=function(_gU,_gV){while(1){var _gW=E(_gU);if(!_gW._){_gU=new T1(1,I_fromInt(_gW.a));continue;}else{return new T1(1,I_shiftLeft(_gW.a,_gV));}}},_gX=function(_gY,_gZ,_h0){if(!B(_gs(_h0,_gS))){var _h1=B(_gJ(_gZ,_h0)),_h2=_h1.a;switch(B(_gc(B(_gT(_h1.b,1)),_h0))){case 0:return new F(function(){return _go(_h2,_gY);});break;case 1:if(!(B(_ff(_h2))&1)){return new F(function(){return _go(_h2,_gY);});}else{return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}break;default:return new F(function(){return _go(B(_gA(_h2,_gb)),_gY);});}}else{return E(_dZ);}},_h3=function(_h4,_h5){var _h6=E(_h4);if(!_h6._){var _h7=_h6.a,_h8=E(_h5);return (_h8._==0)?_h7>_h8.a:I_compareInt(_h8.a,_h7)<0;}else{var _h9=_h6.a,_ha=E(_h5);return (_ha._==0)?I_compareInt(_h9,_ha.a)>0:I_compare(_h9,_ha.a)>0;}},_hb=new T1(0,1),_hc=function(_hd,_he){var _hf=E(_hd);if(!_hf._){var _hg=_hf.a,_hh=E(_he);return (_hh._==0)?_hg<_hh.a:I_compareInt(_hh.a,_hg)>0;}else{var _hi=_hf.a,_hj=E(_he);return (_hj._==0)?I_compareInt(_hi,_hj.a)<0:I_compare(_hi,_hj.a)<0;}},_hk=new T(function(){return B(unCStr("base"));}),_hl=new T(function(){return B(unCStr("Control.Exception.Base"));}),_hm=new T(function(){return B(unCStr("PatternMatchFail"));}),_hn=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hk,_hl,_hm),_ho=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_hn,_Z,_Z),_hp=function(_hq){return E(_ho);},_hr=function(_hs){var _ht=E(_hs);return new F(function(){return _1r(B(_1p(_ht.a)),_hp,_ht.b);});},_hu=function(_hv){return E(E(_hv).a);},_hw=function(_hx){return new T2(0,_hy,_hx);},_hz=function(_hA,_hB){return new F(function(){return _x(E(_hA).a,_hB);});},_hC=function(_hD,_hE){return new F(function(){return _2C(_hz,_hD,_hE);});},_hF=function(_hG,_hH,_hI){return new F(function(){return _x(E(_hH).a,_hI);});},_hJ=new T3(0,_hF,_hu,_hC),_hy=new T(function(){return new T5(0,_hp,_hJ,_hw,_hr,_hu);}),_hK=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_hL=function(_hM,_hN){return new F(function(){return die(new T(function(){return B(A2(_5L,_hN,_hM));}));});},_hO=function(_hP,_dW){return new F(function(){return _hL(_hP,_dW);});},_hQ=function(_hR,_hS){var _hT=E(_hS);if(!_hT._){return new T2(0,_Z,_Z);}else{var _hU=_hT.a;if(!B(A1(_hR,_hU))){return new T2(0,_Z,_hT);}else{var _hV=new T(function(){var _hW=B(_hQ(_hR,_hT.b));return new T2(0,_hW.a,_hW.b);});return new T2(0,new T2(1,_hU,new T(function(){return E(E(_hV).a);})),new T(function(){return E(E(_hV).b);}));}}},_hX=32,_hY=new T(function(){return B(unCStr("\n"));}),_hZ=function(_i0){return (E(_i0)==124)?false:true;},_i1=function(_i2,_i3){var _i4=B(_hQ(_hZ,B(unCStr(_i2)))),_i5=_i4.a,_i6=function(_i7,_i8){var _i9=new T(function(){var _ia=new T(function(){return B(_x(_i3,new T(function(){return B(_x(_i8,_hY));},1)));});return B(unAppCStr(": ",_ia));},1);return new F(function(){return _x(_i7,_i9);});},_ib=E(_i4.b);if(!_ib._){return new F(function(){return _i6(_i5,_Z);});}else{if(E(_ib.a)==124){return new F(function(){return _i6(_i5,new T2(1,_hX,_ib.b));});}else{return new F(function(){return _i6(_i5,_Z);});}}},_ic=function(_id){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_id,_hK));})),_hy);});},_ie=function(_if){var _ig=function(_ih,_ii){while(1){if(!B(_hc(_ih,_if))){if(!B(_h3(_ih,_if))){if(!B(_gs(_ih,_if))){return new F(function(){return _ic("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_ii);}}else{return _ii-1|0;}}else{var _ij=B(_gT(_ih,1)),_ik=_ii+1|0;_ih=_ij;_ii=_ik;continue;}}};return new F(function(){return _ig(_hb,0);});},_il=function(_im){var _in=E(_im);if(!_in._){var _io=_in.a>>>0;if(!_io){return  -1;}else{var _ip=function(_iq,_ir){while(1){if(_iq>=_io){if(_iq<=_io){if(_iq!=_io){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_ir);}}else{return _ir-1|0;}}else{var _is=imul(_iq,2)>>>0,_it=_ir+1|0;_iq=_is;_ir=_it;continue;}}};return new F(function(){return _ip(1,0);});}}else{return new F(function(){return _ie(_in);});}},_iu=function(_iv){var _iw=E(_iv);if(!_iw._){var _ix=_iw.a>>>0;if(!_ix){return new T2(0, -1,0);}else{var _iy=function(_iz,_iA){while(1){if(_iz>=_ix){if(_iz<=_ix){if(_iz!=_ix){return new F(function(){return _ic("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_iA);}}else{return _iA-1|0;}}else{var _iB=imul(_iz,2)>>>0,_iC=_iA+1|0;_iz=_iB;_iA=_iC;continue;}}};return new T2(0,B(_iy(1,0)),(_ix&_ix-1>>>0)>>>0&4294967295);}}else{var _iD=_iw.a;return new T2(0,B(_il(_iw)),I_compareInt(I_and(_iD,I_sub(_iD,I_fromInt(1))),0));}},_iE=function(_iF,_iG){var _iH=E(_iF);if(!_iH._){var _iI=_iH.a,_iJ=E(_iG);return (_iJ._==0)?_iI<=_iJ.a:I_compareInt(_iJ.a,_iI)>=0;}else{var _iK=_iH.a,_iL=E(_iG);return (_iL._==0)?I_compareInt(_iK,_iL.a)<=0:I_compare(_iK,_iL.a)<=0;}},_iM=function(_iN,_iO){while(1){var _iP=E(_iN);if(!_iP._){var _iQ=_iP.a,_iR=E(_iO);if(!_iR._){return new T1(0,(_iQ>>>0&_iR.a>>>0)>>>0&4294967295);}else{_iN=new T1(1,I_fromInt(_iQ));_iO=_iR;continue;}}else{var _iS=E(_iO);if(!_iS._){_iN=_iP;_iO=new T1(1,I_fromInt(_iS.a));continue;}else{return new T1(1,I_and(_iP.a,_iS.a));}}}},_iT=function(_iU,_iV){while(1){var _iW=E(_iU);if(!_iW._){var _iX=_iW.a,_iY=E(_iV);if(!_iY._){var _iZ=_iY.a,_j0=subC(_iX,_iZ);if(!E(_j0.b)){return new T1(0,_j0.a);}else{_iU=new T1(1,I_fromInt(_iX));_iV=new T1(1,I_fromInt(_iZ));continue;}}else{_iU=new T1(1,I_fromInt(_iX));_iV=_iY;continue;}}else{var _j1=E(_iV);if(!_j1._){_iU=_iW;_iV=new T1(1,I_fromInt(_j1.a));continue;}else{return new T1(1,I_sub(_iW.a,_j1.a));}}}},_j2=new T1(0,2),_j3=function(_j4,_j5){var _j6=E(_j4);if(!_j6._){var _j7=(_j6.a>>>0&(2<<_j5>>>0)-1>>>0)>>>0,_j8=1<<_j5>>>0;return (_j8<=_j7)?(_j8>=_j7)?1:2:0;}else{var _j9=B(_iM(_j6,B(_iT(B(_gT(_j2,_j5)),_hb)))),_ja=B(_gT(_hb,_j5));return (!B(_h3(_ja,_j9)))?(!B(_hc(_ja,_j9)))?1:2:0;}},_jb=function(_jc,_jd){while(1){var _je=E(_jc);if(!_je._){_jc=new T1(1,I_fromInt(_je.a));continue;}else{return new T1(1,I_shiftRight(_je.a,_jd));}}},_jf=function(_jg,_jh,_ji,_jj){var _jk=B(_iu(_jj)),_jl=_jk.a;if(!E(_jk.b)){var _jm=B(_il(_ji));if(_jm<((_jl+_jg|0)-1|0)){var _jn=_jl+(_jg-_jh|0)|0;if(_jn>0){if(_jn>_jm){if(_jn<=(_jm+1|0)){if(!E(B(_iu(_ji)).b)){return 0;}else{return new F(function(){return _go(_gb,_jg-_jh|0);});}}else{return 0;}}else{var _jo=B(_jb(_ji,_jn));switch(B(_j3(_ji,_jn-1|0))){case 0:return new F(function(){return _go(_jo,_jg-_jh|0);});break;case 1:if(!(B(_ff(_jo))&1)){return new F(function(){return _go(_jo,_jg-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}break;default:return new F(function(){return _go(B(_gA(_jo,_gb)),_jg-_jh|0);});}}}else{return new F(function(){return _go(_ji,(_jg-_jh|0)-_jn|0);});}}else{if(_jm>=_jh){var _jp=B(_jb(_ji,(_jm+1|0)-_jh|0));switch(B(_j3(_ji,_jm-_jh|0))){case 0:return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});break;case 2:return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});break;default:if(!(B(_ff(_jp))&1)){return new F(function(){return _go(_jp,((_jm-_jl|0)+1|0)-_jh|0);});}else{return new F(function(){return _go(B(_gA(_jp,_gb)),((_jm-_jl|0)+1|0)-_jh|0);});}}}else{return new F(function(){return _go(_ji, -_jl);});}}}else{var _jq=B(_il(_ji))-_jl|0,_jr=function(_js){var _jt=function(_ju,_jv){if(!B(_iE(B(_gT(_jv,_jh)),_ju))){return new F(function(){return _gX(_js-_jh|0,_ju,_jv);});}else{return new F(function(){return _gX((_js-_jh|0)+1|0,_ju,B(_gT(_jv,1)));});}};if(_js>=_jh){if(_js!=_jh){return new F(function(){return _jt(_ji,new T(function(){return B(_gT(_jj,_js-_jh|0));}));});}else{return new F(function(){return _jt(_ji,_jj);});}}else{return new F(function(){return _jt(new T(function(){return B(_gT(_ji,_jh-_js|0));}),_jj);});}};if(_jg>_jq){return new F(function(){return _jr(_jg);});}else{return new F(function(){return _jr(_jq);});}}},_jw=new T1(0,2147483647),_jx=new T(function(){return B(_gA(_jw,_hb));}),_jy=function(_jz){var _jA=E(_jz);if(!_jA._){var _jB=E(_jA.a);return (_jB==( -2147483648))?E(_jx):new T1(0, -_jB);}else{return new T1(1,I_negate(_jA.a));}},_jC=new T(function(){return 0/0;}),_jD=new T(function(){return  -1/0;}),_jE=new T(function(){return 1/0;}),_jF=0,_jG=function(_jH,_jI){if(!B(_gs(_jI,_gS))){if(!B(_gs(_jH,_gS))){if(!B(_hc(_jH,_gS))){return new F(function(){return _jf( -1021,53,_jH,_jI);});}else{return  -B(_jf( -1021,53,B(_jy(_jH)),_jI));}}else{return E(_jF);}}else{return (!B(_gs(_jH,_gS)))?(!B(_hc(_jH,_gS)))?E(_jE):E(_jD):E(_jC);}},_jJ=function(_jK){var _jL=E(_jK);return new F(function(){return _jG(_jL.a,_jL.b);});},_jM=function(_jN){return 1/E(_jN);},_jO=function(_jP){var _jQ=E(_jP);return (_jQ!=0)?(_jQ<=0)? -_jQ:E(_jQ):E(_jF);},_jR=function(_jS){var _jT=E(_jS);if(!_jT._){return _jT.a;}else{return new F(function(){return I_toNumber(_jT.a);});}},_jU=function(_jV){return new F(function(){return _jR(_jV);});},_jW=1,_jX= -1,_jY=function(_jZ){var _k0=E(_jZ);return (_k0<=0)?(_k0>=0)?E(_k0):E(_jX):E(_jW);},_k1=function(_k2,_k3){return E(_k2)-E(_k3);},_k4=function(_k5){return  -E(_k5);},_k6=function(_k7,_k8){return E(_k7)+E(_k8);},_k9=function(_ka,_kb){return E(_ka)*E(_kb);},_kc={_:0,a:_k6,b:_k1,c:_k9,d:_k4,e:_jO,f:_jY,g:_jU},_kd=function(_ke,_kf){return E(_ke)/E(_kf);},_kg=new T4(0,_kc,_kd,_jM,_jJ),_kh=function(_ki){return new F(function(){return Math.acos(E(_ki));});},_kj=function(_kk){return new F(function(){return Math.asin(E(_kk));});},_kl=function(_km){return new F(function(){return Math.atan(E(_km));});},_kn=function(_ko){return new F(function(){return Math.cos(E(_ko));});},_kp=function(_kq){return new F(function(){return cosh(E(_kq));});},_kr=function(_ks){return new F(function(){return Math.exp(E(_ks));});},_kt=function(_ku){return new F(function(){return Math.log(E(_ku));});},_kv=function(_kw,_kx){return new F(function(){return Math.pow(E(_kw),E(_kx));});},_ky=function(_kz){return new F(function(){return Math.sin(E(_kz));});},_kA=function(_kB){return new F(function(){return sinh(E(_kB));});},_kC=function(_kD){return new F(function(){return Math.sqrt(E(_kD));});},_kE=function(_kF){return new F(function(){return Math.tan(E(_kF));});},_kG=function(_kH){return new F(function(){return tanh(E(_kH));});},_kI={_:0,a:_kg,b:_ga,c:_kr,d:_kt,e:_kC,f:_kv,g:_g7,h:_ky,i:_kn,j:_kE,k:_kj,l:_kh,m:_kl,n:_kA,o:_kp,p:_kG,q:_g1,r:_fY,s:_g4},_kJ=0,_kK=function(_){return _kJ;},_kL=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_kM=new T(function(){return eval("(function(ctx){ctx.save();})");}),_kN=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_kO=function(_kP,_kQ,_kR,_){var _kS=__app1(E(_kM),_kR),_kT=__app2(E(_kN),_kR,E(_kP)),_kU=B(A2(_kQ,_kR,_)),_kV=__app1(E(_kL),_kR);return new F(function(){return _kK(_);});},_kW=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_kX=function(_kY,_kZ,_l0,_l1,_){var _l2=__app1(E(_kM),_l1),_l3=__app3(E(_kW),_l1,E(_kY),E(_kZ)),_l4=B(A2(_l0,_l1,_)),_l5=__app1(E(_kL),_l1);return new F(function(){return _kK(_);});},_l6=function(_l7,_l8){return E(_l7)!=E(_l8);},_l9=function(_la,_lb){return E(_la)==E(_lb);},_lc=new T2(0,_l9,_l6),_ld=function(_le){return E(E(_le).a);},_lf=function(_lg){return E(E(_lg).a);},_lh=function(_li){return E(E(_li).b);},_lj=function(_lk){return E(E(_lk).g);},_ll=new T(function(){return B(unCStr("\u30fc\u301c\u3002\u300c\uff1c\uff1e\uff08\uff09"));}),_lm=0,_ln=3.3333333333333335,_lo=16.666666666666668,_lp=function(_lq){return E(E(_lq).b);},_lr=new T1(0,0),_ls=new T1(0,2),_lt=function(_lu){return E(E(_lu).i);},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC,_lD){var _lE=new T(function(){var _lF=E(_lD);if(_lF<=31){return B(_4H(_lc,_lF,_ll));}else{if(_lF>=128){return B(_4H(_lc,_lF,_ll));}else{return true;}}}),_lG=new T(function(){if(E(_lz)==8){return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28+20;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24+8*(E(_lA)-1);}));}else{return new T2(0,new T(function(){return B(_jR(B(A2(_lt,_lx,_lB))))*28;}),new T(function(){return B(_jR(B(A2(_lt,_ly,_lC))))*24;}));}}),_lH=new T(function(){var _lI=B(_ld(_lw));if(!E(_lE)){return B(A2(_lj,B(_lf(_lI)),_lr));}else{return B(A3(_lh,_lI,new T(function(){return B(_lp(_lw));}),new T(function(){return B(A2(_lj,B(_lf(_lI)),_ls));})));}});return new T3(0,new T2(0,new T(function(){return E(E(_lG).a);}),new T(function(){return E(E(_lG).b);})),new T2(0,new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_ln);}}),new T(function(){if(!E(_lE)){return E(_lm);}else{return E(_lo);}})),_lH);},_lJ=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_lK=function(_lL,_lM,_lN){var _lO=new T(function(){return toJSStr(E(_lN));});return function(_lP,_){var _lQ=__app4(E(_lJ),E(_lP),E(_lO),E(_lL),E(_lM));return new F(function(){return _kK(_);});};},_lR=0,_lS=",",_lT="rgba(",_lU=new T(function(){return toJSStr(_Z);}),_lV="rgb(",_lW=")",_lX=new T2(1,_lW,_Z),_lY=function(_lZ){var _m0=E(_lZ);if(!_m0._){var _m1=jsCat(new T2(1,_lV,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),_lX)))))),E(_lU));return E(_m1);}else{var _m2=jsCat(new T2(1,_lT,new T2(1,new T(function(){return String(_m0.a);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.b);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.c);}),new T2(1,_lS,new T2(1,new T(function(){return String(_m0.d);}),_lX)))))))),E(_lU));return E(_m2);}},_m3="strokeStyle",_m4="fillStyle",_m5=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_m6=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_m7=function(_m8,_m9){var _ma=new T(function(){return B(_lY(_m8));});return function(_mb,_){var _mc=E(_mb),_md=E(_m4),_me=E(_m5),_mf=__app2(_me,_mc,_md),_mg=E(_m3),_mh=__app2(_me,_mc,_mg),_mi=E(_ma),_mj=E(_m6),_mk=__app3(_mj,_mc,_md,_mi),_ml=__app3(_mj,_mc,_mg,_mi),_mm=B(A2(_m9,_mc,_)),_mn=String(_mf),_mo=__app3(_mj,_mc,_md,_mn),_mp=String(_mh),_mq=__app3(_mj,_mc,_mg,_mp);return new F(function(){return _kK(_);});};},_mr="font",_ms=function(_mt,_mu){var _mv=new T(function(){return toJSStr(E(_mt));});return function(_mw,_){var _mx=E(_mw),_my=E(_mr),_mz=__app2(E(_m5),_mx,_my),_mA=E(_m6),_mB=__app3(_mA,_mx,_my,E(_mv)),_mC=B(A2(_mu,_mx,_)),_mD=String(_mz),_mE=__app3(_mA,_mx,_my,_mD);return new F(function(){return _kK(_);});};},_mF=new T(function(){return B(unCStr("px IPAGothic"));}),_mG=function(_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_){var _mO=new T(function(){var _mP=new T(function(){var _mQ=B(_lv(_kI,_fX,_fX,_mJ,_mK,_mL,_mM,_mN)),_mR=E(_mQ.a),_mS=E(_mQ.b);return new T5(0,_mR.a,_mR.b,_mS.a,_mS.b,_mQ.c);}),_mT=new T(function(){var _mU=E(_mP);return E(_mU.a)+E(_mU.c);}),_mV=new T(function(){var _mW=E(_mP);return E(_mW.b)-E(_mW.d);}),_mX=new T(function(){return E(E(_mP).e);}),_mY=new T(function(){return B(_lK(_lR,_lR,new T2(1,_mN,_Z)));}),_mZ=function(_n0,_){return new F(function(){return _kO(_mX,_mY,E(_n0),_);});};return B(_ms(new T(function(){return B(_x(B(_H(0,E(_mJ),_Z)),_mF));},1),function(_n1,_){return new F(function(){return _kX(_mT,_mV,_mZ,E(_n1),_);});}));});return new F(function(){return A(_m7,[_mI,_mO,_mH,_]);});},_n2=new T3(0,153,255,255),_n3=new T2(1,_n2,_Z),_n4=new T3(0,255,153,204),_n5=new T2(1,_n4,_n3),_n6=new T3(0,255,204,153),_n7=new T2(1,_n6,_n5),_n8=new T3(0,200,255,200),_n9=new T2(1,_n8,_n7),_na=20,_nb=64,_nc=1,_nd=2,_ne=8,_nf=function(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_){while(1){var _nn=B((function(_no,_np,_nq,_nr,_ns,_nt,_nu,_){var _nv=E(_nu);if(!_nv._){return _kJ;}else{var _nw=_nv.b,_nx=E(_nv.a),_ny=E(_nx);switch(_ny){case 10:var _nz=_no,_nA=_np,_nB=_nr,_nC=_nr;_ng=_nz;_nh=_nA;_ni=0;_nj=_nB;_nk=new T(function(){return E(_ns)-1|0;});_nl=_nC;_nm=_nw;return __continue;case 123:return new F(function(){return _nD(_no,_np,_nq,_nr,_ns,_nt,_nw,_);});break;case 65306:var _nE=new T(function(){return B(_aW(_n9,_nq));}),_nF=function(_nG,_nH,_nI,_nJ,_nK,_nL,_){while(1){var _nM=B((function(_nN,_nO,_nP,_nQ,_nR,_nS,_){var _nT=E(_nS);if(!_nT._){return _kJ;}else{var _nU=_nT.b,_nV=E(_nT.a);if(E(_nV)==65306){var _nW=new T(function(){var _nX=E(_nR);if((_nX+1)*24<=E(_np)-10){return new T2(0,_nQ,_nX+1|0);}else{return new T2(0,new T(function(){return E(_nQ)-1|0;}),_nO);}});return new F(function(){return _nf(_nN,_np,_nq,_nO,new T(function(){return E(E(_nW).a);}),new T(function(){return E(E(_nW).b);}),_nU,_);});}else{var _nY=E(_nN),_nZ=B(_mG(_nY.a,_nE,_ne,_nP,_nQ,_nR,_nV,_)),_o0=_nO,_o1=_nP+1,_o2=_nQ,_o3=_nR;_nG=_nY;_nH=_o0;_nI=_o1;_nJ=_o2;_nK=_o3;_nL=_nU;return __continue;}}})(_nG,_nH,_nI,_nJ,_nK,_nL,_));if(_nM!=__continue){return _nM;}}};return new F(function(){return _nF(_no,_nr,0,new T(function(){if(E(_nr)!=E(_nt)){return E(_ns);}else{return E(_ns)+1|0;}}),new T(function(){var _o4=E(_nt);if(E(_nr)!=_o4){return _o4-1|0;}else{var _o5=(E(_np)-10)/24,_o6=_o5&4294967295;if(_o5>=_o6){return _o6;}else{return _o6-1|0;}}}),_nw,_);});break;default:var _o7=function(_o8,_o9){var _oa=new T(function(){switch(E(_ny)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _nq;}}),_ob=new T(function(){var _oc=E(_nt);if((_oc+1)*24<=E(_np)-10){return new T2(0,_ns,_oc+1|0);}else{return new T2(0,new T(function(){return E(_ns)-1|0;}),_nr);}});if(E(_o8)==64){return new F(function(){return _od(_no,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}else{var _oe=E(_no),_of=B(_mG(_oe.a,new T(function(){return B(_aW(_n9,E(_oa)));},1),_na,_lR,_ns,_nt,_o9,_));return new F(function(){return _od(_oe,_np,_oa,_nr,new T(function(){return E(E(_ob).a);}),new T(function(){return E(E(_ob).b);}),_nw,_);});}},_og=E(_ny);switch(_og){case 42:return new F(function(){return _o7(64,_nb);});break;case 12289:return new F(function(){return _o7(64,_nb);});break;case 12290:return new F(function(){return _o7(64,_nb);});break;default:return new F(function(){return _o7(_og,_nx);});}}}})(_ng,_nh,_ni,_nj,_nk,_nl,_nm,_));if(_nn!=__continue){return _nn;}}},_od=function(_oh,_oi,_oj,_ok,_ol,_om,_on,_){var _oo=E(_on);if(!_oo._){return _kJ;}else{var _op=_oo.b,_oq=E(_oo.a),_or=E(_oq);switch(_or){case 10:return new F(function(){return _nf(_oh,_oi,0,_ok,new T(function(){return E(_ol)-1|0;}),_ok,_op,_);});break;case 123:return new F(function(){return _nD(_oh,_oi,_oj,_ok,_ol,_om,_op,_);});break;case 65306:var _os=new T(function(){return B(_aW(_n9,E(_oj)));}),_ot=function(_ou,_ov,_ow,_ox,_oy,_oz,_){while(1){var _oA=B((function(_oB,_oC,_oD,_oE,_oF,_oG,_){var _oH=E(_oG);if(!_oH._){return _kJ;}else{var _oI=_oH.b,_oJ=E(_oH.a);if(E(_oJ)==65306){var _oK=new T(function(){var _oL=E(_oF);if((_oL+1)*24<=E(_oi)-10){return new T2(0,_oE,_oL+1|0);}else{return new T2(0,new T(function(){return E(_oE)-1|0;}),_oC);}});return new F(function(){return _od(_oB,_oi,_oj,_oC,new T(function(){return E(E(_oK).a);}),new T(function(){return E(E(_oK).b);}),_oI,_);});}else{var _oM=E(_oB),_oN=B(_mG(_oM.a,_os,_ne,_oD,_oE,_oF,_oJ,_)),_oO=_oC,_oP=_oD+1,_oQ=_oE,_oR=_oF;_ou=_oM;_ov=_oO;_ow=_oP;_ox=_oQ;_oy=_oR;_oz=_oI;return __continue;}}})(_ou,_ov,_ow,_ox,_oy,_oz,_));if(_oA!=__continue){return _oA;}}};return new F(function(){return _ot(_oh,_ok,0,new T(function(){if(E(_ok)!=E(_om)){return E(_ol);}else{return E(_ol)+1|0;}}),new T(function(){var _oS=E(_om);if(E(_ok)!=_oS){return _oS-1|0;}else{var _oT=(E(_oi)-10)/24,_oU=_oT&4294967295;if(_oT>=_oU){return _oU;}else{return _oU-1|0;}}}),_op,_);});break;default:var _oV=function(_oW,_oX){var _oY=new T(function(){switch(E(_or)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return E(_oj);}}),_oZ=new T(function(){var _p0=E(_om);if((_p0+1)*24<=E(_oi)-10){return new T2(0,_ol,_p0+1|0);}else{return new T2(0,new T(function(){return E(_ol)-1|0;}),_ok);}});if(E(_oW)==64){return new F(function(){return _od(_oh,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}else{var _p1=E(_oh),_p2=B(_mG(_p1.a,new T(function(){return B(_aW(_n9,E(_oY)));},1),_na,_lR,_ol,_om,_oX,_));return new F(function(){return _od(_p1,_oi,_oY,_ok,new T(function(){return E(E(_oZ).a);}),new T(function(){return E(E(_oZ).b);}),_op,_);});}},_p3=E(_or);switch(_p3){case 42:return new F(function(){return _oV(64,_nb);});break;case 12289:return new F(function(){return _oV(64,_nb);});break;case 12290:return new F(function(){return _oV(64,_nb);});break;default:return new F(function(){return _oV(_p3,_oq);});}}}},_nD=function(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_){while(1){var _pb=B((function(_pc,_pd,_pe,_pf,_pg,_ph,_pi,_){var _pj=E(_pi);if(!_pj._){return _kJ;}else{var _pk=_pj.b;if(E(_pj.a)==125){var _pl=new T(function(){var _pm=E(_ph);if((_pm+1)*24<=E(_pd)-10){return new T2(0,_pg,_pm+1|0);}else{return new T2(0,new T(function(){return E(_pg)-1|0;}),_pf);}});return new F(function(){return _od(_pc,_pd,_pe,_pf,new T(function(){return E(E(_pl).a);}),new T(function(){return E(E(_pl).b);}),_pk,_);});}else{var _pn=_pc,_po=_pd,_pp=_pe,_pq=_pf,_pr=_pg,_ps=_ph;_p4=_pn;_p5=_po;_p6=_pp;_p7=_pq;_p8=_pr;_p9=_ps;_pa=_pk;return __continue;}}})(_p4,_p5,_p6,_p7,_p8,_p9,_pa,_));if(_pb!=__continue){return _pb;}}},_pt=function(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_){while(1){var _pC=B((function(_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_){var _pL=E(_pK);if(!_pL._){return _kJ;}else{var _pM=_pL.b,_pN=E(_pL.a),_pO=E(_pN);switch(_pO){case 10:var _pP=_pD,_pQ=_pE,_pR=_pF,_pS=_pH,_pT=_pH;_pu=_pP;_pv=_pQ;_pw=_pR;_px=0;_py=_pS;_pz=new T(function(){return E(_pI)-1|0;});_pA=_pT;_pB=_pM;return __continue;case 123:return new F(function(){return _nD(new T2(0,_pD,_pE),_pF,_pG,_pH,_pI,_pJ,_pM,_);});break;case 65306:var _pU=new T(function(){return B(_aW(_n9,_pG));}),_pV=function(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_){while(1){var _q3=B((function(_q4,_q5,_q6,_q7,_q8,_q9,_qa,_){var _qb=E(_qa);if(!_qb._){return _kJ;}else{var _qc=_qb.b,_qd=E(_qb.a);if(E(_qd)==65306){var _qe=new T(function(){var _qf=E(_q9);if((_qf+1)*24<=E(_pF)-10){return new T2(0,_q8,_qf+1|0);}else{return new T2(0,new T(function(){return E(_q8)-1|0;}),_q6);}});return new F(function(){return _pt(_q4,_q5,_pF,_pG,_q6,new T(function(){return E(E(_qe).a);}),new T(function(){return E(E(_qe).b);}),_qc,_);});}else{var _qg=B(_mG(_q4,_pU,_ne,_q7,_q8,_q9,_qd,_)),_qh=_q4,_qi=_q5,_qj=_q6,_qk=_q7+1,_ql=_q8,_qm=_q9;_pW=_qh;_pX=_qi;_pY=_qj;_pZ=_qk;_q0=_ql;_q1=_qm;_q2=_qc;return __continue;}}})(_pW,_pX,_pY,_pZ,_q0,_q1,_q2,_));if(_q3!=__continue){return _q3;}}};return new F(function(){return _pV(_pD,_pE,_pH,0,new T(function(){if(E(_pH)!=E(_pJ)){return E(_pI);}else{return E(_pI)+1|0;}}),new T(function(){var _qn=E(_pJ);if(E(_pH)!=_qn){return _qn-1|0;}else{var _qo=(E(_pF)-10)/24,_qp=_qo&4294967295;if(_qo>=_qp){return _qp;}else{return _qp-1|0;}}}),_pM,_);});break;default:var _qq=function(_qr,_qs){var _qt=new T(function(){switch(E(_pO)){case 42:return E(_nd);break;case 12300:return E(_nc);break;default:return _pG;}}),_qu=new T(function(){var _qv=E(_pJ);if((_qv+1)*24<=E(_pF)-10){return new T2(0,_pI,_qv+1|0);}else{return new T2(0,new T(function(){return E(_pI)-1|0;}),_pH);}});if(E(_qr)==64){return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}else{var _qw=B(_mG(_pD,new T(function(){return B(_aW(_n9,E(_qt)));},1),_na,_lR,_pI,_pJ,_qs,_));return new F(function(){return _od(new T2(0,_pD,_pE),_pF,_qt,_pH,new T(function(){return E(E(_qu).a);}),new T(function(){return E(E(_qu).b);}),_pM,_);});}},_qx=E(_pO);switch(_qx){case 42:return new F(function(){return _qq(64,_nb);});break;case 12289:return new F(function(){return _qq(64,_nb);});break;case 12290:return new F(function(){return _qq(64,_nb);});break;default:return new F(function(){return _qq(_qx,_pN);});}}}})(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_));if(_pC!=__continue){return _pC;}}},_qy=function(_qz,_qA){while(1){var _qB=E(_qz);if(!_qB._){return E(_qA);}else{var _qC=_qA+1|0;_qz=_qB.b;_qA=_qC;continue;}}},_qD=function(_qE,_){return _kJ;},_qF=function(_qG){return E(E(_qG).a);},_qH=function(_qI,_qJ){var _qK=E(_qJ),_qL=new T(function(){var _qM=B(_lf(_qI)),_qN=B(_qH(_qI,B(A3(_qF,_qM,_qK,new T(function(){return B(A2(_lj,_qM,_f0));})))));return new T2(1,_qN.a,_qN.b);});return new T2(0,_qK,_qL);},_qO=new T(function(){var _qP=B(_qH(_kg,_lR));return new T2(1,_qP.a,_qP.b);}),_qQ=new T(function(){return B(_H(0,20,_Z));}),_qR=new T(function(){return B(unCStr("px Courier"));}),_qS=new T(function(){return B(_x(_qQ,_qR));}),_qT=function(_qU,_qV,_qW,_qX,_qY){var _qZ=new T(function(){return E(_qW)*16;}),_r0=new T(function(){return E(_qX)*20;}),_r1=function(_r2,_r3){var _r4=E(_r2);if(!_r4._){return E(_qD);}else{var _r5=E(_r3);if(!_r5._){return E(_qD);}else{var _r6=new T(function(){return B(_r1(_r4.b,_r5.b));}),_r7=new T(function(){var _r8=new T(function(){var _r9=new T(function(){return B(_lK(new T(function(){return E(_qZ)+16*E(_r5.a);}),_r0,new T2(1,_r4.a,_Z)));});return B(_ms(_qS,_r9));});return B(_m7(_qV,_r8));});return function(_ra,_){var _rb=B(A2(_r7,_ra,_));return new F(function(){return A2(_r6,_ra,_);});};}}};return new F(function(){return A3(_r1,_qY,_qO,_qU);});},_rc=45,_rd=new T(function(){return B(unCStr("-"));}),_re=new T2(1,_rc,_rd),_rf=function(_rg){var _rh=E(_rg);return (_rh==1)?E(_re):new T2(1,_rc,new T(function(){return B(_rf(_rh-1|0));}));},_ri=new T(function(){return B(unCStr(": empty list"));}),_rj=function(_rk){return new F(function(){return err(B(_x(_aL,new T(function(){return B(_x(_rk,_ri));},1))));});},_rl=new T(function(){return B(unCStr("head"));}),_rm=new T(function(){return B(_rj(_rl));}),_rn=new T(function(){return eval("(function(e){e.width = e.width;})");}),_ro=new T(function(){return B(_lK(_lR,_lR,_Z));}),_rp=32,_rq=new T(function(){return B(unCStr("|"));}),_rr=function(_rs){var _rt=E(_rs);return (_rt._==0)?E(_rq):new T2(1,new T(function(){var _ru=E(_rt.a);switch(E(_ru.b)){case 7:return E(_rp);break;case 8:return E(_rp);break;default:return E(_ru.a);}}),new T(function(){return B(_rr(_rt.b));}));},_rv=function(_rw,_rx,_ry,_rz,_rA,_){var _rB=__app1(E(_rn),_rx),_rC=B(A2(_ro,_rw,_)),_rD=B(unAppCStr("-",new T(function(){var _rE=E(_rA);if(!_rE._){return E(_rm);}else{var _rF=B(_qy(_rE.a,0));if(0>=_rF){return E(_rd);}else{return B(_rf(_rF));}}}))),_rG=B(A(_qT,[_rw,_n8,_ry,_rz,_rD,_])),_rH=function(_rI,_rJ,_rK,_){while(1){var _rL=B((function(_rM,_rN,_rO,_){var _rP=E(_rO);if(!_rP._){return new F(function(){return A(_qT,[_rw,_n8,_rM,_rN,_rD,_]);});}else{var _rQ=B(A(_qT,[_rw,_n8,_rM,_rN,B(unAppCStr("|",new T(function(){return B(_rr(_rP.a));}))),_])),_rR=_rM;_rI=_rR;_rJ=new T(function(){return E(_rN)+1|0;});_rK=_rP.b;return __continue;}})(_rI,_rJ,_rK,_));if(_rL!=__continue){return _rL;}}};return new F(function(){return _rH(_ry,new T(function(){return E(_rz)+1|0;}),_rA,_);});},_rS=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_rT=function(_rU,_rV,_rW,_rX,_){var _rY=__app1(E(_kM),_rX),_rZ=__app3(E(_rS),_rX,E(_rU),E(_rV)),_s0=B(A2(_rW,_rX,_)),_s1=__app1(E(_kL),_rX);return new F(function(){return _kK(_);});},_s2=new T(function(){return eval("(function(ctx,i,x,y){ctx.drawImage(i,x,y);})");}),_s3=function(_s4,_s5,_s6,_s7,_){var _s8=__app4(E(_s2),_s7,_s4,_s5,_s6);return new F(function(){return _kK(_);});},_s9=2,_sa=40,_sb=new T(function(){return B(_aW(_n9,1));}),_sc=new T(function(){return B(_aW(_n9,2));}),_sd=2,_se=function(_sf,_sg,_sh,_si,_sj,_sk,_){var _sl=__app1(E(_rn),_sg),_sm=B(A2(_ro,_sf,_)),_sn=E(_sk),_so=E(_sn.b).a,_sp=E(_sn.a),_sq=_sp.a,_sr=E(_sn.s);if(!E(E(_sn.u).h)){return _kJ;}else{var _ss=B(_rv(_sf,_sg,new T(function(){return B(_f9(_si,_so));}),_sd,_sp.b,_)),_st=B(A(_qT,[_sf,new T(function(){if(E(_sp.e)==32){return E(_sb);}else{return E(_sc);}}),new T(function(){return ((E(E(_sq).a)+1|0)+E(_si)|0)-E(_so)|0;},1),new T(function(){return (E(E(_sq).b)+2|0)+1|0;},1),new T2(1,_sp.d,_Z),_])),_su=function(_sv,_){return new F(function(){return _rT(_s9,_s9,function(_sw,_){return new F(function(){return _s3(B(_aW(E(_sj).b,(imul(E(_sr.a),8)|0)+E(_sr.b)|0)),0,0,E(_sw),_);});},E(_sv),_);});};return new F(function(){return _kX(new T(function(){return E(_sh)-(E(_so)+10|0)*16;},1),_sa,_su,_sf,_);});}},_sx=function(_sy){return E(E(_sy).a);},_sz=function(_sA){return E(E(_sA).a);},_sB=function(_sC,_sD){while(1){var _sE=E(_sC);if(!_sE._){return E(_sD);}else{_sC=_sE.b;_sD=_sE.a;continue;}}},_sF=function(_sG,_sH,_sI){return new F(function(){return _sB(_sH,_sG);});},_sJ=new T1(0,2),_sK=function(_sL,_sM){while(1){var _sN=E(_sL);if(!_sN._){var _sO=_sN.a,_sP=E(_sM);if(!_sP._){var _sQ=_sP.a;if(!(imul(_sO,_sQ)|0)){return new T1(0,imul(_sO,_sQ)|0);}else{_sL=new T1(1,I_fromInt(_sO));_sM=new T1(1,I_fromInt(_sQ));continue;}}else{_sL=new T1(1,I_fromInt(_sO));_sM=_sP;continue;}}else{var _sR=E(_sM);if(!_sR._){_sL=_sN;_sM=new T1(1,I_fromInt(_sR.a));continue;}else{return new T1(1,I_mul(_sN.a,_sR.a));}}}},_sS=function(_sT,_sU,_sV){while(1){if(!(_sU%2)){var _sW=B(_sK(_sT,_sT)),_sX=quot(_sU,2);_sT=_sW;_sU=_sX;continue;}else{var _sY=E(_sU);if(_sY==1){return new F(function(){return _sK(_sT,_sV);});}else{var _sW=B(_sK(_sT,_sT)),_sZ=B(_sK(_sT,_sV));_sT=_sW;_sU=quot(_sY-1|0,2);_sV=_sZ;continue;}}}},_t0=function(_t1,_t2){while(1){if(!(_t2%2)){var _t3=B(_sK(_t1,_t1)),_t4=quot(_t2,2);_t1=_t3;_t2=_t4;continue;}else{var _t5=E(_t2);if(_t5==1){return E(_t1);}else{return new F(function(){return _sS(B(_sK(_t1,_t1)),quot(_t5-1|0,2),_t1);});}}}},_t6=function(_t7){return E(E(_t7).c);},_t8=function(_t9){return E(E(_t9).a);},_ta=function(_tb){return E(E(_tb).b);},_tc=function(_td){return E(E(_td).b);},_te=function(_tf){return E(E(_tf).c);},_tg=new T1(0,0),_th=new T1(0,2),_ti=function(_tj){return E(E(_tj).d);},_tk=function(_tl,_tm){var _tn=B(_sx(_tl)),_to=new T(function(){return B(_sz(_tn));}),_tp=new T(function(){return B(A3(_ti,_tl,_tm,new T(function(){return B(A2(_lj,_to,_th));})));});return new F(function(){return A3(_4F,B(_t8(B(_ta(_tn)))),_tp,new T(function(){return B(A2(_lj,_to,_tg));}));});},_tq=new T(function(){return B(unCStr("Negative exponent"));}),_tr=new T(function(){return B(err(_tq));}),_ts=function(_tt){return E(E(_tt).c);},_tu=function(_tv,_tw,_tx,_ty){var _tz=B(_sx(_tw)),_tA=new T(function(){return B(_sz(_tz));}),_tB=B(_ta(_tz));if(!B(A3(_te,_tB,_ty,new T(function(){return B(A2(_lj,_tA,_tg));})))){if(!B(A3(_4F,B(_t8(_tB)),_ty,new T(function(){return B(A2(_lj,_tA,_tg));})))){var _tC=new T(function(){return B(A2(_lj,_tA,_th));}),_tD=new T(function(){return B(A2(_lj,_tA,_f0));}),_tE=B(_t8(_tB)),_tF=function(_tG,_tH,_tI){while(1){var _tJ=B((function(_tK,_tL,_tM){if(!B(_tk(_tw,_tL))){if(!B(A3(_4F,_tE,_tL,_tD))){var _tN=new T(function(){return B(A3(_ts,_tw,new T(function(){return B(A3(_tc,_tA,_tL,_tD));}),_tC));});_tG=new T(function(){return B(A3(_t6,_tv,_tK,_tK));});_tH=_tN;_tI=new T(function(){return B(A3(_t6,_tv,_tK,_tM));});return __continue;}else{return new F(function(){return A3(_t6,_tv,_tK,_tM);});}}else{var _tO=_tM;_tG=new T(function(){return B(A3(_t6,_tv,_tK,_tK));});_tH=new T(function(){return B(A3(_ts,_tw,_tL,_tC));});_tI=_tO;return __continue;}})(_tG,_tH,_tI));if(_tJ!=__continue){return _tJ;}}},_tP=function(_tQ,_tR){while(1){var _tS=B((function(_tT,_tU){if(!B(_tk(_tw,_tU))){if(!B(A3(_4F,_tE,_tU,_tD))){var _tV=new T(function(){return B(A3(_ts,_tw,new T(function(){return B(A3(_tc,_tA,_tU,_tD));}),_tC));});return new F(function(){return _tF(new T(function(){return B(A3(_t6,_tv,_tT,_tT));}),_tV,_tT);});}else{return E(_tT);}}else{_tQ=new T(function(){return B(A3(_t6,_tv,_tT,_tT));});_tR=new T(function(){return B(A3(_ts,_tw,_tU,_tC));});return __continue;}})(_tQ,_tR));if(_tS!=__continue){return _tS;}}};return new F(function(){return _tP(_tx,_ty);});}else{return new F(function(){return A2(_lj,_tv,_f0);});}}else{return E(_tr);}},_tW=new T(function(){return B(err(_tq));}),_tX=function(_tY){var _tZ=I_decodeDouble(_tY);return new T2(0,new T1(1,_tZ.b),_tZ.a);},_u0=function(_u1,_u2){var _u3=B(_tX(_u2)),_u4=_u3.a,_u5=_u3.b,_u6=new T(function(){return B(_sz(new T(function(){return B(_sx(_u1));})));});if(_u5<0){var _u7= -_u5;if(_u7>=0){var _u8=E(_u7);if(!_u8){var _u9=E(_f0);}else{var _u9=B(_t0(_sJ,_u8));}if(!B(_gs(_u9,_gS))){var _ua=B(_gJ(_u4,_u9));return new T2(0,new T(function(){return B(A2(_lj,_u6,_ua.a));}),new T(function(){return B(_go(_ua.b,_u5));}));}else{return E(_dZ);}}else{return E(_tW);}}else{var _ub=new T(function(){var _uc=new T(function(){return B(_tu(_u6,_fX,new T(function(){return B(A2(_lj,_u6,_sJ));}),_u5));});return B(A3(_t6,_u6,new T(function(){return B(A2(_lj,_u6,_u4));}),_uc));});return new T2(0,_ub,_jF);}},_ud=function(_ue,_uf){while(1){var _ug=E(_uf);if(!_ug._){return __Z;}else{var _uh=_ug.b,_ui=E(_ue);if(_ui==1){return E(_uh);}else{_ue=_ui-1|0;_uf=_uh;continue;}}}},_uj=function(_uk,_ul){var _um=E(_ul);if(!_um._){return __Z;}else{var _un=_um.a,_uo=E(_uk);return (_uo==1)?new T2(1,_un,_Z):new T2(1,_un,new T(function(){return B(_uj(_uo-1|0,_um.b));}));}},_up=function(_uq,_ur,_us,_ut){while(1){if(B(_aW(new T2(1,_us,_ut),_ur))!=_uq){var _uu=_ur+1|0;_ur=_uu;continue;}else{if(0>=_ur){return __Z;}else{return new F(function(){return _uj(_ur,new T2(1,_us,_ut));});}}}},_uv=function(_uw,_ux,_uy){var _uz=E(_uy);if(!_uz._){return __Z;}else{var _uA=E(_uw);if(B(_aW(_uz,_ux))!=_uA){return new F(function(){return _up(_uA,_ux+1|0,_uz.a,_uz.b);});}else{if(0>=_ux){return __Z;}else{return new F(function(){return _uj(_ux,_uz);});}}}},_uB=function(_uC,_uD,_uE){var _uF=_uD+1|0;if(_uF>0){return new F(function(){return _ud(_uF,B(_uv(_uC,_uF,_uE)));});}else{return new F(function(){return _uv(_uC,_uF,_uE);});}},_uG=function(_uH,_uI){return (!B(_ae(_uH,_uI)))?true:false;},_uJ=new T2(0,_ae,_uG),_uK=0,_uL=new T(function(){return B(_ic("Event.hs:(81,1)-(82,68)|function addEvent"));}),_uM=function(_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0,_v1,_v2,_v3,_v4,_v5,_v6,_v7,_v8,_v9){while(1){var _va=E(_uN);if(!_va._){return {_:0,a:_uO,b:_uP,c:_uQ,d:_uR,e:_uS,f:_uT,g:_uU,h:_uV,i:_uW,j:_uX,k:_uY,l:_uZ,m:_v0,n:_v1,o:_v2,p:_v3,q:_v4,r:_v5,s:_v6,t:_v7,u:_v8,v:_v9};}else{var _vb=E(_va.b);if(!_vb._){return E(_uL);}else{var _vc=new T2(1,new T2(0,_va.a,_vb.a),_uS),_vd=new T2(1,_uK,_uT);_uN=_vb.b;_uS=_vc;_uT=_vd;continue;}}}},_ve=function(_vf,_vg,_vh){var _vi=E(_vh);if(!_vi._){return __Z;}else{var _vj=_vi.a,_vk=_vi.b;return (!B(A2(_vf,_vg,_vj)))?new T2(1,_vj,new T(function(){return B(_ve(_vf,_vg,_vk));})):E(_vk);}},_vl=function(_vm,_vn){while(1){var _vo=E(_vm);if(!_vo._){return (E(_vn)._==0)?true:false;}else{var _vp=E(_vn);if(!_vp._){return false;}else{if(E(_vo.a)!=E(_vp.a)){return false;}else{_vm=_vo.b;_vn=_vp.b;continue;}}}}},_vq=function(_vr,_vs){while(1){var _vt=E(_vr);if(!_vt._){return (E(_vs)._==0)?true:false;}else{var _vu=E(_vs);if(!_vu._){return false;}else{if(!B(_ae(_vt.a,_vu.a))){return false;}else{_vr=_vt.b;_vs=_vu.b;continue;}}}}},_vv=function(_vw,_vx){switch(E(_vw)){case 0:return (E(_vx)==0)?true:false;case 1:return (E(_vx)==1)?true:false;case 2:return (E(_vx)==2)?true:false;case 3:return (E(_vx)==3)?true:false;case 4:return (E(_vx)==4)?true:false;case 5:return (E(_vx)==5)?true:false;case 6:return (E(_vx)==6)?true:false;case 7:return (E(_vx)==7)?true:false;default:return (E(_vx)==8)?true:false;}},_vy=function(_vz,_vA,_vB,_vC){if(_vz!=_vB){return false;}else{return new F(function(){return _vv(_vA,_vC);});}},_vD=function(_vE,_vF){var _vG=E(_vE),_vH=E(_vF);return new F(function(){return _vy(E(_vG.a),_vG.b,E(_vH.a),_vH.b);});},_vI=function(_vJ,_vK,_vL,_vM){if(_vJ!=_vL){return true;}else{switch(E(_vK)){case 0:return (E(_vM)==0)?false:true;case 1:return (E(_vM)==1)?false:true;case 2:return (E(_vM)==2)?false:true;case 3:return (E(_vM)==3)?false:true;case 4:return (E(_vM)==4)?false:true;case 5:return (E(_vM)==5)?false:true;case 6:return (E(_vM)==6)?false:true;case 7:return (E(_vM)==7)?false:true;default:return (E(_vM)==8)?false:true;}}},_vN=function(_vO,_vP){var _vQ=E(_vO),_vR=E(_vP);return new F(function(){return _vI(E(_vQ.a),_vQ.b,E(_vR.a),_vR.b);});},_vS=new T2(0,_vD,_vN),_vT=0,_vU=function(_vV,_vW){var _vX=E(_vW);if(!_vX._){return 0;}else{var _vY=_vX.b,_vZ=E(_vV),_w0=E(_vX.a),_w1=_w0.b;if(E(_vZ.a)!=E(_w0.a)){return 1+B(_vU(_vZ,_vY))|0;}else{switch(E(_vZ.b)){case 0:return (E(_w1)==0)?0:1+B(_vU(_vZ,_vY))|0;case 1:return (E(_w1)==1)?0:1+B(_vU(_vZ,_vY))|0;case 2:return (E(_w1)==2)?0:1+B(_vU(_vZ,_vY))|0;case 3:return (E(_w1)==3)?0:1+B(_vU(_vZ,_vY))|0;case 4:return (E(_w1)==4)?0:1+B(_vU(_vZ,_vY))|0;case 5:return (E(_w1)==5)?0:1+B(_vU(_vZ,_vY))|0;case 6:return (E(_w1)==6)?0:1+B(_vU(_vZ,_vY))|0;case 7:return (E(_w1)==7)?0:1+B(_vU(_vZ,_vY))|0;default:return (E(_w1)==8)?0:1+B(_vU(_vZ,_vY))|0;}}}},_w2=function(_w3,_w4){return new F(function(){return _vU(_w3,_w4);});},_w5=function(_w6,_w7){var _w8=E(_w7);if(!_w8._){return new T2(0,_vT,_vT);}else{var _w9=_w8.a,_wa=_w8.b;return (!B(_4H(_vS,_w6,_w9)))?new T2(0,new T(function(){return E(B(_w5(_w6,_wa)).a);}),new T(function(){return 1+E(B(_w5(_w6,_wa)).b)|0;})):new T2(0,new T(function(){return B(_w2(_w6,_w9));}),_vT);}},_wb=function(_wc,_wd){while(1){var _we=E(_wd);if(!_we._){return __Z;}else{var _wf=_we.b,_wg=E(_wc);if(_wg==1){return E(_wf);}else{_wc=_wg-1|0;_wd=_wf;continue;}}}},_wh=new T(function(){return B(unCStr("getch"));}),_wi=new T(function(){return B(unCStr("=="));}),_wj=new T(function(){return B(unCStr("&&"));}),_wk=new T(function(){return B(unCStr("||"));}),_wl=new T(function(){return B(unCStr("getpos"));}),_wm=new T(function(){return B(unCStr("ch"));}),_wn=new T(function(){return B(unCStr("tp"));}),_wo=new T2(1,_wn,_Z),_wp=new T2(1,_wm,_wo),_wq=new T2(0,_wl,_wp),_wr=new T(function(){return B(unCStr("a"));}),_ws=new T(function(){return B(unCStr("b"));}),_wt=new T2(1,_ws,_Z),_wu=new T2(1,_wr,_wt),_wv=new T2(0,_wi,_wu),_ww=new T2(0,_wj,_wu),_wx=new T2(0,_wk,_wu),_wy=new T2(1,_wx,_Z),_wz=new T2(1,_ww,_wy),_wA=new T2(1,_wv,_wz),_wB=new T2(1,_wq,_wA),_wC=new T(function(){return B(unCStr("p"));}),_wD=new T(function(){return B(unCStr("q"));}),_wE=new T2(1,_wD,_Z),_wF=new T2(1,_wC,_wE),_wG=new T2(0,_wh,_wF),_wH=new T2(1,_wG,_wB),_wI=new T(function(){return B(unCStr("foldr1"));}),_wJ=new T(function(){return B(_rj(_wI));}),_wK=function(_wL,_wM){var _wN=E(_wM);if(!_wN._){return E(_wJ);}else{var _wO=_wN.a,_wP=E(_wN.b);if(!_wP._){return E(_wO);}else{return new F(function(){return A2(_wL,_wO,new T(function(){return B(_wK(_wL,_wP));}));});}}},_wQ=function(_wR){return E(E(_wR).a);},_wS=function(_wT,_wU,_wV){while(1){var _wW=E(_wV);if(!_wW._){return __Z;}else{var _wX=E(_wW.a);if(!B(A3(_4F,_wT,_wU,_wX.a))){_wV=_wW.b;continue;}else{return new T1(1,_wX.b);}}}},_wY=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_wZ=new T(function(){return B(err(_wY));}),_x0=new T(function(){return B(unCStr("T"));}),_x1=new T(function(){return B(unCStr("F"));}),_x2=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_x3=new T(function(){return B(err(_x2));}),_x4=new T(function(){return B(unCStr("empty"));}),_x5=new T2(1,_x4,_Z),_x6=new T(function(){return B(_ic("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_x7=function(_x8,_x9){while(1){var _xa=B((function(_xb,_xc){var _xd=E(_xb);switch(_xd._){case 0:var _xe=E(_xc);if(!_xe._){return __Z;}else{_x8=B(A1(_xd.a,_xe.a));_x9=_xe.b;return __continue;}break;case 1:var _xf=B(A1(_xd.a,_xc)),_xg=_xc;_x8=_xf;_x9=_xg;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_xd.a,_xc),new T(function(){return B(_x7(_xd.b,_xc));}));default:return E(_xd.a);}})(_x8,_x9));if(_xa!=__continue){return _xa;}}},_xh=function(_xi,_xj){var _xk=function(_xl){var _xm=E(_xj);if(_xm._==3){return new T2(3,_xm.a,new T(function(){return B(_xh(_xi,_xm.b));}));}else{var _xn=E(_xi);if(_xn._==2){return E(_xm);}else{var _xo=E(_xm);if(_xo._==2){return E(_xn);}else{var _xp=function(_xq){var _xr=E(_xo);if(_xr._==4){var _xs=function(_xt){return new T1(4,new T(function(){return B(_x(B(_x7(_xn,_xt)),_xr.a));}));};return new T1(1,_xs);}else{var _xu=E(_xn);if(_xu._==1){var _xv=_xu.a,_xw=E(_xr);if(!_xw._){return new T1(1,function(_xx){return new F(function(){return _xh(B(A1(_xv,_xx)),_xw);});});}else{var _xy=function(_xz){return new F(function(){return _xh(B(A1(_xv,_xz)),new T(function(){return B(A1(_xw.a,_xz));}));});};return new T1(1,_xy);}}else{var _xA=E(_xr);if(!_xA._){return E(_x6);}else{var _xB=function(_xC){return new F(function(){return _xh(_xu,new T(function(){return B(A1(_xA.a,_xC));}));});};return new T1(1,_xB);}}}},_xD=E(_xn);switch(_xD._){case 1:var _xE=E(_xo);if(_xE._==4){var _xF=function(_xG){return new T1(4,new T(function(){return B(_x(B(_x7(B(A1(_xD.a,_xG)),_xG)),_xE.a));}));};return new T1(1,_xF);}else{return new F(function(){return _xp(_);});}break;case 4:var _xH=_xD.a,_xI=E(_xo);switch(_xI._){case 0:var _xJ=function(_xK){var _xL=new T(function(){return B(_x(_xH,new T(function(){return B(_x7(_xI,_xK));},1)));});return new T1(4,_xL);};return new T1(1,_xJ);case 1:var _xM=function(_xN){var _xO=new T(function(){return B(_x(_xH,new T(function(){return B(_x7(B(A1(_xI.a,_xN)),_xN));},1)));});return new T1(4,_xO);};return new T1(1,_xM);default:return new T1(4,new T(function(){return B(_x(_xH,_xI.a));}));}break;default:return new F(function(){return _xp(_);});}}}}},_xP=E(_xi);switch(_xP._){case 0:var _xQ=E(_xj);if(!_xQ._){var _xR=function(_xS){return new F(function(){return _xh(B(A1(_xP.a,_xS)),new T(function(){return B(A1(_xQ.a,_xS));}));});};return new T1(0,_xR);}else{return new F(function(){return _xk(_);});}break;case 3:return new T2(3,_xP.a,new T(function(){return B(_xh(_xP.b,_xj));}));default:return new F(function(){return _xk(_);});}},_xT=new T(function(){return B(unCStr("("));}),_xU=new T(function(){return B(unCStr(")"));}),_xV=function(_xW,_xX){var _xY=E(_xW);switch(_xY._){case 0:return new T1(0,function(_xZ){return new F(function(){return _xV(B(A1(_xY.a,_xZ)),_xX);});});case 1:return new T1(1,function(_y0){return new F(function(){return _xV(B(A1(_xY.a,_y0)),_xX);});});case 2:return new T0(2);case 3:return new F(function(){return _xh(B(A1(_xX,_xY.a)),new T(function(){return B(_xV(_xY.b,_xX));}));});break;default:var _y1=function(_y2){var _y3=E(_y2);if(!_y3._){return __Z;}else{var _y4=E(_y3.a);return new F(function(){return _x(B(_x7(B(A1(_xX,_y4.a)),_y4.b)),new T(function(){return B(_y1(_y3.b));},1));});}},_y5=B(_y1(_xY.a));return (_y5._==0)?new T0(2):new T1(4,_y5);}},_y6=new T0(2),_y7=function(_y8){return new T2(3,_y8,_y6);},_y9=function(_ya,_yb){var _yc=E(_ya);if(!_yc){return new F(function(){return A1(_yb,_kJ);});}else{var _yd=new T(function(){return B(_y9(_yc-1|0,_yb));});return new T1(0,function(_ye){return E(_yd);});}},_yf=function(_yg,_yh,_yi){var _yj=new T(function(){return B(A1(_yg,_y7));}),_yk=function(_yl,_ym,_yn,_yo){while(1){var _yp=B((function(_yq,_yr,_ys,_yt){var _yu=E(_yq);switch(_yu._){case 0:var _yv=E(_yr);if(!_yv._){return new F(function(){return A1(_yh,_yt);});}else{var _yw=_ys+1|0,_yx=_yt;_yl=B(A1(_yu.a,_yv.a));_ym=_yv.b;_yn=_yw;_yo=_yx;return __continue;}break;case 1:var _yy=B(A1(_yu.a,_yr)),_yz=_yr,_yw=_ys,_yx=_yt;_yl=_yy;_ym=_yz;_yn=_yw;_yo=_yx;return __continue;case 2:return new F(function(){return A1(_yh,_yt);});break;case 3:var _yA=new T(function(){return B(_xV(_yu,_yt));});return new F(function(){return _y9(_ys,function(_yB){return E(_yA);});});break;default:return new F(function(){return _xV(_yu,_yt);});}})(_yl,_ym,_yn,_yo));if(_yp!=__continue){return _yp;}}};return function(_yC){return new F(function(){return _yk(_yj,_yC,0,_yi);});};},_yD=function(_yE){return new F(function(){return A1(_yE,_Z);});},_yF=function(_yG,_yH){var _yI=function(_yJ){var _yK=E(_yJ);if(!_yK._){return E(_yD);}else{var _yL=_yK.a;if(!B(A1(_yG,_yL))){return E(_yD);}else{var _yM=new T(function(){return B(_yI(_yK.b));}),_yN=function(_yO){var _yP=new T(function(){return B(A1(_yM,function(_yQ){return new F(function(){return A1(_yO,new T2(1,_yL,_yQ));});}));});return new T1(0,function(_yR){return E(_yP);});};return E(_yN);}}};return function(_yS){return new F(function(){return A2(_yI,_yS,_yH);});};},_yT=new T0(6),_yU=new T(function(){return B(unCStr("valDig: Bad base"));}),_yV=new T(function(){return B(err(_yU));}),_yW=function(_yX,_yY){var _yZ=function(_z0,_z1){var _z2=E(_z0);if(!_z2._){var _z3=new T(function(){return B(A1(_z1,_Z));});return function(_z4){return new F(function(){return A1(_z4,_z3);});};}else{var _z5=E(_z2.a),_z6=function(_z7){var _z8=new T(function(){return B(_yZ(_z2.b,function(_z9){return new F(function(){return A1(_z1,new T2(1,_z7,_z9));});}));}),_za=function(_zb){var _zc=new T(function(){return B(A1(_z8,_zb));});return new T1(0,function(_zd){return E(_zc);});};return E(_za);};switch(E(_yX)){case 8:if(48>_z5){var _ze=new T(function(){return B(A1(_z1,_Z));});return function(_zf){return new F(function(){return A1(_zf,_ze);});};}else{if(_z5>55){var _zg=new T(function(){return B(A1(_z1,_Z));});return function(_zh){return new F(function(){return A1(_zh,_zg);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 10:if(48>_z5){var _zi=new T(function(){return B(A1(_z1,_Z));});return function(_zj){return new F(function(){return A1(_zj,_zi);});};}else{if(_z5>57){var _zk=new T(function(){return B(A1(_z1,_Z));});return function(_zl){return new F(function(){return A1(_zl,_zk);});};}else{return new F(function(){return _z6(_z5-48|0);});}}break;case 16:if(48>_z5){if(97>_z5){if(65>_z5){var _zm=new T(function(){return B(A1(_z1,_Z));});return function(_zn){return new F(function(){return A1(_zn,_zm);});};}else{if(_z5>70){var _zo=new T(function(){return B(A1(_z1,_Z));});return function(_zp){return new F(function(){return A1(_zp,_zo);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zq=new T(function(){return B(A1(_z1,_Z));});return function(_zr){return new F(function(){return A1(_zr,_zq);});};}else{if(_z5>70){var _zs=new T(function(){return B(A1(_z1,_Z));});return function(_zt){return new F(function(){return A1(_zt,_zs);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{if(_z5>57){if(97>_z5){if(65>_z5){var _zu=new T(function(){return B(A1(_z1,_Z));});return function(_zv){return new F(function(){return A1(_zv,_zu);});};}else{if(_z5>70){var _zw=new T(function(){return B(A1(_z1,_Z));});return function(_zx){return new F(function(){return A1(_zx,_zw);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{if(_z5>102){if(65>_z5){var _zy=new T(function(){return B(A1(_z1,_Z));});return function(_zz){return new F(function(){return A1(_zz,_zy);});};}else{if(_z5>70){var _zA=new T(function(){return B(A1(_z1,_Z));});return function(_zB){return new F(function(){return A1(_zB,_zA);});};}else{return new F(function(){return _z6((_z5-65|0)+10|0);});}}}else{return new F(function(){return _z6((_z5-97|0)+10|0);});}}}else{return new F(function(){return _z6(_z5-48|0);});}}break;default:return E(_yV);}}},_zC=function(_zD){var _zE=E(_zD);if(!_zE._){return new T0(2);}else{return new F(function(){return A1(_yY,_zE);});}};return function(_zF){return new F(function(){return A3(_yZ,_zF,_61,_zC);});};},_zG=16,_zH=8,_zI=function(_zJ){var _zK=function(_zL){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zH,_zL)));});},_zM=function(_zN){return new F(function(){return A1(_zJ,new T1(5,new T2(0,_zG,_zN)));});},_zO=function(_zP){switch(E(_zP)){case 79:return new T1(1,B(_yW(_zH,_zK)));case 88:return new T1(1,B(_yW(_zG,_zM)));case 111:return new T1(1,B(_yW(_zH,_zK)));case 120:return new T1(1,B(_yW(_zG,_zM)));default:return new T0(2);}};return function(_zQ){return (E(_zQ)==48)?E(new T1(0,_zO)):new T0(2);};},_zR=function(_zS){return new T1(0,B(_zI(_zS)));},_zT=function(_zU){return new F(function(){return A1(_zU,_2U);});},_zV=function(_zW){return new F(function(){return A1(_zW,_2U);});},_zX=10,_zY=new T1(0,10),_zZ=function(_A0){return new F(function(){return _eW(E(_A0));});},_A1=new T(function(){return B(unCStr("this should not happen"));}),_A2=new T(function(){return B(err(_A1));}),_A3=function(_A4,_A5){var _A6=E(_A5);if(!_A6._){return __Z;}else{var _A7=E(_A6.b);return (_A7._==0)?E(_A2):new T2(1,B(_gA(B(_sK(_A6.a,_A4)),_A7.a)),new T(function(){return B(_A3(_A4,_A7.b));}));}},_A8=new T1(0,0),_A9=function(_Aa,_Ab,_Ac){while(1){var _Ad=B((function(_Ae,_Af,_Ag){var _Ah=E(_Ag);if(!_Ah._){return E(_A8);}else{if(!E(_Ah.b)._){return E(_Ah.a);}else{var _Ai=E(_Af);if(_Ai<=40){var _Aj=function(_Ak,_Al){while(1){var _Am=E(_Al);if(!_Am._){return E(_Ak);}else{var _An=B(_gA(B(_sK(_Ak,_Ae)),_Am.a));_Ak=_An;_Al=_Am.b;continue;}}};return new F(function(){return _Aj(_A8,_Ah);});}else{var _Ao=B(_sK(_Ae,_Ae));if(!(_Ai%2)){var _Ap=B(_A3(_Ae,_Ah));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}else{var _Ap=B(_A3(_Ae,new T2(1,_A8,_Ah)));_Aa=_Ao;_Ab=quot(_Ai+1|0,2);_Ac=_Ap;return __continue;}}}}})(_Aa,_Ab,_Ac));if(_Ad!=__continue){return _Ad;}}},_Aq=function(_Ar,_As){return new F(function(){return _A9(_Ar,new T(function(){return B(_qy(_As,0));},1),B(_aj(_zZ,_As)));});},_At=function(_Au){var _Av=new T(function(){var _Aw=new T(function(){var _Ax=function(_Ay){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_Ay));})));});};return new T1(1,B(_yW(_zX,_Ax)));}),_Az=function(_AA){if(E(_AA)==43){var _AB=function(_AC){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_Aq(_zY,_AC));})));});};return new T1(1,B(_yW(_zX,_AB)));}else{return new T0(2);}},_AD=function(_AE){if(E(_AE)==45){var _AF=function(_AG){return new F(function(){return A1(_Au,new T1(1,new T(function(){return B(_jy(B(_Aq(_zY,_AG))));})));});};return new T1(1,B(_yW(_zX,_AF)));}else{return new T0(2);}};return B(_xh(B(_xh(new T1(0,_AD),new T1(0,_Az))),_Aw));});return new F(function(){return _xh(new T1(0,function(_AH){return (E(_AH)==101)?E(_Av):new T0(2);}),new T1(0,function(_AI){return (E(_AI)==69)?E(_Av):new T0(2);}));});},_AJ=function(_AK){var _AL=function(_AM){return new F(function(){return A1(_AK,new T1(1,_AM));});};return function(_AN){return (E(_AN)==46)?new T1(1,B(_yW(_zX,_AL))):new T0(2);};},_AO=function(_AP){return new T1(0,B(_AJ(_AP)));},_AQ=function(_AR){var _AS=function(_AT){var _AU=function(_AV){return new T1(1,B(_yf(_At,_zT,function(_AW){return new F(function(){return A1(_AR,new T1(5,new T3(1,_AT,_AV,_AW)));});})));};return new T1(1,B(_yf(_AO,_zV,_AU)));};return new F(function(){return _yW(_zX,_AS);});},_AX=function(_AY){return new T1(1,B(_AQ(_AY)));},_AZ=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_B0=function(_B1){return new F(function(){return _4H(_lc,_B1,_AZ);});},_B2=false,_B3=true,_B4=function(_B5){var _B6=new T(function(){return B(A1(_B5,_zH));}),_B7=new T(function(){return B(A1(_B5,_zG));});return function(_B8){switch(E(_B8)){case 79:return E(_B6);case 88:return E(_B7);case 111:return E(_B6);case 120:return E(_B7);default:return new T0(2);}};},_B9=function(_Ba){return new T1(0,B(_B4(_Ba)));},_Bb=function(_Bc){return new F(function(){return A1(_Bc,_zX);});},_Bd=function(_Be){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_H(9,_Be,_Z));}))));});},_Bf=function(_Bg){return new T0(2);},_Bh=function(_Bi){var _Bj=E(_Bi);if(!_Bj._){return E(_Bf);}else{var _Bk=_Bj.a,_Bl=E(_Bj.b);if(!_Bl._){return E(_Bk);}else{var _Bm=new T(function(){return B(_Bh(_Bl));}),_Bn=function(_Bo){return new F(function(){return _xh(B(A1(_Bk,_Bo)),new T(function(){return B(A1(_Bm,_Bo));}));});};return E(_Bn);}}},_Bp=function(_Bq,_Br){var _Bs=function(_Bt,_Bu,_Bv){var _Bw=E(_Bt);if(!_Bw._){return new F(function(){return A1(_Bv,_Bq);});}else{var _Bx=E(_Bu);if(!_Bx._){return new T0(2);}else{if(E(_Bw.a)!=E(_Bx.a)){return new T0(2);}else{var _By=new T(function(){return B(_Bs(_Bw.b,_Bx.b,_Bv));});return new T1(0,function(_Bz){return E(_By);});}}}};return function(_BA){return new F(function(){return _Bs(_Bq,_BA,_Br);});};},_BB=new T(function(){return B(unCStr("SO"));}),_BC=14,_BD=function(_BE){var _BF=new T(function(){return B(A1(_BE,_BC));});return new T1(1,B(_Bp(_BB,function(_BG){return E(_BF);})));},_BH=new T(function(){return B(unCStr("SOH"));}),_BI=1,_BJ=function(_BK){var _BL=new T(function(){return B(A1(_BK,_BI));});return new T1(1,B(_Bp(_BH,function(_BM){return E(_BL);})));},_BN=function(_BO){return new T1(1,B(_yf(_BJ,_BD,_BO)));},_BP=new T(function(){return B(unCStr("NUL"));}),_BQ=0,_BR=function(_BS){var _BT=new T(function(){return B(A1(_BS,_BQ));});return new T1(1,B(_Bp(_BP,function(_BU){return E(_BT);})));},_BV=new T(function(){return B(unCStr("STX"));}),_BW=2,_BX=function(_BY){var _BZ=new T(function(){return B(A1(_BY,_BW));});return new T1(1,B(_Bp(_BV,function(_C0){return E(_BZ);})));},_C1=new T(function(){return B(unCStr("ETX"));}),_C2=3,_C3=function(_C4){var _C5=new T(function(){return B(A1(_C4,_C2));});return new T1(1,B(_Bp(_C1,function(_C6){return E(_C5);})));},_C7=new T(function(){return B(unCStr("EOT"));}),_C8=4,_C9=function(_Ca){var _Cb=new T(function(){return B(A1(_Ca,_C8));});return new T1(1,B(_Bp(_C7,function(_Cc){return E(_Cb);})));},_Cd=new T(function(){return B(unCStr("ENQ"));}),_Ce=5,_Cf=function(_Cg){var _Ch=new T(function(){return B(A1(_Cg,_Ce));});return new T1(1,B(_Bp(_Cd,function(_Ci){return E(_Ch);})));},_Cj=new T(function(){return B(unCStr("ACK"));}),_Ck=6,_Cl=function(_Cm){var _Cn=new T(function(){return B(A1(_Cm,_Ck));});return new T1(1,B(_Bp(_Cj,function(_Co){return E(_Cn);})));},_Cp=new T(function(){return B(unCStr("BEL"));}),_Cq=7,_Cr=function(_Cs){var _Ct=new T(function(){return B(A1(_Cs,_Cq));});return new T1(1,B(_Bp(_Cp,function(_Cu){return E(_Ct);})));},_Cv=new T(function(){return B(unCStr("BS"));}),_Cw=8,_Cx=function(_Cy){var _Cz=new T(function(){return B(A1(_Cy,_Cw));});return new T1(1,B(_Bp(_Cv,function(_CA){return E(_Cz);})));},_CB=new T(function(){return B(unCStr("HT"));}),_CC=9,_CD=function(_CE){var _CF=new T(function(){return B(A1(_CE,_CC));});return new T1(1,B(_Bp(_CB,function(_CG){return E(_CF);})));},_CH=new T(function(){return B(unCStr("LF"));}),_CI=10,_CJ=function(_CK){var _CL=new T(function(){return B(A1(_CK,_CI));});return new T1(1,B(_Bp(_CH,function(_CM){return E(_CL);})));},_CN=new T(function(){return B(unCStr("VT"));}),_CO=11,_CP=function(_CQ){var _CR=new T(function(){return B(A1(_CQ,_CO));});return new T1(1,B(_Bp(_CN,function(_CS){return E(_CR);})));},_CT=new T(function(){return B(unCStr("FF"));}),_CU=12,_CV=function(_CW){var _CX=new T(function(){return B(A1(_CW,_CU));});return new T1(1,B(_Bp(_CT,function(_CY){return E(_CX);})));},_CZ=new T(function(){return B(unCStr("CR"));}),_D0=13,_D1=function(_D2){var _D3=new T(function(){return B(A1(_D2,_D0));});return new T1(1,B(_Bp(_CZ,function(_D4){return E(_D3);})));},_D5=new T(function(){return B(unCStr("SI"));}),_D6=15,_D7=function(_D8){var _D9=new T(function(){return B(A1(_D8,_D6));});return new T1(1,B(_Bp(_D5,function(_Da){return E(_D9);})));},_Db=new T(function(){return B(unCStr("DLE"));}),_Dc=16,_Dd=function(_De){var _Df=new T(function(){return B(A1(_De,_Dc));});return new T1(1,B(_Bp(_Db,function(_Dg){return E(_Df);})));},_Dh=new T(function(){return B(unCStr("DC1"));}),_Di=17,_Dj=function(_Dk){var _Dl=new T(function(){return B(A1(_Dk,_Di));});return new T1(1,B(_Bp(_Dh,function(_Dm){return E(_Dl);})));},_Dn=new T(function(){return B(unCStr("DC2"));}),_Do=18,_Dp=function(_Dq){var _Dr=new T(function(){return B(A1(_Dq,_Do));});return new T1(1,B(_Bp(_Dn,function(_Ds){return E(_Dr);})));},_Dt=new T(function(){return B(unCStr("DC3"));}),_Du=19,_Dv=function(_Dw){var _Dx=new T(function(){return B(A1(_Dw,_Du));});return new T1(1,B(_Bp(_Dt,function(_Dy){return E(_Dx);})));},_Dz=new T(function(){return B(unCStr("DC4"));}),_DA=20,_DB=function(_DC){var _DD=new T(function(){return B(A1(_DC,_DA));});return new T1(1,B(_Bp(_Dz,function(_DE){return E(_DD);})));},_DF=new T(function(){return B(unCStr("NAK"));}),_DG=21,_DH=function(_DI){var _DJ=new T(function(){return B(A1(_DI,_DG));});return new T1(1,B(_Bp(_DF,function(_DK){return E(_DJ);})));},_DL=new T(function(){return B(unCStr("SYN"));}),_DM=22,_DN=function(_DO){var _DP=new T(function(){return B(A1(_DO,_DM));});return new T1(1,B(_Bp(_DL,function(_DQ){return E(_DP);})));},_DR=new T(function(){return B(unCStr("ETB"));}),_DS=23,_DT=function(_DU){var _DV=new T(function(){return B(A1(_DU,_DS));});return new T1(1,B(_Bp(_DR,function(_DW){return E(_DV);})));},_DX=new T(function(){return B(unCStr("CAN"));}),_DY=24,_DZ=function(_E0){var _E1=new T(function(){return B(A1(_E0,_DY));});return new T1(1,B(_Bp(_DX,function(_E2){return E(_E1);})));},_E3=new T(function(){return B(unCStr("EM"));}),_E4=25,_E5=function(_E6){var _E7=new T(function(){return B(A1(_E6,_E4));});return new T1(1,B(_Bp(_E3,function(_E8){return E(_E7);})));},_E9=new T(function(){return B(unCStr("SUB"));}),_Ea=26,_Eb=function(_Ec){var _Ed=new T(function(){return B(A1(_Ec,_Ea));});return new T1(1,B(_Bp(_E9,function(_Ee){return E(_Ed);})));},_Ef=new T(function(){return B(unCStr("ESC"));}),_Eg=27,_Eh=function(_Ei){var _Ej=new T(function(){return B(A1(_Ei,_Eg));});return new T1(1,B(_Bp(_Ef,function(_Ek){return E(_Ej);})));},_El=new T(function(){return B(unCStr("FS"));}),_Em=28,_En=function(_Eo){var _Ep=new T(function(){return B(A1(_Eo,_Em));});return new T1(1,B(_Bp(_El,function(_Eq){return E(_Ep);})));},_Er=new T(function(){return B(unCStr("GS"));}),_Es=29,_Et=function(_Eu){var _Ev=new T(function(){return B(A1(_Eu,_Es));});return new T1(1,B(_Bp(_Er,function(_Ew){return E(_Ev);})));},_Ex=new T(function(){return B(unCStr("RS"));}),_Ey=30,_Ez=function(_EA){var _EB=new T(function(){return B(A1(_EA,_Ey));});return new T1(1,B(_Bp(_Ex,function(_EC){return E(_EB);})));},_ED=new T(function(){return B(unCStr("US"));}),_EE=31,_EF=function(_EG){var _EH=new T(function(){return B(A1(_EG,_EE));});return new T1(1,B(_Bp(_ED,function(_EI){return E(_EH);})));},_EJ=new T(function(){return B(unCStr("SP"));}),_EK=32,_EL=function(_EM){var _EN=new T(function(){return B(A1(_EM,_EK));});return new T1(1,B(_Bp(_EJ,function(_EO){return E(_EN);})));},_EP=new T(function(){return B(unCStr("DEL"));}),_EQ=127,_ER=function(_ES){var _ET=new T(function(){return B(A1(_ES,_EQ));});return new T1(1,B(_Bp(_EP,function(_EU){return E(_ET);})));},_EV=new T2(1,_ER,_Z),_EW=new T2(1,_EL,_EV),_EX=new T2(1,_EF,_EW),_EY=new T2(1,_Ez,_EX),_EZ=new T2(1,_Et,_EY),_F0=new T2(1,_En,_EZ),_F1=new T2(1,_Eh,_F0),_F2=new T2(1,_Eb,_F1),_F3=new T2(1,_E5,_F2),_F4=new T2(1,_DZ,_F3),_F5=new T2(1,_DT,_F4),_F6=new T2(1,_DN,_F5),_F7=new T2(1,_DH,_F6),_F8=new T2(1,_DB,_F7),_F9=new T2(1,_Dv,_F8),_Fa=new T2(1,_Dp,_F9),_Fb=new T2(1,_Dj,_Fa),_Fc=new T2(1,_Dd,_Fb),_Fd=new T2(1,_D7,_Fc),_Fe=new T2(1,_D1,_Fd),_Ff=new T2(1,_CV,_Fe),_Fg=new T2(1,_CP,_Ff),_Fh=new T2(1,_CJ,_Fg),_Fi=new T2(1,_CD,_Fh),_Fj=new T2(1,_Cx,_Fi),_Fk=new T2(1,_Cr,_Fj),_Fl=new T2(1,_Cl,_Fk),_Fm=new T2(1,_Cf,_Fl),_Fn=new T2(1,_C9,_Fm),_Fo=new T2(1,_C3,_Fn),_Fp=new T2(1,_BX,_Fo),_Fq=new T2(1,_BR,_Fp),_Fr=new T2(1,_BN,_Fq),_Fs=new T(function(){return B(_Bh(_Fr));}),_Ft=34,_Fu=new T1(0,1114111),_Fv=92,_Fw=39,_Fx=function(_Fy){var _Fz=new T(function(){return B(A1(_Fy,_Cq));}),_FA=new T(function(){return B(A1(_Fy,_Cw));}),_FB=new T(function(){return B(A1(_Fy,_CC));}),_FC=new T(function(){return B(A1(_Fy,_CI));}),_FD=new T(function(){return B(A1(_Fy,_CO));}),_FE=new T(function(){return B(A1(_Fy,_CU));}),_FF=new T(function(){return B(A1(_Fy,_D0));}),_FG=new T(function(){return B(A1(_Fy,_Fv));}),_FH=new T(function(){return B(A1(_Fy,_Fw));}),_FI=new T(function(){return B(A1(_Fy,_Ft));}),_FJ=new T(function(){var _FK=function(_FL){var _FM=new T(function(){return B(_eW(E(_FL)));}),_FN=function(_FO){var _FP=B(_Aq(_FM,_FO));if(!B(_iE(_FP,_Fu))){return new T0(2);}else{return new F(function(){return A1(_Fy,new T(function(){var _FQ=B(_ff(_FP));if(_FQ>>>0>1114111){return B(_Bd(_FQ));}else{return _FQ;}}));});}};return new T1(1,B(_yW(_FL,_FN)));},_FR=new T(function(){var _FS=new T(function(){return B(A1(_Fy,_EE));}),_FT=new T(function(){return B(A1(_Fy,_Ey));}),_FU=new T(function(){return B(A1(_Fy,_Es));}),_FV=new T(function(){return B(A1(_Fy,_Em));}),_FW=new T(function(){return B(A1(_Fy,_Eg));}),_FX=new T(function(){return B(A1(_Fy,_Ea));}),_FY=new T(function(){return B(A1(_Fy,_E4));}),_FZ=new T(function(){return B(A1(_Fy,_DY));}),_G0=new T(function(){return B(A1(_Fy,_DS));}),_G1=new T(function(){return B(A1(_Fy,_DM));}),_G2=new T(function(){return B(A1(_Fy,_DG));}),_G3=new T(function(){return B(A1(_Fy,_DA));}),_G4=new T(function(){return B(A1(_Fy,_Du));}),_G5=new T(function(){return B(A1(_Fy,_Do));}),_G6=new T(function(){return B(A1(_Fy,_Di));}),_G7=new T(function(){return B(A1(_Fy,_Dc));}),_G8=new T(function(){return B(A1(_Fy,_D6));}),_G9=new T(function(){return B(A1(_Fy,_BC));}),_Ga=new T(function(){return B(A1(_Fy,_Ck));}),_Gb=new T(function(){return B(A1(_Fy,_Ce));}),_Gc=new T(function(){return B(A1(_Fy,_C8));}),_Gd=new T(function(){return B(A1(_Fy,_C2));}),_Ge=new T(function(){return B(A1(_Fy,_BW));}),_Gf=new T(function(){return B(A1(_Fy,_BI));}),_Gg=new T(function(){return B(A1(_Fy,_BQ));}),_Gh=function(_Gi){switch(E(_Gi)){case 64:return E(_Gg);case 65:return E(_Gf);case 66:return E(_Ge);case 67:return E(_Gd);case 68:return E(_Gc);case 69:return E(_Gb);case 70:return E(_Ga);case 71:return E(_Fz);case 72:return E(_FA);case 73:return E(_FB);case 74:return E(_FC);case 75:return E(_FD);case 76:return E(_FE);case 77:return E(_FF);case 78:return E(_G9);case 79:return E(_G8);case 80:return E(_G7);case 81:return E(_G6);case 82:return E(_G5);case 83:return E(_G4);case 84:return E(_G3);case 85:return E(_G2);case 86:return E(_G1);case 87:return E(_G0);case 88:return E(_FZ);case 89:return E(_FY);case 90:return E(_FX);case 91:return E(_FW);case 92:return E(_FV);case 93:return E(_FU);case 94:return E(_FT);case 95:return E(_FS);default:return new T0(2);}};return B(_xh(new T1(0,function(_Gj){return (E(_Gj)==94)?E(new T1(0,_Gh)):new T0(2);}),new T(function(){return B(A1(_Fs,_Fy));})));});return B(_xh(new T1(1,B(_yf(_B9,_Bb,_FK))),_FR));});return new F(function(){return _xh(new T1(0,function(_Gk){switch(E(_Gk)){case 34:return E(_FI);case 39:return E(_FH);case 92:return E(_FG);case 97:return E(_Fz);case 98:return E(_FA);case 102:return E(_FE);case 110:return E(_FC);case 114:return E(_FF);case 116:return E(_FB);case 118:return E(_FD);default:return new T0(2);}}),_FJ);});},_Gl=function(_Gm){return new F(function(){return A1(_Gm,_kJ);});},_Gn=function(_Go){var _Gp=E(_Go);if(!_Gp._){return E(_Gl);}else{var _Gq=E(_Gp.a),_Gr=_Gq>>>0,_Gs=new T(function(){return B(_Gn(_Gp.b));});if(_Gr>887){var _Gt=u_iswspace(_Gq);if(!E(_Gt)){return E(_Gl);}else{var _Gu=function(_Gv){var _Gw=new T(function(){return B(A1(_Gs,_Gv));});return new T1(0,function(_Gx){return E(_Gw);});};return E(_Gu);}}else{var _Gy=E(_Gr);if(_Gy==32){var _Gz=function(_GA){var _GB=new T(function(){return B(A1(_Gs,_GA));});return new T1(0,function(_GC){return E(_GB);});};return E(_Gz);}else{if(_Gy-9>>>0>4){if(E(_Gy)==160){var _GD=function(_GE){var _GF=new T(function(){return B(A1(_Gs,_GE));});return new T1(0,function(_GG){return E(_GF);});};return E(_GD);}else{return E(_Gl);}}else{var _GH=function(_GI){var _GJ=new T(function(){return B(A1(_Gs,_GI));});return new T1(0,function(_GK){return E(_GJ);});};return E(_GH);}}}}},_GL=function(_GM){var _GN=new T(function(){return B(_GL(_GM));}),_GO=function(_GP){return (E(_GP)==92)?E(_GN):new T0(2);},_GQ=function(_GR){return E(new T1(0,_GO));},_GS=new T1(1,function(_GT){return new F(function(){return A2(_Gn,_GT,_GQ);});}),_GU=new T(function(){return B(_Fx(function(_GV){return new F(function(){return A1(_GM,new T2(0,_GV,_B3));});}));}),_GW=function(_GX){var _GY=E(_GX);if(_GY==38){return E(_GN);}else{var _GZ=_GY>>>0;if(_GZ>887){var _H0=u_iswspace(_GY);return (E(_H0)==0)?new T0(2):E(_GS);}else{var _H1=E(_GZ);return (_H1==32)?E(_GS):(_H1-9>>>0>4)?(E(_H1)==160)?E(_GS):new T0(2):E(_GS);}}};return new F(function(){return _xh(new T1(0,function(_H2){return (E(_H2)==92)?E(new T1(0,_GW)):new T0(2);}),new T1(0,function(_H3){var _H4=E(_H3);if(E(_H4)==92){return E(_GU);}else{return new F(function(){return A1(_GM,new T2(0,_H4,_B2));});}}));});},_H5=function(_H6,_H7){var _H8=new T(function(){return B(A1(_H7,new T1(1,new T(function(){return B(A1(_H6,_Z));}))));}),_H9=function(_Ha){var _Hb=E(_Ha),_Hc=E(_Hb.a);if(E(_Hc)==34){if(!E(_Hb.b)){return E(_H8);}else{return new F(function(){return _H5(function(_Hd){return new F(function(){return A1(_H6,new T2(1,_Hc,_Hd));});},_H7);});}}else{return new F(function(){return _H5(function(_He){return new F(function(){return A1(_H6,new T2(1,_Hc,_He));});},_H7);});}};return new F(function(){return _GL(_H9);});},_Hf=new T(function(){return B(unCStr("_\'"));}),_Hg=function(_Hh){var _Hi=u_iswalnum(_Hh);if(!E(_Hi)){return new F(function(){return _4H(_lc,_Hh,_Hf);});}else{return true;}},_Hj=function(_Hk){return new F(function(){return _Hg(E(_Hk));});},_Hl=new T(function(){return B(unCStr(",;()[]{}`"));}),_Hm=new T(function(){return B(unCStr("=>"));}),_Hn=new T2(1,_Hm,_Z),_Ho=new T(function(){return B(unCStr("~"));}),_Hp=new T2(1,_Ho,_Hn),_Hq=new T(function(){return B(unCStr("@"));}),_Hr=new T2(1,_Hq,_Hp),_Hs=new T(function(){return B(unCStr("->"));}),_Ht=new T2(1,_Hs,_Hr),_Hu=new T(function(){return B(unCStr("<-"));}),_Hv=new T2(1,_Hu,_Ht),_Hw=new T(function(){return B(unCStr("|"));}),_Hx=new T2(1,_Hw,_Hv),_Hy=new T(function(){return B(unCStr("\\"));}),_Hz=new T2(1,_Hy,_Hx),_HA=new T(function(){return B(unCStr("="));}),_HB=new T2(1,_HA,_Hz),_HC=new T(function(){return B(unCStr("::"));}),_HD=new T2(1,_HC,_HB),_HE=new T(function(){return B(unCStr(".."));}),_HF=new T2(1,_HE,_HD),_HG=function(_HH){var _HI=new T(function(){return B(A1(_HH,_yT));}),_HJ=new T(function(){var _HK=new T(function(){var _HL=function(_HM){var _HN=new T(function(){return B(A1(_HH,new T1(0,_HM)));});return new T1(0,function(_HO){return (E(_HO)==39)?E(_HN):new T0(2);});};return B(_Fx(_HL));}),_HP=function(_HQ){var _HR=E(_HQ);switch(E(_HR)){case 39:return new T0(2);case 92:return E(_HK);default:var _HS=new T(function(){return B(A1(_HH,new T1(0,_HR)));});return new T1(0,function(_HT){return (E(_HT)==39)?E(_HS):new T0(2);});}},_HU=new T(function(){var _HV=new T(function(){return B(_H5(_61,_HH));}),_HW=new T(function(){var _HX=new T(function(){var _HY=new T(function(){var _HZ=function(_I0){var _I1=E(_I0),_I2=u_iswalpha(_I1);return (E(_I2)==0)?(E(_I1)==95)?new T1(1,B(_yF(_Hj,function(_I3){return new F(function(){return A1(_HH,new T1(3,new T2(1,_I1,_I3)));});}))):new T0(2):new T1(1,B(_yF(_Hj,function(_I4){return new F(function(){return A1(_HH,new T1(3,new T2(1,_I1,_I4)));});})));};return B(_xh(new T1(0,_HZ),new T(function(){return new T1(1,B(_yf(_zR,_AX,_HH)));})));}),_I5=function(_I6){return (!B(_4H(_lc,_I6,_AZ)))?new T0(2):new T1(1,B(_yF(_B0,function(_I7){var _I8=new T2(1,_I6,_I7);if(!B(_4H(_uJ,_I8,_HF))){return new F(function(){return A1(_HH,new T1(4,_I8));});}else{return new F(function(){return A1(_HH,new T1(2,_I8));});}})));};return B(_xh(new T1(0,_I5),_HY));});return B(_xh(new T1(0,function(_I9){if(!B(_4H(_lc,_I9,_Hl))){return new T0(2);}else{return new F(function(){return A1(_HH,new T1(2,new T2(1,_I9,_Z)));});}}),_HX));});return B(_xh(new T1(0,function(_Ia){return (E(_Ia)==34)?E(_HV):new T0(2);}),_HW));});return B(_xh(new T1(0,function(_Ib){return (E(_Ib)==39)?E(new T1(0,_HP)):new T0(2);}),_HU));});return new F(function(){return _xh(new T1(1,function(_Ic){return (E(_Ic)._==0)?E(_HI):new T0(2);}),_HJ);});},_Id=0,_Ie=function(_If,_Ig){var _Ih=new T(function(){var _Ii=new T(function(){var _Ij=function(_Ik){var _Il=new T(function(){var _Im=new T(function(){return B(A1(_Ig,_Ik));});return B(_HG(function(_In){var _Io=E(_In);return (_Io._==2)?(!B(_vl(_Io.a,_xU)))?new T0(2):E(_Im):new T0(2);}));}),_Ip=function(_Iq){return E(_Il);};return new T1(1,function(_Ir){return new F(function(){return A2(_Gn,_Ir,_Ip);});});};return B(A2(_If,_Id,_Ij));});return B(_HG(function(_Is){var _It=E(_Is);return (_It._==2)?(!B(_vl(_It.a,_xT)))?new T0(2):E(_Ii):new T0(2);}));}),_Iu=function(_Iv){return E(_Ih);};return function(_Iw){return new F(function(){return A2(_Gn,_Iw,_Iu);});};},_Ix=function(_Iy,_Iz){var _IA=function(_IB){var _IC=new T(function(){return B(A1(_Iy,_IB));}),_ID=function(_IE){return new F(function(){return _xh(B(A1(_IC,_IE)),new T(function(){return new T1(1,B(_Ie(_IA,_IE)));}));});};return E(_ID);},_IF=new T(function(){return B(A1(_Iy,_Iz));}),_IG=function(_IH){return new F(function(){return _xh(B(A1(_IF,_IH)),new T(function(){return new T1(1,B(_Ie(_IA,_IH)));}));});};return E(_IG);},_II=0,_IJ=function(_IK,_IL){return new F(function(){return A1(_IL,_II);});},_IM=new T(function(){return B(unCStr("Fr"));}),_IN=new T2(0,_IM,_IJ),_IO=1,_IP=function(_IQ,_IR){return new F(function(){return A1(_IR,_IO);});},_IS=new T(function(){return B(unCStr("Bl"));}),_IT=new T2(0,_IS,_IP),_IU=2,_IV=function(_IW,_IX){return new F(function(){return A1(_IX,_IU);});},_IY=new T(function(){return B(unCStr("Ex"));}),_IZ=new T2(0,_IY,_IV),_J0=3,_J1=function(_J2,_J3){return new F(function(){return A1(_J3,_J0);});},_J4=new T(function(){return B(unCStr("Mv"));}),_J5=new T2(0,_J4,_J1),_J6=4,_J7=function(_J8,_J9){return new F(function(){return A1(_J9,_J6);});},_Ja=new T(function(){return B(unCStr("Pn"));}),_Jb=new T2(0,_Ja,_J7),_Jc=8,_Jd=function(_Je,_Jf){return new F(function(){return A1(_Jf,_Jc);});},_Jg=new T(function(){return B(unCStr("DF"));}),_Jh=new T2(0,_Jg,_Jd),_Ji=new T2(1,_Jh,_Z),_Jj=7,_Jk=function(_Jl,_Jm){return new F(function(){return A1(_Jm,_Jj);});},_Jn=new T(function(){return B(unCStr("DB"));}),_Jo=new T2(0,_Jn,_Jk),_Jp=new T2(1,_Jo,_Ji),_Jq=6,_Jr=function(_Js,_Jt){return new F(function(){return A1(_Jt,_Jq);});},_Ju=new T(function(){return B(unCStr("Cm"));}),_Jv=new T2(0,_Ju,_Jr),_Jw=new T2(1,_Jv,_Jp),_Jx=5,_Jy=function(_Jz,_JA){return new F(function(){return A1(_JA,_Jx);});},_JB=new T(function(){return B(unCStr("Wn"));}),_JC=new T2(0,_JB,_Jy),_JD=new T2(1,_JC,_Jw),_JE=new T2(1,_Jb,_JD),_JF=new T2(1,_J5,_JE),_JG=new T2(1,_IZ,_JF),_JH=new T2(1,_IT,_JG),_JI=new T2(1,_IN,_JH),_JJ=function(_JK,_JL,_JM){var _JN=E(_JK);if(!_JN._){return new T0(2);}else{var _JO=E(_JN.a),_JP=_JO.a,_JQ=new T(function(){return B(A2(_JO.b,_JL,_JM));}),_JR=new T(function(){return B(_HG(function(_JS){var _JT=E(_JS);switch(_JT._){case 3:return (!B(_vl(_JP,_JT.a)))?new T0(2):E(_JQ);case 4:return (!B(_vl(_JP,_JT.a)))?new T0(2):E(_JQ);default:return new T0(2);}}));}),_JU=function(_JV){return E(_JR);};return new F(function(){return _xh(new T1(1,function(_JW){return new F(function(){return A2(_Gn,_JW,_JU);});}),new T(function(){return B(_JJ(_JN.b,_JL,_JM));}));});}},_JX=function(_JY,_JZ){return new F(function(){return _JJ(_JI,_JY,_JZ);});},_K0=function(_K1){var _K2=function(_K3){return E(new T2(3,_K1,_y6));};return new T1(1,function(_K4){return new F(function(){return A2(_Gn,_K4,_K2);});});},_K5=new T(function(){return B(A3(_Ix,_JX,_Id,_K0));}),_K6=new T(function(){return B(err(_wY));}),_K7=new T(function(){return B(err(_x2));}),_K8=function(_K9,_Ka){var _Kb=function(_Kc,_Kd){var _Ke=function(_Kf){return new F(function(){return A1(_Kd,new T(function(){return  -E(_Kf);}));});},_Kg=new T(function(){return B(_HG(function(_Kh){return new F(function(){return A3(_K9,_Kh,_Kc,_Ke);});}));}),_Ki=function(_Kj){return E(_Kg);},_Kk=function(_Kl){return new F(function(){return A2(_Gn,_Kl,_Ki);});},_Km=new T(function(){return B(_HG(function(_Kn){var _Ko=E(_Kn);if(_Ko._==4){var _Kp=E(_Ko.a);if(!_Kp._){return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}else{if(E(_Kp.a)==45){if(!E(_Kp.b)._){return E(new T1(1,_Kk));}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}}else{return new F(function(){return A3(_K9,_Ko,_Kc,_Kd);});}}));}),_Kq=function(_Kr){return E(_Km);};return new T1(1,function(_Ks){return new F(function(){return A2(_Gn,_Ks,_Kq);});});};return new F(function(){return _Ix(_Kb,_Ka);});},_Kt=function(_Ku){var _Kv=E(_Ku);if(!_Kv._){var _Kw=_Kv.b,_Kx=new T(function(){return B(_A9(new T(function(){return B(_eW(E(_Kv.a)));}),new T(function(){return B(_qy(_Kw,0));},1),B(_aj(_zZ,_Kw))));});return new T1(1,_Kx);}else{return (E(_Kv.b)._==0)?(E(_Kv.c)._==0)?new T1(1,new T(function(){return B(_Aq(_zY,_Kv.a));})):__Z:__Z;}},_Ky=function(_Kz,_KA){return new T0(2);},_KB=function(_KC){var _KD=E(_KC);if(_KD._==5){var _KE=B(_Kt(_KD.a));if(!_KE._){return E(_Ky);}else{var _KF=new T(function(){return B(_ff(_KE.a));});return function(_KG,_KH){return new F(function(){return A1(_KH,_KF);});};}}else{return E(_Ky);}},_KI=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_KJ=new T2(1,_F,_Z),_KK=function(_KL){while(1){var _KM=B((function(_KN){var _KO=E(_KN);if(!_KO._){return __Z;}else{var _KP=_KO.b,_KQ=E(_KO.a);if(!E(_KQ.b)._){return new T2(1,_KQ.a,new T(function(){return B(_KK(_KP));}));}else{_KL=_KP;return __continue;}}})(_KL));if(_KM!=__continue){return _KM;}}},_KR=function(_KS,_KT){while(1){var _KU=E(_KS);if(!_KU._){return E(_KT);}else{var _KV=new T2(1,_KU.a,_KT);_KS=_KU.b;_KT=_KV;continue;}}},_KW=function(_KX,_KY){var _KZ=E(_KX);if(!_KZ._){return __Z;}else{var _L0=E(_KY);return (_L0._==0)?__Z:new T2(1,new T2(0,_KZ.a,_L0.a),new T(function(){return B(_KW(_KZ.b,_L0.b));}));}},_L1=function(_L2,_L3,_L4){while(1){var _L5=B((function(_L6,_L7,_L8){var _L9=E(_L8);if(!_L9._){return E(_L7);}else{var _La=_L9.a,_Lb=_L9.b,_Lc=B(_wS(_uJ,_La,_wH));if(!_Lc._){var _Ld=E(_x5);}else{var _Ld=E(_Lc.a);}if(!B(_vq(_Ld,_x5))){var _Le=B(_KR(B(_KW(B(_KR(_L7,_Z)),new T(function(){return B(_KR(_Ld,_Z));},1))),_Z)),_Lf=B(_qy(_Le,0)),_Lg=new T(function(){var _Lh=B(_aj(_wQ,_Le));if(!_Lh._){return __Z;}else{var _Li=_Lh.a,_Lj=E(_Lh.b);if(!_Lj._){return __Z;}else{var _Lk=_Lj.a;if(!E(_Lj.b)._){if(!B(_vl(_La,_wj))){if(!B(_vl(_La,_wi))){if(!B(_vl(_La,_wh))){if(!B(_vl(_La,_wl))){if(!B(_vl(_La,_wk))){return __Z;}else{if(!B(_vl(_Li,_x0))){if(!B(_vl(_Lk,_x0))){return E(_x1);}else{return E(_x0);}}else{return E(_x0);}}}else{var _Ll=B(_w5(new T2(0,new T(function(){var _Lm=E(_Li);if(!_Lm._){return E(_rm);}else{return E(_Lm.a);}}),new T(function(){var _Ln=B(_KK(B(_x7(_K5,_Lk))));if(!_Ln._){return E(_wZ);}else{if(!E(_Ln.b)._){return E(_Ln.a);}else{return E(_x3);}}})),E(E(_L6).a).b)),_Lo=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_Lp){return new F(function(){return _H(0,E(_Ll.a),_Lp);});},new T2(1,function(_Lq){return new F(function(){return _H(0,E(_Ll.b),_Lq);});},_Z)),_KJ));});return new T2(1,_G,_Lo);}}else{return new T2(1,new T(function(){var _Lr=B(_KK(B(_x7(_KI,_Li))));if(!_Lr._){return E(_K6);}else{if(!E(_Lr.b)._){var _Ls=B(_KK(B(_x7(_KI,_Lk))));if(!_Ls._){return E(_K6);}else{if(!E(_Ls.b)._){return E(B(_aW(B(_aW(E(E(_L6).a).b,E(_Ls.a))),E(_Lr.a))).a);}else{return E(_K7);}}}else{return E(_K7);}}}),_Z);}}else{if(!B(_vl(_Li,_Lk))){return E(_x1);}else{return E(_x0);}}}else{if(!B(_vl(_Li,_x0))){return E(_x1);}else{if(!B(_vl(_Lk,_x0))){return E(_x1);}else{return E(_x0);}}}}else{return __Z;}}}});if(_Lf>0){var _Lt=_L6,_Lu=B(_x(B(_KR(B(_wb(_Lf,B(_KR(_L7,_Z)))),_Z)),new T2(1,_Lg,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}else{var _Lt=_L6,_Lu=B(_x(B(_KR(B(_KR(_L7,_Z)),_Z)),new T2(1,_Lg,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}}else{var _Lt=_L6,_Lu=B(_x(_L7,new T2(1,_La,_Z)));_L2=_Lt;_L3=_Lu;_L4=_Lb;return __continue;}}})(_L2,_L3,_L4));if(_L5!=__continue){return _L5;}}},_Lv=new T(function(){return B(_ic("Event.hs:(102,1)-(106,73)|function addMemory"));}),_Lw=function(_Lx,_Ly){var _Lz=E(_Lx),_LA=E(_Ly);if(!B(_vl(_Lz.a,_LA.a))){return false;}else{return new F(function(){return _vl(_Lz.b,_LA.b);});}},_LB=new T2(1,_Z,_Z),_LC=function(_LD,_LE,_LF){var _LG=E(_LF);if(!_LG._){return new T2(0,new T2(1,_LE,_Z),_Z);}else{var _LH=E(_LE),_LI=new T(function(){var _LJ=B(_LC(_LD,_LG.a,_LG.b));return new T2(0,_LJ.a,_LJ.b);});return (_LD!=_LH)?new T2(0,new T2(1,_LH,new T(function(){return E(E(_LI).a);})),new T(function(){return E(E(_LI).b);})):new T2(0,_Z,new T2(1,new T(function(){return E(E(_LI).a);}),new T(function(){return E(E(_LI).b);})));}},_LK=32,_LL=function(_LM){var _LN=E(_LM);if(!_LN._){return __Z;}else{var _LO=new T(function(){return B(_x(_LN.a,new T(function(){return B(_LL(_LN.b));},1)));});return new T2(1,_LK,_LO);}},_LP=function(_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc){while(1){var _Md=B((function(_Me,_Mf,_Mg,_Mh,_Mi,_Mj,_Mk,_Ml,_Mm,_Mn,_Mo,_Mp,_Mq,_Mr,_Ms,_Mt,_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA){var _MB=E(_Me);if(!_MB._){return {_:0,a:_Mf,b:_Mg,c:_Mh,d:_Mi,e:_Mj,f:_Mk,g:_Ml,h:_Mm,i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:_Mr,n:_Ms,o:_Mt,p:_Mu,q:_Mv,r:_Mw,s:_Mx,t:_My,u:_Mz,v:_MA};}else{var _MC=_MB.a,_MD=E(_MB.b);if(!_MD._){return E(_Lv);}else{var _ME=new T(function(){var _MF=E(_MD.a);if(!_MF._){var _MG=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,_LB));if(!_MG._){return __Z;}else{return B(_x(_MG.a,new T(function(){return B(_LL(_MG.b));},1)));}}else{var _MH=_MF.a,_MI=E(_MF.b);if(!_MI._){var _MJ=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,new T2(1,_MH,_Z),_Z)));if(!_MJ._){return __Z;}else{return B(_x(_MJ.a,new T(function(){return B(_LL(_MJ.b));},1)));}}else{var _MK=E(_MH),_ML=new T(function(){var _MM=B(_LC(95,_MI.a,_MI.b));return new T2(0,_MM.a,_MM.b);});if(E(_MK)==95){var _MN=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,_Z,new T2(1,new T(function(){return E(E(_ML).a);}),new T(function(){return E(E(_ML).b);})))));if(!_MN._){return __Z;}else{return B(_x(_MN.a,new T(function(){return B(_LL(_MN.b));},1)));}}else{var _MO=B(_L1({_:0,a:E(_Mf),b:E(_Mg),c:E(_Mh),d:E(_Mi),e:E(_Mj),f:E(_Mk),g:E(_Ml),h:E(_Mm),i:_Mn,j:_Mo,k:_Mp,l:_Mq,m:E(_Mr),n:_Ms,o:E(_Mt),p:E(_Mu),q:_Mv,r:E(_Mw),s:E(_Mx),t:_My,u:E(_Mz),v:E(_MA)},_Z,new T2(1,new T2(1,_MK,new T(function(){return E(E(_ML).a);})),new T(function(){return E(E(_ML).b);}))));if(!_MO._){return __Z;}else{return B(_x(_MO.a,new T(function(){return B(_LL(_MO.b));},1)));}}}}}),_MP=_Mf,_MQ=_Mg,_MR=_Mh,_MS=_Mi,_MT=_Mj,_MU=_Mk,_MV=_Mm,_MW=_Mn,_MX=_Mo,_MY=_Mp,_MZ=_Mq,_N0=_Mr,_N1=_Ms,_N2=_Mt,_N3=_Mu,_N4=_Mv,_N5=_Mw,_N6=_Mx,_N7=_My,_N8=_Mz,_N9=_MA;_LQ=_MD.b;_LR=_MP;_LS=_MQ;_LT=_MR;_LU=_MS;_LV=_MT;_LW=_MU;_LX=new T2(1,new T2(0,_MC,_ME),new T(function(){var _Na=B(_wS(_uJ,_MC,_Ml));if(!_Na._){var _Nb=__Z;}else{var _Nb=E(_Na.a);}if(!B(_vl(_Nb,_Z))){return B(_ve(_Lw,new T2(0,_MC,_Nb),_Ml));}else{return E(_Ml);}}));_LY=_MV;_LZ=_MW;_M0=_MX;_M1=_MY;_M2=_MZ;_M3=_N0;_M4=_N1;_M5=_N2;_M6=_N3;_M7=_N4;_M8=_N5;_M9=_N6;_Ma=_N7;_Mb=_N8;_Mc=_N9;return __continue;}}})(_LQ,_LR,_LS,_LT,_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6,_M7,_M8,_M9,_Ma,_Mb,_Mc));if(_Md!=__continue){return _Md;}}},_Nc=function(_Nd){var _Ne=E(_Nd);if(!_Ne._){return new T2(0,_Z,_Z);}else{var _Nf=E(_Ne.a),_Ng=new T(function(){var _Nh=B(_Nc(_Ne.b));return new T2(0,_Nh.a,_Nh.b);});return new T2(0,new T2(1,_Nf.a,new T(function(){return E(E(_Ng).a);})),new T2(1,_Nf.b,new T(function(){return E(E(_Ng).b);})));}},_Ni=function(_Nj,_Nk,_Nl){while(1){var _Nm=B((function(_Nn,_No,_Np){var _Nq=E(_Np);if(!_Nq._){return __Z;}else{var _Nr=_Nq.b;if(_No!=E(_Nq.a)){var _Ns=_Nn+1|0,_Nt=_No;_Nj=_Ns;_Nk=_Nt;_Nl=_Nr;return __continue;}else{return new T2(1,_Nn,new T(function(){return B(_Ni(_Nn+1|0,_No,_Nr));}));}}})(_Nj,_Nk,_Nl));if(_Nm!=__continue){return _Nm;}}},_Nu=function(_Nv,_Nw,_Nx){var _Ny=E(_Nx);if(!_Ny._){return __Z;}else{var _Nz=_Ny.b,_NA=E(_Nw);if(_NA!=E(_Ny.a)){return new F(function(){return _Ni(_Nv+1|0,_NA,_Nz);});}else{return new T2(1,_Nv,new T(function(){return B(_Ni(_Nv+1|0,_NA,_Nz));}));}}},_NB=function(_NC,_ND,_NE,_NF){var _NG=E(_NF);if(!_NG._){return __Z;}else{var _NH=_NG.b;return (!B(_4H(_3S,_NC,_NE)))?new T2(1,_NG.a,new T(function(){return B(_NB(_NC+1|0,_ND,_NE,_NH));})):new T2(1,_ND,new T(function(){return B(_NB(_NC+1|0,_ND,_NE,_NH));}));}},_NI=function(_NJ,_NK,_NL){var _NM=E(_NL);if(!_NM._){return __Z;}else{var _NN=new T(function(){var _NO=B(_Nc(_NM.a)),_NP=_NO.a,_NQ=new T(function(){return B(_NB(0,_NK,new T(function(){return B(_Nu(0,_NJ,_NP));}),_NO.b));},1);return B(_KW(_NP,_NQ));});return new T2(1,_NN,new T(function(){return B(_NI(_NJ,_NK,_NM.b));}));}},_NR=function(_NS){var _NT=E(_NS);return (_NT._==0)?E(_rm):E(_NT.a);},_NU=new T(function(){return B(_ic("Event.hs:(75,1)-(78,93)|function changeType"));}),_NV=new T(function(){return B(_ic("Event.hs:72:16-116|case"));}),_NW=new T(function(){return B(unCStr("Wn"));}),_NX=new T(function(){return B(unCStr("Pn"));}),_NY=new T(function(){return B(unCStr("Mv"));}),_NZ=new T(function(){return B(unCStr("Fr"));}),_O0=new T(function(){return B(unCStr("Ex"));}),_O1=new T(function(){return B(unCStr("DF"));}),_O2=new T(function(){return B(unCStr("DB"));}),_O3=new T(function(){return B(unCStr("Cm"));}),_O4=new T(function(){return B(unCStr("Bl"));}),_O5=function(_O6){return (!B(_vl(_O6,_O4)))?(!B(_vl(_O6,_O3)))?(!B(_vl(_O6,_O2)))?(!B(_vl(_O6,_O1)))?(!B(_vl(_O6,_O0)))?(!B(_vl(_O6,_NZ)))?(!B(_vl(_O6,_NY)))?(!B(_vl(_O6,_NX)))?(!B(_vl(_O6,_NW)))?E(_NV):5:4:3:0:2:8:7:6:1;},_O7=function(_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou){while(1){var _Ov=B((function(_Ow,_Ox,_Oy,_Oz,_OA,_OB,_OC,_OD,_OE,_OF,_OG,_OH,_OI,_OJ,_OK,_OL,_OM,_ON,_OO,_OP,_OQ,_OR,_OS){var _OT=E(_Ow);if(!_OT._){return {_:0,a:_Ox,b:_Oy,c:_Oz,d:_OA,e:_OB,f:_OC,g:_OD,h:_OE,i:_OF,j:_OG,k:_OH,l:_OI,m:_OJ,n:_OK,o:_OL,p:_OM,q:_ON,r:_OO,s:_OP,t:_OQ,u:_OR,v:_OS};}else{var _OU=E(_OT.b);if(!_OU._){return E(_NU);}else{var _OV=E(_Ox),_OW=_Oy,_OX=_Oz,_OY=_OA,_OZ=_OB,_P0=_OC,_P1=_OD,_P2=_OE,_P3=_OF,_P4=_OG,_P5=_OH,_P6=_OI,_P7=_OJ,_P8=_OK,_P9=_OL,_Pa=_OM,_Pb=_ON,_Pc=_OO,_Pd=_OP,_Pe=_OQ,_Pf=_OR,_Pg=_OS;_O8=_OU.b;_O9={_:0,a:E(_OV.a),b:E(B(_NI(new T(function(){return B(_NR(_OT.a));}),new T(function(){return B(_O5(_OU.a));}),_OV.b))),c:E(_OV.c),d:_OV.d,e:_OV.e,f:_OV.f,g:E(_OV.g),h:_OV.h,i:E(_OV.i),j:E(_OV.j),k:E(_OV.k)};_Oa=_OW;_Ob=_OX;_Oc=_OY;_Od=_OZ;_Oe=_P0;_Of=_P1;_Og=_P2;_Oh=_P3;_Oi=_P4;_Oj=_P5;_Ok=_P6;_Ol=_P7;_Om=_P8;_On=_P9;_Oo=_Pa;_Op=_Pb;_Oq=_Pc;_Or=_Pd;_Os=_Pe;_Ot=_Pf;_Ou=_Pg;return __continue;}}})(_O8,_O9,_Oa,_Ob,_Oc,_Od,_Oe,_Of,_Og,_Oh,_Oi,_Oj,_Ok,_Ol,_Om,_On,_Oo,_Op,_Oq,_Or,_Os,_Ot,_Ou));if(_Ov!=__continue){return _Ov;}}},_Ph=function(_Pi,_Pj){while(1){var _Pk=E(_Pj);if(!_Pk._){return __Z;}else{var _Pl=_Pk.b,_Pm=E(_Pi);if(_Pm==1){return E(_Pl);}else{_Pi=_Pm-1|0;_Pj=_Pl;continue;}}}},_Pn=function(_Po,_Pp){while(1){var _Pq=E(_Pp);if(!_Pq._){return __Z;}else{var _Pr=_Pq.b,_Ps=E(_Po);if(_Ps==1){return E(_Pr);}else{_Po=_Ps-1|0;_Pp=_Pr;continue;}}}},_Pt=function(_Pu,_Pv,_Pw,_Px,_Py){var _Pz=new T(function(){var _PA=E(_Pu),_PB=new T(function(){return B(_aW(_Py,_Pv));}),_PC=new T2(1,new T2(0,_Pw,_Px),new T(function(){var _PD=_PA+1|0;if(_PD>0){return B(_Pn(_PD,_PB));}else{return E(_PB);}}));if(0>=_PA){return E(_PC);}else{var _PE=function(_PF,_PG){var _PH=E(_PF);if(!_PH._){return E(_PC);}else{var _PI=_PH.a,_PJ=E(_PG);return (_PJ==1)?new T2(1,_PI,_PC):new T2(1,_PI,new T(function(){return B(_PE(_PH.b,_PJ-1|0));}));}};return B(_PE(_PB,_PA));}}),_PK=new T2(1,_Pz,new T(function(){var _PL=_Pv+1|0;if(_PL>0){return B(_Ph(_PL,_Py));}else{return E(_Py);}}));if(0>=_Pv){return E(_PK);}else{var _PM=function(_PN,_PO){var _PP=E(_PN);if(!_PP._){return E(_PK);}else{var _PQ=_PP.a,_PR=E(_PO);return (_PR==1)?new T2(1,_PQ,_PK):new T2(1,_PQ,new T(function(){return B(_PM(_PP.b,_PR-1|0));}));}};return new F(function(){return _PM(_Py,_Pv);});}},_PS=32,_PT=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_PU=function(_PV){return new F(function(){return _hO(new T1(0,new T(function(){return B(_i1(_PV,_PT));})),_hy);});},_PW=function(_PX){return new F(function(){return _PU("Event.hs:58:27-53|(x\' : y\' : _)");});},_PY=new T(function(){return B(_PW(_));}),_PZ=function(_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm){while(1){var _Qn=B((function(_Qo,_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv,_Qw,_Qx,_Qy,_Qz,_QA,_QB,_QC,_QD,_QE,_QF,_QG,_QH,_QI,_QJ,_QK){var _QL=E(_Qo);if(!_QL._){return {_:0,a:_Qp,b:_Qq,c:_Qr,d:_Qs,e:_Qt,f:_Qu,g:_Qv,h:_Qw,i:_Qx,j:_Qy,k:_Qz,l:_QA,m:_QB,n:_QC,o:_QD,p:_QE,q:_QF,r:_QG,s:_QH,t:_QI,u:_QJ,v:_QK};}else{var _QM=E(_Qp),_QN=new T(function(){var _QO=E(_QL.a);if(!_QO._){return E(_PY);}else{var _QP=E(_QO.b);if(!_QP._){return E(_PY);}else{var _QQ=_QP.a,_QR=_QP.b,_QS=E(_QO.a);if(E(_QS)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_QQ,_QR)).a);}));}else{var _QT=B(_LC(44,_QQ,_QR)),_QU=E(_QT.b);if(!_QU._){return E(_PY);}else{return new T2(0,new T2(1,_QS,_QT.a),_QU.a);}}}}}),_QV=B(_KK(B(_x7(_KI,new T(function(){return E(E(_QN).b);})))));if(!_QV._){return E(_K6);}else{if(!E(_QV.b)._){var _QW=new T(function(){var _QX=B(_KK(B(_x7(_KI,new T(function(){return E(E(_QN).a);})))));if(!_QX._){return E(_K6);}else{if(!E(_QX.b)._){return E(_QX.a);}else{return E(_K7);}}},1),_QY=_Qq,_QZ=_Qr,_R0=_Qs,_R1=_Qt,_R2=_Qu,_R3=_Qv,_R4=_Qw,_R5=_Qx,_R6=_Qy,_R7=_Qz,_R8=_QA,_R9=_QB,_Ra=_QC,_Rb=_QD,_Rc=_QE,_Rd=_QF,_Re=_QG,_Rf=_QH,_Rg=_QI,_Rh=_QJ,_Ri=_QK;_Q0=_QL.b;_Q1={_:0,a:E(_QM.a),b:E(B(_Pt(_QW,E(_QV.a),_PS,_II,_QM.b))),c:E(_QM.c),d:_QM.d,e:_QM.e,f:_QM.f,g:E(_QM.g),h:_QM.h,i:E(_QM.i),j:E(_QM.j),k:E(_QM.k)};_Q2=_QY;_Q3=_QZ;_Q4=_R0;_Q5=_R1;_Q6=_R2;_Q7=_R3;_Q8=_R4;_Q9=_R5;_Qa=_R6;_Qb=_R7;_Qc=_R8;_Qd=_R9;_Qe=_Ra;_Qf=_Rb;_Qg=_Rc;_Qh=_Rd;_Qi=_Re;_Qj=_Rf;_Qk=_Rg;_Ql=_Rh;_Qm=_Ri;return __continue;}else{return E(_K7);}}}})(_Q0,_Q1,_Q2,_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9,_Qa,_Qb,_Qc,_Qd,_Qe,_Qf,_Qg,_Qh,_Qi,_Qj,_Qk,_Ql,_Qm));if(_Qn!=__continue){return _Qn;}}},_Rj=function(_Rk,_Rl,_Rm){var _Rn=E(_Rm);return (_Rn._==0)?0:(!B(A3(_4F,_Rk,_Rl,_Rn.a)))?1+B(_Rj(_Rk,_Rl,_Rn.b))|0:0;},_Ro=function(_Rp,_Rq){while(1){var _Rr=E(_Rq);if(!_Rr._){return __Z;}else{var _Rs=_Rr.b,_Rt=E(_Rp);if(_Rt==1){return E(_Rs);}else{_Rp=_Rt-1|0;_Rq=_Rs;continue;}}}},_Ru=function(_Rv,_Rw){var _Rx=new T(function(){var _Ry=_Rv+1|0;if(_Ry>0){return B(_Ro(_Ry,_Rw));}else{return E(_Rw);}});if(0>=_Rv){return E(_Rx);}else{var _Rz=function(_RA,_RB){var _RC=E(_RA);if(!_RC._){return E(_Rx);}else{var _RD=_RC.a,_RE=E(_RB);return (_RE==1)?new T2(1,_RD,_Rx):new T2(1,_RD,new T(function(){return B(_Rz(_RC.b,_RE-1|0));}));}};return new F(function(){return _Rz(_Rw,_Rv);});}},_RF=function(_RG,_RH){return new F(function(){return _Ru(E(_RG),_RH);});},_RI= -1,_RJ=function(_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6){while(1){var _S7=B((function(_S8,_S9,_Sa,_Sb,_Sc,_Sd,_Se,_Sf,_Sg,_Sh,_Si,_Sj,_Sk,_Sl,_Sm,_Sn,_So,_Sp,_Sq,_Sr,_Ss,_St,_Su){var _Sv=E(_S8);if(!_Sv._){return {_:0,a:_S9,b:_Sa,c:_Sb,d:_Sc,e:_Sd,f:_Se,g:_Sf,h:_Sg,i:_Sh,j:_Si,k:_Sj,l:_Sk,m:_Sl,n:_Sm,o:_Sn,p:_So,q:_Sp,r:_Sq,s:_Sr,t:_Ss,u:_St,v:_Su};}else{var _Sw=_Sv.a,_Sx=B(_aj(_wQ,_Sd)),_Sy=B(_4H(_uJ,_Sw,_Sx)),_Sz=new T(function(){if(!E(_Sy)){return E(_RI);}else{return B(_Rj(_uJ,_Sw,_Sx));}});if(!E(_Sy)){var _SA=E(_Sd);}else{var _SA=B(_RF(_Sz,_Sd));}if(!E(_Sy)){var _SB=E(_Se);}else{var _SB=B(_RF(_Sz,_Se));}var _SC=_S9,_SD=_Sa,_SE=_Sb,_SF=_Sc,_SG=_Sf,_SH=_Sg,_SI=_Sh,_SJ=_Si,_SK=_Sj,_SL=_Sk,_SM=_Sl,_SN=_Sm,_SO=_Sn,_SP=_So,_SQ=_Sp,_SR=_Sq,_SS=_Sr,_ST=_Ss,_SU=_St,_SV=_Su;_RK=_Sv.b;_RL=_SC;_RM=_SD;_RN=_SE;_RO=_SF;_RP=_SA;_RQ=_SB;_RR=_SG;_RS=_SH;_RT=_SI;_RU=_SJ;_RV=_SK;_RW=_SL;_RX=_SM;_RY=_SN;_RZ=_SO;_S0=_SP;_S1=_SQ;_S2=_SR;_S3=_SS;_S4=_ST;_S5=_SU;_S6=_SV;return __continue;}})(_RK,_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS,_RT,_RU,_RV,_RW,_RX,_RY,_RZ,_S0,_S1,_S2,_S3,_S4,_S5,_S6));if(_S7!=__continue){return _S7;}}},_SW=function(_SX){var _SY=E(_SX);if(!_SY._){return new T2(0,_Z,_Z);}else{var _SZ=E(_SY.a),_T0=new T(function(){var _T1=B(_SW(_SY.b));return new T2(0,_T1.a,_T1.b);});return new T2(0,new T2(1,_SZ.a,new T(function(){return E(E(_T0).a);})),new T2(1,_SZ.b,new T(function(){return E(E(_T0).b);})));}},_T2=function(_T3,_T4){while(1){var _T5=E(_T3);if(!_T5._){return E(_T4);}else{var _T6=_T4+E(_T5.a)|0;_T3=_T5.b;_T4=_T6;continue;}}},_T7=function(_T8,_T9){while(1){var _Ta=E(_T9);if(!_Ta._){return __Z;}else{var _Tb=_Ta.b,_Tc=E(_T8);if(_Tc==1){return E(_Tb);}else{_T8=_Tc-1|0;_T9=_Tb;continue;}}}},_Td=function(_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA){while(1){var _TB=B((function(_TC,_TD,_TE,_TF,_TG,_TH,_TI,_TJ,_TK,_TL,_TM,_TN,_TO,_TP,_TQ,_TR,_TS,_TT,_TU,_TV,_TW,_TX,_TY){var _TZ=E(_TC);if(!_TZ._){return {_:0,a:_TD,b:_TE,c:_TF,d:_TG,e:_TH,f:_TI,g:_TJ,h:_TK,i:_TL,j:_TM,k:_TN,l:_TO,m:_TP,n:_TQ,o:_TR,p:_TS,q:_TT,r:_TU,s:_TV,t:_TW,u:_TX,v:_TY};}else{var _U0=new T(function(){var _U1=B(_KK(B(_x7(_KI,_TZ.a))));if(!_U1._){return E(_K6);}else{if(!E(_U1.b)._){return B(_x(B(_H(0,B(_aW(_TU,E(_U1.a))),_Z)),new T(function(){if(_TL>0){return B(_T7(_TL,_TF));}else{return E(_TF);}},1)));}else{return E(_K7);}}});if(0>=_TL){var _U2=E(_U0);}else{var _U3=function(_U4,_U5){var _U6=E(_U4);if(!_U6._){return E(_U0);}else{var _U7=_U6.a,_U8=E(_U5);return (_U8==1)?new T2(1,_U7,_U0):new T2(1,_U7,new T(function(){return B(_U3(_U6.b,_U8-1|0));}));}},_U2=B(_U3(_TF,_TL));}var _U9=_TD,_Ua=_TE,_Ub=_TG,_Uc=_TH,_Ud=_TI,_Ue=_TJ,_Uf=_TK,_Ug=_TL,_Uh=_TM,_Ui=_TN,_Uj=_TO,_Uk=_TP,_Ul=_TQ,_Um=_TR,_Un=_TS,_Uo=_TT,_Up=_TU,_Uq=_TV,_Ur=_TW,_Us=_TX,_Ut=_TY;_Te=_TZ.b;_Tf=_U9;_Tg=_Ua;_Th=_U2;_Ti=_Ub;_Tj=_Uc;_Tk=_Ud;_Tl=_Ue;_Tm=_Uf;_Tn=_Ug;_To=_Uh;_Tp=_Ui;_Tq=_Uj;_Tr=_Uk;_Ts=_Ul;_Tt=_Um;_Tu=_Un;_Tv=_Uo;_Tw=_Up;_Tx=_Uq;_Ty=_Ur;_Tz=_Us;_TA=_Ut;return __continue;}})(_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv,_Tw,_Tx,_Ty,_Tz,_TA));if(_TB!=__continue){return _TB;}}},_Uu=function(_Uv){return new F(function(){return _PU("Event.hs:119:28-52|(c : d : _)");});},_Uw=new T(function(){return B(_Uu(_));}),_Ux=function(_Uy,_Uz,_UA,_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1){while(1){var _V2=B((function(_V3,_V4,_V5,_V6,_V7,_V8,_V9,_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo,_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw){var _Vx=E(_V3);if(!_Vx._){return {_:0,a:E(_V4),b:E(_V5),c:E(_V6),d:E(_V7),e:E(_V8),f:E(_V9),g:E(_Va),h:E(_Vb),i:_Vc,j:_Vd,k:_Ve,l:_Vf,m:E(_Vg),n:_Vh,o:E(_Vi),p:E(_Vj),q:_Vk,r:E(_Vl),s:E(_Vm),t:_Vn,u:E({_:0,a:E(_Vo),b:E(_Vp),c:E(_Vq),d:E(_B3),e:E(_Vs),f:E(_Vt),g:E(_B3),h:E(_Vv)}),v:E(_Vw)};}else{var _Vy=new T(function(){var _Vz=E(_Vx.a);if(!_Vz._){return E(_Uw);}else{var _VA=E(_Vz.b);if(!_VA._){return E(_Uw);}else{var _VB=_VA.a,_VC=_VA.b,_VD=E(_Vz.a);if(E(_VD)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_VB,_VC)).a);}));}else{var _VE=B(_LC(44,_VB,_VC)),_VF=E(_VE.b);if(!_VF._){return E(_Uw);}else{return new T2(0,new T2(1,_VD,_VE.a),_VF.a);}}}}}),_VG=_V4,_VH=_V5,_VI=_V6,_VJ=_V7,_VK=_V8,_VL=_V9,_VM=_Va,_VN=_Vb,_VO=_Vc,_VP=_Vd,_VQ=_Ve,_VR=_Vf,_VS=B(_x(_Vg,new T2(1,new T2(0,new T(function(){return E(E(_Vy).a);}),new T(function(){return E(E(_Vy).b);})),_Z))),_VT=_Vh,_VU=_Vi,_VV=_Vj,_VW=_Vk,_VX=_Vl,_VY=_Vm,_VZ=_Vn,_W0=_Vo,_W1=_Vp,_W2=_Vq,_W3=_Vr,_W4=_Vs,_W5=_Vt,_W6=_Vu,_W7=_Vv,_W8=_Vw;_Uy=_Vx.b;_Uz=_VG;_UA=_VH;_UB=_VI;_UC=_VJ;_UD=_VK;_UE=_VL;_UF=_VM;_UG=_VN;_UH=_VO;_UI=_VP;_UJ=_VQ;_UK=_VR;_UL=_VS;_UM=_VT;_UN=_VU;_UO=_VV;_UP=_VW;_UQ=_VX;_UR=_VY;_US=_VZ;_UT=_W0;_UU=_W1;_UV=_W2;_UW=_W3;_UX=_W4;_UY=_W5;_UZ=_W6;_V0=_W7;_V1=_W8;return __continue;}})(_Uy,_Uz,_UA,_UB,_UC,_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO,_UP,_UQ,_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY,_UZ,_V0,_V1));if(_V2!=__continue){return _V2;}}},_W9=function(_Wa){return new F(function(){return _PU("Event.hs:65:27-53|(x\' : y\' : _)");});},_Wb=new T(function(){return B(_W9(_));}),_Wc=function(_Wd){return new F(function(){return _PU("Event.hs:66:27-55|(chs : tps : _)");});},_We=new T(function(){return B(_Wc(_));}),_Wf=new T(function(){return B(_ic("Event.hs:(63,1)-(69,83)|function putCell"));}),_Wg=function(_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD){while(1){var _WE=B((function(_WF,_WG,_WH,_WI,_WJ,_WK,_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS,_WT,_WU,_WV,_WW,_WX,_WY,_WZ,_X0,_X1){var _X2=E(_WF);if(!_X2._){return {_:0,a:_WG,b:_WH,c:_WI,d:_WJ,e:_WK,f:_WL,g:_WM,h:_WN,i:_WO,j:_WP,k:_WQ,l:_WR,m:_WS,n:_WT,o:_WU,p:_WV,q:_WW,r:_WX,s:_WY,t:_WZ,u:_X0,v:_X1};}else{var _X3=E(_X2.b);if(!_X3._){return E(_Wf);}else{var _X4=E(_WG),_X5=new T(function(){var _X6=E(_X2.a);if(!_X6._){return E(_Wb);}else{var _X7=E(_X6.b);if(!_X7._){return E(_Wb);}else{var _X8=_X7.a,_X9=_X7.b,_Xa=E(_X6.a);if(E(_Xa)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_X8,_X9)).a);}));}else{var _Xb=B(_LC(44,_X8,_X9)),_Xc=E(_Xb.b);if(!_Xc._){return E(_Wb);}else{return new T2(0,new T2(1,_Xa,_Xb.a),_Xc.a);}}}}}),_Xd=B(_KK(B(_x7(_KI,new T(function(){return E(E(_X5).b);})))));if(!_Xd._){return E(_K6);}else{if(!E(_Xd.b)._){var _Xe=new T(function(){var _Xf=E(_X3.a);if(!_Xf._){return E(_We);}else{var _Xg=E(_Xf.b);if(!_Xg._){return E(_We);}else{var _Xh=_Xg.a,_Xi=_Xg.b,_Xj=E(_Xf.a);if(E(_Xj)==44){return new T2(0,_Z,new T(function(){return E(B(_LC(44,_Xh,_Xi)).a);}));}else{var _Xk=B(_LC(44,_Xh,_Xi)),_Xl=E(_Xk.b);if(!_Xl._){return E(_We);}else{return new T2(0,new T2(1,_Xj,_Xk.a),_Xl.a);}}}}}),_Xm=new T(function(){var _Xn=B(_KK(B(_x7(_KI,new T(function(){return E(E(_X5).a);})))));if(!_Xn._){return E(_K6);}else{if(!E(_Xn.b)._){return E(_Xn.a);}else{return E(_K7);}}},1),_Xo=_WH,_Xp=_WI,_Xq=_WJ,_Xr=_WK,_Xs=_WL,_Xt=_WM,_Xu=_WN,_Xv=_WO,_Xw=_WP,_Xx=_WQ,_Xy=_WR,_Xz=_WS,_XA=_WT,_XB=_WU,_XC=_WV,_XD=_WW,_XE=_WX,_XF=_WY,_XG=_WZ,_XH=_X0,_XI=_X1;_Wh=_X3.b;_Wi={_:0,a:E(_X4.a),b:E(B(_Pt(_Xm,E(_Xd.a),new T(function(){return B(_NR(E(_Xe).a));}),new T(function(){return B(_O5(E(_Xe).b));}),_X4.b))),c:E(_X4.c),d:_X4.d,e:_X4.e,f:_X4.f,g:E(_X4.g),h:_X4.h,i:E(_X4.i),j:E(_X4.j),k:E(_X4.k)};_Wj=_Xo;_Wk=_Xp;_Wl=_Xq;_Wm=_Xr;_Wn=_Xs;_Wo=_Xt;_Wp=_Xu;_Wq=_Xv;_Wr=_Xw;_Ws=_Xx;_Wt=_Xy;_Wu=_Xz;_Wv=_XA;_Ww=_XB;_Wx=_XC;_Wy=_XD;_Wz=_XE;_WA=_XF;_WB=_XG;_WC=_XH;_WD=_XI;return __continue;}else{return E(_K7);}}}}})(_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA,_WB,_WC,_WD));if(_WE!=__continue){return _WE;}}},_XJ=function(_XK,_XL){while(1){var _XM=E(_XL);if(!_XM._){return __Z;}else{var _XN=_XM.b,_XO=E(_XK);if(_XO==1){return E(_XN);}else{_XK=_XO-1|0;_XL=_XN;continue;}}}},_XP=function(_XQ){var _XR=E(_XQ);if(!_XR._){return new T2(0,_Z,_Z);}else{var _XS=E(_XR.a),_XT=new T(function(){var _XU=B(_XP(_XR.b));return new T2(0,_XU.a,_XU.b);});return new T2(0,new T2(1,_XS.a,new T(function(){return E(E(_XT).a);})),new T2(1,_XS.b,new T(function(){return E(E(_XT).b);})));}},_XV=32,_XW=function(_XX,_XY,_XZ,_Y0){var _Y1=E(_Y0);if(!_Y1._){return __Z;}else{var _Y2=_Y1.b;if(!B(_4H(_3S,_XX,_XZ))){var _Y3=new T(function(){return B(_XW(new T(function(){return E(_XX)+1|0;}),_XY,_XZ,_Y2));});return new T2(1,_Y1.a,_Y3);}else{var _Y4=new T(function(){return B(_XW(new T(function(){return E(_XX)+1|0;}),_XY,_XZ,_Y2));});return new T2(1,_XY,_Y4);}}},_Y5=function(_Y6,_Y7){var _Y8=E(_Y7);if(!_Y8._){return __Z;}else{var _Y9=new T(function(){var _Ya=B(_XP(_Y8.a)),_Yb=_Ya.a,_Yc=new T(function(){return B(_Nu(0,_Y6,_Yb));});return B(_KW(B(_XW(_vT,_XV,_Yc,_Yb)),new T(function(){return B(_NB(0,_II,_Yc,_Ya.b));},1)));});return new T2(1,_Y9,new T(function(){return B(_Y5(_Y6,_Y8.b));}));}},_Yd=function(_Ye,_Yf){var _Yg=E(_Yf);return (_Yg._==0)?__Z:new T2(1,_Ye,new T(function(){return B(_Yd(_Yg.a,_Yg.b));}));},_Yh=new T(function(){return B(unCStr("init"));}),_Yi=new T(function(){return B(_rj(_Yh));}),_Yj=function(_Yk,_Yl){var _Ym=function(_Yn){var _Yo=E(_Yn);if(!_Yo._){return __Z;}else{var _Yp=new T(function(){return B(_x(new T2(1,_Yk,_Z),new T(function(){return B(_Ym(_Yo.b));},1)));},1);return new F(function(){return _x(_Yo.a,_Yp);});}},_Yq=B(_Ym(_Yl));if(!_Yq._){return E(_Yi);}else{return new F(function(){return _Yd(_Yq.a,_Yq.b);});}},_Yr=61,_Ys=46,_Yt=new T(function(){return B(_ic("Event.hs:(109,1)-(115,61)|function makeDecision"));}),_Yu=new T(function(){return B(unCStr("sm"));}),_Yv=new T(function(){return B(unCStr("rt"));}),_Yw=new T(function(){return B(unCStr("rs"));}),_Yx=new T(function(){return B(unCStr("rk"));}),_Yy=new T(function(){return B(unCStr("if"));}),_Yz=new T(function(){return B(unCStr("hm"));}),_YA=new T(function(){return B(unCStr("cleq"));}),_YB=new T(function(){return B(unCStr("da"));}),_YC=new T(function(){return B(unCStr("ct"));}),_YD=function(_YE,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0){var _Z1=function(_Z2,_Z3){var _Z4=function(_Z5){if(!B(_vl(_Z2,_YC))){if(!B(_vl(_Z2,_YB))){var _Z6=function(_Z7){if(!B(_vl(_Z2,_YA))){var _Z8=function(_Z9){if(!B(_vl(_Z2,_wm))){if(!B(_vl(_Z2,_Yz))){if(!B(_vl(_Z2,_Yy))){if(!B(_vl(_Z2,_Yx))){if(!B(_vl(_Z2,_Yw))){if(!B(_vl(_Z2,_Yv))){if(!B(_vl(_Z2,_Yu))){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{var _Za=E(_YZ);return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E({_:0,a:E(_Za.a),b:E(_Za.b),c:E(_Za.c),d:E(_Za.d),e:E(_Za.e),f:E(_Za.f),g:E(_Za.g),h:E(_B3)}),v:E(_Z0)};}}else{var _Zb=B(_Td(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_Zb.a),b:E(_Zb.b),c:E(_Zb.c),d:E(_Zb.d),e:E(_Zb.e),f:E(_Zb.f),g:E(_Zb.g),h:E(_Zb.h),i:_Zb.i,j:_Zb.j,k:_Zb.k,l:_Zb.l,m:E(_Zb.m),n:_Zb.n,o:E(_Zb.o),p:E(_Zb.p),q:_Zb.q,r:E(_Zb.r),s:E(_Zb.s),t:_Zb.t,u:E(_Zb.u),v:E(_Zb.v)};}}else{var _Zc=new T(function(){return B(_x(B(_H(0,600-B(_T2(_YW,0))|0,_Z)),new T(function(){if(_YN>0){return B(_XJ(_YN,_YH));}else{return E(_YH);}},1)));});if(0>=_YN){var _Zd=E(_Zc);}else{var _Ze=function(_Zf,_Zg){var _Zh=E(_Zf);if(!_Zh._){return E(_Zc);}else{var _Zi=_Zh.a,_Zj=E(_Zg);return (_Zj==1)?new T2(1,_Zi,_Zc):new T2(1,_Zi,new T(function(){return B(_Ze(_Zh.b,_Zj-1|0));}));}},_Zd=B(_Ze(_YH,_YN));}return {_:0,a:E(_YF),b:E(_YG),c:E(_Zd),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}}else{return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_Z3),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}}else{var _Zk=E(_Z3);if(!_Zk._){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{var _Zl=_Zk.a,_Zm=E(_Zk.b);if(!_Zm._){return E(_Yt);}else{var _Zn=_Zm.a,_Zo=B(_SW(_YL)),_Zp=_Zo.a,_Zq=_Zo.b,_Zr=function(_Zs){if(!B(_4H(_uJ,_Zl,_Zp))){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{if(!B(_vl(_Zn,B(_aW(_Zq,B(_Rj(_uJ,_Zl,_Zp))))))){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{return new F(function(){return _YD(_Zs,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}}},_Zt=B(_Yj(_Ys,_Zm.b));if(!_Zt._){return new F(function(){return _Zr(_Z);});}else{var _Zu=_Zt.a,_Zv=E(_Zt.b);if(!_Zv._){return new F(function(){return _Zr(new T2(1,_Zu,_Z));});}else{var _Zw=_Zv.a,_Zx=_Zv.b,_Zy=E(_Zu);if(E(_Zy)==47){if(!B(_4H(_uJ,_Zl,_Zp))){return new F(function(){return _YD(B(_LC(47,_Zw,_Zx)).a,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}else{if(!B(_vl(_Zn,B(_aW(_Zq,B(_Rj(_uJ,_Zl,_Zp))))))){return new F(function(){return _YD(B(_LC(47,_Zw,_Zx)).a,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}else{return new F(function(){return _YD(_Z,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}}}else{if(!B(_4H(_uJ,_Zl,_Zp))){var _Zz=E(B(_LC(47,_Zw,_Zx)).b);if(!_Zz._){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{return new F(function(){return _YD(_Zz.a,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}}else{if(!B(_vl(_Zn,B(_aW(_Zq,B(_Rj(_uJ,_Zl,_Zp))))))){var _ZA=E(B(_LC(47,_Zw,_Zx)).b);if(!_ZA._){return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}else{return new F(function(){return _YD(_ZA.a,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}}else{return new F(function(){return _YD(new T2(1,_Zy,new T(function(){return E(B(_LC(47,_Zw,_Zx)).a);})),_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0);});}}}}}}}}}else{var _ZB=E(_YZ);return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E({_:0,a:E(_ZB.a),b:E(_ZB.b),c:E(_ZB.c),d:E(_ZB.d),e:E(_ZB.e),f:E(_ZB.f),g:E(_ZB.g),h:E(_B2)}),v:E(_Z0)};}}else{var _ZC=E(_YZ);return new F(function(){return _Ux(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_Z,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_ZC.a,_ZC.b,_ZC.c,_ZC.d,_ZC.e,_ZC.f,_ZC.g,_ZC.h,_Z0);});}},_ZD=E(_Z2);if(!_ZD._){return new F(function(){return _Z8(_);});}else{if(E(_ZD.a)==109){if(!E(_ZD.b)._){var _ZE=B(_LP(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZE.a),b:E(_ZE.b),c:E(_ZE.c),d:E(_ZE.d),e:E(_ZE.e),f:E(_ZE.f),g:E(_ZE.g),h:E(_ZE.h),i:_ZE.i,j:_ZE.j,k:_ZE.k,l:_ZE.l,m:E(_ZE.m),n:_ZE.n,o:E(_ZE.o),p:E(_ZE.p),q:_ZE.q,r:E(_ZE.r),s:E(_ZE.s),t:_ZE.t,u:E(_ZE.u),v:E(_ZE.v)};}else{return new F(function(){return _Z8(_);});}}else{return new F(function(){return _Z8(_);});}}}else{var _ZF=E(_YF);return {_:0,a:E({_:0,a:E(_ZF.a),b:E(B(_Y5(_Yr,_ZF.b))),c:E(_ZF.c),d:_ZF.d,e:_ZF.e,f:_ZF.f,g:E(_ZF.g),h:_ZF.h,i:E(_ZF.i),j:E(_ZF.j),k:E(_ZF.k)}),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_YJ),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}},_ZG=E(_Z2);if(!_ZG._){return new F(function(){return _Z6(_);});}else{var _ZH=_ZG.b;switch(E(_ZG.a)){case 99:if(!E(_ZH)._){var _ZI=B(_PZ(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZI.a),b:E(_ZI.b),c:E(_ZI.c),d:E(_ZI.d),e:E(_ZI.e),f:E(_ZI.f),g:E(_ZI.g),h:E(_ZI.h),i:_ZI.i,j:_ZI.j,k:_ZI.k,l:_ZI.l,m:E(_ZI.m),n:_ZI.n,o:E(_ZI.o),p:E(_ZI.p),q:_ZI.q,r:E(_ZI.r),s:E(_ZI.s),t:_ZI.t,u:E(_ZI.u),v:E(_ZI.v)};}else{return new F(function(){return _Z6(_);});}break;case 112:if(!E(_ZH)._){var _ZJ=B(_Wg(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZJ.a),b:E(_ZJ.b),c:E(_ZJ.c),d:E(_ZJ.d),e:E(_ZJ.e),f:E(_ZJ.f),g:E(_ZJ.g),h:E(_ZJ.h),i:_ZJ.i,j:_ZJ.j,k:_ZJ.k,l:_ZJ.l,m:E(_ZJ.m),n:_ZJ.n,o:E(_ZJ.o),p:E(_ZJ.p),q:_ZJ.q,r:E(_ZJ.r),s:E(_ZJ.s),t:_ZJ.t,u:E(_ZJ.u),v:E(_ZJ.v)};}else{return new F(function(){return _Z6(_);});}break;default:return new F(function(){return _Z6(_);});}}}else{return {_:0,a:E(_YF),b:E(_YG),c:E(_YH),d:E(_YI),e:E(_Z),f:E(_YK),g:E(_YL),h:E(_YM),i:_YN,j:_YO,k:_YP,l:_YQ,m:E(_YR),n:_YS,o:E(_YT),p:E(_YU),q:_YV,r:E(_YW),s:E(_YX),t:_YY,u:E(_YZ),v:E(_Z0)};}}else{var _ZK=B(_O7(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZK.a),b:E(_ZK.b),c:E(_ZK.c),d:E(_ZK.d),e:E(_ZK.e),f:E(_ZK.f),g:E(_ZK.g),h:E(_ZK.h),i:_ZK.i,j:_ZK.j,k:_ZK.k,l:_ZK.l,m:E(_ZK.m),n:_ZK.n,o:E(_ZK.o),p:E(_ZK.p),q:_ZK.q,r:E(_ZK.r),s:E(_ZK.s),t:_ZK.t,u:E(_ZK.u),v:E(_ZK.v)};}},_ZL=E(_Z2);if(!_ZL._){return new F(function(){return _Z4(_);});}else{var _ZM=_ZL.b;switch(E(_ZL.a)){case 100:if(!E(_ZM)._){var _ZN=B(_RJ(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZN.a),b:E(_ZN.b),c:E(_ZN.c),d:E(_ZN.d),e:E(_ZN.e),f:E(_ZN.f),g:E(_ZN.g),h:E(_ZN.h),i:_ZN.i,j:_ZN.j,k:_ZN.k,l:_ZN.l,m:E(_ZN.m),n:_ZN.n,o:E(_ZN.o),p:E(_ZN.p),q:_ZN.q,r:E(_ZN.r),s:E(_ZN.s),t:_ZN.t,u:E(_ZN.u),v:E(_ZN.v)};}else{return new F(function(){return _Z4(_);});}break;case 101:if(!E(_ZM)._){var _ZO=B(_uM(_Z3,_YF,_YG,_YH,_YI,_YJ,_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_YR,_YS,_YT,_YU,_YV,_YW,_YX,_YY,_YZ,_Z0));return {_:0,a:E(_ZO.a),b:E(_ZO.b),c:E(_ZO.c),d:E(_ZO.d),e:E(_ZO.e),f:E(_ZO.f),g:E(_ZO.g),h:E(_ZO.h),i:_ZO.i,j:_ZO.j,k:_ZO.k,l:_ZO.l,m:E(_ZO.m),n:_ZO.n,o:E(_ZO.o),p:E(_ZO.p),q:_ZO.q,r:E(_ZO.r),s:E(_ZO.s),t:_ZO.t,u:E(_ZO.u),v:E(_ZO.v)};}else{return new F(function(){return _Z4(_);});}break;default:return new F(function(){return _Z4(_);});}}},_ZP=E(_YE);if(!_ZP._){return new F(function(){return _Z1(_Z,_Z);});}else{var _ZQ=_ZP.a,_ZR=E(_ZP.b);if(!_ZR._){return new F(function(){return _Z1(new T2(1,_ZQ,_Z),_Z);});}else{var _ZS=E(_ZQ),_ZT=new T(function(){var _ZU=B(_LC(46,_ZR.a,_ZR.b));return new T2(0,_ZU.a,_ZU.b);});if(E(_ZS)==46){return new F(function(){return _Z1(_Z,new T2(1,new T(function(){return E(E(_ZT).a);}),new T(function(){return E(E(_ZT).b);})));});}else{return new F(function(){return _Z1(new T2(1,_ZS,new T(function(){return E(E(_ZT).a);})),new T(function(){return E(E(_ZT).b);}));});}}}},_ZV=new T(function(){return B(unCStr("last"));}),_ZW=new T(function(){return B(_rj(_ZV));}),_ZX=32,_ZY=0,_ZZ=65306,_100=125,_101=new T1(0,1),_102=function(_103,_104,_105,_106,_107){var _108=new T(function(){return E(_107).i;}),_109=new T(function(){var _10a=E(_104)/28,_10b=_10a&4294967295;if(_10a>=_10b){return _10b-1|0;}else{return (_10b-1|0)-1|0;}}),_10c=new T(function(){if(!E(E(_106).h)){return E(_nd);}else{return 2+(E(E(E(_107).b).b)+3|0)|0;}}),_10d=new T(function(){if(!E(_108)){return new T2(0,_109,_10c);}else{return E(E(_107).h);}}),_10e=new T(function(){return E(E(_107).c);}),_10f=new T(function(){var _10g=E(_108)+1|0;if(0>=_10g){return E(_ZX);}else{var _10h=B(_uj(_10g,_10e));if(!_10h._){return E(_ZX);}else{return B(_sF(_10h.a,_10h.b,_ZW));}}}),_10i=new T(function(){var _10j=E(_10f);switch(E(_10j)){case 125:return E(_ZX);break;case 12289:return E(_ZX);break;case 12290:return E(_ZX);break;default:return E(_10j);}}),_10k=new T(function(){if(E(_10i)==10){return true;}else{return false;}}),_10l=new T(function(){return E(E(_10d).b);}),_10m=new T(function(){if(!E(_10k)){if(E(_10i)==12300){return E(_nc);}else{return E(_107).j;}}else{return E(_ZY);}}),_10n=new T(function(){return E(E(_10d).a);}),_10o=new T(function(){if(E(_10i)==65306){return true;}else{return false;}}),_10p=new T(function(){if(!E(_10o)){if(!E(_10k)){var _10q=E(_10l);if((_10q+1)*24<=E(_105)-10){return new T2(0,_10n,_10q+1|0);}else{return new T2(0,new T(function(){return E(_10n)-1|0;}),_10c);}}else{return new T2(0,new T(function(){return E(_10n)-1|0;}),_10c);}}else{return new T2(0,_10n,_10l);}}),_10r=new T(function(){if(E(E(_10p).a)==1){if(E(_10n)==1){return false;}else{return true;}}else{return false;}}),_10s=new T(function(){return B(_qy(_10e,0))-1|0;}),_10t=new T(function(){if(!E(_10o)){return __Z;}else{return B(_uB(_ZZ,E(_108),_10e));}}),_10u=new T(function(){if(E(_10i)==123){return true;}else{return false;}}),_10v=new T(function(){if(!E(_10u)){return __Z;}else{return B(_uB(_100,E(_108),_10e));}}),_10w=new T(function(){if(!E(_10o)){if(!E(_10u)){return E(_nc);}else{return B(_qy(_10v,0))+2|0;}}else{return B(_qy(_10t,0))+2|0;}}),_10x=new T(function(){var _10y=E(_107),_10z=_10y.a,_10A=_10y.b,_10B=_10y.c,_10C=_10y.d,_10D=_10y.e,_10E=_10y.f,_10F=_10y.g,_10G=_10y.h,_10H=_10y.j,_10I=_10y.k,_10J=_10y.l,_10K=_10y.m,_10L=_10y.n,_10M=_10y.o,_10N=_10y.p,_10O=_10y.q,_10P=_10y.r,_10Q=_10y.s,_10R=_10y.t,_10S=_10y.v,_10T=E(_108),_10U=E(_10w);if((_10T+_10U|0)<=E(_10s)){var _10V=E(_106),_10W=_10V.a,_10X=_10V.b,_10Y=_10V.c,_10Z=_10V.e,_110=_10V.f,_111=_10V.g,_112=_10V.h;if(E(_10f)==12290){var _113=true;}else{var _113=false;}if(!E(_10u)){return {_:0,a:E(_10z),b:E(_10A),c:E(_10B),d:E(_10C),e:E(_10D),f:E(_10E),g:E(_10F),h:E(_10G),i:_10T+_10U|0,j:_10H,k:_10I,l:_10J,m:E(_10K),n:_10L,o:E(_10M),p:E(_10N),q:_10O,r:E(_10P),s:E(_10Q),t:_10R,u:E({_:0,a:E(_10W),b:E(_10X),c:E(_10Y),d:E(_113),e:E(_10Z),f:E(_110),g:E(_111),h:E(_112)}),v:E(_10S)};}else{return B(_YD(_10v,_10z,_10A,_10B,_10C,_10D,_10E,_10F,_10G,_10T+_10U|0,_10H,_10I,_10J,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,{_:0,a:E(_10W),b:E(_10X),c:E(_10Y),d:E(_113),e:E(_10Z),f:E(_110),g:E(_111),h:E(_112)},_10S));}}else{var _114=E(_106),_115=_114.a,_116=_114.b,_117=_114.c,_118=_114.e,_119=_114.f,_11a=_114.g,_11b=_114.h;if(E(_10f)==12290){var _11c=true;}else{var _11c=false;}if(!E(_10u)){return {_:0,a:E(_10z),b:E(_10A),c:E(_10B),d:E(_10C),e:E(_10D),f:E(_10E),g:E(_10F),h:E(_10G),i:0,j:_10H,k:_10I,l:_10J,m:E(_10K),n:_10L,o:E(_10M),p:E(_10N),q:_10O,r:E(_10P),s:E(_10Q),t:_10R,u:E({_:0,a:E(_115),b:E(_116),c:E(_117),d:E(_11c),e:E(_118),f:E(_119),g:E(_11a),h:E(_11b)}),v:E(_10S)};}else{return B(_YD(_10v,_10z,_10A,_10B,_10C,_10D,_10E,_10F,_10G,0,_10H,_10I,_10J,_10K,_10L,_10M,_10N,_10O,_10P,_10Q,_10R,{_:0,a:E(_115),b:E(_116),c:E(_117),d:E(_11c),e:E(_118),f:E(_119),g:E(_11a),h:E(_11b)},_10S));}}}),_11d=new T(function(){return E(E(_10x).u);}),_11e=new T(function(){if(!E(_108)){return E(_ZY);}else{return E(_10x).k;}}),_11f=new T(function(){var _11g=B(_sz(B(_sx(_103)))),_11h=new T(function(){var _11i=B(_u0(_103,E(_104)/16)),_11j=_11i.a;if(E(_11i.b)>=0){return E(_11j);}else{return B(A3(_tc,_11g,_11j,new T(function(){return B(A2(_lj,_11g,_101));})));}});return B(A3(_tc,_11g,_11h,new T(function(){return B(A2(_lj,_11g,_ls));})));});return {_:0,a:_10i,b:_10n,c:_10l,d:new T(function(){if(E(_10c)!=E(_10l)){return E(_10n);}else{return E(_10n)+1|0;}}),e:new T(function(){var _11k=E(_10l);if(E(_10c)!=_11k){return _11k-1|0;}else{var _11l=(E(_105)-10)/24,_11m=_11l&4294967295;if(_11l>=_11m){return _11m;}else{return _11m-1|0;}}}),f:_10c,g:_108,h:_10e,i:new T(function(){return B(_aW(_n9,E(_10m)));}),j:_10t,k:_109,l:_11f,m:_11e,n:_ne,o:_10o,p:_10u,q:_10r,r:_11d,s:_10x,t:new T(function(){var _11n=E(_10x),_11o=_11n.a,_11p=_11n.b,_11q=_11n.c,_11r=_11n.d,_11s=_11n.e,_11t=_11n.f,_11u=_11n.g,_11v=_11n.i,_11w=_11n.l,_11x=_11n.m,_11y=_11n.n,_11z=_11n.o,_11A=_11n.p,_11B=_11n.q,_11C=_11n.r,_11D=_11n.s,_11E=_11n.t,_11F=_11n.v;if(!E(_10r)){var _11G=E(_10p);}else{var _11G=new T2(0,_10n,_10c);}var _11H=E(_10m);if(!E(_10r)){var _11I=E(_11d);return {_:0,a:E(_11o),b:E(_11p),c:E(_11q),d:E(_11r),e:E(_11s),f:E(_11t),g:E(_11u),h:E(_11G),i:_11v,j:_11H,k:E(_11e),l:_11w,m:E(_11x),n:_11y,o:E(_11z),p:E(_11A),q:_11B,r:E(_11C),s:E(_11D),t:_11E,u:E({_:0,a:E(_11I.a),b:E(_11I.b),c:(E(_108)+E(_10w)|0)<=E(_10s),d:E(_11I.d),e:E(_11I.e),f:E(_11I.f),g:E(_11I.g),h:E(_11I.h)}),v:E(_11F)};}else{var _11J=E(_11d);return {_:0,a:E(_11o),b:E(_11p),c:E(_11q),d:E(_11r),e:E(_11s),f:E(_11t),g:E(_11u),h:E(_11G),i:_11v,j:_11H,k:E(_11e)+1|0,l:_11w,m:E(_11x),n:_11y,o:E(_11z),p:E(_11A),q:_11B,r:E(_11C),s:E(_11D),t:_11E,u:E({_:0,a:E(_11J.a),b:E(_11J.b),c:(E(_108)+E(_10w)|0)<=E(_10s),d:E(_11J.d),e:E(_11J.e),f:E(_11J.f),g:E(_11J.g),h:E(_11J.h)}),v:E(_11F)};}})};},_11K=function(_11L){var _11M=E(_11L);if(!_11M._){return new T2(0,_Z,_Z);}else{var _11N=E(_11M.a),_11O=new T(function(){var _11P=B(_11K(_11M.b));return new T2(0,_11P.a,_11P.b);});return new T2(0,new T2(1,_11N.a,new T(function(){return E(E(_11O).a);})),new T2(1,_11N.b,new T(function(){return E(E(_11O).b);})));}},_11Q=42,_11R=32,_11S=function(_11T,_11U,_11V){var _11W=E(_11T);if(!_11W._){return __Z;}else{var _11X=_11W.a,_11Y=_11W.b;if(_11U!=_11V){var _11Z=E(_11X);return (_11Z._==0)?E(_rm):(E(_11Z.a)==42)?new T2(1,new T2(1,_11R,_11Z.b),new T(function(){return B(_11S(_11Y,_11U,_11V+1|0));})):new T2(1,new T2(1,_11R,_11Z),new T(function(){return B(_11S(_11Y,_11U,_11V+1|0));}));}else{var _120=E(_11X);return (_120._==0)?E(_rm):(E(_120.a)==42)?new T2(1,new T2(1,_11R,_120),new T(function(){return B(_11S(_11Y,_11U,_11V+1|0));})):new T2(1,new T2(1,_11Q,_120),new T(function(){return B(_11S(_11Y,_11U,_11V+1|0));}));}}},_121=new T(function(){return B(unCStr("\n\n"));}),_122=function(_123){var _124=E(_123);if(!_124._){return __Z;}else{var _125=new T(function(){return B(_x(_121,new T(function(){return B(_122(_124.b));},1)));},1);return new F(function(){return _x(_124.a,_125);});}},_126=function(_127,_128,_129){var _12a=new T(function(){var _12b=new T(function(){var _12c=E(_128);if(!_12c._){return B(_122(_Z));}else{var _12d=_12c.a,_12e=_12c.b,_12f=E(_129);if(!_12f){var _12g=E(_12d);if(!_12g._){return E(_rm);}else{if(E(_12g.a)==42){return B(_122(new T2(1,new T2(1,_11R,_12g),new T(function(){return B(_11S(_12e,0,1));}))));}else{return B(_122(new T2(1,new T2(1,_11Q,_12g),new T(function(){return B(_11S(_12e,0,1));}))));}}}else{var _12h=E(_12d);if(!_12h._){return E(_rm);}else{if(E(_12h.a)==42){return B(_122(new T2(1,new T2(1,_11R,_12h.b),new T(function(){return B(_11S(_12e,_12f,1));}))));}else{return B(_122(new T2(1,new T2(1,_11R,_12h),new T(function(){return B(_11S(_12e,_12f,1));}))));}}}}});return B(unAppCStr("\n\n",_12b));},1);return new F(function(){return _x(_127,_12a);});},_12i=function(_12j){return E(E(_12j).c);},_12k=function(_12l,_12m,_12n,_12o,_12p,_12q,_12r,_12s,_12t){var _12u=new T(function(){if(!E(_12m)){return E(_12n);}else{return false;}}),_12v=new T(function(){if(!E(_12m)){return false;}else{return E(E(_12s).g);}}),_12w=new T(function(){if(!E(_12v)){if(!E(_12u)){return B(A2(_lj,_12l,_lr));}else{return B(A3(_qF,_12l,new T(function(){return B(A3(_qF,_12l,_12q,_12r));}),new T(function(){return B(A2(_lj,_12l,_101));})));}}else{return B(A3(_qF,_12l,_12q,_12r));}}),_12x=new T(function(){if(!E(_12v)){if(!E(_12u)){return __Z;}else{var _12y=E(_12o)+1|0;if(0>=_12y){return __Z;}else{return B(_uj(_12y,_12p));}}}else{return B(_126(B(_12i(_12t)),new T(function(){return E(B(_11K(E(_12t).m)).a);},1),new T(function(){return E(_12t).n;},1)));}});return new T4(0,_12v,_12u,_12x,_12w);},_12z=function(_12A,_12B,_12C){var _12D=E(_12B),_12E=E(_12C),_12F=new T(function(){var _12G=B(_lf(_12A)),_12H=B(_12z(_12A,_12E,B(A3(_tc,_12G,new T(function(){return B(A3(_qF,_12G,_12E,_12E));}),_12D))));return new T2(1,_12H.a,_12H.b);});return new T2(0,_12D,_12F);},_12I=1,_12J=new T(function(){var _12K=B(_12z(_kg,_lR,_12I));return new T2(1,_12K.a,_12K.b);}),_12L=function(_12M,_12N,_12O,_12P,_12Q,_12R,_12S,_12T,_12U,_12V,_12W,_12X,_12Y,_12Z,_130,_131,_132,_133,_134,_135,_136,_137,_138,_139,_13a,_13b,_13c,_13d,_13e,_13f,_13g,_13h,_13i,_13j,_13k,_){var _13l={_:0,a:E(_13c),b:E(_13d),c:E(_13e),d:E(_13f),e:E(_13g),f:E(_13h),g:E(_13i),h:E(_13j)};if(!E(_13e)){return {_:0,a:E(_12Q),b:E(new T2(0,_12R,_12S)),c:E(_12T),d:E(_12U),e:E(_12V),f:E(_12W),g:E(_12X),h:E(new T2(0,_12Y,_12Z)),i:_130,j:_131,k:_132,l:_133,m:E(_134),n:_135,o:E(_136),p:E(_137),q:_138,r:E(_139),s:E(_13a),t:_13b,u:E(_13l),v:E(_13k)};}else{if(!E(_13f)){var _13m=B(_102(_fX,_12N,_12O,_13l,{_:0,a:E(_12Q),b:E(new T2(0,_12R,_12S)),c:E(_12T),d:E(_12U),e:E(_12V),f:E(_12W),g:E(_12X),h:E(new T2(0,_12Y,_12Z)),i:_130,j:_131,k:_132,l:_133,m:E(_134),n:_135,o:E(_136),p:E(_137),q:_138,r:E(_139),s:E(_13a),t:_13b,u:E(_13l),v:E(_13k)})),_13n=_13m.d,_13o=_13m.e,_13p=_13m.f,_13q=_13m.i,_13r=_13m.n,_13s=_13m.p,_13t=_13m.q,_13u=_13m.s,_13v=_13m.t;if(!E(_13m.o)){var _13w=B(_12k(_fs,_13s,_13t,_13m.g,_13m.h,_13m.k,_13m.m,_13m.r,_13u)),_13x=_13w.c,_13y=_13w.d,_13z=function(_){var _13A=function(_){if(!E(_13s)){if(!E(_13t)){var _13B=B(_mG(E(_12M).a,_13q,_na,_lR,_13m.b,_13m.c,_13m.a,_));return _13v;}else{return _13v;}}else{return _13v;}};if(!E(_13w.b)){return new F(function(){return _13A(_);});}else{var _13C=E(_12M),_13D=_13C.a,_13E=_13C.b,_13F=B(_se(_13D,_13E,_12N,_13m.l,_12P,_13u,_)),_13G=B(_pt(_13D,_13E,_12O,0,_13p,_13y,_13p,_13x,_));return new F(function(){return _13A(_);});}};if(!E(_13w.a)){return new F(function(){return _13z(_);});}else{var _13H=B(_nf(_12M,_12O,0,_13p,_13y,_13p,_13x,_));return new F(function(){return _13z(_);});}}else{var _13I=E(_13m.j);if(!_13I._){return _13v;}else{var _13J=E(_12J);if(!_13J._){return _13v;}else{var _13K=E(_12M).a,_13L=B(_mG(_13K,_13q,_13r,_13J.a,_13n,_13o,_13I.a,_)),_13M=function(_13N,_13O,_){while(1){var _13P=E(_13N);if(!_13P._){return _kJ;}else{var _13Q=E(_13O);if(!_13Q._){return _kJ;}else{var _13R=B(_mG(_13K,_13q,_13r,_13Q.a,_13n,_13o,_13P.a,_));_13N=_13P.b;_13O=_13Q.b;continue;}}}},_13S=B(_13M(_13I.b,_13J.b,_));return _13v;}}}}else{return {_:0,a:E(_12Q),b:E(new T2(0,_12R,_12S)),c:E(_12T),d:E(_12U),e:E(_12V),f:E(_12W),g:E(_12X),h:E(new T2(0,_12Y,_12Z)),i:_130,j:_131,k:_132,l:_133,m:E(_134),n:_135,o:E(_136),p:E(_137),q:_138,r:E(_139),s:E(_13a),t:_13b,u:E(_13l),v:E(_13k)};}}},_13T=function(_13U,_13V,_13W,_13X,_13Y,_13Z,_140,_141,_142,_143,_144,_145,_146,_147,_148,_149,_14a,_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_){while(1){var _14t=B(_12L(_13U,_13V,_13W,_13X,_13Y,_13Z,_140,_141,_142,_143,_144,_145,_146,_147,_148,_149,_14a,_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_)),_14u=E(_14t),_14v=_14u.a,_14w=_14u.c,_14x=_14u.d,_14y=_14u.e,_14z=_14u.f,_14A=_14u.g,_14B=_14u.i,_14C=_14u.j,_14D=_14u.k,_14E=_14u.l,_14F=_14u.m,_14G=_14u.n,_14H=_14u.o,_14I=_14u.p,_14J=_14u.q,_14K=_14u.r,_14L=_14u.s,_14M=_14u.t,_14N=_14u.v,_14O=E(_14u.u),_14P=_14O.a,_14Q=_14O.b,_14R=_14O.c,_14S=_14O.e,_14T=_14O.g,_14U=_14O.h,_14V=E(_14u.b),_14W=E(_14u.h);if(!E(_14O.d)){if(!E(_14m)){return {_:0,a:E(_14v),b:E(_14V),c:E(_14w),d:E(_14x),e:E(_14y),f:E(_14z),g:E(_14A),h:E(_14W),i:_14B,j:_14C,k:_14D,l:_14E,m:E(_14F),n:_14G,o:E(_14H),p:E(_14I),q:_14J,r:E(_14K),s:E(_14L),t:_14M,u:E({_:0,a:E(_14P),b:E(_14Q),c:E(_14R),d:E(_B2),e:E(_14S),f:E(_B2),g:E(_14T),h:E(_14U)}),v:E(_14N)};}else{_13Y=_14v;_13Z=_14V.a;_140=_14V.b;_141=_14w;_142=_14x;_143=_14y;_144=_14z;_145=_14A;_146=_14W.a;_147=_14W.b;_148=_14B;_149=_14C;_14a=_14D;_14b=_14E;_14c=_14F;_14d=_14G;_14e=_14H;_14f=_14I;_14g=_14J;_14h=_14K;_14i=_14L;_14j=_14M;_14k=_14P;_14l=_14Q;_14m=_14R;_14n=_B2;_14o=_14S;_14p=_14O.f;_14q=_14T;_14r=_14U;_14s=_14N;continue;}}else{return {_:0,a:E(_14v),b:E(_14V),c:E(_14w),d:E(_14x),e:E(_14y),f:E(_14z),g:E(_14A),h:E(_14W),i:_14B,j:_14C,k:_14D,l:_14E,m:E(_14F),n:_14G,o:E(_14H),p:E(_14I),q:_14J,r:E(_14K),s:E(_14L),t:_14M,u:E({_:0,a:E(_14P),b:E(_14Q),c:E(_14R),d:E(_B3),e:E(_14S),f:E(_B2),g:E(_14T),h:E(_14U)}),v:E(_14N)};}}},_14X=function(_14Y,_14Z,_150,_151,_152,_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v,_){var _15w=B(_12L(_14Y,_14Z,_150,_151,_152,_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_B3,_15q,_15r,_15s,_15t,_15u,_15v,_)),_15x=E(_15w),_15y=_15x.a,_15z=_15x.c,_15A=_15x.d,_15B=_15x.e,_15C=_15x.f,_15D=_15x.g,_15E=_15x.i,_15F=_15x.j,_15G=_15x.k,_15H=_15x.l,_15I=_15x.m,_15J=_15x.n,_15K=_15x.o,_15L=_15x.p,_15M=_15x.q,_15N=_15x.r,_15O=_15x.s,_15P=_15x.t,_15Q=_15x.v,_15R=E(_15x.u),_15S=_15R.a,_15T=_15R.b,_15U=_15R.c,_15V=_15R.e,_15W=_15R.g,_15X=_15R.h,_15Y=E(_15x.b),_15Z=E(_15x.h);if(!E(_15R.d)){return new F(function(){return _13T(_14Y,_14Z,_150,_151,_15y,_15Y.a,_15Y.b,_15z,_15A,_15B,_15C,_15D,_15Z.a,_15Z.b,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L,_15M,_15N,_15O,_15P,_15S,_15T,_15U,_B2,_15V,_15R.f,_15W,_15X,_15Q,_);});}else{return {_:0,a:E(_15y),b:E(_15Y),c:E(_15z),d:E(_15A),e:E(_15B),f:E(_15C),g:E(_15D),h:E(_15Z),i:_15E,j:_15F,k:_15G,l:_15H,m:E(_15I),n:_15J,o:E(_15K),p:E(_15L),q:_15M,r:E(_15N),s:E(_15O),t:_15P,u:E({_:0,a:E(_15S),b:E(_15T),c:E(_15U),d:E(_B3),e:E(_15V),f:E(_B2),g:E(_15W),h:E(_15X)}),v:E(_15Q)};}},_160=function(_161){var _162=E(_161);if(!_162._){return __Z;}else{var _163=E(_162.b);return (_163._==0)?__Z:new T2(1,new T2(0,_162.a,_163.a),new T(function(){return B(_160(_163.b));}));}},_164=function(_165,_166,_167){return new T2(1,new T2(0,_165,_166),new T(function(){return B(_160(_167));}));},_168=function(_169,_16a){var _16b=E(_16a);return (_16b._==0)?__Z:new T2(1,new T2(0,_169,_16b.a),new T(function(){return B(_160(_16b.b));}));},_16c="Invalid JSON!",_16d=new T1(0,_16c),_16e="No such value",_16f=new T1(0,_16e),_16g=new T(function(){return eval("(function(k) {return localStorage.getItem(k);})");}),_16h=function(_16i){return E(E(_16i).c);},_16j=function(_16k,_16l,_){var _16m=__app1(E(_16g),_16l),_16n=__eq(_16m,E(_3h));if(!E(_16n)){var _16o=__isUndef(_16m);return (E(_16o)==0)?new T(function(){var _16p=String(_16m),_16q=jsParseJSON(_16p);if(!_16q._){return E(_16d);}else{return B(A2(_16h,_16k,_16q.a));}}):_16f;}else{return _16f;}},_16r=new T1(0,0),_16s=function(_16t,_16u){while(1){var _16v=E(_16t);if(!_16v._){var _16w=_16v.a,_16x=E(_16u);if(!_16x._){return new T1(0,(_16w>>>0|_16x.a>>>0)>>>0&4294967295);}else{_16t=new T1(1,I_fromInt(_16w));_16u=_16x;continue;}}else{var _16y=E(_16u);if(!_16y._){_16t=_16v;_16u=new T1(1,I_fromInt(_16y.a));continue;}else{return new T1(1,I_or(_16v.a,_16y.a));}}}},_16z=function(_16A){var _16B=E(_16A);if(!_16B._){return E(_16r);}else{return new F(function(){return _16s(new T1(0,E(_16B.a)),B(_gT(B(_16z(_16B.b)),31)));});}},_16C=function(_16D,_16E){if(!E(_16D)){return new F(function(){return _jy(B(_16z(_16E)));});}else{return new F(function(){return _16z(_16E);});}},_16F=1420103680,_16G=465,_16H=new T2(1,_16G,_Z),_16I=new T2(1,_16F,_16H),_16J=new T(function(){return B(_16C(_B3,_16I));}),_16K=function(_16L){return E(_16J);},_16M=new T(function(){return B(unCStr("s"));}),_16N=function(_16O,_16P){while(1){var _16Q=E(_16O);if(!_16Q._){return E(_16P);}else{_16O=_16Q.b;_16P=_16Q.a;continue;}}},_16R=function(_16S,_16T,_16U){return new F(function(){return _16N(_16T,_16S);});},_16V=new T1(0,1),_16W=function(_16X,_16Y){var _16Z=E(_16X);return new T2(0,_16Z,new T(function(){var _170=B(_16W(B(_gA(_16Z,_16Y)),_16Y));return new T2(1,_170.a,_170.b);}));},_171=function(_172){var _173=B(_16W(_172,_16V));return new T2(1,_173.a,_173.b);},_174=function(_175,_176){var _177=B(_16W(_175,new T(function(){return B(_iT(_176,_175));})));return new T2(1,_177.a,_177.b);},_178=new T1(0,0),_179=function(_17a,_17b){var _17c=E(_17a);if(!_17c._){var _17d=_17c.a,_17e=E(_17b);return (_17e._==0)?_17d>=_17e.a:I_compareInt(_17e.a,_17d)<=0;}else{var _17f=_17c.a,_17g=E(_17b);return (_17g._==0)?I_compareInt(_17f,_17g.a)>=0:I_compare(_17f,_17g.a)>=0;}},_17h=function(_17i,_17j,_17k){if(!B(_179(_17j,_178))){var _17l=function(_17m){return (!B(_hc(_17m,_17k)))?new T2(1,_17m,new T(function(){return B(_17l(B(_gA(_17m,_17j))));})):__Z;};return new F(function(){return _17l(_17i);});}else{var _17n=function(_17o){return (!B(_h3(_17o,_17k)))?new T2(1,_17o,new T(function(){return B(_17n(B(_gA(_17o,_17j))));})):__Z;};return new F(function(){return _17n(_17i);});}},_17p=function(_17q,_17r,_17s){return new F(function(){return _17h(_17q,B(_iT(_17r,_17q)),_17s);});},_17t=function(_17u,_17v){return new F(function(){return _17h(_17u,_16V,_17v);});},_17w=function(_17x){return new F(function(){return _ff(_17x);});},_17y=function(_17z){return new F(function(){return _iT(_17z,_16V);});},_17A=function(_17B){return new F(function(){return _gA(_17B,_16V);});},_17C=function(_17D){return new F(function(){return _eW(E(_17D));});},_17E={_:0,a:_17A,b:_17y,c:_17C,d:_17w,e:_171,f:_174,g:_17t,h:_17p},_17F=function(_17G,_17H){while(1){var _17I=E(_17G);if(!_17I._){var _17J=E(_17I.a);if(_17J==( -2147483648)){_17G=new T1(1,I_fromInt( -2147483648));continue;}else{var _17K=E(_17H);if(!_17K._){return new T1(0,B(_do(_17J,_17K.a)));}else{_17G=new T1(1,I_fromInt(_17J));_17H=_17K;continue;}}}else{var _17L=_17I.a,_17M=E(_17H);return (_17M._==0)?new T1(1,I_div(_17L,I_fromInt(_17M.a))):new T1(1,I_div(_17L,_17M.a));}}},_17N=function(_17O,_17P){if(!B(_gs(_17P,_tg))){return new F(function(){return _17F(_17O,_17P);});}else{return E(_dZ);}},_17Q=function(_17R,_17S){while(1){var _17T=E(_17R);if(!_17T._){var _17U=E(_17T.a);if(_17U==( -2147483648)){_17R=new T1(1,I_fromInt( -2147483648));continue;}else{var _17V=E(_17S);if(!_17V._){var _17W=_17V.a;return new T2(0,new T1(0,B(_do(_17U,_17W))),new T1(0,B(_et(_17U,_17W))));}else{_17R=new T1(1,I_fromInt(_17U));_17S=_17V;continue;}}}else{var _17X=E(_17S);if(!_17X._){_17R=_17T;_17S=new T1(1,I_fromInt(_17X.a));continue;}else{var _17Y=I_divMod(_17T.a,_17X.a);return new T2(0,new T1(1,_17Y.a),new T1(1,_17Y.b));}}}},_17Z=function(_180,_181){if(!B(_gs(_181,_tg))){var _182=B(_17Q(_180,_181));return new T2(0,_182.a,_182.b);}else{return E(_dZ);}},_183=function(_184,_185){while(1){var _186=E(_184);if(!_186._){var _187=E(_186.a);if(_187==( -2147483648)){_184=new T1(1,I_fromInt( -2147483648));continue;}else{var _188=E(_185);if(!_188._){return new T1(0,B(_et(_187,_188.a)));}else{_184=new T1(1,I_fromInt(_187));_185=_188;continue;}}}else{var _189=_186.a,_18a=E(_185);return (_18a._==0)?new T1(1,I_mod(_189,I_fromInt(_18a.a))):new T1(1,I_mod(_189,_18a.a));}}},_18b=function(_18c,_18d){if(!B(_gs(_18d,_tg))){return new F(function(){return _183(_18c,_18d);});}else{return E(_dZ);}},_18e=function(_18f,_18g){while(1){var _18h=E(_18f);if(!_18h._){var _18i=E(_18h.a);if(_18i==( -2147483648)){_18f=new T1(1,I_fromInt( -2147483648));continue;}else{var _18j=E(_18g);if(!_18j._){return new T1(0,quot(_18i,_18j.a));}else{_18f=new T1(1,I_fromInt(_18i));_18g=_18j;continue;}}}else{var _18k=_18h.a,_18l=E(_18g);return (_18l._==0)?new T1(0,I_toInt(I_quot(_18k,I_fromInt(_18l.a)))):new T1(1,I_quot(_18k,_18l.a));}}},_18m=function(_18n,_18o){if(!B(_gs(_18o,_tg))){return new F(function(){return _18e(_18n,_18o);});}else{return E(_dZ);}},_18p=function(_18q,_18r){if(!B(_gs(_18r,_tg))){var _18s=B(_gJ(_18q,_18r));return new T2(0,_18s.a,_18s.b);}else{return E(_dZ);}},_18t=function(_18u,_18v){while(1){var _18w=E(_18u);if(!_18w._){var _18x=E(_18w.a);if(_18x==( -2147483648)){_18u=new T1(1,I_fromInt( -2147483648));continue;}else{var _18y=E(_18v);if(!_18y._){return new T1(0,_18x%_18y.a);}else{_18u=new T1(1,I_fromInt(_18x));_18v=_18y;continue;}}}else{var _18z=_18w.a,_18A=E(_18v);return (_18A._==0)?new T1(1,I_rem(_18z,I_fromInt(_18A.a))):new T1(1,I_rem(_18z,_18A.a));}}},_18B=function(_18C,_18D){if(!B(_gs(_18D,_tg))){return new F(function(){return _18t(_18C,_18D);});}else{return E(_dZ);}},_18E=function(_18F){return E(_18F);},_18G=function(_18H){return E(_18H);},_18I=function(_18J){var _18K=E(_18J);if(!_18K._){var _18L=E(_18K.a);return (_18L==( -2147483648))?E(_jx):(_18L<0)?new T1(0, -_18L):E(_18K);}else{var _18M=_18K.a;return (I_compareInt(_18M,0)>=0)?E(_18K):new T1(1,I_negate(_18M));}},_18N=new T1(0, -1),_18O=function(_18P){var _18Q=E(_18P);if(!_18Q._){var _18R=_18Q.a;return (_18R>=0)?(E(_18R)==0)?E(_16r):E(_hb):E(_18N);}else{var _18S=I_compareInt(_18Q.a,0);return (_18S<=0)?(E(_18S)==0)?E(_16r):E(_18N):E(_hb);}},_18T={_:0,a:_gA,b:_iT,c:_sK,d:_jy,e:_18I,f:_18O,g:_18G},_18U=function(_18V,_18W){var _18X=E(_18V);if(!_18X._){var _18Y=_18X.a,_18Z=E(_18W);return (_18Z._==0)?_18Y!=_18Z.a:(I_compareInt(_18Z.a,_18Y)==0)?false:true;}else{var _190=_18X.a,_191=E(_18W);return (_191._==0)?(I_compareInt(_190,_191.a)==0)?false:true:(I_compare(_190,_191.a)==0)?false:true;}},_192=new T2(0,_gs,_18U),_193=function(_194,_195){return (!B(_iE(_194,_195)))?E(_194):E(_195);},_196=function(_197,_198){return (!B(_iE(_197,_198)))?E(_198):E(_197);},_199={_:0,a:_192,b:_gc,c:_hc,d:_iE,e:_h3,f:_179,g:_193,h:_196},_19a=function(_19b){return new T2(0,E(_19b),E(_f0));},_19c=new T3(0,_18T,_199,_19a),_19d={_:0,a:_19c,b:_17E,c:_18m,d:_18B,e:_17N,f:_18b,g:_18p,h:_17Z,i:_18E},_19e=new T1(0,0),_19f=function(_19g,_19h,_19i){var _19j=B(A1(_19g,_19h));if(!B(_gs(_19j,_19e))){return new F(function(){return _17F(B(_sK(_19h,_19i)),_19j);});}else{return E(_dZ);}},_19k=function(_19l,_19m){while(1){if(!B(_gs(_19m,_tg))){var _19n=_19m,_19o=B(_18B(_19l,_19m));_19l=_19n;_19m=_19o;continue;}else{return E(_19l);}}},_19p=5,_19q=new T(function(){return B(_dV(_19p));}),_19r=new T(function(){return die(_19q);}),_19s=function(_19t,_19u){if(!B(_gs(_19u,_tg))){var _19v=B(_19k(B(_18I(_19t)),B(_18I(_19u))));return (!B(_gs(_19v,_tg)))?new T2(0,B(_18e(_19t,_19v)),B(_18e(_19u,_19v))):E(_dZ);}else{return E(_19r);}},_19w=function(_19x,_19y,_19z,_19A){var _19B=B(_sK(_19y,_19z));return new F(function(){return _19s(B(_sK(B(_sK(_19x,_19A)),B(_18O(_19B)))),B(_18I(_19B)));});},_19C=function(_19D,_19E,_19F){var _19G=new T(function(){if(!B(_gs(_19F,_tg))){var _19H=B(_gJ(_19E,_19F));return new T2(0,_19H.a,_19H.b);}else{return E(_dZ);}}),_19I=new T(function(){return B(A2(_lj,B(_sz(B(_sx(_19D)))),new T(function(){return E(E(_19G).a);})));});return new T2(0,_19I,new T(function(){return new T2(0,E(E(_19G).b),E(_19F));}));},_19J=function(_19K,_19L,_19M){var _19N=B(_19C(_19K,_19L,_19M)),_19O=_19N.a,_19P=E(_19N.b);if(!B(_hc(B(_sK(_19P.a,_f0)),B(_sK(_tg,_19P.b))))){return E(_19O);}else{var _19Q=B(_sz(B(_sx(_19K))));return new F(function(){return A3(_tc,_19Q,_19O,new T(function(){return B(A2(_lj,_19Q,_f0));}));});}},_19R=479723520,_19S=40233135,_19T=new T2(1,_19S,_Z),_19U=new T2(1,_19R,_19T),_19V=new T(function(){return B(_16C(_B3,_19U));}),_19W=new T1(0,40587),_19X=function(_19Y){var _19Z=new T(function(){var _1a0=B(_19w(_19Y,_f0,_16J,_f0)),_1a1=B(_19w(_19V,_f0,_16J,_f0)),_1a2=B(_19w(_1a0.a,_1a0.b,_1a1.a,_1a1.b));return B(_19J(_19d,_1a2.a,_1a2.b));});return new T2(0,new T(function(){return B(_gA(_19W,_19Z));}),new T(function(){return B(_iT(_19Y,B(_19f(_16K,B(_sK(_19Z,_16J)),_19V))));}));},_1a3=function(_1a4,_){var _1a5=__get(_1a4,0),_1a6=__get(_1a4,1),_1a7=Number(_1a5),_1a8=jsTrunc(_1a7),_1a9=Number(_1a6),_1aa=jsTrunc(_1a9);return new T2(0,_1a8,_1aa);},_1ab=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_1ac=660865024,_1ad=465661287,_1ae=new T2(1,_1ad,_Z),_1af=new T2(1,_1ac,_1ae),_1ag=new T(function(){return B(_16C(_B3,_1af));}),_1ah=function(_){var _1ai=__app0(E(_1ab)),_1aj=B(_1a3(_1ai,_));return new T(function(){var _1ak=E(_1aj);if(!B(_gs(_1ag,_19e))){return B(_gA(B(_sK(B(_eW(E(_1ak.a))),_16J)),B(_17F(B(_sK(B(_sK(B(_eW(E(_1ak.b))),_16J)),_16J)),_1ag))));}else{return E(_dZ);}});},_1al=new T(function(){return B(err(_x2));}),_1am=new T(function(){return B(err(_wY));}),_1an=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1ao=new T1(0,1),_1ap=new T1(0,10),_1aq=function(_1ar){while(1){var _1as=E(_1ar);if(!_1as._){_1ar=new T1(1,I_fromInt(_1as.a));continue;}else{return new F(function(){return I_toString(_1as.a);});}}},_1at=function(_1au,_1av){return new F(function(){return _x(fromJSStr(B(_1aq(_1au))),_1av);});},_1aw=new T1(0,0),_1ax=function(_1ay,_1az,_1aA){if(_1ay<=6){return new F(function(){return _1at(_1az,_1aA);});}else{if(!B(_hc(_1az,_1aw))){return new F(function(){return _1at(_1az,_1aA);});}else{return new T2(1,_G,new T(function(){return B(_x(fromJSStr(B(_1aq(_1az))),new T2(1,_F,_1aA)));}));}}},_1aB=function(_1aC){return new F(function(){return _1ax(0,_1aC,_Z);});},_1aD=new T(function(){return B(_gs(_1ap,_19e));}),_1aE=function(_1aF){while(1){if(!B(_gs(_1aF,_19e))){if(!E(_1aD)){if(!B(_gs(B(_183(_1aF,_1ap)),_19e))){return new F(function(){return _1aB(_1aF);});}else{var _1aG=B(_17F(_1aF,_1ap));_1aF=_1aG;continue;}}else{return E(_dZ);}}else{return __Z;}}},_1aH=46,_1aI=48,_1aJ=function(_1aK,_1aL,_1aM){if(!B(_hc(_1aM,_19e))){var _1aN=B(A1(_1aK,_1aM));if(!B(_gs(_1aN,_19e))){var _1aO=B(_17Q(_1aM,_1aN)),_1aP=_1aO.b,_1aQ=new T(function(){var _1aR=Math.log(B(_jR(_1aN)))/Math.log(10),_1aS=_1aR&4294967295,_1aT=function(_1aU){if(_1aU>=0){var _1aV=E(_1aU);if(!_1aV){var _1aW=B(_17F(B(_iT(B(_gA(B(_sK(_1aP,_f0)),_1aN)),_1ao)),_1aN));}else{var _1aW=B(_17F(B(_iT(B(_gA(B(_sK(_1aP,B(_t0(_1ap,_1aV)))),_1aN)),_1ao)),_1aN));}var _1aX=function(_1aY){var _1aZ=B(_1ax(0,_1aW,_Z)),_1b0=_1aU-B(_qy(_1aZ,0))|0;if(0>=_1b0){if(!E(_1aL)){return E(_1aZ);}else{return new F(function(){return _1aE(_1aW);});}}else{var _1b1=new T(function(){if(!E(_1aL)){return E(_1aZ);}else{return B(_1aE(_1aW));}}),_1b2=function(_1b3){var _1b4=E(_1b3);return (_1b4==1)?E(new T2(1,_1aI,_1b1)):new T2(1,_1aI,new T(function(){return B(_1b2(_1b4-1|0));}));};return new F(function(){return _1b2(_1b0);});}};if(!E(_1aL)){var _1b5=B(_1aX(_));return (_1b5._==0)?__Z:new T2(1,_1aH,_1b5);}else{if(!B(_gs(_1aW,_19e))){var _1b6=B(_1aX(_));return (_1b6._==0)?__Z:new T2(1,_1aH,_1b6);}else{return __Z;}}}else{return E(_tW);}};if(_1aS>=_1aR){return B(_1aT(_1aS));}else{return B(_1aT(_1aS+1|0));}},1);return new F(function(){return _x(B(_1ax(0,_1aO.a,_Z)),_1aQ);});}else{return E(_dZ);}}else{return new F(function(){return unAppCStr("-",new T(function(){return B(_1aJ(_1aK,_1aL,B(_jy(_1aM))));}));});}},_1b7=function(_1b8,_1b9,_){var _1ba=B(_1ah(_)),_1bb=new T(function(){var _1bc=new T(function(){var _1bd=new T(function(){var _1be=B(_x(B(_1aJ(_16K,_B3,B(_19X(_1ba)).b)),_16M));if(!_1be._){return E(_Yi);}else{var _1bf=B(_Yd(_1be.a,_1be.b));if(!_1bf._){return B(_16R(_Z,_Z,_ZW));}else{var _1bg=_1bf.a,_1bh=E(_1bf.b);if(!_1bh._){return B(_16R(new T2(1,_1bg,_Z),_Z,_ZW));}else{var _1bi=E(_1bg),_1bj=new T(function(){var _1bk=B(_LC(46,_1bh.a,_1bh.b));return new T2(0,_1bk.a,_1bk.b);});if(E(_1bi)==46){return B(_16R(_Z,new T2(1,new T(function(){return E(E(_1bj).a);}),new T(function(){return E(E(_1bj).b);})),_ZW));}else{return B(_16R(new T2(1,_1bi,new T(function(){return E(E(_1bj).a);})),new T(function(){return E(E(_1bj).b);}),_ZW));}}}}}),_1bl=B(_KK(B(_x7(_1an,_1bd))));if(!_1bl._){return E(_1am);}else{if(!E(_1bl.b)._){return B(_uj(3,B(_H(0,E(_1bl.a)+(imul(E(_1b9),E(_1b8)-1|0)|0)|0,_Z))));}else{return E(_1al);}}}),_1bm=B(_KK(B(_x7(_1an,_1bc))));if(!_1bm._){return E(_1am);}else{if(!E(_1bm.b)._){return E(_1bm.a);}else{return E(_1al);}}});return new T2(0,new T(function(){return B(_eA(_1bb,_1b8));}),_1bb);},_1bn=function(_1bo,_1bp,_1bq,_1br,_1bs,_1bt,_){var _1bu=function(_1bv,_){return new F(function(){return _rT(_s9,_s9,function(_1bw,_){return new F(function(){return _s3(B(_aW(_1bp,E(_1bt))),0,0,E(_1bw),_);});},E(_1bv),_);});};return new F(function(){return _kX(new T(function(){return E(_1bq)-E(_1br)*16;},1),new T(function(){return E(_1bs)*20;},1),_1bu,_1bo,_);});},_1bx=1,_1by=new T(function(){return B(_aW(_n9,1));}),_1bz=function(_1bA){return E(_1bA).d;},_1bB=function(_1bC,_1bD,_1bE,_1bF,_1bG,_1bH,_){var _1bI=new T(function(){return E(E(_1bH).s);}),_1bJ=new T(function(){return E(E(_1bI).a);}),_1bK=new T(function(){if(!B(_et(E(_1bH).t,10))){var _1bL=E(E(_1bI).b);if(!(_1bL%2)){return _1bL+1|0;}else{return _1bL-1|0;}}else{return E(E(_1bI).b);}}),_1bM=new T(function(){var _1bN=E(_1bH);return {_:0,a:E(_1bN.a),b:E(_1bN.b),c:E(_1bN.c),d:E(_1bN.d),e:E(_1bN.e),f:E(_1bN.f),g:E(_1bN.g),h:E(_1bN.h),i:_1bN.i,j:_1bN.j,k:_1bN.k,l:_1bN.l,m:E(_1bN.m),n:_1bN.n,o:E(_1bN.o),p:E(_1bN.p),q:_1bN.q,r:E(_1bN.r),s:E(new T2(0,_1bJ,_1bK)),t:_1bN.t,u:E(_1bN.u),v:E(_1bN.v)};}),_1bO=new T(function(){return E(E(_1bM).a);}),_1bP=new T(function(){return E(E(_1bM).b);}),_1bQ=new T(function(){return E(E(_1bP).a);}),_1bR=new T(function(){var _1bS=E(_1bE)/16,_1bT=_1bS&4294967295;if(_1bS>=_1bT){return _1bT-2|0;}else{return (_1bT-1|0)-2|0;}}),_1bU=B(_rv(_1bC,_1bD,new T(function(){return B(_f9(_1bR,_1bQ));}),_sd,new T(function(){return E(E(_1bO).b);}),_)),_1bV=new T(function(){return E(E(E(_1bM).a).a);}),_1bW=B(A(_qT,[_1bC,new T(function(){if(E(E(_1bO).e)==32){return E(_sb);}else{return E(_sc);}}),new T(function(){return ((E(E(_1bV).a)+E(_1bR)|0)-E(_1bQ)|0)+1|0;},1),new T(function(){return (E(E(_1bV).b)+2|0)+1|0;},1),new T2(1,new T(function(){return B(_1bz(_1bO));}),_Z),_])),_1bX=E(_1bM),_1bY=_1bX.c,_1bZ=_1bX.k,_1c0=E(_1bX.u),_1c1=new T(function(){var _1c2=E(_1bE)/28,_1c3=_1c2&4294967295;if(_1c2>=_1c3){return (_1c3-1|0)+_1bZ|0;}else{return ((_1c3-1|0)-1|0)+_1bZ|0;}}),_1c4=new T(function(){return (2+E(E(_1bP).b)|0)+3|0;}),_1c5=new T2(0,_1bC,_1bD),_1c6=function(_){var _1c7=function(_){var _1c8=function(_){var _1c9=B(_1bn(_1bC,new T(function(){return E(E(_1bG).b);},1),_1bE,new T(function(){return E(_1bQ)+10|0;},1),_sd,new T(function(){return (imul(E(_1bJ),8)|0)+E(_1bK)|0;},1),_));return _1bX;};if(!E(_1bX.p)._){return new F(function(){return _1c8(_);});}else{var _1ca=B(A(_qT,[_1bC,_1by,_1bx,_1bx,B(_H(0,_1bX.q,_Z)),_]));return new F(function(){return _1c8(_);});}};if(!E(_1c0.g)){return new F(function(){return _1c7(_);});}else{var _1cb=B(_nf(_1c5,_1bF,0,_1c4,_1c1,_1c4,B(_126(_1bY,new T(function(){return B(_aj(_wQ,_1bX.m));},1),_1bX.n)),_));return new F(function(){return _1c7(_);});}};if(!E(_1c0.c)){var _1cc=B(_nf(_1c5,_1bF,0,_1c4,_1c1,_1c4,_1bY,_));return new F(function(){return _1c6(_);});}else{return new F(function(){return _1c6(_);});}},_1cd=function(_1ce,_1cf){while(1){var _1cg=E(_1cf);if(!_1cg._){return __Z;}else{var _1ch=_1cg.b,_1ci=E(_1ce);if(_1ci==1){return E(_1ch);}else{_1ce=_1ci-1|0;_1cf=_1ch;continue;}}}},_1cj=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1ck=new T(function(){return B(err(_1cj));}),_1cl=0,_1cm=function(_1cn,_1co,_1cp){return new F(function(){return _H(E(_1cn),E(_1co),_1cp);});},_1cq=function(_1cr,_1cs){return new F(function(){return _H(0,E(_1cr),_1cs);});},_1ct=function(_1cu,_1cv){return new F(function(){return _2C(_1cq,_1cu,_1cv);});},_1cw=new T3(0,_1cm,_aG,_1ct),_1cx=0,_1cy=new T(function(){return B(unCStr(" out of range "));}),_1cz=new T(function(){return B(unCStr("}.index: Index "));}),_1cA=new T(function(){return B(unCStr("Ix{"));}),_1cB=new T2(1,_F,_Z),_1cC=new T2(1,_F,_1cB),_1cD=0,_1cE=function(_1cF){return E(E(_1cF).a);},_1cG=function(_1cH,_1cI,_1cJ,_1cK,_1cL){var _1cM=new T(function(){var _1cN=new T(function(){var _1cO=new T(function(){var _1cP=new T(function(){var _1cQ=new T(function(){return B(A3(_wK,_aC,new T2(1,new T(function(){return B(A3(_1cE,_1cJ,_1cD,_1cK));}),new T2(1,new T(function(){return B(A3(_1cE,_1cJ,_1cD,_1cL));}),_Z)),_1cC));});return B(_x(_1cy,new T2(1,_G,new T2(1,_G,_1cQ))));});return B(A(_1cE,[_1cJ,_1cx,_1cI,new T2(1,_F,_1cP)]));});return B(_x(_1cz,new T2(1,_G,_1cO)));},1);return B(_x(_1cH,_1cN));},1);return new F(function(){return err(B(_x(_1cA,_1cM)));});},_1cR=function(_1cS,_1cT,_1cU,_1cV,_1cW){return new F(function(){return _1cG(_1cS,_1cT,_1cW,_1cU,_1cV);});},_1cX=function(_1cY,_1cZ,_1d0,_1d1){var _1d2=E(_1d0);return new F(function(){return _1cR(_1cY,_1cZ,_1d2.a,_1d2.b,_1d1);});},_1d3=function(_1d4,_1d5,_1d6,_1d7){return new F(function(){return _1cX(_1d7,_1d6,_1d5,_1d4);});},_1d8=new T(function(){return B(unCStr("Int"));}),_1d9=function(_1da,_1db,_1dc){return new F(function(){return _1d3(_1cw,new T2(0,_1db,_1dc),_1da,_1d8);});},_1dd=new T(function(){return B(unCStr("Negative range size"));}),_1de=new T(function(){return B(err(_1dd));}),_1df=function(_1dg){var _1dh=B(A1(_1dg,_));return E(_1dh);},_1di=function(_1dj,_1dk,_1dl,_){var _1dm=E(_1dj);if(!_1dm){return new T2(0,_Z,_1dk);}else{var _1dn=new T(function(){return B(_qy(_1dl,0))-1|0;}),_1do=B(_1b7(new T(function(){return E(_1dn)+1|0;}),_1dk,_)),_1dp=E(_1do),_1dq=_1dp.a,_1dr=_1dp.b,_1ds=new T(function(){var _1dt=E(_1dq);if(B(_qy(_1dl,0))>=(_1dt+1|0)){var _1du=new T(function(){var _1dv=_1dt+1|0;if(_1dv>0){return B(_1cd(_1dv,_1dl));}else{return E(_1dl);}});if(0>=_1dt){return E(_1du);}else{var _1dw=function(_1dx,_1dy){var _1dz=E(_1dx);if(!_1dz._){return E(_1du);}else{var _1dA=_1dz.a,_1dB=E(_1dy);return (_1dB==1)?new T2(1,_1dA,_1du):new T2(1,_1dA,new T(function(){return B(_1dw(_1dz.b,_1dB-1|0));}));}};return B(_1dw(_1dl,_1dt));}}else{return E(_1dl);}}),_1dC=B(_1di(_1dm-1|0,_1dr,_1ds,_)),_1dD=new T(function(){var _1dE=function(_){var _1dF=E(_1dn),_1dG=function(_1dH){if(_1dH>=0){var _1dI=newArr(_1dH,_1ck),_1dJ=_1dI,_1dK=E(_1dH);if(!_1dK){return new T4(0,E(_1cl),E(_1dF),0,_1dJ);}else{var _1dL=function(_1dM,_1dN,_){while(1){var _1dO=E(_1dM);if(!_1dO._){return E(_);}else{var _=_1dJ[_1dN]=_1dO.a;if(_1dN!=(_1dK-1|0)){var _1dP=_1dN+1|0;_1dM=_1dO.b;_1dN=_1dP;continue;}else{return E(_);}}}},_=B(_1dL(_1dl,0,_));return new T4(0,E(_1cl),E(_1dF),_1dK,_1dJ);}}else{return E(_1de);}};if(0>_1dF){return new F(function(){return _1dG(0);});}else{return new F(function(){return _1dG(_1dF+1|0);});}},_1dQ=B(_1df(_1dE)),_1dR=E(_1dQ.a),_1dS=E(_1dQ.b),_1dT=E(_1dq);if(_1dR>_1dT){return B(_1d9(_1dT,_1dR,_1dS));}else{if(_1dT>_1dS){return B(_1d9(_1dT,_1dR,_1dS));}else{return E(_1dQ.d[_1dT-_1dR|0]);}}});return new T2(0,new T2(1,_1dD,new T(function(){return B(_wQ(_1dC));})),_1dr);}},_1dU=function(_1dV,_1dW){while(1){var _1dX=E(_1dV);if(!_1dX._){return E(_1dW);}else{_1dV=_1dX.b;_1dW=_1dX.a;continue;}}},_1dY=function(_1dZ,_1e0,_1e1){return new F(function(){return _1dU(_1e0,_1dZ);});},_1e2=function(_1e3,_1e4){while(1){var _1e5=E(_1e3);if(!_1e5._){return E(_1e4);}else{_1e3=_1e5.b;_1e4=_1e5.a;continue;}}},_1e6=function(_1e7,_1e8,_1e9){return new F(function(){return _1e2(_1e8,_1e7);});},_1ea=function(_1eb,_1ec){while(1){var _1ed=E(_1ec);if(!_1ed._){return __Z;}else{var _1ee=_1ed.b,_1ef=E(_1eb);if(_1ef==1){return E(_1ee);}else{_1eb=_1ef-1|0;_1ec=_1ee;continue;}}}},_1eg=function(_1eh,_1ei){var _1ej=new T(function(){var _1ek=_1eh+1|0;if(_1ek>0){return B(_1ea(_1ek,_1ei));}else{return E(_1ei);}});if(0>=_1eh){return E(_1ej);}else{var _1el=function(_1em,_1en){var _1eo=E(_1em);if(!_1eo._){return E(_1ej);}else{var _1ep=_1eo.a,_1eq=E(_1en);return (_1eq==1)?new T2(1,_1ep,_1ej):new T2(1,_1ep,new T(function(){return B(_1el(_1eo.b,_1eq-1|0));}));}};return new F(function(){return _1el(_1ei,_1eh);});}},_1er=new T(function(){return B(unCStr(":"));}),_1es=function(_1et){var _1eu=E(_1et);if(!_1eu._){return __Z;}else{var _1ev=new T(function(){return B(_x(_1er,new T(function(){return B(_1es(_1eu.b));},1)));},1);return new F(function(){return _x(_1eu.a,_1ev);});}},_1ew=function(_1ex,_1ey){var _1ez=new T(function(){return B(_x(_1er,new T(function(){return B(_1es(_1ey));},1)));},1);return new F(function(){return _x(_1ex,_1ez);});},_1eA=function(_1eB){return new F(function(){return _PU("Check.hs:173:7-35|(co : na : xs)");});},_1eC=new T(function(){return B(_1eA(_));}),_1eD=new T(function(){return B(err(_wY));}),_1eE=new T(function(){return B(err(_x2));}),_1eF=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1eG=0,_1eH=new T(function(){return B(unCStr("!"));}),_1eI=function(_1eJ,_1eK){var _1eL=E(_1eK);if(!_1eL._){return E(_1eC);}else{var _1eM=E(_1eL.b);if(!_1eM._){return E(_1eC);}else{var _1eN=E(_1eL.a),_1eO=new T(function(){var _1eP=B(_LC(58,_1eM.a,_1eM.b));return new T2(0,_1eP.a,_1eP.b);}),_1eQ=function(_1eR,_1eS,_1eT){var _1eU=function(_1eV){if((_1eJ+1|0)!=_1eV){return new T3(0,_1eJ+1|0,_1eS,_1eL);}else{var _1eW=E(_1eT);return (_1eW._==0)?new T3(0,_1eG,_1eS,_Z):new T3(0,_1eG,_1eS,new T(function(){var _1eX=B(_1ew(_1eW.a,_1eW.b));if(!_1eX._){return E(_Yi);}else{return B(_Yd(_1eX.a,_1eX.b));}}));}};if(!B(_vl(_1eR,_1eH))){var _1eY=B(_KK(B(_x7(_1eF,_1eR))));if(!_1eY._){return E(_1eD);}else{if(!E(_1eY.b)._){return new F(function(){return _1eU(E(_1eY.a));});}else{return E(_1eE);}}}else{return new F(function(){return _1eU( -1);});}};if(E(_1eN)==58){return new F(function(){return _1eQ(_Z,new T(function(){return E(E(_1eO).a);}),new T(function(){return E(E(_1eO).b);}));});}else{var _1eZ=E(_1eO),_1f0=E(_1eZ.b);if(!_1f0._){return E(_1eC);}else{return new F(function(){return _1eQ(new T2(1,_1eN,_1eZ.a),_1f0.a,_1f0.b);});}}}}},_1f1=function(_1f2,_1f3){while(1){var _1f4=E(_1f3);if(!_1f4._){return __Z;}else{var _1f5=_1f4.b,_1f6=E(_1f2);if(_1f6==1){return E(_1f5);}else{_1f2=_1f6-1|0;_1f3=_1f5;continue;}}}},_1f7=function(_1f8,_1f9,_1fa){var _1fb=new T2(1,_1f9,new T(function(){var _1fc=_1f8+1|0;if(_1fc>0){return B(_1f1(_1fc,_1fa));}else{return E(_1fa);}}));if(0>=_1f8){return E(_1fb);}else{var _1fd=function(_1fe,_1ff){var _1fg=E(_1fe);if(!_1fg._){return E(_1fb);}else{var _1fh=_1fg.a,_1fi=E(_1ff);return (_1fi==1)?new T2(1,_1fh,_1fb):new T2(1,_1fh,new T(function(){return B(_1fd(_1fg.b,_1fi-1|0));}));}};return new F(function(){return _1fd(_1fa,_1f8);});}},_1fj=new T2(0,_XV,_II),_1fk=function(_1fl,_1fm,_1fn){while(1){var _1fo=E(_1fn);if(!_1fo._){return E(_1fj);}else{var _1fp=_1fo.b,_1fq=E(_1fo.a),_1fr=E(_1fq.a);if(_1fl!=E(_1fr.a)){_1fn=_1fp;continue;}else{if(_1fm!=E(_1fr.b)){_1fn=_1fp;continue;}else{return E(_1fq.b);}}}}},_1fs=function(_1ft,_1fu){while(1){var _1fv=E(_1fu);if(!_1fv._){return __Z;}else{var _1fw=_1fv.b,_1fx=E(_1ft);if(_1fx==1){return E(_1fw);}else{_1ft=_1fx-1|0;_1fu=_1fw;continue;}}}},_1fy=function(_1fz,_1fA,_1fB){var _1fC=E(_1fz);if(_1fC==1){return E(_1fB);}else{return new F(function(){return _1fs(_1fC-1|0,_1fB);});}},_1fD=function(_1fE,_1fF,_1fG){return new T2(1,new T(function(){if(0>=_1fE){return __Z;}else{return B(_uj(_1fE,new T2(1,_1fF,_1fG)));}}),new T(function(){if(_1fE>0){return B(_1fH(_1fE,B(_1fy(_1fE,_1fF,_1fG))));}else{return B(_1fD(_1fE,_1fF,_1fG));}}));},_1fH=function(_1fI,_1fJ){var _1fK=E(_1fJ);if(!_1fK._){return __Z;}else{var _1fL=_1fK.a,_1fM=_1fK.b;return new T2(1,new T(function(){if(0>=_1fI){return __Z;}else{return B(_uj(_1fI,_1fK));}}),new T(function(){if(_1fI>0){return B(_1fH(_1fI,B(_1fy(_1fI,_1fL,_1fM))));}else{return B(_1fD(_1fI,_1fL,_1fM));}}));}},_1fN=function(_1fO,_1fP,_1fQ){var _1fR=_1fP-1|0;if(0<=_1fR){var _1fS=E(_1fO),_1fT=function(_1fU){var _1fV=new T(function(){if(_1fU!=_1fR){return B(_1fT(_1fU+1|0));}else{return __Z;}}),_1fW=function(_1fX){var _1fY=E(_1fX);return (_1fY._==0)?E(_1fV):new T2(1,new T(function(){var _1fZ=E(_1fQ);if(!_1fZ._){return E(_1fj);}else{var _1g0=_1fZ.b,_1g1=E(_1fZ.a),_1g2=E(_1g1.a),_1g3=E(_1fY.a);if(_1g3!=E(_1g2.a)){return B(_1fk(_1g3,_1fU,_1g0));}else{if(_1fU!=E(_1g2.b)){return B(_1fk(_1g3,_1fU,_1g0));}else{return E(_1g1.b);}}}}),new T(function(){return B(_1fW(_1fY.b));}));};return new F(function(){return _1fW(B(_cx(0,_1fS-1|0)));});};return new F(function(){return _1fH(_1fS,B(_1fT(0)));});}else{return __Z;}},_1g4=function(_1g5){return new F(function(){return _PU("Check.hs:72:21-47|(l : r : _)");});},_1g6=new T(function(){return B(_1g4(_));}),_1g7=61,_1g8=function(_1g9,_1ga){while(1){var _1gb=E(_1g9);if(!_1gb._){return E(_1ga);}else{_1g9=_1gb.b;_1ga=_1gb.a;continue;}}},_1gc=function(_1gd,_1ge,_1gf){return new F(function(){return _1g8(_1ge,_1gd);});},_1gg=function(_1gh,_1gi){var _1gj=E(_1gi);if(!_1gj._){return new T2(0,_Z,_Z);}else{var _1gk=_1gj.a;if(!B(A1(_1gh,_1gk))){var _1gl=new T(function(){var _1gm=B(_1gg(_1gh,_1gj.b));return new T2(0,_1gm.a,_1gm.b);});return new T2(0,new T2(1,_1gk,new T(function(){return E(E(_1gl).a);})),new T(function(){return E(E(_1gl).b);}));}else{return new T2(0,_Z,_1gj);}}},_1gn=function(_1go,_1gp){while(1){var _1gq=E(_1gp);if(!_1gq._){return __Z;}else{if(!B(A1(_1go,_1gq.a))){return E(_1gq);}else{_1gp=_1gq.b;continue;}}}},_1gr=function(_1gs){var _1gt=_1gs>>>0;if(_1gt>887){var _1gu=u_iswspace(_1gs);return (E(_1gu)==0)?false:true;}else{var _1gv=E(_1gt);return (_1gv==32)?true:(_1gv-9>>>0>4)?(E(_1gv)==160)?true:false:true;}},_1gw=function(_1gx){return new F(function(){return _1gr(E(_1gx));});},_1gy=function(_1gz){var _1gA=B(_1gn(_1gw,_1gz));if(!_1gA._){return __Z;}else{var _1gB=new T(function(){var _1gC=B(_1gg(_1gw,_1gA));return new T2(0,_1gC.a,_1gC.b);});return new T2(1,new T(function(){return E(E(_1gB).a);}),new T(function(){return B(_1gy(E(_1gB).b));}));}},_1gD=function(_1gE){if(!B(_4H(_lc,_1g7,_1gE))){return new T2(0,_1gE,_Z);}else{var _1gF=new T(function(){var _1gG=E(_1gE);if(!_1gG._){return E(_1g6);}else{var _1gH=E(_1gG.b);if(!_1gH._){return E(_1g6);}else{var _1gI=_1gH.a,_1gJ=_1gH.b,_1gK=E(_1gG.a);if(E(_1gK)==61){return new T2(0,_Z,new T(function(){return E(B(_LC(61,_1gI,_1gJ)).a);}));}else{var _1gL=B(_LC(61,_1gI,_1gJ)),_1gM=E(_1gL.b);if(!_1gM._){return E(_1g6);}else{return new T2(0,new T2(1,_1gK,_1gL.a),_1gM.a);}}}}});return new T2(0,new T(function(){var _1gN=B(_1gy(E(_1gF).a));if(!_1gN._){return __Z;}else{return B(_1gc(_1gN.a,_1gN.b,_ZW));}}),new T(function(){var _1gO=B(_1gy(E(_1gF).b));if(!_1gO._){return __Z;}else{return E(_1gO.a);}}));}},_1gP=function(_1gQ,_1gR){return new F(function(){return _1eg(E(_1gQ),_1gR);});},_1gS=function(_1gT){var _1gU=E(_1gT);if(!_1gU._){return new T2(0,_Z,_Z);}else{var _1gV=E(_1gU.a),_1gW=new T(function(){var _1gX=B(_1gS(_1gU.b));return new T2(0,_1gX.a,_1gX.b);});return new T2(0,new T2(1,_1gV.a,new T(function(){return E(E(_1gW).a);})),new T2(1,_1gV.b,new T(function(){return E(E(_1gW).b);})));}},_1gY=new T(function(){return B(unCStr("\u570b\uff1a\u3053\u304f\uff1a\u53f2\uff1a\u3057\uff1a\u4e26\uff1a\u306a\u3089\uff1a\u3079\u66ff\uff1a\u304b\uff1a\u3078\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002\n{sm}{ch.\u554f\u984c\u3078,s0.\u30c1\u30e5\u30fc\u30c8\u30ea\u30a2\u30eb,t0}"));}),_1gZ=new T(function(){return B(unCStr("t0"));}),_1h0=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u30de\u30c3\u30d7\u4e0a\u306e\uff20\u3092\u52d5\uff1a\u3046\u3054\uff1a\u304b\u3057\u307e\u3059\u3002\n\u753b\uff1a\u304c\uff1a\u9762\uff1a\u3081\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u4e0b\uff1a\u304b\uff1a\u7aef\uff1a\u305f\u3093\uff1a\u30fb\u5de6\uff1a\u3072\u3060\u308a\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u30fb\u53f3\uff1a\u307f\u304e\uff1a\u7aef\uff1a\u306f\u3057\uff1a\u306a\u3069\u3092\u30bf\u30c3\u30d7\u3059\u308b\u3068\uff20\u306f\u305d\u306e\u65b9\uff1a\u306f\u3046\uff1a\u5411\uff1a\u304b\u3046\uff1a\u3078\u52d5\u304d\u307e\u3059\u3002\n{e.ea.m1:t1}{e.eb.m1:t1}{e.ec.m1:t1}"));}),_1h1=new T2(0,_1gZ,_1h0),_1h2=new T(function(){return B(unCStr("t1"));}),_1h3=new T(function(){return B(unCStr("\n\u3053\u308c\u3089\u306e\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u306e\u65b9\u5411\u3078\u884c\uff1a\u3044\uff1a\u304f\u3068 \u3042\u306a\u305f\u306f \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 <\u6301\uff1a\u3082\uff1a\u3063\u305f> \u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u306b\u306a\u308a\u307e\u3059\u3002\n\u3053\u306e\u3068\u304d\uff20\u306e\u8272\uff1a\u3044\u308d\uff1a\u304c\u6fc3\uff1a\u3053\uff1a\u304f\u306a\u3063\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f \uff20\u3092\u3069\u3053\u304b \u5225\uff1a\u3079\u3064\uff1a\u306e\u3068\u3053\u308d\u3078\u6301\u3063\u3066\u3044\u304d \u753b\u9762\u306e\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u90e8\uff1a\u3076\uff1a\u3092\u30bf\u30c3\u30d7\u3057\u3066\u304f\u3060\u3055\u3044\u3002\n{da}{e.oa.m1:t2}{e.ob.m1:t2}{e.oc.m1:t2}"));}),_1h4=new T2(0,_1h2,_1h3),_1h5=new T(function(){return B(unCStr("t2"));}),_1h6=new T(function(){return B(unCStr("\n{da}\n\u3053\u306e\u3068\u304d \u6301\u3063\u3066\u3090\u305f\u6587\u5b57\u304c\u958b\uff1a\u304b\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3055\u308c \u30de\u30c3\u30d7\u4e0a\u306b \u7f6e\uff1a\u304a\uff1a\u304b\u308c\u305f\u72b6\u614b\u306b\u306a\u308a\u307e\u3059\u3002\n\u554f\u984c\u3092\u89e3\uff1a\u3068\uff1a\u304f\u3068\u304d \u3053\u308c\u3089\u306e\u6587\u5b57\u3092 \u30a4\u30b3\u30fc\u30eb <\uff1d>\u306e\u53f3\uff1a\u307f\u304e\uff1a\u306b \u5de6\uff1a\u3072\u3060\u308a\uff1a\u304b\u3089\u9806\uff1a\u3058\u3085\u3093\uff1a\u756a\uff1a\u3070\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u304c\u3042\u308a\u307e\u3059\u3002\n\u305d\u308c\u3067\u306f\u554f\u984c\u3092\u59cb\uff1a\u306f\u3058\uff1a\u3081\u307e\u3059\u3002{e.X.m1:t3}"));}),_1h7=new T2(0,_1h5,_1h6),_1h8=new T(function(){return B(unCStr("t3"));}),_1h9=new T(function(){return B(unCStr("\n\u3088\u308d\u3057\u3044\u3067\u3059\u304b\uff1f{ch.\u306f\u3044,t4.\u6700\uff1a\u3055\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u304b\u3089,t0}"));}),_1ha=new T2(0,_1h8,_1h9),_1hb=new T(function(){return B(unCStr("t4"));}),_1hc=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f\u59cb\u3081\u307e\u3059 {e.X.jl0}\n{e.X.m1:s0}"));}),_1hd=new T2(0,_1hb,_1hc),_1he=new T(function(){return B(unCStr("s0"));}),_1hf=new T(function(){return B(unCStr("\n\u53e4\uff1a\u3075\u308b\uff1a\u3044\u9806\uff1a\u3058\u3085\u3093\uff1a\u306b\u4e26\uff1a\u306a\u3089\uff1a\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abc.s0c}{e.b=0.m0:s0eq}"));}),_1hg=new T2(0,_1he,_1hf),_1hh=new T(function(){return B(unCStr("s0eq"));}),_1hi=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\u3002"));}),_1hj=new T2(0,_1hh,_1hi),_1hk=new T(function(){return B(unCStr("s0c"));}),_1hl=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306f{rt.0}\n\u79d2\uff1a\u3079\u3046\uff1a\u3067\u3057\u305f\u3002\n\u8a73\uff1a\u304f\u306f\uff1a\u3057\u3044\u8aac\uff1a\u305b\u3064\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f \u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3060\u3063\u305f\u6587\uff1a\u3082\uff1a\u5b57\uff1a\u3058\uff1a\u3092<\u6301\uff1a\u3082\uff1a\u3064>\u3068\u898b\uff1a\u307f\uff1a\u308b\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002\n\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304c\u3067\u304d\u305f\u3089 \u6b21\uff1a\u3064\u304e\uff1a\u306e\u554f\u984c\u3078\u884c\uff1a\u3044\uff1a\u304d\u307e\u305b\u3046\u3002\n\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u51fa\uff1a\u3057\u3085\u3064\uff1a\u73fe\uff1a\u3052\u3093\uff1a\u3057\u305f\u6587\u5b57\u3078\u79fb\uff1a\u3044\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u3057\u3066\u304f\u3060\u3055\u3044\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c0.m1:s1}"));}),_1hm=new T2(0,_1hk,_1hl),_1hn=new T(function(){return B(unCStr("s1"));}),_1ho=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u307e\u305b\u3046\u3002\n{da}{rk.1.z.abc.s1c}{e.b=0.m0:s1eq}"));}),_1hp=new T2(0,_1hn,_1ho),_1hq=new T(function(){return B(unCStr("s1eq"));}),_1hr=new T2(0,_1hq,_1hi),_1hs=new T(function(){return B(unCStr("s1c"));}),_1ht=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.1}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.n,Ex}{e.un.l}{e.c1.m1:s2}"));}),_1hu=new T2(0,_1hs,_1ht),_1hv=new T(function(){return B(unCStr("s2"));}),_1hw=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bA.m1:s2A0}{e.bB.m0:s2B0}{e.bC.m0:s2C0}{e.bD.m0:s2D0}{e.un.m0:s2n}"));}),_1hx=new T2(0,_1hv,_1hw),_1hy=new T(function(){return B(unCStr("s2A0"));}),_1hz=new T(function(){return B(unCStr("\n\u3042\u306a\u305f\u306f \u81ea\uff1a\u3058\uff1a\u5206\uff1a\u3076\u3093\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3092\u77e5\uff1a\u3057\uff1a\u308a\u305f\u3044\u3067\u3059\u304b\uff1f\u3002\n{ch.\u306f\u3044,s2A1_0.\u3044\u3044\u3048,s2A1_1}"));}),_1hA=new T2(0,_1hy,_1hz),_1hB=new T(function(){return B(unCStr("s2A1_0"));}),_1hC=new T(function(){return B(unCStr("\n\u3055\u3046\u3067\u3059\u304b\u30fb\u30fb\u30fb\u3002\n\u3061\u306a\u307f\u306b <\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\uff1a\u306a\u3093\uff1a\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n{e.bA.m0:s2A1_2}"));}),_1hD=new T2(0,_1hB,_1hC),_1hE=new T(function(){return B(unCStr("s2A1_1"));}),_1hF=new T(function(){return B(unCStr("\n\u77e5\u308a\u305f\u304f\u3082\u306a\u3044\u3053\u3068\u3092 \u7121\uff1a\u3080\uff1a\u7406\uff1a\u308a\uff1a\u306b\u77e5\u308b\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306f\u3042\u308a\u307e\u305b\u3093\u3088\u306d\u3002 {e.bA.m1:s2A1_1}"));}),_1hG=new T2(0,_1hE,_1hF),_1hH=new T(function(){return B(unCStr("s2A1_2"));}),_1hI=new T(function(){return B(unCStr("\n<\u81ea\u5206\u306e\u570b> \u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n<\u6b74\u53f2>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002\n\u305d\u306e\u6b74\u53f2\u3092<\u77e5\u308b>\u3068\u306f\u4f55\u3067\u305b\u3046\u304b\u3002"));}),_1hJ=new T2(0,_1hH,_1hI),_1hK=new T(function(){return B(unCStr("s2B0"));}),_1hL=new T(function(){return B(unCStr("\n\u79c1\uff1a\u308f\u305f\u3057\uff1a\u306e\u6301\uff1a\u3082\uff1a\u3063\u3066\u3090\u308b\u60c5\uff1a\u3058\u3083\u3046\uff1a\u5831\uff1a\u307b\u3046\uff1a\u306b\u3088\u308b\u3068\u3002\n\u30d4\u30e9\u30df\u30c3\u30c9\u3092\u9020\uff1a\u3064\u304f\uff1a\u308b\u306e\u306b\u4f7f\uff1a\u3064\u304b\uff1a\u306f\u308c\u305f\u77f3\uff1a\u3044\u3057\uff1a\u306f \u7a7a\uff1a\u304f\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306b\u6301\uff1a\u3082\uff1a\u3061\u4e0a\uff1a\u3042\uff1a\u3052\u3089\u308c\u3066 \u7d44\uff1a\u304f\uff1a\u307f\u4e0a\u3052\u3089\u308c\u3066\u3090\u307e\u3057\u305f\u3002"));}),_1hM=new T2(0,_1hK,_1hL),_1hN=new T(function(){return B(unCStr("s2C0"));}),_1hO=new T(function(){return B(unCStr("\n\u30a4\u30a8\u30b9\u30fb\u30ad\u30ea\u30b9\u30c8\u306f \u30a4\u30f3\u30c9\u3084\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3092\u8a2a\uff1a\u304a\u3068\u3065\uff1a\u308c\u3066\u3090\u305f\u3055\u3046\u3067\u3059\u3002\n\u3053\u308c\u3089\u306e\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u306f \u305d\u306e\u5f62\uff1a\u3051\u3044\uff1a\u8de1\uff1a\u305b\u304d\uff1a\u304c \u3044\u304f\u3064\u3082\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u307e\u3059\u3002\n\u307e\u305f\u5f7c\uff1a\u304b\u308c\uff1a\u306f \u30a8\u30b8\u30d7\u30c8\u306e\u30d4\u30e9\u30df\u30c3\u30c8\u3067 \u79d8\uff1a\u3072\uff1a\u6280\uff1a\u304e\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u304b\u3063\u305f \u3068\u3044\u3075\u8a18\uff1a\u304d\uff1a\u9332\uff1a\u308d\u304f\uff1a\u304c\u3042\u308a\u307e\u3059\u3002"));}),_1hP=new T2(0,_1hN,_1hO),_1hQ=new T(function(){return B(unCStr("s2D0"));}),_1hR=new T(function(){return B(unCStr("\n\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u3068\u3044\u3075\u3082\u306e\u306f \u305d\u308c\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u3084 \u50b3\u3078\u308b\u4eba\uff1a\u3072\u3068\uff1a\u3005\uff1a\u3073\u3068\uff1a\u306e\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u89c0\uff1a\u304b\u3093\uff1a \u50b3\u3078\u305f\u7576\uff1a\u305f\u3046\uff1a\u6642\uff1a\u3058\uff1a\u306b\u6b98\uff1a\u306e\u3053\uff1a\u3063\u3066\u3090\u305f\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3046\uff1a\u306e\u7a2e\uff1a\u3057\u3085\uff1a\u985e\uff1a\u308b\u3044\uff1a\u306a\u3069\u306b\u3088\u3063\u3066 \u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u3082\u306e\u3067\u3082 \u76f8\uff1a\u3055\u3046\uff1a\u7576\uff1a\u305f\u3046\uff1a\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u305f\u50b3\uff1a\u3064\u305f\uff1a\u3078\u65b9\uff1a\u304b\u305f\uff1a\u304c\u70ba\uff1a\u306a\uff1a\u3055\u308c\u308b\u3082\u306e\u3067\u3059\u3002\n\u3057\u304b\u3057 \u305d\u308c\u306f \u78ba\uff1a\u304b\u304f\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u306a\u6b74\u53f2\u306f\u5b58\uff1a\u305d\u3093\uff1a\u5728\uff1a\u3056\u3044\uff1a\u305b\u305a \u6b74\u53f2\u3092\u5b78\uff1a\u307e\u306a\uff1a\u3076\u610f\uff1a\u3044\uff1a\u7fa9\uff1a\u304e\uff1a\u3082\u306a\u3044 \u3068\u3044\u3075\u3053\u3068\u306b\u306f\u306a\u308a\u307e\u305b\u3093\u3002\n\u3042\u306a\u305f\u304c\u7d0d\uff1a\u306a\u3063\uff1a\u5f97\uff1a\u3068\u304f\uff1a\u3057 \u4ed6\uff1a\u307b\u304b\uff1a\u306e\u4eba\uff1a\u3072\u3068\uff1a\u9054\uff1a\u305f\u3061\uff1a\u3068\u5171\uff1a\u304d\u3087\u3046\uff1a\u6709\uff1a\u3044\u3046\n\uff1a\u3067\u304d\u308b \u5171\u6709\u3057\u305f\u3044\u6b74\u53f2\u3092 \u3042\u306a\u305f\u81ea\uff1a\u3058\uff1a\u8eab\uff1a\u3057\u3093\uff1a\u304c\u898b\uff1a\u307f\uff1a\u51fa\uff1a\u3044\u3060\uff1a\u3057 \u7d21\uff1a\u3064\u3080\uff1a\u304c\u306a\u3051\u308c\u3070\u306a\u3089\u306a\u3044\u4ed5\uff1a\u3057\uff1a\u7d44\uff1a\u304f\uff1a\u307f\u306b\u306a\u3063\u3066\u3090\u308b\u304b\u3089\u3053\u305d \u6b74\u53f2\u306b\u306f\u4fa1\uff1a\u304b\uff1a\u5024\uff1a\u3061\uff1a\u304c\u3042\u308a \u3042\u306a\u305f\u306e\u751f\uff1a\u3044\uff1a\u304d\u308b\u610f\uff1a\u3044\uff1a\u5473\uff1a\u307f\uff1a\u306b\u3082 \u7e4b\uff1a\u3064\u306a\uff1a\u304c\u3063\u3066\u304f\u308b\u306e\u3067\u306f\u306a\u3044\u3067\u305b\u3046\u304b\u3002"));}),_1hS=new T2(0,_1hQ,_1hR),_1hT=new T(function(){return B(unCStr("s2n"));}),_1hU=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\uff1a\u3059\u3059\uff1a\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s2n1.\u9032\u307e\u306a\u3044,s2n0}"));}),_1hV=new T2(0,_1hT,_1hU),_1hW=new T(function(){return B(unCStr("s2n0"));}),_1hX=new T(function(){return B(unCStr("\n\u884c\u304f\u306e\u3092\u3084\u3081\u307e\u3057\u305f\u3002"));}),_1hY=new T2(0,_1hW,_1hX),_1hZ=new T(function(){return B(unCStr("s8I2"));}),_1i0=new T(function(){return B(unCStr("\n\u3067\u306f \u3088\u3044\u4e00\uff1a\u3044\u3061\uff1a\u65e5\uff1a\u306b\u3061\uff1a\u3092\u30fb\u30fb\u30fb\u3002{e.X.l}"));}),_1i1=new T2(0,_1hZ,_1i0),_1i2=new T2(1,_1i1,_Z),_1i3=new T(function(){return B(unCStr("s8I1"));}),_1i4=new T(function(){return B(unCStr("\n\u305d\u308c\u3067\u306f \u59cb\u3081\u307e\u305b\u3046\u3002{da}{e.c8.m1:s0}{e.X.jl0}"));}),_1i5=new T2(0,_1i3,_1i4),_1i6=new T2(1,_1i5,_1i2),_1i7=new T(function(){return B(unCStr("s8I0"));}),_1i8=new T(function(){return B(unCStr("\n\u304a\u3064\u304b\u308c\u3055\u307e\u3067\u3059\u3002\n\u3042\u306a\u305f\u306e\u9ede\uff1a\u3066\u3093\uff1a\u6578\uff1a\u3059\u3046\uff1a\u306f{rs}\n\u9ede\uff1a\u3066\u3093\uff1a\u3067\u3059\u3002\n\u307e\u3046\u3044\u3061\u3069 \u3084\u308a\u307e\u3059\u304b\uff1f{ch.\u3084\u308b,s8I1.\u3084\u3081\u308b,s8I2}"));}),_1i9=new T2(0,_1i7,_1i8),_1ia=new T2(1,_1i9,_1i6),_1ib=new T(function(){return B(unCStr("s8"));}),_1ic=new T(function(){return B(unCStr("\n\u3060\u308c\u304b\u3090\u307e\u3059\u3002{da}{e.bI.m0:s8I0}"));}),_1id=new T2(0,_1ib,_1ic),_1ie=new T2(1,_1id,_1ia),_1if=new T(function(){return B(unCStr("s7c"));}),_1ig=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.5}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c7.m1:s8}"));}),_1ih=new T2(0,_1if,_1ig),_1ii=new T2(1,_1ih,_1ie),_1ij=new T(function(){return B(unCStr("s7eq"));}),_1ik=new T2(0,_1ij,_1hi),_1il=new T2(1,_1ik,_1ii),_1im=new T(function(){return B(unCStr("s7"));}),_1in=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcde.s7c}{e.b=0.m0:s7eq}"));}),_1io=new T2(0,_1im,_1in),_1ip=new T2(1,_1io,_1il),_1iq=new T(function(){return B(unCStr("s6c"));}),_1ir=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.4}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c6.m1:s7}"));}),_1is=new T2(0,_1iq,_1ir),_1it=new T2(1,_1is,_1ip),_1iu=new T(function(){return B(unCStr("s6eq"));}),_1iv=new T2(0,_1iu,_1hi),_1iw=new T2(1,_1iv,_1it),_1ix=new T(function(){return B(unCStr("s6"));}),_1iy=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{rk.1.z.abcde.s6c}{e.b=0.m0:s6eq}"));}),_1iz=new T2(0,_1ix,_1iy),_1iA=new T2(1,_1iz,_1iw),_1iB=new T(function(){return B(unCStr("s5n1"));}),_1iC=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c5.m1:s6}"));}),_1iD=new T2(0,_1iB,_1iC),_1iE=new T2(1,_1iD,_1iA),_1iF=new T(function(){return B(unCStr("s5n0"));}),_1iG=new T2(0,_1iF,_1hX),_1iH=new T2(1,_1iG,_1iE),_1iI=new T(function(){return B(unCStr("s5n"));}),_1iJ=new T(function(){return B(unCStr("\n\u6b21\u3078\u9032\u307f\u307e\u3059\u304b\uff1f\n{ch.\u9032\u3080,s5n1.\u9032\u307e\u306a\u3044,s5n0}"));}),_1iK=new T2(0,_1iI,_1iJ),_1iL=new T2(1,_1iK,_1iH),_1iM=new T(function(){return B(unCStr("s5H0"));}),_1iN=new T(function(){return B(unCStr("\n\u6211\uff1a\u308f\uff1a\u304c\u570b\uff1a\u304f\u306b\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u7279\uff1a\u3068\u304f\uff1a\u306b\u5f37\uff1a\u3064\u3088\uff1a\u307e\u3063\u305f \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8a9e\uff1a\u3054\uff1a\u306e\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u5de5\uff1a\u3053\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u306f \u305d\u308c\u3092\u4ed5\uff1a\u3057\uff1a\u639b\uff1a\u304b\uff1a\u3051\u305f\u4eba\uff1a\u3072\u3068\uff1a\u306e\u610f\uff1a\u3044\uff1a\u5716\uff1a\u3068\uff1a\u3068\u9006\uff1a\u304e\u3083\u304f\uff1a\u306b \u65e5\u672c\u8a9e\u3092\u5f37\uff1a\u304d\u3083\u3046\uff1a\u5316\uff1a\u304f\u308f\uff1a\u3057 \u305d\u306e\u67d4\uff1a\u3058\u3046\uff1a\u8edf\uff1a\u306a\u3093\uff1a\u3055\u3092 \u3088\u308a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u306b\u767c\uff1a\u306f\u3063\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u3059\u308b\u571f\uff1a\u3069\uff1a\u58cc\uff1a\u3058\u3083\u3046\uff1a\u3092\u4f5c\uff1a\u3064\u304f\uff1a\u3063\u305f\u306e\u3067\u306f\u306a\u3044\u304b\u3068 \u79c1\u306f\u8003\uff1a\u304b\u3093\u304c\uff1a\u3078\u3066\u3090\u307e\u3059\u3002\n\u3067\u3059\u304b\u3089 \u304b\u306a\u9063\uff1a\u3065\u304b\uff1a\u3072\u3092\u6df7\uff1a\u3053\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3055\u305b\u305f\u308a \u6f22\uff1a\u304b\u3093\uff1a\u5b57\uff1a\u3058\uff1a\u3092\u3068\u3063\u305f\u308a\u3064\u3051\u305f\u308a\u3057\u305f\u3053\u3068\u304c \u9006\u306b\u65e5\u672c\u8a9e\u306e\u5f37\u3055 \u67d4\u8edf\u3055\u306e\u8a3c\uff1a\u3057\u3087\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u3092\u3082\u305f\u3089\u3057\u305f\u3068\u3082\u3044\u3078\u308b\u306e\u3067 \u65e5\u672c\u8a9e\u3092\u6df7\u4e82\u3055\u305b\u305f\u4eba\u3005\u306b \u79c1\u306f\u611f\uff1a\u304b\u3093\uff1a\u8b1d\uff1a\u3057\u3083\uff1a\u3057\u3066\u3090\u308b\u306e\u3067\u3059\u3002"));}),_1iO=new T2(0,_1iM,_1iN),_1iP=new T2(1,_1iO,_1iL),_1iQ=new T(function(){return B(unCStr("s5G0"));}),_1iR=new T(function(){return B(unCStr("\n\u540c\uff1a\u304a\u306a\uff1a\u3058\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e \u540c\u3058\u5834\uff1a\u3070\uff1a\u6240\uff1a\u3057\u3087\uff1a\u306b\u95dc\uff1a\u304b\u3093\uff1a\u3059\u308b\u898b\uff1a\u307f\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u9055\uff1a\u3061\u304c\uff1a\u3075\u306e\u306f\n\u4eca\uff1a\u3044\u307e\uff1a \u79c1\u3068 \u3042\u306a\u305f\u304c\u540c\u3058\u5834\u6240\u306b\u3090\u3066 \u305d\u3053\u306b\u5c45\uff1a\u3090\uff1a\u308b\u5225\uff1a\u3079\u3064\uff1a\u306e\u8ab0\uff1a\u3060\u308c\uff1a\u304b\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3059\u308b\u5370\uff1a\u3044\u3093\uff1a\u8c61\uff1a\u3057\u3083\u3046\uff1a\u304c \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u3067\u7570\uff1a\u3053\u3068\uff1a\u306a\u3063\u3066\u3090\u308b\u3053\u3068\u3068 \u4f3c\uff1a\u306b\uff1a\u3066\u3090\u307e\u3059\u3002\n\u305d\u308c\u306f \u81ea\uff1a\u3057\uff1a\u7136\uff1a\u305c\u3093\uff1a\u306a\u3053\u3068\u3067 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306e\u898b\u65b9\u304c\u9055\u3075\u306e\u306f \u5168\uff1a\u307e\u3063\u305f\uff1a\u304f\u554f\uff1a\u3082\u3093\uff1a\u984c\uff1a\u3060\u3044\uff1a\u3042\u308a\u307e\u305b\u3093\u3002\n\u898b\u65b9\u304c\u5168\uff1a\u305c\u3093\uff1a\u7136\uff1a\u305c\u3093\uff1a\u7570\u306a\u3063\u3066\u3090\u3066\u3082 \u308f\u305f\u3057\u3068 \u3042\u306a\u305f\u306f \u5171\uff1a\u304d\u3087\u3046\uff1a\u611f\uff1a\u304b\u3093\uff1a\u3059\u308b\u559c\uff1a\u3088\u308d\u3053\uff1a\u3073\u3092\u5473\uff1a\u3042\u3058\uff1a\u306f\u3046\u3053\u3068\u304c\u3067\u304d\u307e\u3059\u3002"));}),_1iS=new T2(0,_1iQ,_1iR),_1iT=new T2(1,_1iS,_1iP),_1iU=new T(function(){return B(unCStr("s5F0"));}),_1iV=new T(function(){return B(unCStr("\n\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u306f\u7576\uff1a\u305f\u3046\uff1a\u7136\uff1a\u305c\u3093\uff1a\u3055\u3046\u3067\u3059\u304c \u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3092\u6c7a\uff1a\u304d\uff1a\u3081\u308b\u306e\u3082 \u4eca\uff1a\u3044\u307e\uff1a\u306e\u3042\u306a\u305f\u6b21\uff1a\u3057\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u3067\u3059\u3002"));}),_1iW=new T2(0,_1iU,_1iV),_1iX=new T2(1,_1iW,_1iT),_1iY=new T(function(){return B(unCStr("s5E0"));}),_1iZ=new T(function(){return B(unCStr("\n\u904e\uff1a\u304b\uff1a\u53bb\uff1a\u3053\uff1a\u3082\u672a\uff1a\u307f\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3082 \u305d\u3057\u3066\u5225\uff1a\u3079\u3064\uff1a\u306e\u4e26\uff1a\u3078\u3044\uff1a\u884c\uff1a\u304b\u3046\uff1a\u4e16\uff1a\u305b\uff1a\u754c\uff1a\u304b\u3044\uff1a\u3082 \u3059\u3079\u3066\u306f \u4eca\uff1a\u3044\u307e\uff1a \u3053\u3053\u306b\u3042\u308a\u307e\u3059\u3002"));}),_1j0=new T2(0,_1iY,_1iZ),_1j1=new T2(1,_1j0,_1iX),_1j2=new T(function(){return B(unCStr("s5"));}),_1j3=new T(function(){return B(unCStr("\n\u3060\u308c\u304b \u3090\u308b\u307f\u305f\u3044\u3067\u3059\u3002{da}{e.bE.m0:s5E0}{e.bF.m0:s5F0}{e.bG.m0:s5G0}{e.bH.m0:s5H0}{e.un.m0:s5n}"));}),_1j4=new T2(0,_1j2,_1j3),_1j5=new T2(1,_1j4,_1j1),_1j6=new T(function(){return B(unCStr("s4c"));}),_1j7=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.3}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u306b\u9032\u307f\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c4.m1:s5}"));}),_1j8=new T2(0,_1j6,_1j7),_1j9=new T2(1,_1j8,_1j5),_1ja=new T(function(){return B(unCStr("s4eq"));}),_1jb=new T2(0,_1ja,_1hi),_1jc=new T2(1,_1jb,_1j9),_1jd=new T(function(){return B(unCStr("s4"));}),_1je=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s4c}{e.b=0.m0:s4eq}"));}),_1jf=new T2(0,_1jd,_1je),_1jg=new T2(1,_1jf,_1jc),_1jh=new T(function(){return B(unCStr("s3c"));}),_1ji=new T(function(){return B(unCStr("\n\u305b\u3044\u304b\u3044\u3067\u3059\uff01\u3002\n\u304b\u304b\u3063\u305f\u6642\u9593\u306f{rt.2}\n\u79d2\u3067\u3057\u305f\u3002\n\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002\n{d.b=0}{p.3,3.%,Ex}{e.u%.l}{e.c3.m1:s4}"));}),_1jj=new T2(0,_1jh,_1ji),_1jk=new T2(1,_1jj,_1jg),_1jl=new T(function(){return B(unCStr("s3eq"));}),_1jm=new T2(0,_1jl,_1hi),_1jn=new T2(1,_1jm,_1jk),_1jo=new T(function(){return B(unCStr("s3"));}),_1jp=new T(function(){return B(unCStr("\n\u53e4\u3044\u9806\u306b\u4e26\u3079\u3066\u304f\u3060\u3055\u3044\n{da}{rk.1.z.abcd.s3c}{e.b=0.m0:s3eq}"));}),_1jq=new T2(0,_1jo,_1jp),_1jr=new T2(1,_1jq,_1jn),_1js=new T(function(){return B(unCStr("s2n1"));}),_1jt=new T(function(){return B(unCStr("\n\u3067\u306f\u6b21\u3078\u884c\u304d\u307e\u305b\u3046\u3002{e.X.l}{e.c2.m1:s3}"));}),_1ju=new T2(0,_1js,_1jt),_1jv=new T2(1,_1ju,_1jr),_1jw=new T2(1,_1hY,_1jv),_1jx=new T2(1,_1hV,_1jw),_1jy=new T2(1,_1hS,_1jx),_1jz=new T2(1,_1hP,_1jy),_1jA=new T2(1,_1hM,_1jz),_1jB=new T2(1,_1hJ,_1jA),_1jC=new T2(1,_1hG,_1jB),_1jD=new T2(1,_1hD,_1jC),_1jE=new T2(1,_1hA,_1jD),_1jF=new T2(1,_1hx,_1jE),_1jG=new T2(1,_1hu,_1jF),_1jH=new T2(1,_1hr,_1jG),_1jI=new T2(1,_1hp,_1jH),_1jJ=new T(function(){return B(unCStr("nubatama"));}),_1jK=new T(function(){return B(unCStr("\n\u306c\u3070\u305f\u307e\u306e \u4e16\u306f\u96e3\u3057\u304f \u601d\u3078\u308c\u3069\u3002   \n\u660e\u3051\u3066\u898b\u3086\u308b\u306f \u552f\u5927\u6cb3\u306a\u308a"));}),_1jL=new T2(0,_1jJ,_1jK),_1jM=new T2(1,_1jL,_1jI),_1jN=new T(function(){return B(unCStr("\n\u4f55\u304c\u8d77\uff1a\u304a\uff1a\u3053\u3063\u305f\uff1f"));}),_1jO=new T(function(){return B(unCStr("msgW"));}),_1jP=new T2(0,_1jO,_1jN),_1jQ=new T2(1,_1jP,_1jM),_1jR=new T(function(){return B(unCStr("\n\u307e\u3046\u4e00\u5ea6 \u3084\u3063\u3066\u307f\u3084\u3046"));}),_1jS=new T(function(){return B(unCStr("msgR"));}),_1jT=new T2(0,_1jS,_1jR),_1jU=new T2(1,_1jT,_1jQ),_1jV=new T2(1,_1hm,_1jU),_1jW=new T2(1,_1hj,_1jV),_1jX=new T2(1,_1hg,_1jW),_1jY=new T2(1,_1hd,_1jX),_1jZ=new T2(1,_1ha,_1jY),_1k0=new T2(1,_1h7,_1jZ),_1k1=new T2(1,_1h4,_1k0),_1k2=new T2(1,_1h1,_1k1),_1k3=new T(function(){return B(unCStr("initMsg"));}),_1k4=function(_1k5,_1k6){var _1k7=new T(function(){var _1k8=B(_1gS(_1k5));return new T2(0,_1k8.a,_1k8.b);}),_1k9=function(_1ka){var _1kb=E(_1ka);if(!_1kb._){return E(_1k7);}else{var _1kc=E(_1kb.a),_1kd=new T(function(){return B(_1k9(_1kb.b));});return new T2(0,new T2(1,_1kc.a,new T(function(){return E(E(_1kd).a);})),new T2(1,_1kc.b,new T(function(){return E(E(_1kd).b);})));}},_1ke=function(_1kf,_1kg,_1kh){var _1ki=new T(function(){return B(_1k9(_1kh));});return new T2(0,new T2(1,_1kf,new T(function(){return E(E(_1ki).a);})),new T2(1,_1kg,new T(function(){return E(E(_1ki).b);})));},_1kj=B(_1ke(_1k3,_1gY,_1k2)),_1kk=_1kj.a;if(!B(_4H(_uJ,_1k6,_1kk))){return __Z;}else{return new F(function(){return _aW(_1kj.b,B(_Rj(_uJ,_1k6,_1kk)));});}},_1kl=5,_1km=new T2(0,_1kl,_1kl),_1kn=7,_1ko=new T2(0,_1kn,_1kl),_1kp=6,_1kq=new T2(0,_1kl,_1kp),_1kr=new T2(1,_1kq,_Z),_1ks=new T2(1,_1ko,_1kr),_1kt=new T2(1,_1ko,_1ks),_1ku=new T2(1,_1kq,_1kt),_1kv=new T2(1,_1ko,_1ku),_1kw=new T2(1,_1ko,_1kv),_1kx=new T2(1,_1kq,_1kw),_1ky=new T2(1,_1km,_1kx),_1kz=new T2(1,_1km,_1ky),_1kA=2,_1kB=new T2(0,_1kA,_1kA),_1kC=new T2(1,_1kB,_Z),_1kD=new T2(1,_1kB,_1kC),_1kE=new T2(1,_1kB,_1kD),_1kF=new T2(1,_1kB,_1kE),_1kG=new T2(1,_1kB,_1kF),_1kH=new T2(1,_1kB,_1kG),_1kI=new T2(1,_1kB,_1kH),_1kJ=new T2(1,_1kB,_1kI),_1kK=new T2(1,_1kB,_1kJ),_1kL=new T(function(){return B(unCStr("Int"));}),_1kM=function(_1kN,_1kO,_1kP){return new F(function(){return _1d3(_1cw,new T2(0,_1kO,_1kP),_1kN,_1kL);});},_1kQ=new T(function(){return B(unCStr("msgR"));}),_1kR=new T(function(){return B(_1k4(_Z,_1kQ));}),_1kS=new T(function(){return B(unCStr("msgW"));}),_1kT=new T(function(){return B(_1k4(_Z,_1kS));}),_1kU=function(_1kV){var _1kW=E(_1kV);return 0;},_1kX=new T(function(){return B(unCStr("@@@@@@@@@"));}),_1kY=new T(function(){var _1kZ=E(_1kX);if(!_1kZ._){return E(_rm);}else{return E(_1kZ.a);}}),_1l0=122,_1l1=new T2(0,_1l0,_IO),_1l2=0,_1l3=new T2(0,_1l2,_1l2),_1l4=new T2(0,_1l3,_1l1),_1l5=61,_1l6=new T2(0,_1l5,_IO),_1l7=1,_1l8=new T2(0,_1l7,_1l2),_1l9=new T2(0,_1l8,_1l6),_1la=97,_1lb=new T2(0,_1la,_II),_1lc=4,_1ld=new T2(0,_1l2,_1lc),_1le=new T2(0,_1ld,_1lb),_1lf=98,_1lg=new T2(0,_1lf,_II),_1lh=new T2(0,_1kA,_1lc),_1li=new T2(0,_1lh,_1lg),_1lj=99,_1lk=new T2(0,_1lj,_II),_1ll=new T2(0,_1lc,_1lc),_1lm=new T2(0,_1ll,_1lk),_1ln=new T2(1,_1lm,_Z),_1lo=new T2(1,_1li,_1ln),_1lp=new T2(1,_1le,_1lo),_1lq=new T2(1,_1l9,_1lp),_1lr=new T2(1,_1l4,_1lq),_1ls=new T(function(){return B(_1fN(_1kl,5,_1lr));}),_1lt=new T(function(){return B(_PU("Check.hs:142:22-33|(ch : po)"));}),_1lu=new T(function(){return B(_ic("Check.hs:(108,1)-(163,19)|function trEvent"));}),_1lv=110,_1lw=new T2(0,_1lv,_IU),_1lx=new T2(0,_1lc,_1kl),_1ly=new T2(0,_1lx,_1lw),_1lz=new T2(1,_1ly,_Z),_1lA=new T2(0,_1kA,_1kl),_1lB=66,_1lC=new T2(0,_1lB,_IO),_1lD=new T2(0,_1lA,_1lC),_1lE=new T2(1,_1lD,_1lz),_1lF=3,_1lG=new T2(0,_1l2,_1lF),_1lH=67,_1lI=new T2(0,_1lH,_IO),_1lJ=new T2(0,_1lG,_1lI),_1lK=new T2(1,_1lJ,_1lE),_1lL=new T2(0,_1lc,_1l7),_1lM=65,_1lN=new T2(0,_1lM,_IO),_1lO=new T2(0,_1lL,_1lN),_1lP=new T2(1,_1lO,_1lK),_1lQ=68,_1lR=new T2(0,_1lQ,_IO),_1lS=new T2(0,_1l8,_1lR),_1lT=new T2(1,_1lS,_1lP),_1lU=100,_1lV=new T2(0,_1lU,_II),_1lW=new T2(0,_1kp,_1lc),_1lX=new T2(0,_1lW,_1lV),_1lY=new T2(1,_1lX,_Z),_1lZ=new T2(1,_1lm,_1lY),_1m0=new T2(1,_1li,_1lZ),_1m1=new T2(1,_1le,_1m0),_1m2=new T2(1,_1l9,_1m1),_1m3=new T2(1,_1l4,_1m2),_1m4=70,_1m5=new T2(0,_1m4,_IO),_1m6=new T2(0,_1lA,_1m5),_1m7=new T2(1,_1m6,_1lz),_1m8=72,_1m9=new T2(0,_1m8,_IO),_1ma=new T2(0,_1lG,_1m9),_1mb=new T2(1,_1ma,_1m7),_1mc=69,_1md=new T2(0,_1mc,_IO),_1me=new T2(0,_1lL,_1md),_1mf=new T2(1,_1me,_1mb),_1mg=71,_1mh=new T2(0,_1mg,_IO),_1mi=new T2(0,_1l8,_1mh),_1mj=new T2(1,_1mi,_1mf),_1mk=101,_1ml=new T2(0,_1mk,_II),_1mm=new T2(0,_1lc,_1kA),_1mn=new T2(0,_1mm,_1ml),_1mo=new T2(1,_1mn,_1m1),_1mp=new T2(1,_1l9,_1mo),_1mq=new T2(1,_1l4,_1mp),_1mr=73,_1ms=new T2(0,_1mr,_IO),_1mt=new T2(0,_1kA,_1l2),_1mu=new T2(0,_1mt,_1ms),_1mv=new T2(1,_1mu,_Z),_1mw=new T2(1,_1mv,_Z),_1mx=new T2(1,_1mq,_1mw),_1my=new T2(1,_1mq,_1mx),_1mz=new T2(1,_1mj,_1my),_1mA=new T2(1,_1m3,_1mz),_1mB=new T2(1,_1m3,_1mA),_1mC=new T2(1,_1lT,_1mB),_1mD=new T2(1,_1lr,_1mC),_1mE=new T2(1,_1lr,_1mD),_1mF=function(_1mG){var _1mH=E(_1mG);if(!_1mH._){return __Z;}else{var _1mI=_1mH.b,_1mJ=E(_1mH.a),_1mK=_1mJ.b,_1mL=E(_1mJ.a),_1mM=function(_1mN){if(E(_1mL)==32){return new T2(1,_1mJ,new T(function(){return B(_1mF(_1mI));}));}else{switch(E(_1mK)){case 0:return new T2(1,new T2(0,_1mL,_II),new T(function(){return B(_1mF(_1mI));}));case 1:return new T2(1,new T2(0,_1mL,_Jj),new T(function(){return B(_1mF(_1mI));}));case 2:return new T2(1,new T2(0,_1mL,_IU),new T(function(){return B(_1mF(_1mI));}));case 3:return new T2(1,new T2(0,_1mL,_J0),new T(function(){return B(_1mF(_1mI));}));case 4:return new T2(1,new T2(0,_1mL,_J6),new T(function(){return B(_1mF(_1mI));}));case 5:return new T2(1,new T2(0,_1mL,_Jx),new T(function(){return B(_1mF(_1mI));}));case 6:return new T2(1,new T2(0,_1mL,_Jq),new T(function(){return B(_1mF(_1mI));}));case 7:return new T2(1,new T2(0,_1mL,_Jj),new T(function(){return B(_1mF(_1mI));}));default:return new T2(1,new T2(0,_1mL,_Jc),new T(function(){return B(_1mF(_1mI));}));}}};if(E(_1mL)==32){return new F(function(){return _1mM(_);});}else{switch(E(_1mK)){case 0:return new T2(1,new T2(0,_1mL,_Jc),new T(function(){return B(_1mF(_1mI));}));case 1:return new F(function(){return _1mM(_);});break;case 2:return new F(function(){return _1mM(_);});break;case 3:return new F(function(){return _1mM(_);});break;case 4:return new F(function(){return _1mM(_);});break;case 5:return new F(function(){return _1mM(_);});break;case 6:return new F(function(){return _1mM(_);});break;case 7:return new F(function(){return _1mM(_);});break;default:return new F(function(){return _1mM(_);});}}}},_1mO=function(_1mP){var _1mQ=E(_1mP);return (_1mQ._==0)?__Z:new T2(1,new T(function(){return B(_1mF(_1mQ.a));}),new T(function(){return B(_1mO(_1mQ.b));}));},_1mR=function(_1mS){var _1mT=E(_1mS);if(!_1mT._){return __Z;}else{var _1mU=_1mT.b,_1mV=E(_1mT.a),_1mW=_1mV.b,_1mX=E(_1mV.a),_1mY=function(_1mZ){if(E(_1mX)==32){return new T2(1,_1mV,new T(function(){return B(_1mR(_1mU));}));}else{switch(E(_1mW)){case 0:return new T2(1,new T2(0,_1mX,_II),new T(function(){return B(_1mR(_1mU));}));case 1:return new T2(1,new T2(0,_1mX,_IO),new T(function(){return B(_1mR(_1mU));}));case 2:return new T2(1,new T2(0,_1mX,_IU),new T(function(){return B(_1mR(_1mU));}));case 3:return new T2(1,new T2(0,_1mX,_J0),new T(function(){return B(_1mR(_1mU));}));case 4:return new T2(1,new T2(0,_1mX,_J6),new T(function(){return B(_1mR(_1mU));}));case 5:return new T2(1,new T2(0,_1mX,_Jx),new T(function(){return B(_1mR(_1mU));}));case 6:return new T2(1,new T2(0,_1mX,_Jq),new T(function(){return B(_1mR(_1mU));}));case 7:return new T2(1,new T2(0,_1mX,_IO),new T(function(){return B(_1mR(_1mU));}));default:return new T2(1,new T2(0,_1mX,_Jc),new T(function(){return B(_1mR(_1mU));}));}}};if(E(_1mX)==32){return new F(function(){return _1mY(_);});}else{if(E(_1mW)==8){return new T2(1,new T2(0,_1mX,_II),new T(function(){return B(_1mR(_1mU));}));}else{return new F(function(){return _1mY(_);});}}}},_1n0=function(_1n1){var _1n2=E(_1n1);return (_1n2._==0)?__Z:new T2(1,new T(function(){return B(_1mR(_1n2.a));}),new T(function(){return B(_1n0(_1n2.b));}));},_1n3=function(_1n4,_1n5,_1n6,_1n7,_1n8,_1n9,_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1nl,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI){var _1nJ=E(_1n5);if(!_1nJ._){return E(_1lu);}else{var _1nK=_1nJ.b,_1nL=E(_1nJ.a),_1nM=new T(function(){var _1nN=function(_){var _1nO=B(_qy(_1nl,0))-1|0,_1nP=function(_1nQ){if(_1nQ>=0){var _1nR=newArr(_1nQ,_1ck),_1nS=_1nR,_1nT=E(_1nQ);if(!_1nT){return new T4(0,E(_1eG),E(_1nO),0,_1nS);}else{var _1nU=function(_1nV,_1nW,_){while(1){var _1nX=E(_1nV);if(!_1nX._){return E(_);}else{var _=_1nS[_1nW]=_1nX.a;if(_1nW!=(_1nT-1|0)){var _1nY=_1nW+1|0;_1nV=_1nX.b;_1nW=_1nY;continue;}else{return E(_);}}}},_=B(_1nU(_1nl,0,_));return new T4(0,E(_1eG),E(_1nO),_1nT,_1nS);}}else{return E(_1de);}};if(0>_1nO){return new F(function(){return _1nP(0);});}else{return new F(function(){return _1nP(_1nO+1|0);});}},_1nZ=B(_1df(_1nN)),_1o0=E(_1nZ.a),_1o1=E(_1nZ.b),_1o2=E(_1n4);if(_1o0>_1o2){return B(_1kM(_1o2,_1o0,_1o1));}else{if(_1o2>_1o1){return B(_1kM(_1o2,_1o0,_1o1));}else{return E(_1nZ.d[_1o2-_1o0|0]);}}});switch(E(_1nL)){case 97:var _1o3=new T(function(){var _1o4=E(_1nK);if(!_1o4._){return E(_1lt);}else{return new T2(0,_1o4.a,_1o4.b);}}),_1o5=new T(function(){var _1o6=B(_1gD(E(_1o3).b));return new T2(0,_1o6.a,_1o6.b);}),_1o7=B(_KK(B(_x7(_1eF,new T(function(){return E(E(_1o5).b);})))));if(!_1o7._){return E(_1eD);}else{if(!E(_1o7.b)._){var _1o8=new T(function(){var _1o9=B(_KK(B(_x7(_1eF,new T(function(){return E(E(_1o5).a);})))));if(!_1o9._){return E(_1eD);}else{if(!E(_1o9.b)._){return E(_1o9.a);}else{return E(_1eE);}}},1);return {_:0,a:E({_:0,a:E(_1n6),b:E(B(_Pt(_1o8,E(_1o7.a),new T(function(){return E(E(_1o3).a);}),_II,_1n7))),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};}else{return E(_1eE);}}break;case 104:return {_:0,a:E({_:0,a:E(_1n6),b:E(B(_1mO(_1n7))),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};case 106:var _1oa=E(_1nK);if(!_1oa._){return {_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l: -1,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};}else{if(E(_1oa.a)==108){var _1ob=E(_1n4),_1oc=B(_KK(B(_x7(_1eF,_1oa.b))));return (_1oc._==0)?E(_1eD):(E(_1oc.b)._==0)?{_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(B(_1eg(_1ob,_1nk))),f:E(B(_1eg(_1ob,_1nl))),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:E(_1oc.a),m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_B3),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)}:E(_1eE);}else{var _1od=B(_KK(B(_x7(_1eF,_1oa))));return (_1od._==0)?E(_1eD):(E(_1od.b)._==0)?{_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:E(_1od.a),m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)}:E(_1eE);}}break;case 108:var _1oe=E(_1n4);return {_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(B(_1eg(_1oe,_1nk))),f:E(B(_1eg(_1oe,_1nl))),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_B3),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};case 109:var _1of=B(_1eI(E(_1nM),_1nK)),_1og=_1of.c,_1oh=B(_vl(_1og,_Z));if(!E(_1oh)){var _1oi=E(_1n4),_1oj=new T(function(){var _1ok=function(_){var _1ol=B(_qy(_1nk,0))-1|0,_1om=function(_1on){if(_1on>=0){var _1oo=newArr(_1on,_1ck),_1op=_1oo,_1oq=E(_1on);if(!_1oq){return new T4(0,E(_1eG),E(_1ol),0,_1op);}else{var _1or=function(_1os,_1ot,_){while(1){var _1ou=E(_1os);if(!_1ou._){return E(_);}else{var _=_1op[_1ot]=_1ou.a;if(_1ot!=(_1oq-1|0)){var _1ov=_1ot+1|0;_1os=_1ou.b;_1ot=_1ov;continue;}else{return E(_);}}}},_=B(_1or(_1nk,0,_));return new T4(0,E(_1eG),E(_1ol),_1oq,_1op);}}else{return E(_1de);}};if(0>_1ol){return new F(function(){return _1om(0);});}else{return new F(function(){return _1om(_1ol+1|0);});}},_1ow=B(_1df(_1ok)),_1ox=E(_1ow.a),_1oy=E(_1ow.b);if(_1ox>_1oi){return B(_1kM(_1oi,_1ox,_1oy));}else{if(_1oi>_1oy){return B(_1kM(_1oi,_1ox,_1oy));}else{return E(E(_1ow.d[_1oi-_1ox|0]).a);}}}),_1oz=B(_1f7(_1oi,new T2(0,_1oj,new T2(1,_1nL,_1og)),_1nk));}else{var _1oz=B(_1gP(_1n4,_1nk));}if(!E(_1oh)){var _1oA=B(_1f7(E(_1n4),_1of.a,_1nl));}else{var _1oA=B(_1gP(_1n4,_1nl));}return {_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(B(_1k4(_1nj,_1of.b))),d:E(_1nj),e:E(_1oz),f:E(_1oA),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_B3),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};case 114:var _1oB=B(_aW(_1kz,_1nb));return {_:0,a:E({_:0,a:E(B(_aW(_1kK,_1nb))),b:E(B(_1fN(_1oB.a,E(_1oB.b),new T(function(){return B(_aW(_1mE,_1nb));})))),c:E(_1n8),d:B(_aW(_1kX,_1nb)),e:32,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1oB),c:E(_1kR),d:E(_1nj),e:E(_1nk),f:E(B(_aj(_1kU,_1nl))),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_B3),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};case 115:return {_:0,a:E({_:0,a:E(_1n6),b:E(B(_1n0(_1n7))),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};case 116:var _1oC=E(_1nM),_1oD=B(_1eI(_1oC,_1nK)),_1oE=E(_1oD.a);if(!E(_1oE)){var _1oF=true;}else{var _1oF=false;}if(!E(_1oF)){var _1oG=B(_1f7(E(_1n4),_1oE,_1nl));}else{var _1oG=B(_1f7(E(_1n4),_1oC+1|0,_1nl));}if(!E(_1oF)){var _1oH=__Z;}else{var _1oH=E(_1oD.b);}if(!B(_vl(_1oH,_Z))){var _1oI=B(_1n3(_1n4,_1oH,_1n6,_1n7,_1n8,_1n9,_1na,_1nb,_1nc,_1nd,_1ne,_1nf,_1ng,_1nh,_1ni,_1nj,_1nk,_1oG,_1nm,_1nn,_1no,_1np,_1nq,_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB,_1nC,_1nD,_1nE,_1nF,_1nG,_1nH,_1nI)),_1oJ=E(_1oI.a);return {_:0,a:E({_:0,a:E(_1oJ.a),b:E(_1oJ.b),c:E(_1oJ.c),d:_1oJ.d,e:_1oJ.e,f:_1oJ.f,g:E(_1oJ.g),h:_1oJ.h,i:E(B(_x(_1ne,_1nJ))),j:E(_1oJ.j),k:E(_1oJ.k)}),b:E(_1oI.b),c:E(_1oI.c),d:E(_1oI.d),e:E(_1oI.e),f:E(_1oI.f),g:E(_1oI.g),h:E(_1oI.h),i:_1oI.i,j:_1oI.j,k:_1oI.k,l:_1oI.l,m:E(_1oI.m),n:_1oI.n,o:E(_1oI.o),p:E(_1oI.p),q:_1oI.q,r:E(_1oI.r),s:E(_1oI.s),t:_1oI.t,u:E(_1oI.u),v:E(_1oI.v)};}else{return {_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1oG),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};}break;case 119:return {_:0,a:E({_:0,a:E(_1kB),b:E(_1ls),c:E(_1n8),d:E(_1kY),e:32,f:0,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1km),c:E(_1kT),d:E(_1nj),e:E(_1nk),f:E(B(_aj(_1kU,_1nl))),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_B3),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};default:return {_:0,a:E({_:0,a:E(_1n6),b:E(_1n7),c:E(_1n8),d:_1n9,e:_1na,f:_1nb,g:E(_1nc),h:_1nd,i:E(B(_x(_1ne,_1nJ))),j:E(_1nf),k:E(_1ng)}),b:E(_1nh),c:E(_1ni),d:E(_1nj),e:E(_1nk),f:E(_1nl),g:E(_1nm),h:E(_1nn),i:_1no,j:_1np,k:_1nq,l:_1nr,m:E(_1ns),n:_1nt,o:E(_1nu),p:E(_1nv),q:_1nw,r:E(_1nx),s:E(_1ny),t:_1nz,u:E({_:0,a:E(_1nA),b:E(_1nB),c:E(_1nC),d:E(_1nD),e:E(_1nE),f:E(_1nF),g:E(_1nG),h:E(_1nH)}),v:E(_1nI)};}}},_1oK=function(_1oL,_1oM){while(1){var _1oN=E(_1oM);if(!_1oN._){return __Z;}else{var _1oO=_1oN.b,_1oP=E(_1oL);if(_1oP==1){return E(_1oO);}else{_1oL=_1oP-1|0;_1oM=_1oO;continue;}}}},_1oQ=new T(function(){return B(unCStr("X"));}),_1oR=new T(function(){return B(_ic("Check.hs:(87,7)-(92,39)|function chAnd"));}),_1oS=38,_1oT=function(_1oU,_1oV,_1oW,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa,_1pb,_1pc,_1pd,_1pe,_1pf,_1pg,_1ph,_1pi){var _1pj=E(_1oW);if(!_1pj._){return {_:0,a:_1oX,b:_1oY,c:_1oZ,d:_1p0,e:_1p1,f:_1p2,g:_1p3,h:_1p4,i:_1p5,j:_1p6,k:_1p7,l:_1p8,m:_1p9,n:_1pa,o:_1pb,p:_1pc,q:_1pd,r:_1pe,s:_1pf,t:_1pg,u:_1ph,v:_1pi};}else{var _1pk=_1pj.b,_1pl=E(_1pj.a),_1pm=_1pl.a,_1pn=_1pl.b,_1po=function(_1pp,_1pq,_1pr){var _1ps=function(_1pt,_1pu){if(!B(_vl(_1pt,_Z))){var _1pv=E(_1oX),_1pw=E(_1ph),_1px=B(_1n3(_1pu,_1pt,_1pv.a,_1pv.b,_1pv.c,_1pv.d,_1pv.e,_1pv.f,_1pv.g,_1pv.h,_1pv.i,_1pv.j,_1pv.k,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa,_1pb,_1pc,_1pd,_1pe,_1pf,_1pg,_1pw.a,_1pw.b,_1pw.c,_1pw.d,_1pw.e,_1pw.f,_1pw.g,_1pw.h,_1pi)),_1py=_1px.a,_1pz=_1px.b,_1pA=_1px.c,_1pB=_1px.d,_1pC=_1px.e,_1pD=_1px.f,_1pE=_1px.g,_1pF=_1px.h,_1pG=_1px.i,_1pH=_1px.j,_1pI=_1px.k,_1pJ=_1px.l,_1pK=_1px.m,_1pL=_1px.n,_1pM=_1px.o,_1pN=_1px.p,_1pO=_1px.q,_1pP=_1px.r,_1pQ=_1px.s,_1pR=_1px.t,_1pS=_1px.u,_1pT=_1px.v;if(B(_qy(_1pD,0))!=B(_qy(_1p2,0))){return {_:0,a:_1py,b:_1pz,c:_1pA,d:_1pB,e:_1pC,f:_1pD,g:_1pE,h:_1pF,i:_1pG,j:_1pH,k:_1pI,l:_1pJ,m:_1pK,n:_1pL,o:_1pM,p:_1pN,q:_1pO,r:_1pP,s:_1pQ,t:_1pR,u:_1pS,v:_1pT};}else{return new F(function(){return _1oT(new T(function(){return E(_1oU)+1|0;}),_1oV,_1pk,_1py,_1pz,_1pA,_1pB,_1pC,_1pD,_1pE,_1pF,_1pG,_1pH,_1pI,_1pJ,_1pK,_1pL,_1pM,_1pN,_1pO,_1pP,_1pQ,_1pR,_1pS,_1pT);});}}else{return new F(function(){return _1oT(new T(function(){return E(_1oU)+1|0;}),_1oV,_1pk,_1oX,_1oY,_1oZ,_1p0,_1p1,_1p2,_1p3,_1p4,_1p5,_1p6,_1p7,_1p8,_1p9,_1pa,_1pb,_1pc,_1pd,_1pe,_1pf,_1pg,_1ph,_1pi);});}},_1pU=B(_qy(_1oV,0))-B(_qy(new T2(1,_1pp,_1pq),0))|0;if(_1pU>0){var _1pV=B(_1oK(_1pU,_1oV));}else{var _1pV=E(_1oV);}if(E(B(_1dY(_1pp,_1pq,_ZW)))==63){var _1pW=B(_Yd(_1pp,_1pq));}else{var _1pW=new T2(1,_1pp,_1pq);}var _1pX=function(_1pY){if(!B(_4H(_lc,_1oS,_1pm))){return new T2(0,_1pn,_1oU);}else{var _1pZ=function(_1q0){while(1){var _1q1=B((function(_1q2){var _1q3=E(_1q2);if(!_1q3._){return true;}else{var _1q4=_1q3.b,_1q5=E(_1q3.a);if(!_1q5._){return E(_1oR);}else{switch(E(_1q5.a)){case 99:var _1q6=E(_1oX);if(!E(_1q6.k)){return false;}else{var _1q7=function(_1q8){while(1){var _1q9=E(_1q8);if(!_1q9._){return true;}else{var _1qa=_1q9.b,_1qb=E(_1q9.a);if(!_1qb._){return E(_1oR);}else{if(E(_1qb.a)==115){var _1qc=B(_KK(B(_x7(_1eF,_1qb.b))));if(!_1qc._){return E(_1eD);}else{if(!E(_1qc.b)._){if(_1q6.f!=E(_1qc.a)){return false;}else{_1q8=_1qa;continue;}}else{return E(_1eE);}}}else{_1q8=_1qa;continue;}}}}};return new F(function(){return _1q7(_1q4);});}break;case 115:var _1qd=E(_1oX),_1qe=_1qd.f,_1qf=B(_KK(B(_x7(_1eF,_1q5.b))));if(!_1qf._){return E(_1eD);}else{if(!E(_1qf.b)._){if(_1qe!=E(_1qf.a)){return false;}else{var _1qg=function(_1qh){while(1){var _1qi=E(_1qh);if(!_1qi._){return true;}else{var _1qj=_1qi.b,_1qk=E(_1qi.a);if(!_1qk._){return E(_1oR);}else{switch(E(_1qk.a)){case 99:if(!E(_1qd.k)){return false;}else{_1qh=_1qj;continue;}break;case 115:var _1ql=B(_KK(B(_x7(_1eF,_1qk.b))));if(!_1ql._){return E(_1eD);}else{if(!E(_1ql.b)._){if(_1qe!=E(_1ql.a)){return false;}else{_1qh=_1qj;continue;}}else{return E(_1eE);}}break;default:_1qh=_1qj;continue;}}}}};return new F(function(){return _1qg(_1q4);});}}else{return E(_1eE);}}break;default:_1q0=_1q4;return __continue;}}}})(_1q0));if(_1q1!=__continue){return _1q1;}}};return (!B(_1pZ(_1pr)))?(!B(_vl(_1pW,_1oQ)))?new T2(0,_Z,_1oU):new T2(0,_1pn,_1oU):new T2(0,_1pn,_1oU);}};if(E(B(_1e6(_1pp,_1pq,_ZW)))==63){if(!B(_ae(_1pV,_Z))){var _1qm=E(_1pV);if(!_1qm._){return E(_Yi);}else{if(!B(_vl(_1pW,B(_Yd(_1qm.a,_1qm.b))))){if(!B(_vl(_1pW,_1oQ))){return new F(function(){return _1ps(_Z,_1oU);});}else{return new F(function(){return _1ps(_1pn,_1oU);});}}else{var _1qn=B(_1pX(_));return new F(function(){return _1ps(_1qn.a,_1qn.b);});}}}else{if(!B(_vl(_1pW,_1pV))){if(!B(_vl(_1pW,_1oQ))){return new F(function(){return _1ps(_Z,_1oU);});}else{return new F(function(){return _1ps(_1pn,_1oU);});}}else{var _1qo=B(_1pX(_));return new F(function(){return _1ps(_1qo.a,_1qo.b);});}}}else{if(!B(_vl(_1pW,_1pV))){if(!B(_vl(_1pW,_1oQ))){return new F(function(){return _1ps(_Z,_1oU);});}else{return new F(function(){return _1ps(_1pn,_1oU);});}}else{var _1qp=B(_1pX(_));return new F(function(){return _1ps(_1qp.a,_1qp.b);});}}},_1qq=E(_1pm);if(!_1qq._){return E(_ZW);}else{var _1qr=_1qq.a,_1qs=E(_1qq.b);if(!_1qs._){return new F(function(){return _1po(_1qr,_Z,_Z);});}else{var _1qt=E(_1qr),_1qu=new T(function(){var _1qv=B(_LC(38,_1qs.a,_1qs.b));return new T2(0,_1qv.a,_1qv.b);});if(E(_1qt)==38){return E(_ZW);}else{return new F(function(){return _1po(_1qt,new T(function(){return E(E(_1qu).a);}),new T(function(){return E(E(_1qu).b);}));});}}}}},_1qw="]",_1qx="}",_1qy=":",_1qz=",",_1qA=new T(function(){return eval("JSON.stringify");}),_1qB="false",_1qC="null",_1qD="[",_1qE="{",_1qF="\"",_1qG="true",_1qH=function(_1qI,_1qJ){var _1qK=E(_1qJ);switch(_1qK._){case 0:return new T2(0,new T(function(){return jsShow(_1qK.a);}),_1qI);case 1:return new T2(0,new T(function(){var _1qL=__app1(E(_1qA),_1qK.a);return String(_1qL);}),_1qI);case 2:return (!E(_1qK.a))?new T2(0,_1qB,_1qI):new T2(0,_1qG,_1qI);case 3:var _1qM=E(_1qK.a);if(!_1qM._){return new T2(0,_1qD,new T2(1,_1qw,_1qI));}else{var _1qN=new T(function(){var _1qO=new T(function(){var _1qP=function(_1qQ){var _1qR=E(_1qQ);if(!_1qR._){return E(new T2(1,_1qw,_1qI));}else{var _1qS=new T(function(){var _1qT=B(_1qH(new T(function(){return B(_1qP(_1qR.b));}),_1qR.a));return new T2(1,_1qT.a,_1qT.b);});return new T2(1,_1qz,_1qS);}};return B(_1qP(_1qM.b));}),_1qU=B(_1qH(_1qO,_1qM.a));return new T2(1,_1qU.a,_1qU.b);});return new T2(0,_1qD,_1qN);}break;case 4:var _1qV=E(_1qK.a);if(!_1qV._){return new T2(0,_1qE,new T2(1,_1qx,_1qI));}else{var _1qW=E(_1qV.a),_1qX=new T(function(){var _1qY=new T(function(){var _1qZ=function(_1r0){var _1r1=E(_1r0);if(!_1r1._){return E(new T2(1,_1qx,_1qI));}else{var _1r2=E(_1r1.a),_1r3=new T(function(){var _1r4=B(_1qH(new T(function(){return B(_1qZ(_1r1.b));}),_1r2.b));return new T2(1,_1r4.a,_1r4.b);});return new T2(1,_1qz,new T2(1,_1qF,new T2(1,_1r2.a,new T2(1,_1qF,new T2(1,_1qy,_1r3)))));}};return B(_1qZ(_1qV.b));}),_1r5=B(_1qH(_1qY,_1qW.b));return new T2(1,_1r5.a,_1r5.b);});return new T2(0,_1qE,new T2(1,new T(function(){var _1r6=__app1(E(_1qA),E(_1qW.a));return String(_1r6);}),new T2(1,_1qy,_1qX)));}break;default:return new T2(0,_1qC,_1qI);}},_1r7=new T(function(){return toJSStr(_Z);}),_1r8=function(_1r9){var _1ra=B(_1qH(_Z,_1r9)),_1rb=jsCat(new T2(1,_1ra.a,_1ra.b),E(_1r7));return E(_1rb);},_1rc=function(_1rd){var _1re=E(_1rd);if(!_1re._){return new T2(0,_Z,_Z);}else{var _1rf=E(_1re.a),_1rg=new T(function(){var _1rh=B(_1rc(_1re.b));return new T2(0,_1rh.a,_1rh.b);});return new T2(0,new T2(1,_1rf.a,new T(function(){return E(E(_1rg).a);})),new T2(1,_1rf.b,new T(function(){return E(E(_1rg).b);})));}},_1ri=new T(function(){return B(unCStr("Rk"));}),_1rj=function(_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr,_1rs,_1rt,_1ru,_1rv,_1rw,_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG){while(1){var _1rH=B((function(_1rI,_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP,_1rQ,_1rR,_1rS,_1rT,_1rU,_1rV,_1rW,_1rX,_1rY,_1rZ,_1s0,_1s1,_1s2,_1s3,_1s4){var _1s5=E(_1rI);if(!_1s5._){return {_:0,a:_1rJ,b:_1rK,c:_1rL,d:_1rM,e:_1rN,f:_1rO,g:_1rP,h:_1rQ,i:_1rR,j:_1rS,k:_1rT,l:_1rU,m:_1rV,n:_1rW,o:_1rX,p:_1rY,q:_1rZ,r:_1s0,s:_1s1,t:_1s2,u:_1s3,v:_1s4};}else{var _1s6=_1s5.a,_1s7=B(_YD(B(unAppCStr("e.e",new T2(1,_1s6,new T(function(){return B(unAppCStr(".m0:",new T2(1,_1s6,_1ri)));})))),_1rJ,_1rK,_1rL,_1rM,_1rN,_1rO,_1rP,_1rQ,_1rR,_1rS,_1rT,_1rU,_1rV,_1rW,_1rX,_1rY,_1rZ,_1s0,_1s1,_1s2,_1s3,_1s4));_1rk=_1s5.b;_1rl=_1s7.a;_1rm=_1s7.b;_1rn=_1s7.c;_1ro=_1s7.d;_1rp=_1s7.e;_1rq=_1s7.f;_1rr=_1s7.g;_1rs=_1s7.h;_1rt=_1s7.i;_1ru=_1s7.j;_1rv=_1s7.k;_1rw=_1s7.l;_1rx=_1s7.m;_1ry=_1s7.n;_1rz=_1s7.o;_1rA=_1s7.p;_1rB=_1s7.q;_1rC=_1s7.r;_1rD=_1s7.s;_1rE=_1s7.t;_1rF=_1s7.u;_1rG=_1s7.v;return __continue;}})(_1rk,_1rl,_1rm,_1rn,_1ro,_1rp,_1rq,_1rr,_1rs,_1rt,_1ru,_1rv,_1rw,_1rx,_1ry,_1rz,_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG));if(_1rH!=__continue){return _1rH;}}},_1s8=function(_1s9){var _1sa=E(_1s9);switch(_1sa){case 68:return 100;case 72:return 104;case 74:return 106;case 75:return 107;case 76:return 108;case 78:return 110;case 82:return 114;case 83:return 115;default:if(_1sa>>>0>1114111){return new F(function(){return _Bd(_1sa);});}else{return _1sa;}}},_1sb=function(_1sc,_1sd,_1se){while(1){var _1sf=E(_1sd);if(!_1sf._){return (E(_1se)._==0)?true:false;}else{var _1sg=E(_1se);if(!_1sg._){return false;}else{if(!B(A3(_4F,_1sc,_1sf.a,_1sg.a))){return false;}else{_1sd=_1sf.b;_1se=_1sg.b;continue;}}}}},_1sh=function(_1si,_1sj){return (!B(_1sb(_vS,_1si,_1sj)))?true:false;},_1sk=function(_1sl,_1sm){return new F(function(){return _1sb(_vS,_1sl,_1sm);});},_1sn=new T2(0,_1sk,_1sh),_1so=function(_1sp){var _1sq=E(_1sp);if(!_1sq._){return new T2(0,_Z,_Z);}else{var _1sr=E(_1sq.a),_1ss=new T(function(){var _1st=B(_1so(_1sq.b));return new T2(0,_1st.a,_1st.b);});return new T2(0,new T2(1,_1sr.a,new T(function(){return E(E(_1ss).a);})),new T2(1,_1sr.b,new T(function(){return E(E(_1ss).b);})));}},_1su=function(_1sv,_1sw){while(1){var _1sx=E(_1sw);if(!_1sx._){return __Z;}else{var _1sy=_1sx.b,_1sz=E(_1sv);if(_1sz==1){return E(_1sy);}else{_1sv=_1sz-1|0;_1sw=_1sy;continue;}}}},_1sA=function(_1sB,_1sC){while(1){var _1sD=E(_1sC);if(!_1sD._){return __Z;}else{var _1sE=_1sD.b,_1sF=E(_1sB);if(_1sF==1){return E(_1sE);}else{_1sB=_1sF-1|0;_1sC=_1sE;continue;}}}},_1sG=function(_1sH){return new F(function(){return _KR(_1sH,_Z);});},_1sI=function(_1sJ,_1sK,_1sL,_1sM){var _1sN=new T(function(){return B(_Rj(_lc,_1sK,_1sL));}),_1sO=new T(function(){var _1sP=E(_1sN),_1sQ=new T(function(){var _1sR=_1sP+1|0;if(_1sR>0){return B(_1sA(_1sR,_1sL));}else{return E(_1sL);}});if(0>=_1sP){return E(_1sQ);}else{var _1sS=function(_1sT,_1sU){var _1sV=E(_1sT);if(!_1sV._){return E(_1sQ);}else{var _1sW=_1sV.a,_1sX=E(_1sU);return (_1sX==1)?new T2(1,_1sW,_1sQ):new T2(1,_1sW,new T(function(){return B(_1sS(_1sV.b,_1sX-1|0));}));}};return B(_1sS(_1sL,_1sP));}}),_1sY=new T(function(){var _1sZ=E(_1sN),_1t0=new T(function(){if(E(_1sK)==94){return B(A2(_1sJ,new T(function(){return B(_aW(_1sM,_1sZ+1|0));}),new T(function(){return B(_aW(_1sM,_1sZ));})));}else{return B(A2(_1sJ,new T(function(){return B(_aW(_1sM,_1sZ));}),new T(function(){return B(_aW(_1sM,_1sZ+1|0));})));}}),_1t1=new T2(1,_1t0,new T(function(){var _1t2=_1sZ+2|0;if(_1t2>0){return B(_1su(_1t2,_1sM));}else{return E(_1sM);}}));if(0>=_1sZ){return E(_1t1);}else{var _1t3=function(_1t4,_1t5){var _1t6=E(_1t4);if(!_1t6._){return E(_1t1);}else{var _1t7=_1t6.a,_1t8=E(_1t5);return (_1t8==1)?new T2(1,_1t7,_1t1):new T2(1,_1t7,new T(function(){return B(_1t3(_1t6.b,_1t8-1|0));}));}};return B(_1t3(_1sM,_1sZ));}});return (E(_1sK)==94)?new T2(0,new T(function(){return B(_1sG(_1sO));}),new T(function(){return B(_1sG(_1sY));})):new T2(0,_1sO,_1sY);},_1t9=new T(function(){return B(_gs(_th,_tg));}),_1ta=function(_1tb,_1tc,_1td){while(1){if(!E(_1t9)){if(!B(_gs(B(_18t(_1tc,_th)),_tg))){if(!B(_gs(_1tc,_f0))){var _1te=B(_sK(_1tb,_1tb)),_1tf=B(_18e(B(_iT(_1tc,_f0)),_th)),_1tg=B(_sK(_1tb,_1td));_1tb=_1te;_1tc=_1tf;_1td=_1tg;continue;}else{return new F(function(){return _sK(_1tb,_1td);});}}else{var _1te=B(_sK(_1tb,_1tb)),_1tf=B(_18e(_1tc,_th));_1tb=_1te;_1tc=_1tf;continue;}}else{return E(_dZ);}}},_1th=function(_1ti,_1tj){while(1){if(!E(_1t9)){if(!B(_gs(B(_18t(_1tj,_th)),_tg))){if(!B(_gs(_1tj,_f0))){return new F(function(){return _1ta(B(_sK(_1ti,_1ti)),B(_18e(B(_iT(_1tj,_f0)),_th)),_1ti);});}else{return E(_1ti);}}else{var _1tk=B(_sK(_1ti,_1ti)),_1tl=B(_18e(_1tj,_th));_1ti=_1tk;_1tj=_1tl;continue;}}else{return E(_dZ);}}},_1tm=function(_1tn,_1to){if(!B(_hc(_1to,_tg))){if(!B(_gs(_1to,_tg))){return new F(function(){return _1th(_1tn,_1to);});}else{return E(_f0);}}else{return E(_tW);}},_1tp=94,_1tq=45,_1tr=43,_1ts=42,_1tt=function(_1tu,_1tv){while(1){var _1tw=B((function(_1tx,_1ty){var _1tz=E(_1ty);if(!_1tz._){return __Z;}else{if((B(_qy(_1tx,0))+1|0)==B(_qy(_1tz,0))){if(!B(_4H(_lc,_1tp,_1tx))){if(!B(_4H(_lc,_1ts,_1tx))){if(!B(_4H(_lc,_1tr,_1tx))){if(!B(_4H(_lc,_1tq,_1tx))){return E(_1tz);}else{var _1tA=B(_1sI(_iT,45,_1tx,_1tz));_1tu=_1tA.a;_1tv=_1tA.b;return __continue;}}else{var _1tB=B(_1sI(_gA,43,_1tx,_1tz));_1tu=_1tB.a;_1tv=_1tB.b;return __continue;}}else{var _1tC=B(_1sI(_sK,42,_1tx,_1tz));_1tu=_1tC.a;_1tv=_1tC.b;return __continue;}}else{var _1tD=B(_1sI(_1tm,94,new T(function(){return B(_1sG(_1tx));}),new T(function(){return B(_KR(_1tz,_Z));})));_1tu=_1tD.a;_1tv=_1tD.b;return __continue;}}else{return __Z;}}})(_1tu,_1tv));if(_1tw!=__continue){return _1tw;}}},_1tE=function(_1tF){var _1tG=E(_1tF);if(!_1tG._){return new T2(0,_Z,_Z);}else{var _1tH=E(_1tG.a),_1tI=new T(function(){var _1tJ=B(_1tE(_1tG.b));return new T2(0,_1tJ.a,_1tJ.b);});return new T2(0,new T2(1,_1tH.a,new T(function(){return E(E(_1tI).a);})),new T2(1,_1tH.b,new T(function(){return E(E(_1tI).b);})));}},_1tK=new T(function(){return B(unCStr("0123456789+-"));}),_1tL=function(_1tM){while(1){var _1tN=E(_1tM);if(!_1tN._){return true;}else{if(!B(_4H(_lc,_1tN.a,_1tK))){return false;}else{_1tM=_1tN.b;continue;}}}},_1tO=new T(function(){return B(err(_wY));}),_1tP=new T(function(){return B(err(_x2));}),_1tQ=function(_1tR,_1tS){var _1tT=function(_1tU,_1tV){var _1tW=function(_1tX){return new F(function(){return A1(_1tV,new T(function(){return B(_jy(_1tX));}));});},_1tY=new T(function(){return B(_HG(function(_1tZ){return new F(function(){return A3(_1tR,_1tZ,_1tU,_1tW);});}));}),_1u0=function(_1u1){return E(_1tY);},_1u2=function(_1u3){return new F(function(){return A2(_Gn,_1u3,_1u0);});},_1u4=new T(function(){return B(_HG(function(_1u5){var _1u6=E(_1u5);if(_1u6._==4){var _1u7=E(_1u6.a);if(!_1u7._){return new F(function(){return A3(_1tR,_1u6,_1tU,_1tV);});}else{if(E(_1u7.a)==45){if(!E(_1u7.b)._){return E(new T1(1,_1u2));}else{return new F(function(){return A3(_1tR,_1u6,_1tU,_1tV);});}}else{return new F(function(){return A3(_1tR,_1u6,_1tU,_1tV);});}}}else{return new F(function(){return A3(_1tR,_1u6,_1tU,_1tV);});}}));}),_1u8=function(_1u9){return E(_1u4);};return new T1(1,function(_1ua){return new F(function(){return A2(_Gn,_1ua,_1u8);});});};return new F(function(){return _Ix(_1tT,_1tS);});},_1ub=function(_1uc){var _1ud=E(_1uc);if(_1ud._==5){var _1ue=B(_Kt(_1ud.a));return (_1ue._==0)?E(_Ky):function(_1uf,_1ug){return new F(function(){return A1(_1ug,_1ue.a);});};}else{return E(_Ky);}},_1uh=new T(function(){return B(A3(_1tQ,_1ub,_Id,_K0));}),_1ui=function(_1uj,_1uk){var _1ul=E(_1uk);if(!_1ul._){return __Z;}else{var _1um=_1ul.a,_1un=_1ul.b,_1uo=function(_1up){var _1uq=B(_1tE(_1uj)),_1ur=_1uq.a;return (!B(_4H(_uJ,_1um,_1ur)))?__Z:new T2(1,new T(function(){return B(_aW(_1uq.b,B(_Rj(_uJ,_1um,_1ur))));}),new T(function(){return B(_1ui(_1uj,_1un));}));};if(!B(_ae(_1um,_Z))){if(!B(_1tL(_1um))){return new F(function(){return _1uo(_);});}else{return new T2(1,new T(function(){var _1us=B(_KK(B(_x7(_1uh,_1um))));if(!_1us._){return E(_1tO);}else{if(!E(_1us.b)._){return E(_1us.a);}else{return E(_1tP);}}}),new T(function(){return B(_1ui(_1uj,_1un));}));}}else{return new F(function(){return _1uo(_);});}}},_1ut=new T(function(){return B(unCStr("+-*^"));}),_1uu=new T(function(){return B(unCStr("0123456789"));}),_1uv=new T(function(){return B(_PU("Siki.hs:12:9-28|(hn : ns, cs)"));}),_1uw=new T2(1,_Z,_Z),_1ux=function(_1uy){var _1uz=E(_1uy);if(!_1uz._){return new T2(0,_1uw,_Z);}else{var _1uA=_1uz.a,_1uB=new T(function(){var _1uC=B(_1ux(_1uz.b)),_1uD=E(_1uC.a);if(!_1uD._){return E(_1uv);}else{return new T3(0,_1uD.a,_1uD.b,_1uC.b);}});return (!B(_4H(_lc,_1uA,_1uu)))?(!B(_4H(_lc,_1uA,_1ut)))?new T2(0,new T2(1,new T2(1,_1uA,new T(function(){return E(E(_1uB).a);})),new T(function(){return E(E(_1uB).b);})),new T(function(){return E(E(_1uB).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1uB).a);}),new T(function(){return E(E(_1uB).b);}))),new T2(1,_1uA,new T(function(){return E(E(_1uB).c);}))):new T2(0,new T2(1,new T2(1,_1uA,new T(function(){return E(E(_1uB).a);})),new T(function(){return E(E(_1uB).b);})),new T(function(){return E(E(_1uB).c);}));}},_1uE=function(_1uF,_1uG){var _1uH=new T(function(){var _1uI=B(_1ux(_1uG)),_1uJ=E(_1uI.a);if(!_1uJ._){return E(_1uv);}else{return new T3(0,_1uJ.a,_1uJ.b,_1uI.b);}});return (!B(_4H(_lc,_1uF,_1uu)))?(!B(_4H(_lc,_1uF,_1ut)))?new T2(0,new T2(1,new T2(1,_1uF,new T(function(){return E(E(_1uH).a);})),new T(function(){return E(E(_1uH).b);})),new T(function(){return E(E(_1uH).c);})):new T2(0,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1uH).a);}),new T(function(){return E(E(_1uH).b);}))),new T2(1,_1uF,new T(function(){return E(E(_1uH).c);}))):new T2(0,new T2(1,new T2(1,_1uF,new T(function(){return E(E(_1uH).a);})),new T(function(){return E(E(_1uH).b);})),new T(function(){return E(E(_1uH).c);}));},_1uK=function(_1uL,_1uM){while(1){var _1uN=E(_1uL);if(!_1uN._){return E(_1uM);}else{_1uL=_1uN.b;_1uM=_1uN.a;continue;}}},_1uO=function(_1uP,_1uQ,_1uR){return new F(function(){return _1uK(_1uQ,_1uP);});},_1uS=function(_1uT,_1uU){var _1uV=E(_1uU);if(!_1uV._){return __Z;}else{var _1uW=B(_1uE(_1uV.a,_1uV.b)),_1uX=B(_1tt(_1uW.b,B(_1ui(_1uT,_1uW.a))));if(!_1uX._){return E(_1uV);}else{return new F(function(){return _1ax(0,B(_1uO(_1uX.a,_1uX.b,_ZW)),_Z);});}}},_1uY=function(_1uZ,_1v0){var _1v1=function(_1v2,_1v3){while(1){var _1v4=B((function(_1v5,_1v6){var _1v7=E(_1v6);if(!_1v7._){return (!B(_vl(_1v5,_Z)))?new T2(0,_B3,_1v5):new T2(0,_B2,_Z);}else{var _1v8=_1v7.b,_1v9=B(_1so(_1v7.a)).a;if(!B(_4H(_lc,_1g7,_1v9))){var _1va=_1v5;_1v2=_1va;_1v3=_1v8;return __continue;}else{var _1vb=B(_1gD(_1v9)),_1vc=_1vb.a,_1vd=_1vb.b;if(!B(_ae(_1vd,_Z))){if(!B(_vl(B(_1uS(_1uZ,_1vc)),B(_1uS(_1uZ,_1vd))))){return new T2(0,_B2,_Z);}else{var _1ve=new T(function(){if(!B(_vl(_1v5,_Z))){return B(_x(_1v5,new T(function(){return B(unAppCStr(" ",_1vc));},1)));}else{return E(_1vc);}});_1v2=_1ve;_1v3=_1v8;return __continue;}}else{return new T2(0,_B2,_Z);}}}})(_1v2,_1v3));if(_1v4!=__continue){return _1v4;}}};return new F(function(){return _1v1(_Z,_1v0);});},_1vf=function(_1vg,_1vh){var _1vi=new T(function(){var _1vj=B(_KK(B(_x7(_1an,new T(function(){return B(_uj(3,B(_H(0,imul(E(_1vh),E(_1vg)-1|0)|0,_Z))));})))));if(!_1vj._){return E(_1am);}else{if(!E(_1vj.b)._){return E(_1vj.a);}else{return E(_1al);}}});return new T2(0,new T(function(){return B(_eA(_1vi,_1vg));}),_1vi);},_1vk=function(_1vl,_1vm){while(1){var _1vn=E(_1vm);if(!_1vn._){return __Z;}else{var _1vo=_1vn.b,_1vp=E(_1vl);if(_1vp==1){return E(_1vo);}else{_1vl=_1vp-1|0;_1vm=_1vo;continue;}}}},_1vq=function(_1vr,_1vs){while(1){var _1vt=E(_1vs);if(!_1vt._){return __Z;}else{var _1vu=_1vt.b,_1vv=E(_1vr);if(_1vv==1){return E(_1vu);}else{_1vr=_1vv-1|0;_1vs=_1vu;continue;}}}},_1vw=64,_1vx=new T2(1,_1vw,_Z),_1vy=function(_1vz,_1vA,_1vB,_1vC){return (!B(_vl(_1vz,_1vB)))?true:(!B(_gs(_1vA,_1vC)))?true:false;},_1vD=function(_1vE,_1vF){var _1vG=E(_1vE),_1vH=E(_1vF);return new F(function(){return _1vy(_1vG.a,_1vG.b,_1vH.a,_1vH.b);});},_1vI=function(_1vJ,_1vK,_1vL,_1vM){if(!B(_vl(_1vJ,_1vL))){return false;}else{return new F(function(){return _gs(_1vK,_1vM);});}},_1vN=function(_1vO,_1vP){var _1vQ=E(_1vO),_1vR=E(_1vP);return new F(function(){return _1vI(_1vQ.a,_1vQ.b,_1vR.a,_1vR.b);});},_1vS=new T2(0,_1vN,_1vD),_1vT=function(_1vU){var _1vV=E(_1vU);if(!_1vV._){return new T2(0,_Z,_Z);}else{var _1vW=E(_1vV.a),_1vX=new T(function(){var _1vY=B(_1vT(_1vV.b));return new T2(0,_1vY.a,_1vY.b);});return new T2(0,new T2(1,_1vW.a,new T(function(){return E(E(_1vX).a);})),new T2(1,_1vW.b,new T(function(){return E(E(_1vX).b);})));}},_1vZ=function(_1w0){var _1w1=E(_1w0);if(!_1w1._){return new T2(0,_Z,_Z);}else{var _1w2=E(_1w1.a),_1w3=new T(function(){var _1w4=B(_1vZ(_1w1.b));return new T2(0,_1w4.a,_1w4.b);});return new T2(0,new T2(1,_1w2.a,new T(function(){return E(E(_1w3).a);})),new T2(1,_1w2.b,new T(function(){return E(E(_1w3).b);})));}},_1w5=function(_1w6){var _1w7=E(_1w6);if(!_1w7._){return new T2(0,_Z,_Z);}else{var _1w8=E(_1w7.a),_1w9=new T(function(){var _1wa=B(_1w5(_1w7.b));return new T2(0,_1wa.a,_1wa.b);});return new T2(0,new T2(1,_1w8.a,new T(function(){return E(E(_1w9).a);})),new T2(1,_1w8.b,new T(function(){return E(E(_1w9).b);})));}},_1wb=function(_1wc,_1wd){return (_1wc<=_1wd)?new T2(1,_1wc,new T(function(){return B(_1wb(_1wc+1|0,_1wd));})):__Z;},_1we=new T(function(){return B(_1wb(65,90));}),_1wf=function(_1wg){return (_1wg<=122)?new T2(1,_1wg,new T(function(){return B(_1wf(_1wg+1|0));})):E(_1we);},_1wh=new T(function(){return B(_1wf(97));}),_1wi=function(_1wj){while(1){var _1wk=E(_1wj);if(!_1wk._){return true;}else{if(!B(_4H(_lc,_1wk.a,_1wh))){return false;}else{_1wj=_1wk.b;continue;}}}},_1wl=new T2(0,_Z,_Z),_1wm=new T(function(){return B(err(_wY));}),_1wn=new T(function(){return B(err(_x2));}),_1wo=new T(function(){return B(A3(_1tQ,_1ub,_Id,_K0));}),_1wp=function(_1wq,_1wr,_1ws){while(1){var _1wt=B((function(_1wu,_1wv,_1ww){var _1wx=E(_1ww);if(!_1wx._){return __Z;}else{var _1wy=_1wx.b,_1wz=B(_1vZ(_1wv)),_1wA=_1wz.a,_1wB=B(_1vT(_1wA)),_1wC=_1wB.a,_1wD=new T(function(){return E(B(_1w5(_1wx.a)).a);}),_1wE=new T(function(){return B(_4H(_lc,_1g7,_1wD));}),_1wF=new T(function(){if(!E(_1wE)){return E(_1wl);}else{var _1wG=B(_1gD(_1wD));return new T2(0,_1wG.a,_1wG.b);}}),_1wH=new T(function(){return E(E(_1wF).a);}),_1wI=new T(function(){return B(_Rj(_uJ,_1wH,_1wC));}),_1wJ=new T(function(){var _1wK=function(_){var _1wL=B(_qy(_1wv,0))-1|0,_1wM=function(_1wN){if(_1wN>=0){var _1wO=newArr(_1wN,_1ck),_1wP=_1wO,_1wQ=E(_1wN);if(!_1wQ){return new T4(0,E(_1eG),E(_1wL),0,_1wP);}else{var _1wR=function(_1wS,_1wT,_){while(1){var _1wU=E(_1wS);if(!_1wU._){return E(_);}else{var _=_1wP[_1wT]=_1wU.a;if(_1wT!=(_1wQ-1|0)){var _1wV=_1wT+1|0;_1wS=_1wU.b;_1wT=_1wV;continue;}else{return E(_);}}}},_=B(_1wR(_1wz.b,0,_));return new T4(0,E(_1eG),E(_1wL),_1wQ,_1wP);}}else{return E(_1de);}};if(0>_1wL){return new F(function(){return _1wM(0);});}else{return new F(function(){return _1wM(_1wL+1|0);});}};return B(_1df(_1wK));});if(!B(_4H(_uJ,_1wH,_1wC))){var _1wW=false;}else{var _1wX=E(_1wJ),_1wY=E(_1wX.a),_1wZ=E(_1wX.b),_1x0=E(_1wI);if(_1wY>_1x0){var _1x1=B(_1kM(_1x0,_1wY,_1wZ));}else{if(_1x0>_1wZ){var _1x2=B(_1kM(_1x0,_1wY,_1wZ));}else{var _1x2=E(_1wX.d[_1x0-_1wY|0])==E(_1wu);}var _1x1=_1x2;}var _1wW=_1x1;}var _1x3=new T(function(){return E(E(_1wF).b);}),_1x4=new T(function(){return B(_Rj(_uJ,_1x3,_1wC));}),_1x5=new T(function(){if(!B(_4H(_uJ,_1x3,_1wC))){return false;}else{var _1x6=E(_1wJ),_1x7=E(_1x6.a),_1x8=E(_1x6.b),_1x9=E(_1x4);if(_1x7>_1x9){return B(_1kM(_1x9,_1x7,_1x8));}else{if(_1x9>_1x8){return B(_1kM(_1x9,_1x7,_1x8));}else{return E(_1x6.d[_1x9-_1x7|0])==E(_1wu);}}}}),_1xa=new T(function(){var _1xb=function(_){var _1xc=B(_qy(_1wA,0))-1|0,_1xd=function(_1xe){if(_1xe>=0){var _1xf=newArr(_1xe,_1ck),_1xg=_1xf,_1xh=E(_1xe);if(!_1xh){return new T4(0,E(_1eG),E(_1xc),0,_1xg);}else{var _1xi=function(_1xj,_1xk,_){while(1){var _1xl=E(_1xj);if(!_1xl._){return E(_);}else{var _=_1xg[_1xk]=_1xl.a;if(_1xk!=(_1xh-1|0)){var _1xm=_1xk+1|0;_1xj=_1xl.b;_1xk=_1xm;continue;}else{return E(_);}}}},_=B(_1xi(_1wB.b,0,_));return new T4(0,E(_1eG),E(_1xc),_1xh,_1xg);}}else{return E(_1de);}};if(0>_1xc){return new F(function(){return _1xd(0);});}else{return new F(function(){return _1xd(_1xc+1|0);});}};return B(_1df(_1xb));}),_1xn=function(_1xo){var _1xp=function(_1xq){return (!E(_1wW))?__Z:(!E(_1x5))?__Z:new T2(1,new T2(0,_1wH,new T(function(){var _1xr=E(_1xa),_1xs=E(_1xr.a),_1xt=E(_1xr.b),_1xu=E(_1wI);if(_1xs>_1xu){return B(_1kM(_1xu,_1xs,_1xt));}else{if(_1xu>_1xt){return B(_1kM(_1xu,_1xs,_1xt));}else{return E(_1xr.d[_1xu-_1xs|0]);}}})),new T2(1,new T2(0,_1x3,new T(function(){var _1xv=E(_1xa),_1xw=E(_1xv.a),_1xx=E(_1xv.b),_1xy=E(_1x4);if(_1xw>_1xy){return B(_1kM(_1xy,_1xw,_1xx));}else{if(_1xy>_1xx){return B(_1kM(_1xy,_1xw,_1xx));}else{return E(_1xv.d[_1xy-_1xw|0]);}}})),_Z));};if(!E(_1wW)){if(!E(_1x5)){return new F(function(){return _1xp(_);});}else{return new T2(1,new T2(0,_1x3,new T(function(){var _1xz=E(_1xa),_1xA=E(_1xz.a),_1xB=E(_1xz.b),_1xC=E(_1x4);if(_1xA>_1xC){return B(_1kM(_1xC,_1xA,_1xB));}else{if(_1xC>_1xB){return B(_1kM(_1xC,_1xA,_1xB));}else{return E(_1xz.d[_1xC-_1xA|0]);}}})),_Z);}}else{return new F(function(){return _1xp(_);});}};if(!E(_1wW)){var _1xD=B(_1xn(_));}else{if(!E(_1x5)){var _1xE=new T2(1,new T2(0,_1wH,new T(function(){var _1xF=E(_1xa),_1xG=E(_1xF.a),_1xH=E(_1xF.b),_1xI=E(_1wI);if(_1xG>_1xI){return B(_1kM(_1xI,_1xG,_1xH));}else{if(_1xI>_1xH){return B(_1kM(_1xI,_1xG,_1xH));}else{return E(_1xF.d[_1xI-_1xG|0]);}}})),_Z);}else{var _1xE=B(_1xn(_));}var _1xD=_1xE;}if(!B(_1sb(_1vS,_1xD,_Z))){return new F(function(){return _x(_1xD,new T(function(){return B(_1wp(_1wu,_1wv,_1wy));},1));});}else{if(!E(_1wE)){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{if(!B(_1wi(_1wH))){if(!B(_1wi(_1x3))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{if(!E(_1wW)){if(!E(_1x5)){if(!B(_ae(_1wH,_Z))){if(!B(_1tL(_1wH))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{return new T2(1,new T2(0,_1x3,new T(function(){var _1xL=B(_KK(B(_x7(_1wo,_1wH))));if(!_1xL._){return E(_1wm);}else{if(!E(_1xL.b)._){return E(_1xL.a);}else{return E(_1wn);}}})),new T(function(){return B(_1wp(_1wu,_1wv,_1wy));}));}}else{var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}else{var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}else{var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}}else{if(!E(_1wW)){if(!E(_1x5)){if(!B(_ae(_1x3,_Z))){if(!B(_1tL(_1x3))){if(!B(_1wi(_1x3))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{if(!B(_ae(_1wH,_Z))){if(!B(_1tL(_1wH))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{return new T2(1,new T2(0,_1x3,new T(function(){var _1xM=B(_KK(B(_x7(_1wo,_1wH))));if(!_1xM._){return E(_1wm);}else{if(!E(_1xM.b)._){return E(_1xM.a);}else{return E(_1wn);}}})),new T(function(){return B(_1wp(_1wu,_1wv,_1wy));}));}}else{var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}}else{return new T2(1,new T2(0,_1wH,new T(function(){var _1xN=B(_KK(B(_x7(_1wo,_1x3))));if(!_1xN._){return E(_1wm);}else{if(!E(_1xN.b)._){return E(_1xN.a);}else{return E(_1wn);}}})),new T(function(){return B(_1wp(_1wu,_1wv,_1wy));}));}}else{if(!B(_1wi(_1x3))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{if(!B(_ae(_1wH,_Z))){if(!B(_1tL(_1wH))){var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}else{return new T2(1,new T2(0,_1x3,new T(function(){var _1xO=B(_KK(B(_x7(_1wo,_1wH))));if(!_1xO._){return E(_1wm);}else{if(!E(_1xO.b)._){return E(_1xO.a);}else{return E(_1wn);}}})),new T(function(){return B(_1wp(_1wu,_1wv,_1wy));}));}}else{var _1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}}}else{var _1xP=B(_1wi(_1x3)),_1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}else{var _1xQ=B(_1wi(_1x3)),_1xJ=_1wu,_1xK=_1wv;_1wq=_1xJ;_1wr=_1xK;_1ws=_1wy;return __continue;}}}}}})(_1wq,_1wr,_1ws));if(_1wt!=__continue){return _1wt;}}},_1xR=102,_1xS=101,_1xT=new T(function(){return B(unCStr("=="));}),_1xU=new T(function(){return B(_ic("Action.hs:(103,17)-(107,70)|case"));}),_1xV=new T(function(){return B(_ic("Action.hs:(118,9)-(133,75)|function wnMove\'"));}),_1xW=5,_1xX=117,_1xY=98,_1xZ=110,_1y0=118,_1y1=function(_1y2,_1y3,_1y4,_1y5,_1y6,_1y7,_1y8,_1y9,_1ya,_1yb,_1yc,_1yd,_1ye,_1yf){var _1yg=B(_aW(B(_aW(_1y6,_1y3)),_1y2)),_1yh=_1yg.a,_1yi=_1yg.b;if(E(_1y9)==32){if(!B(_4H(_lc,_1yh,_1vx))){var _1yj=false;}else{switch(E(_1yi)){case 0:var _1yk=true;break;case 1:var _1yk=false;break;case 2:var _1yk=false;break;case 3:var _1yk=false;break;case 4:var _1yk=false;break;case 5:var _1yk=false;break;case 6:var _1yk=false;break;case 7:var _1yk=false;break;default:var _1yk=false;}var _1yj=_1yk;}var _1yl=_1yj;}else{var _1yl=false;}if(E(_1y9)==32){if(E(_1yh)==32){var _1ym=false;}else{switch(E(_1yi)){case 0:if(!E(_1yl)){var _1yn=true;}else{var _1yn=false;}var _1yo=_1yn;break;case 1:var _1yo=false;break;case 2:var _1yo=false;break;case 3:var _1yo=false;break;case 4:var _1yo=false;break;case 5:var _1yo=false;break;case 6:var _1yo=false;break;case 7:var _1yo=false;break;default:if(!E(_1yl)){var _1yp=true;}else{var _1yp=false;}var _1yo=_1yp;}var _1ym=_1yo;}var _1yq=_1ym;}else{var _1yq=false;}var _1yr=new T(function(){return B(_Pt(_1y2,_1y3,new T(function(){if(!E(_1yq)){if(!E(_1yl)){return E(_1yh);}else{return _1y8;}}else{return E(_11R);}}),_1yi,_1y6));});switch(E(_1yi)){case 3:var _1ys=true;break;case 4:if(E(_1y9)==32){var _1yt=true;}else{var _1yt=false;}var _1ys=_1yt;break;default:var _1ys=false;}if(!E(_1ys)){var _1yu=E(_1yr);}else{var _1yv=E(_1y4),_1yw=new T(function(){return B(_aW(_1yr,_1y3));}),_1yx=function(_1yy,_1yz){var _1yA=E(_1yy);if(_1yA==( -1)){return E(_1yr);}else{var _1yB=new T(function(){return B(_Pt(_1y2,_1y3,_11R,_II,_1yr));}),_1yC=E(_1yz);if(_1yC==( -1)){var _1yD=__Z;}else{var _1yD=B(_aW(_1yB,_1yC));}if(E(B(_aW(_1yD,_1yA)).a)==32){var _1yE=new T(function(){var _1yF=new T(function(){return B(_aW(_1yw,_1y2));}),_1yG=new T2(1,new T2(0,new T(function(){return E(E(_1yF).a);}),new T(function(){return E(E(_1yF).b);})),new T(function(){var _1yH=_1yA+1|0;if(_1yH>0){return B(_1vq(_1yH,_1yD));}else{return E(_1yD);}}));if(0>=_1yA){return E(_1yG);}else{var _1yI=function(_1yJ,_1yK){var _1yL=E(_1yJ);if(!_1yL._){return E(_1yG);}else{var _1yM=_1yL.a,_1yN=E(_1yK);return (_1yN==1)?new T2(1,_1yM,_1yG):new T2(1,_1yM,new T(function(){return B(_1yI(_1yL.b,_1yN-1|0));}));}};return B(_1yI(_1yD,_1yA));}}),_1yO=new T2(1,_1yE,new T(function(){var _1yP=_1yz+1|0;if(_1yP>0){return B(_1vk(_1yP,_1yB));}else{return E(_1yB);}}));if(0>=_1yz){return E(_1yO);}else{var _1yQ=function(_1yR,_1yS){var _1yT=E(_1yR);if(!_1yT._){return E(_1yO);}else{var _1yU=_1yT.a,_1yV=E(_1yS);return (_1yV==1)?new T2(1,_1yU,_1yO):new T2(1,_1yU,new T(function(){return B(_1yQ(_1yT.b,_1yV-1|0));}));}};return new F(function(){return _1yQ(_1yB,_1yz);});}}else{return E(_1yr);}}};if(_1y2<=_1yv){if(_1yv<=_1y2){var _1yW=E(_1y5);if(_1y3<=_1yW){if(_1yW<=_1y3){var _1yX=E(_1xU);}else{var _1yY=E(_1y3);if(!_1yY){var _1yZ=B(_1yx( -1, -1));}else{var _1yZ=B(_1yx(_1y2,_1yY-1|0));}var _1yX=_1yZ;}var _1z0=_1yX;}else{if(_1y3!=(B(_qy(_1yr,0))-1|0)){var _1z1=B(_1yx(_1y2,_1y3+1|0));}else{var _1z1=B(_1yx( -1, -1));}var _1z0=_1z1;}var _1z2=_1z0;}else{var _1z3=E(_1y2);if(!_1z3){var _1z4=B(_1yx( -1, -1));}else{var _1z4=B(_1yx(_1z3-1|0,_1y3));}var _1z2=_1z4;}var _1z5=_1z2;}else{if(_1y2!=(B(_qy(_1yw,0))-1|0)){var _1z6=B(_1yx(_1y2+1|0,_1y3));}else{var _1z6=B(_1yx( -1, -1));}var _1z5=_1z6;}var _1yu=_1z5;}if(!E(_1ye)){var _1z7=E(_1yu);}else{var _1z8=new T(function(){var _1z9=E(_1yu);if(!_1z9._){return E(_rm);}else{return B(_qy(_1z9.a,0));}}),_1za=new T(function(){return B(_qy(_1yu,0));}),_1zb=function(_1zc,_1zd,_1ze,_1zf,_1zg,_1zh,_1zi){while(1){var _1zj=B((function(_1zk,_1zl,_1zm,_1zn,_1zo,_1zp,_1zq){var _1zr=E(_1zq);if(!_1zr._){return E(_1zn);}else{var _1zs=_1zr.b,_1zt=E(_1zr.a);if(!_1zt._){return E(_1xV);}else{var _1zu=_1zt.b,_1zv=E(_1zt.a);if(E(_1zv.b)==5){var _1zw=new T(function(){var _1zx=B(_1vf(_1xW,_1zk));return new T2(0,_1zx.a,_1zx.b);}),_1zy=new T(function(){var _1zz=function(_1zA,_1zB){var _1zC=function(_1zD){return new F(function(){return _Pt(_1zl,_1zm,_11R,_II,new T(function(){return B(_Pt(_1zA,_1zB,_1zv.a,_Jx,_1zn));}));});};if(_1zA!=_1zl){return new F(function(){return _1zC(_);});}else{if(_1zB!=_1zm){return new F(function(){return _1zC(_);});}else{return E(_1zn);}}};switch(E(E(_1zw).a)){case 1:var _1zE=_1zl-1|0;if(_1zE<0){return B(_1zz(_1zl,_1zm));}else{if(_1zE>=E(_1z8)){return B(_1zz(_1zl,_1zm));}else{if(_1zm<0){return B(_1zz(_1zl,_1zm));}else{if(_1zm>=E(_1za)){return B(_1zz(_1zl,_1zm));}else{if(_1zE!=_1zo){if(E(B(_aW(B(_aW(_1zn,_1zm)),_1zE)).a)==32){return B(_1zz(_1zE,_1zm));}else{return B(_1zz(_1zl,_1zm));}}else{if(_1zm!=_1zp){if(E(B(_aW(B(_aW(_1zn,_1zm)),_1zE)).a)==32){return B(_1zz(_1zE,_1zm));}else{return B(_1zz(_1zl,_1zm));}}else{return B(_1zz(_1zl,_1zm));}}}}}}break;case 2:if(_1zl<0){return B(_1zz(_1zl,_1zm));}else{if(_1zl>=E(_1z8)){return B(_1zz(_1zl,_1zm));}else{var _1zF=_1zm-1|0;if(_1zF<0){return B(_1zz(_1zl,_1zm));}else{if(_1zF>=E(_1za)){return B(_1zz(_1zl,_1zm));}else{if(_1zl!=_1zo){if(E(B(_aW(B(_aW(_1zn,_1zF)),_1zl)).a)==32){return B(_1zz(_1zl,_1zF));}else{return B(_1zz(_1zl,_1zm));}}else{if(_1zF!=_1zp){if(E(B(_aW(B(_aW(_1zn,_1zF)),_1zl)).a)==32){return B(_1zz(_1zl,_1zF));}else{return B(_1zz(_1zl,_1zm));}}else{return B(_1zz(_1zl,_1zm));}}}}}}break;case 3:var _1zG=_1zl+1|0;if(_1zG<0){return B(_1zz(_1zl,_1zm));}else{if(_1zG>=E(_1z8)){return B(_1zz(_1zl,_1zm));}else{if(_1zm<0){return B(_1zz(_1zl,_1zm));}else{if(_1zm>=E(_1za)){return B(_1zz(_1zl,_1zm));}else{if(_1zG!=_1zo){if(E(B(_aW(B(_aW(_1zn,_1zm)),_1zG)).a)==32){return B(_1zz(_1zG,_1zm));}else{return B(_1zz(_1zl,_1zm));}}else{if(_1zm!=_1zp){if(E(B(_aW(B(_aW(_1zn,_1zm)),_1zG)).a)==32){return B(_1zz(_1zG,_1zm));}else{return B(_1zz(_1zl,_1zm));}}else{return B(_1zz(_1zl,_1zm));}}}}}}break;case 4:if(_1zl<0){return B(_1zz(_1zl,_1zm));}else{if(_1zl>=E(_1z8)){return B(_1zz(_1zl,_1zm));}else{var _1zH=_1zm+1|0;if(_1zH<0){return B(_1zz(_1zl,_1zm));}else{if(_1zH>=E(_1za)){return B(_1zz(_1zl,_1zm));}else{if(_1zl!=_1zo){if(E(B(_aW(B(_aW(_1zn,_1zH)),_1zl)).a)==32){return B(_1zz(_1zl,_1zH));}else{return B(_1zz(_1zl,_1zm));}}else{if(_1zH!=_1zp){if(E(B(_aW(B(_aW(_1zn,_1zH)),_1zl)).a)==32){return B(_1zz(_1zl,_1zH));}else{return B(_1zz(_1zl,_1zm));}}else{return B(_1zz(_1zl,_1zm));}}}}}}break;default:if(_1zl<0){return B(_1zz(_1zl,_1zm));}else{if(_1zl>=E(_1z8)){return B(_1zz(_1zl,_1zm));}else{if(_1zm<0){return B(_1zz(_1zl,_1zm));}else{if(_1zm>=E(_1za)){return B(_1zz(_1zl,_1zm));}else{if(_1zl!=_1zo){var _1zI=E(B(_aW(B(_aW(_1zn,_1zm)),_1zl)).a);return B(_1zz(_1zl,_1zm));}else{if(_1zm!=_1zp){var _1zJ=E(B(_aW(B(_aW(_1zn,_1zm)),_1zl)).a);return B(_1zz(_1zl,_1zm));}else{return B(_1zz(_1zl,_1zm));}}}}}}}}),_1zK=E(_1zu);if(!_1zK._){var _1zL=_1zm+1|0,_1zM=_1zo,_1zN=_1zp;_1zc=new T(function(){return E(E(_1zw).b);},1);_1zd=0;_1ze=_1zL;_1zf=_1zy;_1zg=_1zM;_1zh=_1zN;_1zi=_1zs;return __continue;}else{return new F(function(){return _1zO(new T(function(){return E(E(_1zw).b);},1),_1zl+1|0,_1zm,_1zy,_1zo,_1zp,_1zK.a,_1zK.b,_1zs);});}}else{var _1zP=E(_1zu);if(!_1zP._){var _1zQ=_1zk,_1zL=_1zm+1|0,_1zR=_1zn,_1zM=_1zo,_1zN=_1zp;_1zc=_1zQ;_1zd=0;_1ze=_1zL;_1zf=_1zR;_1zg=_1zM;_1zh=_1zN;_1zi=_1zs;return __continue;}else{return new F(function(){return _1zO(_1zk,_1zl+1|0,_1zm,_1zn,_1zo,_1zp,_1zP.a,_1zP.b,_1zs);});}}}}})(_1zc,_1zd,_1ze,_1zf,_1zg,_1zh,_1zi));if(_1zj!=__continue){return _1zj;}}},_1zO=function(_1zS,_1zT,_1zU,_1zV,_1zW,_1zX,_1zY,_1zZ,_1A0){while(1){var _1A1=B((function(_1A2,_1A3,_1A4,_1A5,_1A6,_1A7,_1A8,_1A9,_1Aa){var _1Ab=E(_1A8);if(E(_1Ab.b)==5){var _1Ac=new T(function(){var _1Ad=B(_1vf(_1xW,_1A2));return new T2(0,_1Ad.a,_1Ad.b);}),_1Ae=new T(function(){var _1Af=function(_1Ag,_1Ah){var _1Ai=function(_1Aj){return new F(function(){return _Pt(_1A3,_1A4,_11R,_II,new T(function(){return B(_Pt(_1Ag,_1Ah,_1Ab.a,_Jx,_1A5));}));});};if(_1Ag!=_1A3){return new F(function(){return _1Ai(_);});}else{if(_1Ah!=_1A4){return new F(function(){return _1Ai(_);});}else{return E(_1A5);}}};switch(E(E(_1Ac).a)){case 1:var _1Ak=_1A3-1|0;if(_1Ak<0){return B(_1Af(_1A3,_1A4));}else{if(_1Ak>=E(_1z8)){return B(_1Af(_1A3,_1A4));}else{if(_1A4<0){return B(_1Af(_1A3,_1A4));}else{if(_1A4>=E(_1za)){return B(_1Af(_1A3,_1A4));}else{if(_1Ak!=_1A6){if(E(B(_aW(B(_aW(_1A5,_1A4)),_1Ak)).a)==32){return B(_1Af(_1Ak,_1A4));}else{return B(_1Af(_1A3,_1A4));}}else{if(_1A4!=_1A7){if(E(B(_aW(B(_aW(_1A5,_1A4)),_1Ak)).a)==32){return B(_1Af(_1Ak,_1A4));}else{return B(_1Af(_1A3,_1A4));}}else{return B(_1Af(_1A3,_1A4));}}}}}}break;case 2:if(_1A3<0){return B(_1Af(_1A3,_1A4));}else{if(_1A3>=E(_1z8)){return B(_1Af(_1A3,_1A4));}else{var _1Al=_1A4-1|0;if(_1Al<0){return B(_1Af(_1A3,_1A4));}else{if(_1Al>=E(_1za)){return B(_1Af(_1A3,_1A4));}else{if(_1A3!=_1A6){if(E(B(_aW(B(_aW(_1A5,_1Al)),_1A3)).a)==32){return B(_1Af(_1A3,_1Al));}else{return B(_1Af(_1A3,_1A4));}}else{if(_1Al!=_1A7){if(E(B(_aW(B(_aW(_1A5,_1Al)),_1A3)).a)==32){return B(_1Af(_1A3,_1Al));}else{return B(_1Af(_1A3,_1A4));}}else{return B(_1Af(_1A3,_1A4));}}}}}}break;case 3:var _1Am=_1A3+1|0;if(_1Am<0){return B(_1Af(_1A3,_1A4));}else{if(_1Am>=E(_1z8)){return B(_1Af(_1A3,_1A4));}else{if(_1A4<0){return B(_1Af(_1A3,_1A4));}else{if(_1A4>=E(_1za)){return B(_1Af(_1A3,_1A4));}else{if(_1Am!=_1A6){if(E(B(_aW(B(_aW(_1A5,_1A4)),_1Am)).a)==32){return B(_1Af(_1Am,_1A4));}else{return B(_1Af(_1A3,_1A4));}}else{if(_1A4!=_1A7){if(E(B(_aW(B(_aW(_1A5,_1A4)),_1Am)).a)==32){return B(_1Af(_1Am,_1A4));}else{return B(_1Af(_1A3,_1A4));}}else{return B(_1Af(_1A3,_1A4));}}}}}}break;case 4:if(_1A3<0){return B(_1Af(_1A3,_1A4));}else{if(_1A3>=E(_1z8)){return B(_1Af(_1A3,_1A4));}else{var _1An=_1A4+1|0;if(_1An<0){return B(_1Af(_1A3,_1A4));}else{if(_1An>=E(_1za)){return B(_1Af(_1A3,_1A4));}else{if(_1A3!=_1A6){if(E(B(_aW(B(_aW(_1A5,_1An)),_1A3)).a)==32){return B(_1Af(_1A3,_1An));}else{return B(_1Af(_1A3,_1A4));}}else{if(_1An!=_1A7){if(E(B(_aW(B(_aW(_1A5,_1An)),_1A3)).a)==32){return B(_1Af(_1A3,_1An));}else{return B(_1Af(_1A3,_1A4));}}else{return B(_1Af(_1A3,_1A4));}}}}}}break;default:if(_1A3<0){return B(_1Af(_1A3,_1A4));}else{if(_1A3>=E(_1z8)){return B(_1Af(_1A3,_1A4));}else{if(_1A4<0){return B(_1Af(_1A3,_1A4));}else{if(_1A4>=E(_1za)){return B(_1Af(_1A3,_1A4));}else{if(_1A3!=_1A6){var _1Ao=E(B(_aW(B(_aW(_1A5,_1A4)),_1A3)).a);return B(_1Af(_1A3,_1A4));}else{if(_1A4!=_1A7){var _1Ap=E(B(_aW(B(_aW(_1A5,_1A4)),_1A3)).a);return B(_1Af(_1A3,_1A4));}else{return B(_1Af(_1A3,_1A4));}}}}}}}}),_1Aq=E(_1A9);if(!_1Aq._){return new F(function(){return _1zb(new T(function(){return E(E(_1Ac).b);},1),0,_1A4+1|0,_1Ae,_1A6,_1A7,_1Aa);});}else{var _1Ar=_1A3+1|0,_1As=_1A4,_1At=_1A6,_1Au=_1A7,_1Av=_1Aa;_1zS=new T(function(){return E(E(_1Ac).b);},1);_1zT=_1Ar;_1zU=_1As;_1zV=_1Ae;_1zW=_1At;_1zX=_1Au;_1zY=_1Aq.a;_1zZ=_1Aq.b;_1A0=_1Av;return __continue;}}else{var _1Aw=E(_1A9);if(!_1Aw._){return new F(function(){return _1zb(_1A2,0,_1A4+1|0,_1A5,_1A6,_1A7,_1Aa);});}else{var _1Ax=_1A2,_1Ar=_1A3+1|0,_1As=_1A4,_1Ay=_1A5,_1At=_1A6,_1Au=_1A7,_1Av=_1Aa;_1zS=_1Ax;_1zT=_1Ar;_1zU=_1As;_1zV=_1Ay;_1zW=_1At;_1zX=_1Au;_1zY=_1Aw.a;_1zZ=_1Aw.b;_1A0=_1Av;return __continue;}}})(_1zS,_1zT,_1zU,_1zV,_1zW,_1zX,_1zY,_1zZ,_1A0));if(_1A1!=__continue){return _1A1;}}},_1z7=B(_1zb(_1yc,0,0,_1yu,_1y2,_1y3,_1yu));}var _1Az=function(_1AA){var _1AB=function(_1AC){var _1AD=new T(function(){switch(E(_1yi)){case 1:return true;break;case 5:return true;break;case 7:return true;break;default:return false;}}),_1AE=new T(function(){if(!E(_1ys)){if(!E(_1AD)){return new T2(0,_1y2,_1y3);}else{return new T2(0,_1y4,_1y5);}}else{if(!B(_1sb(_1sn,_1z7,_1yr))){if(!E(_1AD)){return new T2(0,_1y2,_1y3);}else{return new T2(0,_1y4,_1y5);}}else{return new T2(0,_1y4,_1y5);}}}),_1AF=new T(function(){return E(E(_1AE).b);}),_1AG=new T(function(){return E(E(_1AE).a);});if(!E(_1ys)){var _1AH=E(_1yf);}else{var _1AH=E(B(_1uY(new T(function(){return B(_1wp(_1ya,_1yb,_1z7));}),_1z7)).a);}var _1AI=new T(function(){if(!E(_1yq)){if(!E(_1yl)){var _1AJ=function(_1AK){var _1AL=function(_1AM){var _1AN=E(_1yi);if(_1AN==4){return new T2(1,_1xZ,new T2(1,_1yh,_Z));}else{if(!E(_1AD)){return (E(_1AN)==2)?new T2(1,_1xX,new T2(1,_1yh,_Z)):__Z;}else{var _1AO=E(_1yh);return (E(_1AO)==61)?new T2(1,_1xY,new T2(1,_1AO,new T(function(){return B(_H(0,_1y3,_Z));}))):new T2(1,_1xY,new T2(1,_1AO,_Z));}}};if(!E(_1ys)){return new F(function(){return _1AL(_);});}else{if(E(_1y4)!=E(_1AG)){return new T2(1,_1y0,new T2(1,_1yh,_Z));}else{if(E(_1y5)!=E(_1AF)){return new T2(1,_1y0,new T2(1,_1yh,_Z));}else{return new F(function(){return _1AL(_);});}}}};if(!E(_1ys)){return B(_1AJ(_));}else{if(!E(_1AH)){return B(_1AJ(_));}else{return E(_1xT);}}}else{return new T2(1,_1xR,new T2(1,_1yh,_Z));}}else{return new T2(1,_1xS,new T2(1,_1yh,_Z));}},1);return {_:0,a:E(new T2(0,_1AG,_1AF)),b:E(_1z7),c:E(_1y7),d:_1AA,e:_1AC,f:_1ya,g:E(_1yb),h:_1yc,i:E(B(_x(_1yd,_1AI))),j:E(_1ye),k:E(_1AH)};};if(!E(_1yq)){return new F(function(){return _1AB(_1y9);});}else{return new F(function(){return _1AB(E(_1yh));});}};if(!E(_1yl)){return new F(function(){return _1Az(_1y8);});}else{return new F(function(){return _1Az(E(_1yh));});}},_1AP=new T2(1,_61,_Z),_1AQ=5,_1AR=new T2(1,_1AQ,_Z),_1AS=function(_1AT,_1AU){while(1){var _1AV=E(_1AT);if(!_1AV._){return E(_1AU);}else{_1AT=_1AV.b;_1AU=_1AV.a;continue;}}},_1AW=57,_1AX=48,_1AY=new T2(1,_1vw,_Z),_1AZ=new T(function(){return B(err(_x2));}),_1B0=new T(function(){return B(err(_wY));}),_1B1=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1B2=function(_1B3,_1B4){if((_1B4-48|0)>>>0>9){var _1B5=_1B4+_1B3|0,_1B6=function(_1B7){if(!B(_4H(_lc,_1B7,_1AY))){return E(_1B7);}else{return new F(function(){return _1B2(_1B3,_1B7);});}};if(_1B5<=122){if(_1B5>=97){if(_1B5>>>0>1114111){return new F(function(){return _Bd(_1B5);});}else{return new F(function(){return _1B6(_1B5);});}}else{if(_1B5<=90){if(_1B5>>>0>1114111){return new F(function(){return _Bd(_1B5);});}else{return new F(function(){return _1B6(_1B5);});}}else{var _1B8=65+(_1B5-90|0)|0;if(_1B8>>>0>1114111){return new F(function(){return _Bd(_1B8);});}else{return new F(function(){return _1B6(_1B8);});}}}}else{var _1B9=97+(_1B5-122|0)|0;if(_1B9>>>0>1114111){return new F(function(){return _Bd(_1B9);});}else{return new F(function(){return _1B6(_1B9);});}}}else{var _1Ba=B(_KK(B(_x7(_1B1,new T2(1,_1B4,_Z)))));if(!_1Ba._){return E(_1B0);}else{if(!E(_1Ba.b)._){var _1Bb=E(_1Ba.a)+_1B3|0;switch(_1Bb){case  -1:return E(_1AX);case 10:return E(_1AW);default:return new F(function(){return _1AS(B(_H(0,_1Bb,_Z)),_ZW);});}}else{return E(_1AZ);}}}},_1Bc=function(_1Bd,_1Be){if((_1Bd-48|0)>>>0>9){return _1Be;}else{var _1Bf=B(_KK(B(_x7(_1B1,new T2(1,_1Bd,_Z)))));if(!_1Bf._){return E(_1B0);}else{if(!E(_1Bf.b)._){return new F(function(){return _1B2(E(_1Bf.a),_1Be);});}else{return E(_1AZ);}}}},_1Bg=function(_1Bh,_1Bi){return new F(function(){return _1Bc(E(_1Bh),E(_1Bi));});},_1Bj=new T2(1,_1Bg,_Z),_1Bk=112,_1Bl=111,_1Bm=function(_1Bn,_1Bo,_1Bp,_1Bq,_1Br,_1Bs,_1Bt,_1Bu,_1Bv,_1Bw,_1Bx,_1By){var _1Bz=new T(function(){return B(_aW(B(_aW(_1Bp,_1Bo)),E(_1Bn)));}),_1BA=new T(function(){return E(E(_1Bz).b);}),_1BB=new T(function(){if(E(_1BA)==4){return true;}else{return false;}}),_1BC=new T(function(){return E(E(_1Bz).a);});if(E(_1Bs)==32){var _1BD=false;}else{if(E(_1BC)==32){var _1BE=true;}else{var _1BE=false;}var _1BD=_1BE;}var _1BF=new T(function(){var _1BG=new T(function(){return B(A3(_aW,_1AP,B(_Rj(_lc,_1Br,_1vx)),_1Bs));});if(!E(_1BD)){if(!E(_1BB)){return E(_1BC);}else{if(!B(_4H(_3S,_1Bt,_1AR))){return E(_1BC);}else{return B(A(_aW,[_1Bj,B(_Rj(_3S,_1Bt,_1AR)),_1BG,_1BC]));}}}else{return E(_1BG);}}),_1BH=B(_Pt(_1Bn,_1Bo,_1BF,_1BA,_1Bp)),_1BI=function(_1BJ){var _1BK=B(_1uY(new T(function(){return B(_1wp(_1Bt,_1Bu,_1BH));}),_1BH)).a;return {_:0,a:E(new T2(0,_1Bn,_1Bo)),b:E(_1BH),c:E(_1Bq),d:_1Br,e:_1BJ,f:_1Bt,g:E(_1Bu),h:_1Bv,i:E(B(_x(_1Bw,new T(function(){if(!E(_1BK)){if(!E(_1BD)){if(!E(_1BB)){return __Z;}else{return new T2(1,_1Bk,new T2(1,_1BF,_Z));}}else{return new T2(1,_1Bl,new T2(1,_1BF,_Z));}}else{return E(_1xT);}},1)))),j:E(_1Bx),k:E(_1BK)};};if(!E(_1BD)){return new F(function(){return _1BI(_1Bs);});}else{return new F(function(){return _1BI(32);});}},_1BL=function(_1BM,_1BN){while(1){var _1BO=E(_1BN);if(!_1BO._){return __Z;}else{var _1BP=_1BO.b,_1BQ=E(_1BM);if(_1BQ==1){return E(_1BP);}else{_1BM=_1BQ-1|0;_1BN=_1BP;continue;}}}},_1BR=4,_1BS=new T(function(){return B(unCStr("\u5e74 "));}),_1BT=function(_1BU,_1BV,_1BW,_1BX,_1BY){var _1BZ=new T(function(){var _1C0=new T(function(){var _1C1=new T(function(){var _1C2=new T(function(){var _1C3=new T(function(){return B(_x(_1BW,new T(function(){return B(unAppCStr(" >>",_1BX));},1)));});return B(unAppCStr(" >>",_1C3));},1);return B(_x(_1BV,_1C2));},1);return B(_x(_1BS,_1C1));},1);return B(_x(B(_H(0,_1BU,_Z)),_1C0));});return new T2(0,new T2(1,_1BY,_1ri),_1BZ);},_1C4=function(_1C5){var _1C6=E(_1C5),_1C7=E(_1C6.a),_1C8=B(_1BT(_1C7.a,_1C7.b,_1C7.c,_1C7.d,_1C6.b));return new T2(0,_1C8.a,_1C8.b);},_1C9=function(_1Ca){var _1Cb=E(_1Ca);return new T2(0,new T2(1,_1Cb.b,_1ri),E(_1Cb.a).b);},_1Cc=new T(function(){return B(_ic("Grid.hs:(31,1)-(38,56)|function checkGrid"));}),_1Cd=function(_1Ce,_1Cf){while(1){var _1Cg=E(_1Cf);if(!_1Cg._){return false;}else{var _1Ch=_1Cg.b,_1Ci=E(_1Ce),_1Cj=_1Ci.a,_1Ck=_1Ci.b,_1Cl=E(_1Cg.a);if(!_1Cl._){return E(_1Cc);}else{var _1Cm=E(_1Cl.a),_1Cn=_1Cm.a,_1Co=_1Cm.b,_1Cp=E(_1Cl.b);if(!_1Cp._){var _1Cq=E(_1Cj),_1Cr=E(_1Cq);if(_1Cr==32){switch(E(_1Ck)){case 0:if(!E(_1Co)){return true;}else{_1Ce=new T2(0,_1Cq,_II);_1Cf=_1Ch;continue;}break;case 1:if(E(_1Co)==1){return true;}else{_1Ce=new T2(0,_1Cq,_IO);_1Cf=_1Ch;continue;}break;case 2:if(E(_1Co)==2){return true;}else{_1Ce=new T2(0,_1Cq,_IU);_1Cf=_1Ch;continue;}break;case 3:if(E(_1Co)==3){return true;}else{_1Ce=new T2(0,_1Cq,_J0);_1Cf=_1Ch;continue;}break;case 4:if(E(_1Co)==4){return true;}else{_1Ce=new T2(0,_1Cq,_J6);_1Cf=_1Ch;continue;}break;case 5:if(E(_1Co)==5){return true;}else{_1Ce=new T2(0,_1Cq,_Jx);_1Cf=_1Ch;continue;}break;case 6:if(E(_1Co)==6){return true;}else{_1Ce=new T2(0,_1Cq,_Jq);_1Cf=_1Ch;continue;}break;case 7:if(E(_1Co)==7){return true;}else{_1Ce=new T2(0,_1Cq,_Jj);_1Cf=_1Ch;continue;}break;default:if(E(_1Co)==8){return true;}else{_1Ce=new T2(0,_1Cq,_Jc);_1Cf=_1Ch;continue;}}}else{if(_1Cr!=E(_1Cn)){_1Ce=_1Ci;_1Cf=_1Ch;continue;}else{switch(E(_1Ck)){case 0:if(!E(_1Co)){return true;}else{_1Ce=new T2(0,_1Cq,_II);_1Cf=_1Ch;continue;}break;case 1:if(E(_1Co)==1){return true;}else{_1Ce=new T2(0,_1Cq,_IO);_1Cf=_1Ch;continue;}break;case 2:if(E(_1Co)==2){return true;}else{_1Ce=new T2(0,_1Cq,_IU);_1Cf=_1Ch;continue;}break;case 3:if(E(_1Co)==3){return true;}else{_1Ce=new T2(0,_1Cq,_J0);_1Cf=_1Ch;continue;}break;case 4:if(E(_1Co)==4){return true;}else{_1Ce=new T2(0,_1Cq,_J6);_1Cf=_1Ch;continue;}break;case 5:if(E(_1Co)==5){return true;}else{_1Ce=new T2(0,_1Cq,_Jx);_1Cf=_1Ch;continue;}break;case 6:if(E(_1Co)==6){return true;}else{_1Ce=new T2(0,_1Cq,_Jq);_1Cf=_1Ch;continue;}break;case 7:if(E(_1Co)==7){return true;}else{_1Ce=new T2(0,_1Cq,_Jj);_1Cf=_1Ch;continue;}break;default:if(E(_1Co)==8){return true;}else{_1Ce=new T2(0,_1Cq,_Jc);_1Cf=_1Ch;continue;}}}}}else{var _1Cs=E(_1Cj),_1Ct=E(_1Cs);if(_1Ct==32){switch(E(_1Ck)){case 0:if(!E(_1Co)){return true;}else{_1Ce=new T2(0,_1Cs,_II);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 1:if(E(_1Co)==1){return true;}else{_1Ce=new T2(0,_1Cs,_IO);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 2:if(E(_1Co)==2){return true;}else{_1Ce=new T2(0,_1Cs,_IU);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 3:if(E(_1Co)==3){return true;}else{_1Ce=new T2(0,_1Cs,_J0);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 4:if(E(_1Co)==4){return true;}else{_1Ce=new T2(0,_1Cs,_J6);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 5:if(E(_1Co)==5){return true;}else{_1Ce=new T2(0,_1Cs,_Jx);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 6:if(E(_1Co)==6){return true;}else{_1Ce=new T2(0,_1Cs,_Jq);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 7:if(E(_1Co)==7){return true;}else{_1Ce=new T2(0,_1Cs,_Jj);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;default:if(E(_1Co)==8){return true;}else{_1Ce=new T2(0,_1Cs,_Jc);_1Cf=new T2(1,_1Cp,_1Ch);continue;}}}else{if(_1Ct!=E(_1Cn)){_1Ce=_1Ci;_1Cf=new T2(1,_1Cp,_1Ch);continue;}else{switch(E(_1Ck)){case 0:if(!E(_1Co)){return true;}else{_1Ce=new T2(0,_1Cs,_II);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 1:if(E(_1Co)==1){return true;}else{_1Ce=new T2(0,_1Cs,_IO);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 2:if(E(_1Co)==2){return true;}else{_1Ce=new T2(0,_1Cs,_IU);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 3:if(E(_1Co)==3){return true;}else{_1Ce=new T2(0,_1Cs,_J0);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 4:if(E(_1Co)==4){return true;}else{_1Ce=new T2(0,_1Cs,_J6);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 5:if(E(_1Co)==5){return true;}else{_1Ce=new T2(0,_1Cs,_Jx);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 6:if(E(_1Co)==6){return true;}else{_1Ce=new T2(0,_1Cs,_Jq);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;case 7:if(E(_1Co)==7){return true;}else{_1Ce=new T2(0,_1Cs,_Jj);_1Cf=new T2(1,_1Cp,_1Ch);continue;}break;default:if(E(_1Co)==8){return true;}else{_1Ce=new T2(0,_1Cs,_Jc);_1Cf=new T2(1,_1Cp,_1Ch);continue;}}}}}}}}},_1Cu=new T(function(){return B(unCStr("\n"));}),_1Cv=function(_1Cw,_1Cx,_){var _1Cy=jsWriteHandle(E(_1Cw),toJSStr(E(_1Cx)));return _kJ;},_1Cz=function(_1CA,_1CB,_){var _1CC=E(_1CA),_1CD=jsWriteHandle(_1CC,toJSStr(E(_1CB)));return new F(function(){return _1Cv(_1CC,_1Cu,_);});},_1CE=function(_1CF){var _1CG=E(_1CF);if(!_1CG._){return __Z;}else{return new F(function(){return _x(_1CG.a,new T(function(){return B(_1CE(_1CG.b));},1));});}},_1CH=new T(function(){return B(unCStr("removed"));}),_1CI=new T(function(){return B(unCStr("loadError"));}),_1CJ=new T(function(){return B(unCStr("saved"));}),_1CK=new T(function(){return B(err(_wY));}),_1CL=new T(function(){return B(err(_x2));}),_1CM=12,_1CN=3,_1CO=new T(function(){return B(unCStr("Coding : yokoP"));}),_1CP=8,_1CQ=32,_1CR=new T2(0,_1CQ,_Jx),_1CS=99,_1CT=64,_1CU=new T(function(){return B(_qy(_1mE,0));}),_1CV=new T(function(){return B(unCStr("loadError"));}),_1CW=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1CX=new T(function(){return B(unCStr(","));}),_1CY=new T(function(){return B(unCStr("~"));}),_1CZ=new T(function(){return B(unCStr("savedata"));}),_1D0=new T(function(){return B(unCStr("---"));}),_1D1=new T(function(){return B(unCStr("=="));}),_1D2=4,_1D3=6,_1D4=5,_1D5=new T1(0,333),_1D6=new T(function(){return B(_cx(1,2147483647));}),_1D7=function(_1D8){var _1D9=B(_KK(B(_x7(_1CW,_1D8))));return (_1D9._==0)?E(_1CK):(E(_1D9.b)._==0)?E(_1D9.a):E(_1CL);},_1Da=new T(function(){var _1Db=E(_1kX);if(!_1Db._){return E(_rm);}else{return E(_1Db.a);}}),_1Dc=new T(function(){return B(unAppCStr("[]",_Z));}),_1Dd=new T(function(){return B(unCStr("\""));}),_1De=new T2(1,_Z,_Z),_1Df=new T(function(){return B(_aj(_1D7,_1De));}),_1Dg=function(_1Dh,_1Di){return new T2(1,_aI,new T(function(){return B(_cp(_1Dh,new T2(1,_aI,_1Di)));}));},_1Dj=function(_1Dk,_1Dl){var _1Dm=E(_1Dk),_1Dn=new T(function(){var _1Do=function(_1Dp){var _1Dq=E(_1Dm.a),_1Dr=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Ds){return new F(function(){return _1Dg(_1Dq.a,_1Ds);});},new T2(1,function(_1Dt){return new F(function(){return _1ax(0,_1Dq.b,_1Dt);});},_Z)),new T2(1,_F,_1Dp)));});return new T2(1,_G,_1Dr);};return B(A3(_wK,_aC,new T2(1,_1Do,new T2(1,function(_1Du){return new F(function(){return _H(0,E(_1Dm.b),_1Du);});},_Z)),new T2(1,_F,_1Dl)));});return new T2(1,_G,_1Dn);},_1Dv=new T2(1,_aI,_Z),_1Dw=new T(function(){return B(_1fN(_1kl,5,_1lr));}),_1Dx=new T(function(){return B(unCStr("Thank you!"));}),_1Dy=17,_1Dz=2,_1DA=new T(function(){return B(unCStr("First Up : 2024 12 24"));}),_1DB=function(_1DC,_1DD){var _1DE=E(_1DD);return (_1DE._==0)?__Z:new T2(1,_1DC,new T2(1,_1DE.a,new T(function(){return B(_1DB(_1DC,_1DE.b));})));},_1DF=new T(function(){return B(unCStr("noContent"));}),_1DG=new T(function(){return B(unCStr("noHint"));}),_1DH=new T(function(){return B(err(_x2));}),_1DI=new T(function(){return B(err(_wY));}),_1DJ=new T(function(){return B(A3(_K8,_KB,_Id,_K0));}),_1DK=function(_1DL,_1DM){var _1DN=E(_1DM);if(!_1DN._){var _1DO=B(_KK(B(_x7(_1DJ,_1DL))));return (_1DO._==0)?E(_1DI):(E(_1DO.b)._==0)?new T4(0,E(_1DO.a),_Z,_Z,_Z):E(_1DH);}else{var _1DP=_1DN.a,_1DQ=E(_1DN.b);if(!_1DQ._){var _1DR=B(_KK(B(_x7(_1DJ,_1DL))));return (_1DR._==0)?E(_1DI):(E(_1DR.b)._==0)?new T4(0,E(_1DR.a),E(_1DP),E(_1DG),E(_1DF)):E(_1DH);}else{var _1DS=_1DQ.a,_1DT=E(_1DQ.b);if(!_1DT._){var _1DU=B(_KK(B(_x7(_1DJ,_1DL))));return (_1DU._==0)?E(_1DI):(E(_1DU.b)._==0)?new T4(0,E(_1DU.a),E(_1DP),E(_1DS),E(_1DF)):E(_1DH);}else{if(!E(_1DT.b)._){var _1DV=B(_KK(B(_x7(_1DJ,_1DL))));return (_1DV._==0)?E(_1DI):(E(_1DV.b)._==0)?new T4(0,E(_1DV.a),E(_1DP),E(_1DS),E(_1DT.a)):E(_1DH);}else{return new T4(0,0,_Z,_Z,_Z);}}}}},_1DW=function(_1DX){var _1DY=E(_1DX);if(!_1DY._){return new F(function(){return _1DK(_Z,_Z);});}else{var _1DZ=_1DY.a,_1E0=E(_1DY.b);if(!_1E0._){return new F(function(){return _1DK(new T2(1,_1DZ,_Z),_Z);});}else{var _1E1=E(_1DZ),_1E2=new T(function(){var _1E3=B(_LC(44,_1E0.a,_1E0.b));return new T2(0,_1E3.a,_1E3.b);});if(E(_1E1)==44){return new F(function(){return _1DK(_Z,new T2(1,new T(function(){return E(E(_1E2).a);}),new T(function(){return E(E(_1E2).b);})));});}else{var _1E4=E(_1E2);return new F(function(){return _1DK(new T2(1,_1E1,_1E4.a),_1E4.b);});}}}},_1E5=function(_1E6){var _1E7=B(_1DW(_1E6));return new T4(0,_1E7.a,E(_1E7.b),E(_1E7.c),E(_1E7.d));},_1E8=function(_1E9){return (E(_1E9)==10)?true:false;},_1Ea=function(_1Eb){var _1Ec=E(_1Eb);if(!_1Ec._){return __Z;}else{var _1Ed=new T(function(){var _1Ee=B(_1gg(_1E8,_1Ec));return new T2(0,_1Ee.a,new T(function(){var _1Ef=E(_1Ee.b);if(!_1Ef._){return __Z;}else{return B(_1Ea(_1Ef.b));}}));});return new T2(1,new T(function(){return E(E(_1Ed).a);}),new T(function(){return E(E(_1Ed).b);}));}},_1Eg=new T(function(){return B(unCStr("57,\u5974\uff1a\u306a\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304c\u5f8c\uff1a\u3053\u3046\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u304b\u3089\u91d1\uff1a\u304d\u3093\uff1a\u5370\uff1a\u3044\u3093\uff1a,<\u5f8c\uff1a\u3054\uff1a\u6f22\uff1a\u304b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308a \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u671f\uff1a\u304d\uff1a\u306b\u305d\u308c\u3089\u3057\u304d\u91d1\u5370\u304c\u767a\u898b\u3055\u308c\u308b,\u798f\uff1a\u3075\u304f\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a\u5fd7\uff1a\u3057\uff1a\u8cc0\uff1a\u304b\u306e\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u3066<\u6f22\uff1a\u304b\u3093\u306e\uff1a\u59d4\uff1a\u308f\u306e\uff1a\u5974\uff1a\u306a\u306e\uff1a\u570b\uff1a\u3053\u304f\uff1a\u738b\uff1a\u304a\u3046\uff1a>\u3068\u523b\uff1a\u304d\u3056\uff1a\u307e\u308c\u305f\u91d1\u5370\u304c\u6c5f\u6238\u6642\u4ee3\u306b\u767c\uff1a\u306f\u3063\uff1a\u898b\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b >>\u5927\uff1a\u3084\uff1a\u548c\uff1a\u307e\u3068\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u3068\u306e\u95dc\uff1a\u304b\u3093\uff1a\u4fc2\uff1a\u3051\u3044\uff1a\u4e0d\uff1a\u3075\uff1a\u660e\uff1a\u3081\u3044\uff1a\u306f\n239,<\u5351\uff1a\u3072\uff1a\u5f25\uff1a\u307f\uff1a\u547c\uff1a\u3053\uff1a>\u304c\u9b4f\uff1a\u304e\uff1a\u306b\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u306e\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u66f8\uff1a\u3057\u3087\uff1a<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u3055\u308c\u3066\u3090\u308b\u5deb\uff1a\u307f\uff1a\u5973\uff1a\u3053\uff1a,<\u9b4f\uff1a\u304e\uff1a\u5fd7\uff1a\u3057\uff1a>\u502d\uff1a\u308f\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u4f1d\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u3057\u308b\uff1a\u3055\u308c\u3066\u3090\u308b<\u90aa\u99ac\u58f9\u570b(\u3084\u307e\u3044\u3061\u3053\u304f)>\u3082<\u5351\u5f25\u547c>\u3082\u65e5\u672c\u306b\u6b98\uff1a\u306e\u3053\uff1a\u308b\u8cc7\uff1a\u3057\uff1a\u6599\uff1a\u308c\u3044\uff1a\u3067\u306f\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3067\u304d\u306a\u3044\n316,\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687 \u7a0e\uff1a\u305c\u3044\uff1a\u3092\u514d\uff1a\u3081\u3093\uff1a\u9664\uff1a\u3058\u3087\uff1a,<\u53e4\uff1a\u3053\uff1a\u4e8b\uff1a\u3058\uff1a\u8a18\uff1a\u304d\uff1a><\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u66f8\uff1a\u3057\u3087\uff1a\u7d00\uff1a\u304d\uff1a>\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b,16\u4ee3\u4ec1\uff1a\u306b\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c<\u6c11\uff1a\u305f\u307f\uff1a\u306e\u304b\u307e\u3069\u3088\u308a\u7159\uff1a\u3051\u3080\u308a\uff1a\u304c\u305f\u3061\u306e\u307c\u3089\u306a\u3044\u306e\u306f \u8ca7\uff1a\u307e\u3065\uff1a\u3057\u304f\u3066\u708a\uff1a\u305f\uff1a\u304f\u3082\u306e\u304c\u306a\u3044\u304b\u3089\u3067\u306f\u306a\u3044\u304b>\u3068\u3057\u3066 \u5bae\uff1a\u304d\u3085\u3046\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u306e\u4fee\uff1a\u3057\u3085\u3046\uff1a\u7e55\uff1a\u305c\u3093\uff1a\u3092\u5f8c\uff1a\u3042\u3068\uff1a\u307e\u306f\u3057\u306b\u3057 \u6c11\u306e\u751f\u6d3b\u3092\u8c4a\uff1a\u3086\u305f\uff1a\u304b\u306b\u3059\u308b\u8a71\u304c<\u65e5\u672c\u66f8\u7d00>\u306b\u3042\u308b\n478,<\u502d\uff1a\u308f\uff1a>\u306e\u6b66\uff1a\u3076\uff1a\u738b\uff1a\u304a\u3046\uff1a \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5b8b\uff1a\u305d\u3046\uff1a\u3078\u9063\uff1a\u3051\u3093\uff1a\u4f7f\uff1a\u3057\uff1a,\u96c4\uff1a\u3086\u3046\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u5929\u7687\u3092\u6307\u3059\u3068\u3044\u3075\u306e\u304c\u5b9a\uff1a\u3066\u3044\uff1a\u8aac\uff1a\u305b\u3064\uff1a,<\u5b8b\uff1a\u305d\u3046\uff1a\u66f8\uff1a\u3057\u3087\uff1a>\u502d\uff1a\u308f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u50b3\uff1a\u3067\u3093\uff1a\u306b\u8a18\uff1a\u304d\uff1a\u8f09\uff1a\u3055\u3044\uff1a\u304c\u3042\u308b >> \u96c4\u7565\u5929\u7687\u306f\u7b2c21\u4ee3\u5929\u7687\n538,\u4ecf\uff1a\u3076\u3063\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f1d\uff1a\u3067\u3093\uff1a,\u6b3d\uff1a\u304d\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u5fa1\uff1a\u307f\uff1a\u4ee3\uff1a\u3088\uff1a\u306b\u767e\uff1a\u304f\uff1a\u6e08\uff1a\u3060\u3089\uff1a\u306e\u8056\uff1a\u305b\u3044\uff1a\u660e\uff1a\u3081\u3044\uff1a\u738b\uff1a\u304a\u3046\uff1a\u304b\u3089\u50b3\uff1a\u3067\u3093\uff1a\u4f86\uff1a\u3089\u3044\uff1a\u3057\u305f\u3068\u306e\u6587\uff1a\u3076\u3093\uff1a\u732e\uff1a\u3051\u3093\uff1a\u3042\u308a,\u6b63\u78ba\u306a\u5e74\u4ee3\u306b\u3064\u3044\u3066\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\n604,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e03\uff1a\u3057\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u61b2\uff1a\u3051\u3093\uff1a\u6cd5\uff1a\u307d\u3046\uff1a\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u304c\u5236\uff1a\u305b\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u305f\u3068\u3055\u308c\u308b,<\u548c\uff1a\u308f\uff1a\u3092\u4ee5\uff1a\u3082\u3063\uff1a\u3066\u8cb4\uff1a\u305f\u3075\u3068\uff1a\u3057\u3068\u70ba\uff1a\u306a\uff1a\u3057 \u5fe4(\u3055\u304b)\u3075\u308b\u3053\u3068\u7121\uff1a\u306a\uff1a\u304d\u3092\u5b97\uff1a\u3080\u306d\uff1a\u3068\u305b\u3088>\n607,\u6cd5\uff1a\u307b\u3046\uff1a\u9686\uff1a\u308a\u3085\u3046\uff1a\u5bfa\uff1a\u3058\uff1a\u304c\u5275\uff1a\u305d\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u3055\u308c\u308b,\u8056\uff1a\u3057\u3087\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u592a\uff1a\u305f\u3044\uff1a\u5b50\uff1a\u3057\uff1a\u3086\u304b\u308a\u306e\u5bfa\uff1a\u3058\uff1a\u9662\uff1a\u3044\u3093\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u9662\uff1a\u3044\u3093\uff1a\u4f3d\uff1a\u304c\uff1a\u85cd\uff1a\u3089\u3093\uff1a\u306f\u73fe\uff1a\u3052\u3093\uff1a\u5b58\uff1a\u305e\u3093\uff1a\u3059\u308b\u4e16\u754c\u6700\uff1a\u3055\u3044\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u6728\uff1a\u3082\u304f\uff1a\u9020\uff1a\u305e\u3046\uff1a\u5efa\uff1a\u3051\u3093\uff1a\u7bc9\uff1a\u3061\u304f\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3068\u3055\u308c\u3066\u3090\u308b\n645,\u4e59\uff1a\u3044\u3063\uff1a\u5df3\uff1a\u3057\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u3053\u306e\u5f8c\u3059\u3050\u5927\uff1a\u305f\u3044\uff1a\u5316\uff1a\u304b\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306a\u308b,\u4e2d\uff1a\u306a\u304b\u306e\uff1a\u5927\uff1a\u304a\u304a\uff1a\u5144\uff1a\u3048\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a(\u5f8c\u306e38\u4ee3\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687)\u304c\u8607\uff1a\u305d\uff1a\u6211\uff1a\u304c\uff1a\u6c0f\uff1a\u3057\uff1a\u3092\u4ea1\uff1a\u307b\u308d\uff1a\u307c\u3059\n663,\u767d\uff1a\u306f\u304f\uff1a\u6751\uff1a\u3059\u304d\u306e\uff1a\u6c5f\uff1a\u3048\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u3068\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u306b\u6ec5\uff1a\u307b\u308d\uff1a\u307c\u3055\u308c\u305f\u767e\uff1a\u304f\u3060\uff1a\u6e08\uff1a\u3089\uff1a\u3092\u518d\uff1a\u3055\u3044\uff1a\u8208\uff1a\u3053\u3046\uff1a\u3059\u308b\u76ee\uff1a\u3082\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a,\u5510\uff1a\u3068\u3046\uff1a\u30fb\u65b0\uff1a\u3057\u3089\uff1a\u7f85\uff1a\u304e\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u3054\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u308b\n672,\u58ec\uff1a\u3058\u3093\uff1a\u7533\uff1a\u3057\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u667a\uff1a\u3062\uff1a\u5929\u7687\u304a\u304b\u304f\u308c\u5f8c\u306e\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u4e89\uff1a\u3042\u3089\u305d\uff1a\u3072,\u5f8c\uff1a\u3053\u3046\uff1a\u7d99\uff1a\u3051\u3044\uff1a\u8005\uff1a\u3057\u3083\uff1a\u3067\u3042\u3063\u305f\u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u306b\u53d4\uff1a\u304a\uff1a\u7236\uff1a\u3058\uff1a\u306e\u5927\uff1a\u304a\u304a\uff1a\u6d77\uff1a\u3042\uff1a\u4eba\uff1a\u307e\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u304c\u53cd\uff1a\u306f\u3093\uff1a\u65d7\uff1a\u304d\uff1a\u3092\u7ffb\uff1a\u3072\u308b\u304c\u3078\uff1a\u3057 \u5927\uff1a\u304a\u304a\uff1a\u53cb\uff1a\u3068\u3082\u306e\uff1a\u7687\uff1a\u304a\u3046\uff1a\u5b50\uff1a\u3058\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u3066\u5929\uff1a\u3066\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u3068\u306a\u308b\n710,\u5e73\uff1a\u3078\u3044\uff1a\u57ce\uff1a\u3058\u3087\u3046\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5e73\u57ce\u3068\u3044\u3075\u6f22\u5b57\u306f<\u306a\u3089>\u3068\u3082\u8b80\uff1a\u3088\uff1a\u3080,\u548c\uff1a\u308f\uff1a\u9285\uff1a\u3069\u3046\uff1a3\u5e74 \u7b2c43\u4ee3\u5143\uff1a\u3052\u3093\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306b\u3088\u308b \u5148\uff1a\u305b\u3093\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u6587\uff1a\u3082\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687\u304c\u75ab\uff1a\u3048\u304d\uff1a\u75c5\uff1a\u3073\u3087\u3046\uff1a\u3067\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u305f\u3053\u3068\u304c \u9077\u90fd\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3067\u3082\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n794,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\uff1a\u305b\u3093\uff1a\u90fd\uff1a\u3068\uff1a,\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a13\u5e74 \u7b2c50\u4ee3\u6853\uff1a\u304b\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u5929\u7687 \u9577\uff1a\u306a\u304c\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u304b\u3089\u9077\u90fd\u3055\u308c\u308b,\u3053\u306e\u5f8c\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u306b\u3088\u308b\u798f\uff1a\u3075\u304f\uff1a\u539f\uff1a\u306f\u3089\uff1a\u4eac\uff1a\u304d\u3087\u3046\uff1a\u9077\u90fd\u3084\u5357\uff1a\u306a\u3093\uff1a\u5317\uff1a\u307c\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u6642\u4ee3\u306e\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306a\u3069\u306e\u4f8b\uff1a\u308c\u3044\uff1a\u5916\uff1a\u304c\u3044\uff1a\u306f\u3042\u308b\u3082\u306e\u306e \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u7dad\uff1a\u3044\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u307e\u3067\u5343\u5e74\u4ee5\u4e0a\u7e8c\uff1a\u3064\u3065\uff1a\u304f\n806,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u304c\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u304c\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a,\u5e73\uff1a\u3078\u3044\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u521d\uff1a\u3057\u3087\uff1a\u671f\uff1a\u304d\uff1a \u3069\u3061\u3089\u3082\u5510\uff1a\u3068\u3046\uff1a\u3067\u4fee\uff1a\u3057\u3085\uff1a\u884c\uff1a\u304e\u3087\u3046\uff1a\u3057\u5e30\uff1a\u304d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u5f8c\uff1a\u3054\uff1a \u4ecf\uff1a\u3076\u3064\uff1a\u6559\uff1a\u304d\u3087\u3046\uff1a\u3092\u50b3\uff1a\u3064\u305f\uff1a\u3078\u308b,\u6700\uff1a\u3055\u3044\uff1a\u6f84\uff1a\u3061\u3087\u3046\uff1a\u306f\u5929\uff1a\u3066\u3093\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u6bd4\uff1a\u3072\uff1a\u53e1\uff1a\u3048\u3044\uff1a\u5c71\uff1a\u3056\u3093\uff1a\u306b\u5ef6\uff1a\u3048\u3093\uff1a\u66a6\uff1a\u308a\u3083\u304f\uff1a\u5bfa\uff1a\u3058\uff1a\u3092 \u7a7a\uff1a\u304f\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u306f\u771f\uff1a\u3057\u3093\uff1a\u8a00\uff1a\u3054\u3093\uff1a\u5b97\uff1a\u3057\u3085\u3046\uff1a\u3092\u958b\u304d \u9ad8\uff1a\u3053\u3046\uff1a\u91ce\uff1a\u3084\uff1a\u5c71\uff1a\u3055\u3093\uff1a\u306b\u91d1\uff1a\u3053\u3093\uff1a\u525b\uff1a\u3054\u3046\uff1a\u5cf0\uff1a\u3076\uff1a\u5bfa\uff1a\u3058\uff1a\u3092\u5efa\uff1a\u3053\u3093\uff1a\u7acb\uff1a\u308a\u3085\u3046\uff1a\n857,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u826f\uff1a\u3088\u3057\uff1a\u623f\uff1a\u3075\u3055\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,56\u4ee3\u6e05\uff1a\u305b\u3044\uff1a\u548c\uff1a\u308f\uff1a\u5929\u7687\u306e\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a,\u81e3\uff1a\u3057\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u306e\u8eab\uff1a\u307f\uff1a\u5206\uff1a\u3076\u3093\uff1a\u3067\u521d\u3081\u3066\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b\u306a\u3063\u305f\n894,\u9063\uff1a\u3051\u3093\uff1a\u5510\uff1a\u3068\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u304c\u5ec3\uff1a\u306f\u3044\uff1a\u6b62\uff1a\u3057\uff1a\u3055\u308c\u308b,\u83c5\uff1a\u3059\u304c\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u771f\uff1a\u3056\u306d\uff1a\u306e\u5efa\uff1a\u3051\u3093\uff1a\u8b70\uff1a\u304e\uff1a\u306b\u3088\u308b,\u3053\u306e\u5f8c904\u5e74\u306b\u5510\uff1a\u3068\u3046\uff1a\u306f\u6ec5\uff1a\u307b\u308d\uff1a\u3073\u5c0f\uff1a\u3057\u3087\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5206\uff1a\u3076\u3093\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3057\u305f\u5f8c \u5b8b\uff1a\u305d\u3046\uff1a(\u5317\uff1a\u307b\u304f\uff1a\u5b8b\uff1a\u305d\u3046\uff1a)\u304c\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5927\uff1a\u305f\u3044\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3092\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3059\u308b\n935,\u627f\uff1a\u3057\u3087\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5929\uff1a\u3066\u3093\uff1a\u6176\uff1a\u304e\u3087\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u5c06\uff1a\u306e\u307e\u3055\uff1a\u9580\uff1a\u304b\u3069\uff1a\u3084\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u7d14\uff1a\u3059\u307f\uff1a\u53cb\uff1a\u3068\u3082\uff1a\u3068\u3044\u3064\u305f\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u95a2\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u3078\u306e\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u5e95\uff1a\u3066\u3044\uff1a\u306b\u3042\u3063\u305f\u3068\u3055\u308c\u308b\n1016,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\u306e\uff1a\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u306b,\u85e4\uff1a\u3075\u3058\uff1a\u539f\uff1a\u308f\u3089\uff1a\u6c0f\uff1a\u3057\uff1a\u5168\uff1a\u305c\u3093\uff1a\u76db\uff1a\u305b\u3044\uff1a\u6642\u4ee3\u3068\u3044\u306f\u308c\u308b,\u9053\uff1a\u307f\u3061\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u9577\uff1a\u3061\u3087\u3046\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(66\u4ee3)\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b \u6b21\uff1a\u3058\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u4e09\uff1a\u3055\u3093\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(67\u4ee3)\u306e\u540e\u306b \u4e09\uff1a\u3055\u3093\uff1a\u5973\uff1a\u3058\u3087\uff1a\u3092\u5f8c\uff1a\u3054\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u5929\u7687(68\u4ee3)\u306e\u540e\u306b\u3059\u308b\n1086,\u9662\uff1a\u3044\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u958b\uff1a\u304b\u3044\uff1a\u59cb\uff1a\u3057\uff1a,\u6442\uff1a\u305b\u3063\uff1a\u653f\uff1a\u3057\u3087\u3046\uff1a\u3084\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3092\u6291\uff1a\u304a\u3055\uff1a\u3078\u308b,72\u4ee3\u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u5929\u7687\u304c\u8b72\uff1a\u3058\u3087\u3046\uff1a\u4f4d\uff1a\u3044\uff1a\u5f8c \u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u3068\u306a\u308a \u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u306e\u5b9f\uff1a\u3058\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u63e1\uff1a\u306b\u304e\uff1a\u308b\n1167,\u5e73\uff1a\u305f\u3044\u3089\uff1a\u6e05\uff1a\u306e\u304d\u3088\uff1a\u76db\uff1a\u3082\u308a\uff1a\u304c\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b,\u5a18\uff1a\u3080\u3059\u3081\uff1a\u3092\u5929\u7687\u306e\u540e\uff1a\u304d\u3055\u304d\uff1a\u306b\u3057 81\u4ee3\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u304c\u8a95\uff1a\u305f\u3093\uff1a\u751f\uff1a\u3058\u3087\u3046\uff1a,\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u3068\u3057\u3066\u521d\uff1a\u306f\u3058\uff1a\u3081\u3066\u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3087\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c\u308b\n1185,\u5e73\uff1a\u3078\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u307c\u3046\uff1a,\u58c7\uff1a\u3060\u3093\uff1a\u30ce\uff1a\u306e\uff1a\u6d66\uff1a\u3046\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u306e\u547d\uff1a\u3081\u3044\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u305f \u5f1f\uff1a\u304a\u3068\u3046\u3068\uff1a\u306e\u7fa9\uff1a\u3088\u3057\uff1a\u7d4c\uff1a\u3064\u306d\uff1a\u3089\u306e\u6d3b\uff1a\u304b\u3064\uff1a\u8e8d\uff1a\u3084\u304f\uff1a\u304c\u3042\u3063\u305f \u3053\u306e\u3068\u304d\u5b89\uff1a\u3042\u3093\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5929\u7687\u306f\u6578\uff1a\u304b\u305e\uff1a\u3078\u5e74\u4e03\u6b73\uff1a\u3055\u3044\uff1a\u3067\u5165\uff1a\u306b\u3085\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u3057\u5d29\uff1a\u307b\u3046\uff1a\u5fa1\uff1a\u304e\u3087\uff1a\u3055\u308c\u308b\n1192,\u6e90\uff1a\u307f\u306a\u3082\uff1a\u983c\uff1a\u3068\u306e\u3088\uff1a\u671d\uff1a\u308a\u3068\u3082\uff1a\u304c\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b,\u6b66\uff1a\u3076\uff1a\u5bb6\uff1a\u3051\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u672c\uff1a\u307b\u3093\uff1a\u683c\uff1a\u304b\u304f\uff1a\u7684\uff1a\u3066\u304d\uff1a\u306b\u59cb\uff1a\u306f\u3058\uff1a\u307e\u308b\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a\n1221,\u627f\uff1a\u3058\u3087\u3046\uff1a\u4e45\uff1a\u304d\u3085\u3046\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,\u5168\uff1a\u305c\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u6b66\uff1a\u3076\uff1a\u58eb\uff1a\u3057\uff1a\u306b \u57f7\uff1a\u3057\u3063\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3058\u3087\u3046\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6642\uff1a\u3068\u304d\uff1a\u306e\u8a0e\uff1a\u3068\u3046\uff1a\u4f10\uff1a\u3070\u3064\uff1a\u3092\u547d\uff1a\u3081\u3044\uff1a\u305a\u308b\u5f8c\uff1a\u3054\uff1a\u9ce5\uff1a\u3068\uff1a\u7fbd\uff1a\u3070\uff1a\u4e0a\uff1a\u3058\u3087\u3046\uff1a\u7687\uff1a\u3053\u3046\uff1a\u306e\u9662\uff1a\u3044\u3093\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u304c\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c\u308b,\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306f\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3055\u308c\u5931\uff1a\u3057\u3063\uff1a\u6557\uff1a\u3071\u3044\uff1a \n1274,\u6587\uff1a\u3076\u3093\uff1a\u6c38\uff1a\u3048\u3044\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,1281\u5e74\u306e\u5f18\uff1a\u3053\u3046\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3068\u5408\uff1a\u3042\uff1a\u306f\u305b\u3066 \u5143\uff1a\u3052\u3093\uff1a\u5bc7\uff1a\u3053\u3046\uff1a\u3068\u547c\uff1a\u3088\uff1a\u3076,\u7d04\u4e09\u4e07\u306e\u5143\uff1a\u3052\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u304c\u7d04\uff1a\u3084\u304f\uff1a900\u96bb\uff1a\u305b\u304d\uff1a\u306e\u8ecd\uff1a\u3050\u3093\uff1a\u8239\uff1a\u305b\u3093\uff1a\u3067\u5317\uff1a\u304d\u305f\uff1a\u4e5d\uff1a\u304d\u3085\u3046\uff1a\u5dde\uff1a\u3057\u3085\u3046\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u653b\uff1a\u3053\u3046\uff1a\u3059\u308b\u3082\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u6483\uff1a\u3052\u304d\uff1a\u9000\uff1a\u305f\u3044\uff1a\u3055\u308c\u308b\n1334,\u5efa\uff1a\u3051\u3093\uff1a\u6b66\uff1a\u3080\uff1a\u306e\u65b0\uff1a\u3057\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a,\u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u304c\u938c\uff1a\u304b\u307e\uff1a\u5009\uff1a\u304f\u3089\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u5012\uff1a\u305f\u304a\uff1a\u3057\u5929\u7687\u4e2d\u5fc3\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u3092\u5fd7\uff1a\u3053\u3053\u308d\u3056\uff1a\u3059,\u4e8c\u5e74\u3042\u307e\u308a\u3067\u6b66\u58eb\u304c\u96e2\uff1a\u308a\uff1a\u53cd\uff1a\u306f\u3093\uff1a\u3057 \u5f8c\uff1a\u3054\uff1a\u918d\uff1a\u3060\u3044\uff1a\u9190\uff1a\u3054\uff1a\u5929\u7687\u306f\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u306b\u9003\uff1a\u306e\u304c\uff1a\u308c \u5357\uff1a\u306a\u3093\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304d \u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u306f\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3092\u64c1\uff1a\u3088\u3046\uff1a\u3057\u305f\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u3092\u958b\u304f\n1338,\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u5c0a\uff1a\u305f\u304b\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u304c\u5317\uff1a\u307b\u304f\uff1a\u671d\uff1a\u3061\u3087\u3046\uff1a\u306e\u5149\uff1a\u3053\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u3058\u3089\u308c\u308b\u3053\u3068\u306b\u3088\u308a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u6e80\uff1a\u307f\u3064\uff1a(3\u4ee3)\u304c\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u306b<\u82b1\uff1a\u306f\u306a\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u6240\uff1a\u3057\u3087\uff1a>\u3092\u69cb\uff1a\u304b\u307e\uff1a\u3078\u653f\u6cbb\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3063\u305f\u3053\u3068\u304b\u3089<\u5ba4\u753a\u5e55\u5e9c>\u3068\u79f0\uff1a\u3057\u3087\u3046\uff1a\u3055\u308c\u308b\n1429,\u7409\uff1a\u308a\u3085\u3046\uff1a\u7403\uff1a\u304d\u3085\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,\u4e09\u3064\u306e\u52e2\uff1a\u305b\u3044\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u304c\u5341\u4e94\u4e16\uff1a\u305b\u3044\uff1a\u7d00\uff1a\u304d\uff1a\u306b\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3055\u308c\u308b,\u660e\uff1a\u307f\u3093\uff1a\u306e\u518a\uff1a\u3055\u304f\uff1a\u5c01\uff1a\u307b\u3046\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3061\u3087\u3046\uff1a\u8ca2\uff1a\u3053\u3046\uff1a\u8cbf\uff1a\u307c\u3046\uff1a\u6613\uff1a\u3048\u304d\uff1a\u3092\u884c\uff1a\u304a\u3053\u306a\uff1a\u3075\n1467,\u61c9\uff1a\u304a\u3046\uff1a\u4ec1\uff1a\u306b\u3093\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u5e55\uff1a\u307e\u304f\uff1a\u958b\uff1a\u3042\uff1a\u3051,\u5c06\uff1a\u3057\u3087\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u5bb6\uff1a\u3051\uff1a\u3068\u7ba1\uff1a\u304b\u3093\uff1a\u9818\uff1a\u308c\u3044\uff1a\u5bb6\uff1a\u3051\uff1a\u306e\u8de1\uff1a\u3042\u3068\uff1a\u7d99\uff1a\u3064\u304e\uff1a\u304e\u722d\uff1a\u3042\u3089\u305d\uff1a\u3072\u304c11\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u304d\u4eac\uff1a\u304d\u3087\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u306e\u753a\uff1a\u307e\u3061\uff1a\u306f\u7126\uff1a\u3057\u3087\u3046\uff1a\u571f\uff1a\u3069\uff1a\u3068\u5316\uff1a\u304b\uff1a\u3059\n1495,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u304c\u5c0f\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u539f\uff1a\u306f\u3089\uff1a\u5165\uff1a\u306b\u3075\uff1a\u57ce\uff1a\u3058\u3083\u3046\uff1a,\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u65e9\uff1a\u3055\u3046\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u306f\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u306e\u5148\uff1a\u3055\u304d\uff1a\u99c6\uff1a\u304c\uff1a\u3051\u3068\u8a00\u306f\u308c\u308b,\u65e9\u96f2\u304c\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3059\u308b\u5927\u540d\u306b\u306a\u3063\u305f\u904e\uff1a\u304b\uff1a\u7a0b\uff1a\u3066\u3044\uff1a\u306f \u5bb6\uff1a\u304b\uff1a\u81e3\uff1a\u3057\u3093\uff1a\u304c\u4e3b\uff1a\u3057\u3085\uff1a\u541b\uff1a\u304f\u3093\uff1a\u304b\u3089\u6a29\uff1a\u3051\u3093\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3063\u3066\u306e\u3057\u4e0a\uff1a\u3042\u304c\uff1a\u308b\u3068\u3044\u3075<\u4e0b\uff1a\u3052\uff1a\u524b\uff1a\u3053\u304f\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a>\u3067\u3042\u308a \u65e9\u96f2\u306f\u6230\u570b\u5927\u540d\u306e\u5686\uff1a\u304b\u3046\uff1a\u77e2\uff1a\u3057\uff1a\u3068\u3044\u3078\u308b\n1542,\u658e\uff1a\u3055\u3044\uff1a\u85e4\uff1a\u3068\u3046\uff1a\u9053\uff1a\u3069\u3046\uff1a\u4e09\uff1a\u3056\u3093\uff1a\u304c\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u596a\uff1a\u3046\u3070\uff1a\u3046,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6b66\uff1a\u3076\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u306e\u4e00\uff1a\u3044\u3061\uff1a,\u4ed6\uff1a\u307b\u304b\uff1a\u306b\u3082\u95a2\uff1a\u304f\u308f\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u5186\uff1a\u3048\u3093\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u3057\u305f\u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u5eb7\uff1a\u3084\u3059\uff1a \u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a \u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3048\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a \u51fa\uff1a\u3067\uff1a\u7fbd\uff1a\u306f\uff1a\u3068\u9678\uff1a\u3080\uff1a\u5965\uff1a\u3064\uff1a\u306e\u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u6b63\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a \u5b89\uff1a\u3042\uff1a\u82b8\uff1a\u304d\uff1a\u306e\u6bdb\uff1a\u3082\u3046\uff1a\u5229\uff1a\u308a\uff1a\u5143\uff1a\u3082\u3068\uff1a\u5c31\uff1a\u306a\u308a\uff1a \u571f\uff1a\u3068\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u9577\uff1a\u3061\u3083\u3046\uff1a\u5b97\uff1a\u305d\uff1a\u6211\uff1a\u304b\uff1a\u90e8\uff1a\u3079\uff1a\u5143\uff1a\u3082\u3068\uff1a\u89aa\uff1a\u3061\u304b\uff1a \u85a9\uff1a\u3055\u3064\uff1a\u6469\uff1a\u307e\uff1a\u306e\u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u8cb4\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a\u306a\u3069\u304c\u3090\u305f\n1553,\u5ddd\uff1a\u304b\u306f\uff1a\u4e2d\uff1a\u306a\u304b\uff1a\u5cf6\uff1a\u3058\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u7532\uff1a\u304b\uff1a\u6590\uff1a\u3072\uff1a\u306e\u6b66\uff1a\u305f\u3051\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u3057\u3093\uff1a\u7384\uff1a\u3052\u3093\uff1a\u3068\u8d8a\uff1a\u3048\u3061\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u4e0a\uff1a\u3046\u3078\uff1a\u6749\uff1a\u3059\u304e\uff1a\u8b19\uff1a\u3051\u3093\uff1a\u4fe1\uff1a\u3057\u3093\uff1a,\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u306e\u975e\uff1a\u3072\uff1a\u5e38\uff1a\u3058\u3083\u3046\uff1a\u306b\u6709\uff1a\u3044\u3046\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306a\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3067\u52dd\uff1a\u3057\u3087\u3046\uff1a\u6557\uff1a\u306f\u3044\uff1a\u306f\u8af8\uff1a\u3057\u3087\uff1a\u8aac\uff1a\u305b\u3064\uff1a\u3042\u308b\u3082\u5b9a\uff1a\u3055\u3060\uff1a\u307e\u3063\u3066\u3090\u306a\u3044\n1560,\u6876\uff1a\u304a\u3051\uff1a\u72ed\uff1a\u306f\u3056\uff1a\u9593\uff1a\u307e\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u306e\u7e54\uff1a\u304a\uff1a\u7530\uff1a\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u304c\u99ff\uff1a\u3059\u308b\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u4eca\uff1a\u3044\u307e\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u5143\uff1a\u3082\u3068\uff1a\u3092\u7834\uff1a\u3084\u3076\uff1a\u308b,\u4fe1\uff1a\u306e\u3076\uff1a\u9577\uff1a\u306a\u304c\uff1a\u306f\u5c3e\uff1a\u3092\uff1a\u5f35\uff1a\u306f\u308a\uff1a\u3068\u7f8e\uff1a\u307f\uff1a\u6fc3\uff1a\u306e\uff1a\u3092\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u4e0b\uff1a\u304b\uff1a\u306b\u304a\u304d <\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5e03\uff1a\u3075\uff1a\u6b66\uff1a\u3076\uff1a>\u3092\u304b\u304b\u3052 \u5f8c\uff1a\u306e\u3061\uff1a\u306b\u8db3\uff1a\u3042\u3057\uff1a\u5229\uff1a\u304b\u304c\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u662d\uff1a\u3042\u304d\uff1a\u3092\u4eac\uff1a\u304d\u3083\u3046\uff1a\u90fd\uff1a\u3068\uff1a\u304b\u3089\u8ffd\uff1a\u3064\u3044\uff1a\u653e\uff1a\u306f\u3046\uff1a\u3057\u3066\u5ba4\uff1a\u3080\u308d\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6ec5\uff1a\u3081\u3064\uff1a\u4ea1\uff1a\u3070\u3046\uff1a\u3055\u305b\u308b\n1590,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a,106\u4ee3\u6b63\uff1a\u304a\u307b\uff1a\u89aa\uff1a\u304e\uff1a\u753a\uff1a\u307e\u3061\uff1a\u5929\u7687\u304b\u3089\u95a2\uff1a\u304b\u3093\uff1a\u767d\uff1a\u3071\u304f\uff1a\u306e\u4f4d\uff1a\u304f\u3089\u3090\uff1a\u3092\u6388\uff1a\u3055\u3065\uff1a\u3051\u3089\u308c \u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u4e00\uff1a\u3044\u3064\uff1a\u3078\u306e\u5f8c\uff1a\u3042\u3068\uff1a\u62bc\uff1a\u304a\uff1a\u3057\u3092\u3082\u3089\u3075,\u60e3\uff1a\u3055\u3046\uff1a\u7121\uff1a\u3076\uff1a\u4e8b\uff1a\u3058\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u3092\u51fa\uff1a\u3060\uff1a\u3057\u3066\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3084\u3046\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u79c1\uff1a\u3057\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u3058 \u5929\uff1a\u3066\u3093\uff1a\u7687\uff1a\u308f\u3046\uff1a\u3088\u308a\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u306e\u59d3\uff1a\u305b\u3044\uff1a\u3092\u8cdc\uff1a\u305f\u307e\u306f\uff1a\u308a \u592a\uff1a\u3060\uff1a\u653f\uff1a\u3058\u3083\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u81e3\uff1a\u3058\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u5cf6\uff1a\u3057\u307e\uff1a\u6d25\uff1a\u3065\uff1a\u7fa9\uff1a\u3088\u3057\uff1a\u4e45\uff1a\u3072\u3055\uff1a \u5317\uff1a\u307b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6c0f\uff1a\u3046\u3058\uff1a\u653f\uff1a\u307e\u3055\uff1a \u4f0a\uff1a\u3060\uff1a\u9054\uff1a\u3066\uff1a\u653f\uff1a\u307e\u3055\uff1a\u5b97\uff1a\u3080\u306d\uff1a\u3089\u8af8\uff1a\u3057\u3087\uff1a\u5927\uff1a\u3060\u3044\uff1a\u540d\uff1a\u307f\u3083\u3046\uff1a\u3092\u5e73\uff1a\u3078\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u3057\u3066 \u5929\u4e0b\u7d71\u4e00\n1592,\u6587\uff1a\u3076\u3093\uff1a\u7984\uff1a\u308d\u304f\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a,\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u306e\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3063\uff1a\u5175\uff1a\u307a\u3044\uff1a,\u4e8c\uff1a\u306b\uff1a\u5ea6\uff1a\u3069\uff1a\u76ee\uff1a\u3081\uff1a\u306e\u6176\uff1a\u3051\u3044\uff1a\u9577\uff1a\u3061\u3083\u3046\uff1a\u306e\u5f79\uff1a\u3048\u304d\uff1a\u3067\u79c0\uff1a\u3072\u3067\uff1a\u5409\uff1a\u3088\u3057\uff1a\u304c\u6ca1\uff1a\u307c\u3063\uff1a\u3057 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u304b\u3089\u64a4\uff1a\u3066\u3063\uff1a\u9000\uff1a\u305f\u3044\uff1a\n1600,\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\u3072\uff1a,\u3053\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u5f8c\uff1a\u3054\uff1a\u967d\uff1a\u3084\u3046\uff1a\u6210\uff1a\u305c\u3044\uff1a\u5929\u7687\u306b\u3088\u308a\u5f81\uff1a\u305b\u3044\uff1a\u5937\uff1a\u3044\uff1a\u5927\uff1a\u305f\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u4efb\uff1a\u306b\u3093\uff1a\u547d\uff1a\u3081\u3044\uff1a\u3055\u308c \u6c5f\uff1a\u3048\uff1a\u6238\uff1a\u3069\uff1a\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\u304c\uff1a\u6210\uff1a\u305b\u3044\uff1a\u7acb\uff1a\u308a\u3064\uff1a,\u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u653f\uff1a\u305b\u3044\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306b\u304a\u3051\u308b\u4e94\uff1a\u3054\uff1a\u5927\uff1a\u305f\u3044\uff1a\u8001\uff1a\u3089\u3046\uff1a\u306e\u7b46\uff1a\u3072\u3063\uff1a\u982d\uff1a\u3068\u3046\uff1a\u3067\u3042\u3063\u305f\u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u5eb7\uff1a\u3084\u3059\uff1a\u304c \u8c4a\uff1a\u3068\u3088\uff1a\u81e3\uff1a\u3068\u307f\uff1a\u6c0f\uff1a\u3057\uff1a\u306e\u652f\uff1a\u3057\uff1a\u914d\uff1a\u306f\u3044\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u7dad\uff1a\u3090\uff1a\u6301\uff1a\u3062\uff1a\u3057\u3084\u3046\u3068\u3059\u308b\u77f3\uff1a\u3044\u3057\uff1a\u7530\uff1a\u3060\uff1a\u4e09\uff1a\u307f\u3064\uff1a\u6210\uff1a\u306a\u308a\uff1a\u3068\u95a2\uff1a\u305b\u304d\uff1a\u30f6\uff1a\u304c\uff1a\u539f\uff1a\u306f\u3089\uff1a\u3067\u5c0d\uff1a\u305f\u3044\uff1a\u6c7a\uff1a\u3051\u3064\uff1a\u30fc\u5929\uff1a\u3066\u3093\uff1a\u4e0b\uff1a\u304b\uff1a\u5206\uff1a\u308f\uff1a\u3051\u76ee\uff1a\u3081\uff1a\u306e\u6230\uff1a\u305f\u305f\u304b\uff1a\u3072\u3068\u3044\u306f\u308c \u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3067\u3042\u308b\u5fb3\u5ddd\u5bb6\u5eb7\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u305f\n1637,\u5cf6\uff1a\u3057\u307e\uff1a\u539f\uff1a\u3070\u3089\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u3044\u306f\u3086\u308b<\u9396\uff1a\u3055\uff1a\u570b\uff1a\u3053\u304f\uff1a>\u653f\uff1a\u305b\u3044\uff1a\u7b56\uff1a\u3055\u304f\uff1a\u306e\u5f15\uff1a\u3072\uff1a\u304d\u91d1\uff1a\u304c\u306d\uff1a\u3068\u3082\u306a\u3064\u305f,\u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u3089\u304c\u5bfa\uff1a\u3058\uff1a\u793e\uff1a\u3057\u3083\uff1a\u306b\u653e\uff1a\u306f\u3046\uff1a\u706b\uff1a\u304f\u308f\uff1a\u3057\u50e7\uff1a\u305d\u3046\uff1a\u4fb6\uff1a\u308a\u3087\uff1a\u3092\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a\u3059\u308b\u306a\u3069\u3057\u305f\u305f\u3081 \u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306f\u5927\uff1a\u305f\u3044\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u9001\uff1a\u304a\u304f\uff1a\u308a\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3059\u308b\n1685,\u751f\uff1a\u3057\u3083\u3046\uff1a\u985e\uff1a\u308b\uff1a\u6190\uff1a\u3042\u306f\u308c\uff1a\u307f\u306e\u4ee4\uff1a\u308c\u3044\uff1a,\u4e94\uff1a\u3054\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u7db1\uff1a\u3064\u306a\uff1a\u5409\uff1a\u3088\u3057\uff1a,\u75c5\uff1a\u3073\u3083\u3046\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u907a\uff1a\u3090\uff1a\u68c4\uff1a\u304d\uff1a\u3084\u6368\uff1a\u3059\uff1a\u3066\u5b50\uff1a\u3054\uff1a\u3092\u7981\uff1a\u304d\u3093\uff1a\u6b62\uff1a\u3057\uff1a \u4eba\uff1a\u306b\u3093\uff1a\u9593\uff1a\u3052\u3093\uff1a\u4ee5\uff1a\u3044\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u3042\u3089\u3086\u308b\u751f\uff1a\u305b\u3044\uff1a\u7269\uff1a\u3076\u3064\uff1a\u3078\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3084\u6bba\uff1a\u305b\u3063\uff1a\u751f\uff1a\u3057\u3083\u3046\uff1a\u3092\u3082\u7f70\uff1a\u3070\u3064\uff1a\u3059\u308b\u3053\u3068\u3067 \u9053\uff1a\u3060\u3046\uff1a\u5fb3\uff1a\u3068\u304f\uff1a\u5fc3\uff1a\u3057\u3093\uff1a\u3092\u559a\uff1a\u304b\u3093\uff1a\u8d77\uff1a\u304d\uff1a\u3057\u3084\u3046\u3068\u3057\u305f\u3068\u3055\u308c\u308b\n1716,\u4eab\uff1a\u304d\u3084\u3046\uff1a\u4fdd\uff1a\u307b\u3046\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u516b\uff1a\u306f\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5409\uff1a\u3088\u3057\uff1a\u5b97\uff1a\u3080\u306d\uff1a,\u8cea\uff1a\u3057\u3063\uff1a\u7d20\uff1a\u305d\uff1a\u5039\uff1a\u3051\u3093\uff1a\u7d04\uff1a\u3084\u304f\uff1a \u7c73\uff1a\u3053\u3081\uff1a\u306e\u5897\uff1a\u305e\u3046\uff1a\u53ce\uff1a\u3057\u3046\uff1a \u516c\uff1a\u304f\uff1a\u4e8b\uff1a\u3058\uff1a\u65b9\uff1a\u304b\u305f\uff1a\u5fa1\uff1a\u304a\uff1a\u5b9a\uff1a\u3055\u3060\u3081\uff1a\u66f8\uff1a\u304c\u304d\uff1a \u5be6\uff1a\u3058\u3064\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u306e\u5968\uff1a\u3057\u3084\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u76ee\uff1a\u3081\uff1a\u5b89\uff1a\u3084\u3059\uff1a\u7bb1\uff1a\u3070\u3053\uff1a\u306a\u3069\n1767,\u7530\uff1a\u305f\uff1a\u6cbc\uff1a\u306c\u307e\uff1a\u610f\uff1a\u304a\u304d\uff1a\u6b21\uff1a\u3064\u3050\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6cbb\uff1a\u306f\u308b\uff1a\u306e\u6642\uff1a\u3058\uff1a\u4ee3\uff1a\u3060\u3044\uff1a,\u682a\uff1a\u304b\u3076\uff1a\u4ef2\uff1a\u306a\u304b\uff1a\u9593\uff1a\u307e\uff1a\u3092\u516c\uff1a\u3053\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a \u7a0e\uff1a\u305c\u3044\uff1a\u5236\uff1a\u305b\u3044\uff1a\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a \u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u3092\u6d3b\uff1a\u304b\u3063\uff1a\u6027\uff1a\u305b\u3044\uff1a\u5316\uff1a\u304b\uff1a\u3055\u305b\u308b\n1787,\u5bdb\uff1a\u304b\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u6539\uff1a\u304b\u3044\uff1a\u9769\uff1a\u304b\u304f\uff1a,\u5341\uff1a\u3058\u3085\u3046\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u4ee3\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a \u5fb3\uff1a\u3068\u304f\uff1a\u5ddd\uff1a\u304c\u306f\uff1a\u5bb6\uff1a\u3044\u3078\uff1a\u6589\uff1a\u306a\u308a\uff1a\u304c \u767d\uff1a\u3057\u3089\uff1a\u6cb3\uff1a\u304b\u306f\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u4e3b\uff1a\u3057\u3085\uff1a \u677e\uff1a\u307e\u3064\uff1a\u5e73\uff1a\u3060\u3044\u3089\uff1a\u5b9a\uff1a\u3055\u3060\uff1a\u4fe1\uff1a\u306e\u3076\uff1a\u3092\u767b\uff1a\u3068\u3046\uff1a\u7528\uff1a\u3088\u3046\uff1a,\u56f2\u7c73(\u304b\u3053\u3044\u307e\u3044) \u501f\uff1a\u3057\u3083\u3063\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u306e\u5e33\uff1a\u3061\u3083\u3046\uff1a\u6d88\uff1a\u3051\uff1a\u3057 \u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u306e\u5e30\uff1a\u304d\uff1a\u90f7\uff1a\u304d\u3083\u3046\uff1a\u3092\u4fc3\uff1a\u3046\u306a\u304c\uff1a\u3059 \u6e6f\uff1a\u3086\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u306b\u660c\uff1a\u3057\u3083\u3046\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u5742\uff1a\u3056\u304b\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u6240\uff1a\u3058\u3087\uff1a\u3092\u3064\u304f\u308a\u5b78\uff1a\u304c\u304f\uff1a\u554f\uff1a\u3082\u3093\uff1a\u30fb\u6b66\uff1a\u3076\uff1a\u8853\uff1a\u3058\u3085\u3064\uff1a\u3092\u5968\uff1a\u3057\u3083\u3046\uff1a\u52b1\uff1a\u308c\u3044\uff1a \u53b3\uff1a\u304d\u3073\uff1a\u3057\u3044\u7dca\uff1a\u304d\u3093\uff1a\u7e2e\uff1a\u3057\u3085\u304f\uff1a\u8ca1\uff1a\u3056\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u3067\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u306f\u505c\uff1a\u3066\u3044\uff1a\u6ede\uff1a\u305f\u3044\uff1a\n1837,\u5927\uff1a\u304a\u307b\uff1a\u5869\uff1a\u3057\u307b\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u516b\uff1a\u306f\u3061\uff1a\u90ce\uff1a\u3089\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a,\u5929\uff1a\u3066\u3093\uff1a\u4fdd\uff1a\u307d\u3046\uff1a\u306e\u98e2\uff1a\u304d\uff1a\u9949\uff1a\u304d\u3093\uff1a\u304c\u6839\uff1a\u3053\u3093\uff1a\u672c\uff1a\u307d\u3093\uff1a\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064,\u5e55\uff1a\u3070\u304f\uff1a\u5e9c\uff1a\u3075\uff1a\u306e\u5143\uff1a\u3082\u3068\uff1a\u5f79\uff1a\u3084\u304f\uff1a\u4eba\uff1a\u306b\u3093\uff1a\u306e\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u5e55\u5e9c\u306b\u885d\uff1a\u3057\u3087\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1854,\u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u548c\uff1a\u308f\uff1a\u89aa\uff1a\u3057\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u30de\u30b7\u30e5\u30fc\u30fb\u30da\u30ea\u30fc\u304c\u6d66\uff1a\u3046\u3089\uff1a\u8cc0\uff1a\u304c\uff1a\u306b\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u56db\uff1a\u3088\u3093\uff1a\u96bb\uff1a\u305b\u304d\uff1a\u3067\u4f86\uff1a\u3089\u3044\uff1a\u822a\uff1a\u304b\u3046\uff1a,\u4e0b\uff1a\u3057\u3082\uff1a\u7530\uff1a\u3060\uff1a(\u9759\uff1a\u3057\u3065\uff1a\u5ca1\uff1a\u304a\u304b\uff1a\u770c\uff1a\u3051\u3093\uff1a)\u30fb\u7bb1\uff1a\u306f\u3053\uff1a\u9928\uff1a\u3060\u3066\uff1a(\u5317\uff1a\u307b\u3063\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u9053\uff1a\u3060\u3046\uff1a)\u306e\u4e8c\uff1a\u306b\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u3092\u958b\uff1a\u3072\u3089\uff1a\u304f\n1860,\u685c\uff1a\u3055\u304f\u3089\uff1a\u7530\uff1a\u3060\uff1a\u9580\uff1a\u3082\u3093\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u8b8a\uff1a\u3078\u3093\uff1a,121\u4ee3\uff1a\u3060\u3044\uff1a\u5b5d\uff1a\u304b\u3046\uff1a\u660e\uff1a\u3081\u3044\uff1a\u5929\u7687\u306e\u52c5\uff1a\u3061\u3087\u304f\uff1a\u8a31\uff1a\u304d\u3087\uff1a\u3092\u5f97\u305a \u65e5\uff1a\u306b\u3061\uff1a\u7c73\uff1a\u3079\u3044\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3093\u3060 \u3068\u3044\u3075\u6279\uff1a\u3072\uff1a\u5224\uff1a\u306f\u3093\uff1a\u306b \u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c \u5b89\uff1a\u3042\u3093\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u7344\uff1a\u3054\u304f\uff1a\u3067\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u5fd7\uff1a\u3057\uff1a\u58eb\uff1a\u3057\uff1a\u3092\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u3057\u305f\u3053\u3068\u304c\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u3068\u3055\u308c\u308b,\u4e95\uff1a\u3090\uff1a\u4f0a\uff1a\u3044\uff1a\u76f4\uff1a\u306a\u307b\uff1a\u5f3c\uff1a\u3059\u3051\uff1a\u304c\u6c34\uff1a\u307f\uff1a\u6238\uff1a\u3068\uff1a\u85e9\uff1a\u306f\u3093\uff1a\u306e\u6d6a\uff1a\u3089\u3046\uff1a\u58eb\uff1a\u3057\uff1a\u3089\u306b\u6697\uff1a\u3042\u3093\uff1a\u6bba\uff1a\u3055\u3064\uff1a\u3055\u308c\u308b\n1868,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a,\u524d\uff1a\u305c\u3093\uff1a\u5e74\uff1a\u306d\u3093\uff1a\u306e\u5927\uff1a\u305f\u3044\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5949\uff1a\u307b\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051 \u671d\uff1a\u3066\u3046\uff1a\u5ef7\uff1a\u3066\u3044\uff1a\u304c<\u738b\uff1a\u308f\u3046\uff1a\u653f\uff1a\u305b\u3044\uff1a\u5fa9\uff1a\u3075\u3063\uff1a\u53e4\uff1a\u3053\uff1a\u306e\u5927\uff1a\u3060\u3044\uff1a\u53f7\uff1a\u304c\u3046\uff1a\u4ee4\uff1a\u308c\u3044\uff1a>\u3092\u51fa\uff1a\u3060\uff1a\u3059,\u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u5929\u7687\u304c \u4e94\uff1a\u3054\uff1a\u7b87\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u306e\u5fa1\uff1a\u3054\uff1a\u8a93\uff1a\u305b\u3044\uff1a\u6587\uff1a\u3082\u3093\uff1a\u3092\u767c\uff1a\u306f\u3063\uff1a\u5e03\uff1a\u3077\uff1a\u3055\u308c\u308b\n1875,\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a,\u3053\u306e\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u306e\u7d50\uff1a\u3051\u3064\uff1a\u679c\uff1a\u304b\uff1a \u65e5\uff1a\u306b\u3063\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u4fee\uff1a\u3057\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u898f\uff1a\u304d\uff1a(\u4e0d\uff1a\u3075\uff1a\u5e73\uff1a\u3073\u3084\u3046\uff1a\u7b49\uff1a\u3069\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3068\u3055\u308c\u308b)\u3092\u7de0\uff1a\u3066\u3044\uff1a\u7d50\uff1a\u3051\u3064\uff1a,\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u53f7\uff1a\u3054\u3046\uff1a\u304c\u98f2\uff1a\u3044\u3093\uff1a\u6599\uff1a\u308c\u3046\uff1a\u6c34\uff1a\u3059\u3044\uff1a\u78ba\uff1a\u304b\u304f\uff1a\u4fdd\uff1a\u307b\uff1a\u306e\u305f\u3081\u6c5f\uff1a\u304b\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u306b\u63a5\uff1a\u305b\u3063\uff1a\u8fd1\uff1a\u304d\u3093\uff1a\u3057\u305f\u969b\uff1a\u3055\u3044\uff1a \u7a81\uff1a\u3068\u3064\uff1a\u5982\uff1a\u3058\u3087\uff1a\u540c\uff1a\u3069\u3046\uff1a\u5cf6\uff1a\u3068\u3046\uff1a\u306e\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3088\u308a\u5f37\uff1a\u304d\u3083\u3046\uff1a\u70c8\uff1a\u308c\u3064\uff1a\u306a\u7832\uff1a\u306f\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b >>\u96f2\uff1a\u3046\u3093\uff1a\u63da\uff1a\u3084\u3046\uff1a\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a\u3057\u9678\uff1a\u308a\u304f\uff1a\u6230\uff1a\u305b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u9678\uff1a\u308a\u304f\uff1a\u3055\u305b\u7832\uff1a\u306f\u3046\uff1a\u53f0\uff1a\u3060\u3044\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u62e0\uff1a\u304d\u3087\uff1a \u6b66\uff1a\u3076\uff1a\u5668\uff1a\u304d\uff1a\u3092\u6355\uff1a\u307b\uff1a\u7372\uff1a\u304b\u304f\uff1a\u3057\u3066\u9577\uff1a\u306a\u304c\uff1a\u5d0e\uff1a\u3055\u304d\uff1a\u3078\u5e30\uff1a\u304d\uff1a\u7740\uff1a\u3061\u3083\u304f\uff1a\n1877,\u897f\uff1a\u305b\u3044\uff1a\u5357\uff1a\u306a\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092\u6230\uff1a\u305f\u305f\u304b\uff1a\u3063\u305f\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u305f\u3061\u304c \u660e\uff1a\u3081\u3044\uff1a\u6cbb\uff1a\u3062\uff1a\u7dad\uff1a\u3090\uff1a\u65b0\uff1a\u3057\u3093\uff1a\u306b\u4e0d\uff1a\u3075\uff1a\u6e80\uff1a\u307e\u3093\uff1a\u3092\u62b1\uff1a\u3044\u3060\uff1a\u304d \u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u62c5\uff1a\u304b\u3064\uff1a\u3044\u3067\u8702\uff1a\u307b\u3046\uff1a\u8d77\uff1a\u304d\uff1a,\u897f\uff1a\u3055\u3044\uff1a\u90f7\uff1a\u304c\u3046\uff1a\u9686\uff1a\u305f\u304b\uff1a\u76db\uff1a\u3082\u308a\uff1a\u3092\u7dcf\uff1a\u305d\u3046\uff1a\u5927\uff1a\u3060\u3044\uff1a\u5c06\uff1a\u3057\u3083\u3046\uff1a\u3068\u3059\u308b\u53cd\uff1a\u306f\u3093\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u93ae\uff1a\u3061\u3093\uff1a\u58d3\uff1a\u3042\u3064\uff1a\u3055\u308c \u897f\u90f7\u306f\u81ea\uff1a\u3058\uff1a\u6c7a\uff1a\u3051\u3064\uff1a \u4ee5\uff1a\u3044\uff1a\u5f8c\uff1a\u3054\uff1a\u58eb\uff1a\u3057\uff1a\u65cf\uff1a\u305e\u304f\uff1a\u306e\u53cd\u4e82\u306f\u9014\uff1a\u3068\uff1a\u7d76\uff1a\u3060\uff1a\u3078 \u620a\uff1a\u307c\uff1a\u8fb0\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u304b\u3089\u5341\u5e74\u7e8c\uff1a\u3064\u3065\uff1a\u3044\u3066\u3090\u305f\u52d5\uff1a\u3069\u3046\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u306f\u53ce\uff1a\u3057\u3046\uff1a\u675f\uff1a\u305d\u304f\uff1a\u3057\u305f\n1894,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u3067\u8fb2\uff1a\u306e\u3046\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u4e00\uff1a\u3044\u3063\uff1a\u63c6\uff1a\u304d\uff1a\u304c\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u66b4\uff1a\u307c\u3046\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u5316\uff1a\u304b\uff1a(\u6771\uff1a\u3068\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u9ee8\uff1a\u305f\u3046\uff1a\u306e\u4e82\uff1a\u3089\u3093\uff1a) \u304c\u8d77\uff1a\u304d\uff1a\u7206\uff1a\u3070\u304f\uff1a\u5264\uff1a\u3056\u3044\uff1a\u3068\u306a\u308b,\u8c4a\uff1a\u3068\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306f \u6211\uff1a\u308f\uff1a\u304c\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u7b2c\uff1a\u3060\u3044\uff1a\u4e00\uff1a\u3044\u3061\uff1a\u904a\uff1a\u3044\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u968a\uff1a\u305f\u3044\uff1a\u5409\uff1a\u3088\u3057\uff1a\u91ce\uff1a\u306e\uff1a\u304c\u793c\uff1a\u308c\u3044\uff1a\u7832\uff1a\u306f\u3046\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u63db\uff1a\u304f\u308f\u3093\uff1a\u306e\u7528\uff1a\u3088\u3046\uff1a\u610f\uff1a\u3044\uff1a\u3092\u3057\u3066\u8fd1\uff1a\u304d\u3093\uff1a\u63a5\uff1a\u305b\u3064\uff1a\u3057\u305f\u306e\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u8266\uff1a\u304b\u3093\uff1a\u6e08\uff1a\u305b\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u305f\u3046\uff1a\u6e96\uff1a\u3058\u3085\u3093\uff1a\u5099\uff1a\u3073\uff1a\u304a\u3088\u3073\u767c\uff1a\u306f\u3063\uff1a\u7832\uff1a\u3071\u3046\uff1a\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\uff1a\u3057\u3082\u306e\uff1a\u95a2\uff1a\u305b\u304d\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306b\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a\u3057\u3066\u7d50\uff1a\u3080\u3059\uff1a\u3070\u308c\u305f\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a >> \u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u5e72\uff1a\u304b\u3093\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u53d7\uff1a\u3046\uff1a\u3051\u308b,\u4e00 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u671d\uff1a\u3066\u3046\uff1a\u9bae\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5b8c\uff1a\u304b\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u7121\uff1a\u3080\uff1a\u6b20\uff1a\u3051\u3064\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u81ea\uff1a\u3058\uff1a\u4e3b\uff1a\u3057\u3085\uff1a\u306e\u570b\uff1a\u304f\u306b\uff1a\u3067\u3042\u308b\u3053\u3068\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u4e8c \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u907c\uff1a\u308a\u3087\u3046\uff1a\u6771\uff1a\u3068\u3046\uff1a\u534a\uff1a\u306f\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a \u53f0\uff1a\u305f\u3044\uff1a\u6e7e\uff1a\u308f\u3093\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u53ca\uff1a\u304a\u3088\uff1a\u3073\u6f8e\uff1a\u307b\u3046\uff1a\u6e56\uff1a\u3053\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u6c38\uff1a\u3048\u3044\uff1a\u9060\uff1a\u3048\u3093\uff1a\u306b\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306b\u5272\uff1a\u304b\u3064\uff1a\u8b72\uff1a\u3058\u3083\u3046\uff1a\u3059\u308b \u4e09 \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u8ecd\uff1a\u3050\u3093\uff1a\u8cbb\uff1a\u3074\uff1a\u8ce0\uff1a\u3070\u3044\uff1a\u511f\uff1a\u3057\u3083\u3046\uff1a\u91d1\uff1a\u304d\u3093\uff1a\u4e8c\uff1a\u306b\uff1a\u5104\uff1a\u304a\u304f\uff1a\u4e21\uff1a\u30c6\u30fc\u30eb\uff1a\u3092\u652f\uff1a\u3057\uff1a\u6255\uff1a\u306f\u3089\uff1a\u3075 \u56db \u65e5\uff1a\u306b\u3063\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u306f\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u305f\u3081\u6d88\uff1a\u3057\u3087\u3046\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u305f\u306e\u3067\u65b0\uff1a\u3042\u3089\uff1a\u305f\u306b\u901a\uff1a\u3064\u3046\uff1a\u5546\uff1a\u3057\u3083\u3046\uff1a\u822a\uff1a\u304b\u3046\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u7d50\uff1a\u3080\u3059\uff1a\u3076 \u4e94 \u672c\uff1a\u307b\u3093\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u5f8c\uff1a\u3054\uff1a \u76f4\uff1a\u305f\u3060\uff1a\u3061\u306b\u4fd8\uff1a\u3075\uff1a\u865c\uff1a\u308a\u3087\uff1a\u3092\u8fd4\uff1a\u3078\u3093\uff1a\u9084\uff1a\u304b\u3093\uff1a\u3059\u308b \u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u9001\uff1a\u305d\u3046\uff1a\u9084\uff1a\u304f\u308f\u3093\uff1a\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\uff1a\u304e\u3083\u304f\uff1a\u5f85\uff1a\u305f\u3044\uff1a\u3042\u308b\u3044\u306f\u51e6\uff1a\u3057\u3087\uff1a\u5211\uff1a\u3051\u3044\uff1a\u305b\u306c\u3053\u3068\n1899,\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u539f\uff1a\u3052\u3093\uff1a\u56e0\uff1a\u3044\u3093\uff1a\u306e\u3072\u3068\u3064\u3068\u8a00\uff1a\u3044\uff1a\u3078\u308b,\u5b97\uff1a\u3057\u3085\u3046\uff1a\u6559\uff1a\u3051\u3046\uff1a\u7684\uff1a\u3066\u304d\uff1a\u79d8\uff1a\u3072\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u7d50\uff1a\u3051\u3063\uff1a\u793e\uff1a\u3057\u3083\uff1a\u3067\u3042\u308b\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u304c<\u6276\uff1a\u3075\uff1a\u6e05\uff1a\u3057\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u6d0b\uff1a\u3084\u3046\uff1a>\u3092\u304b\u304b\u3052 \u5c71\uff1a\u3055\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u7701\uff1a\u3057\u3083\u3046\uff1a\u3067 \u30ad\u30ea\u30b9\u30c8\u6559\uff1a\u3051\u3046\uff1a\u5f92\uff1a\u3068\uff1a\u306e\u6bba\uff1a\u3055\u3064\uff1a\u5bb3\uff1a\u304c\u3044\uff1a \u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u7834\uff1a\u306f\uff1a\u58ca\uff1a\u304b\u3044\uff1a\u306a\u3069\u3092\u884c\uff1a\u304a\u3053\uff1a\u306a\u3044 \u6e05\uff1a\u3057\u3093\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u7d50\uff1a\u3051\u3063\uff1a\u8a17\uff1a\u305f\u304f\uff1a\u3057\u3066 \u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u306e\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a \u6e05\uff1a\u3057\u3093\uff1a\u5e1d\uff1a\u3066\u3044\uff1a\u306f\u5217\uff1a\u308c\u3063\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057 \u5ba3\uff1a\u305b\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306e\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u8aed\uff1a\u3086\uff1a\u3092\u767c\uff1a\u306f\u3064\uff1a\u3059\u308b\u3082 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3092\u4e3b\uff1a\u3057\u3085\uff1a\u529b\uff1a\u308a\u3087\u304f\uff1a\u3068\u3059\u308b\u516b\uff1a\u306f\u3061\uff1a\u30f6\uff1a\u304b\uff1a\u570b\uff1a\u3053\u304f\uff1a\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u5317\uff1a\u307a\uff1a\u4eac\uff1a\u304d\u3093\uff1a\u516c\uff1a\u3053\u3046\uff1a\u4f7f\uff1a\u3057\uff1a\u9928\uff1a\u304f\u308f\u3093\uff1a\u5340\uff1a\u304f\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u7fa9\uff1a\u304e\uff1a\u548c\uff1a\u308f\uff1a\u5718\uff1a\u3060\u3093\uff1a\u30fb\u6e05\uff1a\u3057\u3093\uff1a\u5175\uff1a\u307a\u3044\uff1a\u306e\u5305\uff1a\u306f\u3046\uff1a\u56f2\uff1a\u3090\uff1a\u304b\u3089\u6551\uff1a\u304d\u3046\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1902,\u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u52dd\uff1a\u3057\u3083\u3046\uff1a\u5229\uff1a\u308a\uff1a\u306b\u852d\uff1a\u304b\u3052\uff1a\u306e\u529b\uff1a\u3061\u304b\u3089\uff1a\u3068\u306a\u308b,\u4e00 \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3059\u308b \u3057\u304b\u3057\u82f1\uff1a\u3048\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u306f\u6e05\uff1a\u3057\u3093\uff1a\u97d3\uff1a\u304b\u3093\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u653f\uff1a\u305b\u3044\uff1a\u6cbb\uff1a\u3058\uff1a\u30fb\u7d4c\uff1a\u3051\u3044\uff1a\u6e08\uff1a\u3056\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u683c\uff1a\u304b\u304f\uff1a\u6bb5\uff1a\u3060\u3093\uff1a\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u6709\uff1a\u3044\u3046\uff1a\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u304c\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u306e\u4fb5\uff1a\u3057\u3093\uff1a\u7565\uff1a\u308a\u3083\u304f\uff1a\u3084\u5185\uff1a\u306a\u3044\uff1a\u4e82\uff1a\u3089\u3093\uff1a\u3067\u4fb5\uff1a\u3057\u3093\uff1a\u8feb\uff1a\u3071\u304f\uff1a\u3055\u308c\u305f\u6642\uff1a\u3068\u304d\uff1a\u306f\u5fc5\uff1a\u3072\u3064\uff1a\u8981\uff1a\u3048\u3046\uff1a\u306a\u63aa\uff1a\u305d\uff1a\u7f6e\uff1a\u3061\uff1a\u3092\u3068\u308b \u4e8c \u65e5\uff1a\u306b\u3061\uff1a\u82f1\uff1a\u3048\u3044\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u304c\u3053\u306e\u5229\uff1a\u308a\uff1a\u76ca\uff1a\u3048\u304d\uff1a\u3092\u8b77\uff1a\u307e\u3082\uff1a\u308b\u305f\u3081\u7b2c\uff1a\u3060\u3044\uff1a\u4e09\uff1a\u3055\u3093\uff1a\u570b\uff1a\u3054\u304f\uff1a\u3068\u6230\uff1a\u305f\u305f\u304b\uff1a\u3075\u6642\uff1a\u3068\u304d\uff1a\u306f\u4ed6\uff1a\u305f\uff1a\u306e\u4e00\uff1a\u3044\u3063\uff1a\u65b9\uff1a\u3071\u3046\uff1a\u306f\u53b3\uff1a\u3052\u3093\uff1a\u6b63\uff1a\u305b\u3044\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u3092\u5b88\uff1a\u307e\u3082\uff1a\u308a \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u6575\uff1a\u3066\u304d\uff1a\u5074\uff1a\u304c\u306f\uff1a\u306b\u53c2\uff1a\u3055\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u3059\u308b\u306e\u3092\u9632\uff1a\u3075\u305b\uff1a\u3050 \u4e09 \u4ed6\uff1a\u305f\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308b\u6642\uff1a\u3068\u304d\uff1a\u306f \u4ed6\uff1a\u305f\uff1a\u306e\u540c\uff1a\u3069\u3046\uff1a\u76df\uff1a\u3081\u3044\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306f \u63f4\uff1a\u3048\u3093\uff1a\u52a9\uff1a\u3058\u3087\uff1a\u3092\u8207\uff1a\u3042\u305f\uff1a\u3078\u308b\n1904,\u65e5\uff1a\u306b\u3061\uff1a\u9732\uff1a\u308d\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6975\uff1a\u304d\u3087\u304f\uff1a\u6771\uff1a\u3068\u3046\uff1a\u306e\u30ed\u30b7\u30a2\u8ecd\uff1a\u3050\u3093\uff1a\u306b\u52d5\uff1a\u3069\u3046\uff1a\u54e1\uff1a\u3090\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u306b\u306f\u6212\uff1a\u304b\u3044\uff1a\u53b3\uff1a\u3052\u3093\uff1a\u4ee4\uff1a\u308c\u3044\uff1a\u304c\u4e0b\uff1a\u304f\u3060\uff1a\u3055\u308c \u5bfe\uff1a\u305f\u3044\uff1a\u9732\uff1a\u308d\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u306f\u6c7a\uff1a\u3051\u3064\uff1a\u88c2\uff1a\u308c\u3064\uff1a \u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f\u570b\uff1a\u3053\u3063\uff1a\u4ea4\uff1a\u304b\u3046\uff1a\u65ad\uff1a\u3060\u3093\uff1a\u7d76\uff1a\u305c\u3064\uff1a\u3092\u9732\uff1a\u308d\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u901a\uff1a\u3064\u3046\uff1a\u544a\uff1a\u3053\u304f\uff1a,\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u806f\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u306b\u3088\u308b \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u6e2f\uff1a\u304b\u3046\uff1a\u5916\uff1a\u3050\u308f\u3044\uff1a\u306e\u653b\uff1a\u3053\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a \u4ec1\uff1a\u3058\u3093\uff1a\u5ddd\uff1a\u305b\u3093\uff1a\u6c96\uff1a\u304a\u304d\uff1a\u306b\u3066\u6575\uff1a\u3066\u304d\uff1a\u8266\uff1a\u304b\u3093\uff1a\u306e\u6483\uff1a\u3052\u304d\uff1a\u6c88\uff1a\u3061\u3093\uff1a\u304c\u3042\u308a \u6b21\uff1a\u3064\u304e\uff1a\u306e\u65e5\uff1a\u3072\uff1a\u306b\u5ba3\u6226 >> \u907c\uff1a\u308a\u3083\u3046\uff1a\u967d\uff1a\u3084\u3046\uff1a\u30fb\u6c99\uff1a\u3057\u3083\uff1a\u6cb3\uff1a\u304b\uff1a\u306e\u6703\uff1a\u304f\u308f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u52dd\uff1a\u3057\u3087\u3046\uff1a\u5229\uff1a\u308a\uff1a \u6d77\uff1a\u304b\u3044\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u306e\u7372\uff1a\u304b\u304f\uff1a\u5f97\uff1a\u3068\u304f\uff1a \u65c5\uff1a\u308a\u3087\uff1a\u9806\uff1a\u3058\u3085\u3093\uff1a\u9665\uff1a\u304b\u3093\uff1a\u843d\uff1a\u3089\u304f\uff1a \u5949\uff1a\u307b\u3046\uff1a\u5929\uff1a\u3066\u3093\uff1a\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3087\u3046\uff1a\u3092\u7d4c\uff1a\u3078\uff1a\u3066 \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6d77\uff1a\u304b\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\uff1a\u304b\u3093\uff1a\u968a\uff1a\u305f\u3044\uff1a\u3092\u5168\uff1a\u305c\u3093\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3055\u305b \u6a3a\uff1a\u304b\u3089\uff1a\u592a\uff1a\u3075\u3068\uff1a\u5168\uff1a\u305c\u3093\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\n1931,\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u30bd\u9023\uff1a\u308c\u3093\uff1a\u306e\u5916\uff1a\u304c\u3044\uff1a\u8499\uff1a\u3082\u3046\uff1a\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a \u4e8b\uff1a\u3058\uff1a\u5be6\uff1a\u3058\u3064\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a\u4e09\u3064\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u3092\u6301\uff1a\u3082\uff1a\u3064\u4e0d\uff1a\u3075\uff1a\u5b89\uff1a\u3042\u3093\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u306a\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a \u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u8650\uff1a\u304e\u3083\u304f\uff1a\u6bba\uff1a\u3055\u3064\uff1a \u5f35\uff1a\u3061\u3087\u3046\uff1a\u4f5c\uff1a\u3055\u304f\uff1a\u9716\uff1a\u308a\u3093\uff1a\u30fb\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304c\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u79d5\uff1a\u3072\uff1a\u653f\uff1a\u305b\u3044\uff1a\u306b\u3088\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u4eba\uff1a\u3058\u3093\uff1a\u306e\u7aae\uff1a\u304d\u3085\u3046\uff1a\u4e4f\uff1a\u307c\u3075\uff1a \u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u72ec\uff1a\u3069\u304f\uff1a\u7acb\uff1a\u308a\u3064\uff1a\u904b\uff1a\u3046\u3093\uff1a\u52d5\uff1a\u3069\u3046\uff1a\u306a\u3069 \u6e80\u6d32\u306b\u306f\u3044\u3064\u7206\uff1a\u3070\u304f\uff1a\u767c\uff1a\u306f\u3064\uff1a\u3057\u3066\u3082\u304a\u304b\u3057\u304f\u306a\u3044 \u7dca\uff1a\u304d\u3093\uff1a\u5f35\uff1a\u3061\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u304c\u3042\u3063\u305f,\u77f3\uff1a\u3044\u3057\uff1a\u539f\uff1a\u306f\u3089\uff1a\u839e\uff1a\u304b\u3093\uff1a\u723e\uff1a\u3058\uff1a\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u4f50\uff1a\u3055\uff1a\u306e\u7dbf\uff1a\u3081\u3093\uff1a\u5bc6\uff1a\u307f\u3064\uff1a\u306a\u8a08\uff1a\u3051\u3044\uff1a\u753b\uff1a\u304b\u304f\uff1a\u306b\u3088\u308a \u67f3\uff1a\u308a\u3046\uff1a\u6761\uff1a\u3067\u3046\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u306b\u304a\u3051\u308b\u6e80\uff1a\u307e\u3093\uff1a\u6d32\uff1a\u3057\u3046\uff1a\u9244\uff1a\u3066\u3064\uff1a\u9053\uff1a\u3060\u3046\uff1a\u306e\u7dda\uff1a\u305b\u3093\uff1a\u8def\uff1a\u308d\uff1a\u304c\u5c0f\uff1a\u305b\u3046\uff1a\u898f\uff1a\u304d\uff1a\u6a21\uff1a\u307c\uff1a\u306b\u7206\uff1a\u3070\u304f\uff1a\u7834\uff1a\u306f\uff1a\u3055\u308c \u305d\u308c\u3092\u5f35\uff1a\u3061\u3087\u3046\uff1a\u5b78\uff1a\u304b\u304f\uff1a\u826f\uff1a\u308a\u3087\u3046\uff1a\u306e\u4ed5\uff1a\u3057\uff1a\u696d\uff1a\u308f\u3056\uff1a\u3068\u3057\u305f\u95a2\uff1a\u304b\u3093\uff1a\u6771\uff1a\u3068\u3046\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f \u5317\uff1a\u307b\u304f\uff1a\u5927\uff1a\u305f\u3044\uff1a\u55b6\uff1a\u3048\u3044\uff1a\u306e\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3092\u6557\uff1a\u306f\u3044\uff1a\u8d70\uff1a\u305d\u3046\uff1a\u305b\u3057\u3081 \u3053\u308c\u3092\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u3057\u305f\n1937,\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u3078\u3093\uff1a,\u76e7\uff1a\u308d\uff1a\u6e9d\uff1a\u3053\u3046\uff1a\u6a4b\uff1a\u3051\u3046\uff1a\u4e8b\uff1a\u3058\uff1a\u4ef6\uff1a\u3051\u3093\uff1a\u3092\u5951\uff1a\u3051\u3044\uff1a\u6a5f\uff1a\u304d\uff1a\u3068\u3057 \u4e0a\uff1a\u3057\u3083\u3093\uff1a\u6d77\uff1a\u306f\u3044\uff1a\u4e8b\uff1a\u3058\uff1a\u8b8a\uff1a\u306f\u3093\uff1a\u3078 \u305d\u3057\u3066\u65e5\uff1a\u306b\u3063\uff1a\u652f\uff1a\u3057\uff1a\u4e21\uff1a\u308a\u3083\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u304c\u5168\uff1a\u305c\u3093\uff1a\u9762\uff1a\u3081\u3093\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6bb5\uff1a\u3060\u3093\uff1a\u968e\uff1a\u304b\u3044\uff1a\u306b\u7a81\uff1a\u3068\u3064\uff1a\u5165\uff1a\u306b\u3075\uff1a\u3057\u305f,\u8ecd\uff1a\u3050\u3093\uff1a\u4e8b\uff1a\u3058\uff1a\u6f14\uff1a\u3048\u3093\uff1a\u7fd2\uff1a\u3057\u3075\uff1a\u3092\u7d42\uff1a\u3057\u3085\u3046\uff1a\u4e86\uff1a\u308c\u3046\uff1a\u3057\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u99d0\uff1a\u3061\u3085\u3046\uff1a\u5c6f\uff1a\u3068\u3093\uff1a\u6b69\uff1a\u307b\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306b\u5c0d\uff1a\u305f\u3044\uff1a\u3057\u9283\uff1a\u3058\u3085\u3046\uff1a\u6483\uff1a\u3052\u304d\uff1a\u304c\u6d74\uff1a\u3042\uff1a\u3073\u305b\u3089\u308c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306f\u61c9\uff1a\u304a\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u305b\u305a\u306b\u72b6\uff1a\u3058\u3083\u3046\uff1a\u6cc1\uff1a\u304d\u3083\u3046\uff1a\u306e\u628a\uff1a\u306f\uff1a\u63e1\uff1a\u3042\u304f\uff1a \u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u3068\u306e\u4ea4\uff1a\u304b\u3046\uff1a\u6e09\uff1a\u305b\u3075\uff1a\u3092\u9032\uff1a\u3059\u3059\uff1a\u3081\u305f\u304c \u6211\uff1a\u308f\u304c\uff1a\u8ecd\uff1a\u3050\u3093\uff1a\u306e\u6230\uff1a\u305b\u3093\uff1a\u95d8\uff1a\u3068\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u52e2\uff1a\u305b\u3044\uff1a\u3092\u307f\u305f\u652f\uff1a\u3057\uff1a\u90a3\uff1a\u306a\uff1a\u5175\uff1a\u3078\u3044\uff1a\u306f\u731b\uff1a\u307e\u3046\uff1a\u5c04\uff1a\u3057\u3083\uff1a\u3057 \u4e03\u6642\uff1a\u3058\uff1a\u9593\uff1a\u304b\u3093\uff1a\u306e\u81ea\uff1a\u3058\uff1a\u91cd\uff1a\u3061\u3087\u3046\uff1a\u3082\u865a\uff1a\u3080\u306a\uff1a\u3057\u304f\u6211\u8ecd\u306f\u53cd\uff1a\u306f\u3093\uff1a\u6483\uff1a\u3052\u304d\uff1a \u7adc\uff1a\u308a\u3085\u3046\uff1a\u738b\uff1a\u308f\u3046\uff1a\u5ef3\uff1a\u3061\u3087\u3046\uff1a\u306e\u6575\uff1a\u3066\u304d\uff1a\u3092\u6483\uff1a\u3052\u304d\uff1a\u6ec5\uff1a\u3081\u3064\uff1a\u3057\u6c38\uff1a\u3048\u3044\uff1a\u5b9a\uff1a\u3066\u3044\uff1a\u6cb3\uff1a\u304c\uff1a\u306e\u53f3\uff1a\u3046\uff1a\u5cb8\uff1a\u304c\u3093\uff1a\u3078\u9032\uff1a\u3057\u3093\uff1a\u51fa\uff1a\u3057\u3085\u3064\uff1a\n1941,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a,\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u5f8c\uff1a\u3054\uff1a\u306e\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u306f \u3053\u306e\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u3092<\u592a\uff1a\u305f\u3044\uff1a\u5e73\uff1a\u3078\u3044\uff1a\u6d0b\uff1a\u3084\u3046\uff1a\u6230\u722d>\u3068\u547c\uff1a\u3053\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u3057\u3066\u3090\u308b,\u3053\u306e\u6230\u722d\u306b\u6557\uff1a\u3084\u3076\uff1a\u308c\u305f\u6211\u570b\u306f\u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c \u52dd\uff1a\u3057\u3087\u3046\uff1a\u8005\uff1a\u3057\u3083\uff1a\u306b\u90fd\uff1a\u3064\uff1a\u5408\uff1a\u304c\u3075\uff1a\u306e\u60e1\uff1a\u308f\u308b\uff1a\u3044\u6b74\uff1a\u308c\u304d\uff1a\u53f2\uff1a\u3057\uff1a\u306e\u6559\uff1a\u3051\u3046\uff1a\u80b2\uff1a\u3044\u304f\uff1a\u3092\u4e00\uff1a\u3044\u3063\uff1a\u5207\uff1a\u3055\u3044\uff1a\u6392\uff1a\u306f\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u4eca\uff1a\u3044\u307e\uff1a\u306b\u81f3\uff1a\u3044\u305f\uff1a\u308b\n1945,\u30dd\u30c4\u30c0\u30e0\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u7a31\uff1a\u305b\u3046\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u3078\u306e\u964d\uff1a\u304b\u3046\uff1a\u4f0f\uff1a\u3075\u304f\uff1a\u8981\uff1a\u3048\u3046\uff1a\u6c42\uff1a\u304d\u3046\uff1a\u306e\u6700\uff1a\u3055\u3044\uff1a\u7d42\uff1a\u3057\u3085\u3046\uff1a\u5ba3\uff1a\u305b\u3093\uff1a\u8a00\uff1a\u3052\u3093\uff1a>,\u5168\uff1a\u305c\u3093\uff1a13\u30f6\uff1a\u304b\uff1a\u6761\uff1a\u3067\u3046\uff1a\u304b\u3089\u306a\u308a \u30a4\u30ae\u30ea\u30b9\u30fb\u30a2\u30e1\u30ea\u30ab\u5408\uff1a\u304c\u3063\uff1a\u8846\uff1a\u3057\u3085\u3046\uff1a\u570b\uff1a\u3053\u304f\uff1a\u30fb\u4e2d\uff1a\u3061\u3085\u3046\uff1a\u83ef\uff1a\u304f\u308f\uff1a\u6c11\uff1a\u307f\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306e\u653f\uff1a\u305b\u3044\uff1a\u5e9c\uff1a\u3075\uff1a\u9996\uff1a\u3057\u3085\uff1a\u8133\uff1a\u306e\u3046\uff1a\u306e\u9023\uff1a\u308c\u3093\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306b\u304a\u3044\u3066\u767c\uff1a\u306f\u3063\uff1a\u305b\u3089\u308c \u30bd\u30d3\u30a8\u30c8\u9023\uff1a\u308c\u3093\uff1a\u90a6\uff1a\u3071\u3046\uff1a\u306f \u5f8c\uff1a\u3042\u3068\uff1a\u304b\u3089\u52a0\uff1a\u304f\u306f\uff1a\u306f\u308a\u8ffd\uff1a\u3064\u3044\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3057\u305f\n1951,\u30b5\u30f3\u30d5\u30e9\u30f3\u30b7\u30b9\u30b3\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a,\u6b63\uff1a\u305b\u3044\uff1a\u5f0f\uff1a\u3057\u304d\uff1a\u540d\uff1a\u3081\u3044\uff1a\u306f<\u65e5\uff1a\u306b\uff1a\u672c\uff1a\u307b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3068\u306e\u5e73\uff1a\u3078\u3044\uff1a\u548c\uff1a\u308f\uff1a\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a>,\u5927\uff1a\u3060\u3044\uff1a\u6771\uff1a\u3068\u3046\uff1a\u4e9e\uff1a\u3042\uff1a\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u306e\u6557\uff1a\u306f\u3044\uff1a\u6230\uff1a\u305b\u3093\uff1a\u570b\uff1a\u3053\u304f\uff1a\u3067\u3042\u308a \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u7d71\uff1a\u3068\u3046\uff1a\u6cbb\uff1a\u3061\uff1a\u3055\u308c\u3066\u3090\u305f\u6211\uff1a\u308f\u304c\uff1a\u570b\uff1a\u304f\u306b\uff1a\u304c \u3053\u306e\u6761\uff1a\u3067\u3046\uff1a\u7d04\uff1a\u3084\u304f\uff1a\u3092\u6279\uff1a\u3072\uff1a\u51c6\uff1a\u3058\u3085\u3093\uff1a\u3057\u305f\u9023\uff1a\u308c\u3093\uff1a\u5408\uff1a\u304c\u3075\uff1a\u570b\uff1a\u3053\u304f\uff1a\u306b\u3088\u308a\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u3092\u627f\uff1a\u3057\u3087\u3046\uff1a\u8a8d\uff1a\u306b\u3093\uff1a\u3055\u308c \u570b\uff1a\u3053\u304f\uff1a\u969b\uff1a\u3055\u3044\uff1a\u6cd5\uff1a\u306f\u3046\uff1a\u4e0a\uff1a\u3058\u3083\u3046\uff1a \u6211\u570b\u3068\u591a\uff1a\u304a\u307b\uff1a\u304f\u306e\u9023\u5408\u570b\u3068\u306e\u9593\uff1a\u3042\u3072\u3060\uff1a\u306e<\u6230\uff1a\u305b\u3093\uff1a\u722d\uff1a\u3055\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a>\u304c\u7d42\uff1a\u3057\u3085\u3046\uff1a\u7d50\uff1a\u3051\u3064\uff1a\u3057\u305f \u3053\u306e\u6761\u7d04\u3067\u6211\u570b\u306f1875\u5e74\u306b\u5168\uff1a\u305c\u3093\uff1a\u57df\uff1a\u3044\u304d\uff1a\u3092\u9818\uff1a\u308a\u3083\u3046\uff1a\u6709\uff1a\u3044\u3046\uff1a\u3057\u305f\u5343\uff1a\u3061\uff1a\u5cf6\uff1a\u3057\u307e\uff1a\u5217\uff1a\u308c\u3063\uff1a\u5cf6\uff1a\u305f\u3046\uff1a\u3092\u653e\uff1a\u306f\u3046\uff1a\u68c4\uff1a\u304d\uff1a\u3057\u3066\u3090\u308b \u306a\u307b \u3053\u306e\u6761\u7d04\u306e\u767c\uff1a\u306f\u3063\uff1a\u52b9\uff1a\u304b\u3046\uff1a\u65e5\uff1a\u3073\uff1a\u306f1952\u5e74<\u662d\u548c27\u5e74>4\u670828\u65e5\u3067\u3042\u308a \u6211\u570b\u306e\u4e3b\uff1a\u3057\u3085\uff1a\u6a29\uff1a\u3051\u3093\uff1a\u304c\u56de\uff1a\u304b\u3044\uff1a\u5fa9\uff1a\u3075\u304f\uff1a\u3057 \u5360\uff1a\u305b\u3093\uff1a\u9818\uff1a\u308a\u3083\u3046\uff1a\u72b6\uff1a\u3058\u3083\u3046\uff1a\u614b\uff1a\u305f\u3044\uff1a\u3082\u89e3\uff1a\u304b\u3044\uff1a\u9664\uff1a\u3058\u3087\uff1a\u3055\u308c\u305f"));}),_1Eh=new T(function(){return B(_1Ea(_1Eg));}),_1Ei=new T(function(){return B(_aj(_1E5,_1Eh));}),_1Ej=new T(function(){return B(_cU(1,2));}),_1Ek=new T(function(){return B(unCStr("1871,\u65e5\u6e05\u4fee\u597d\u6761\u898f,\u3053\u306e\u6642\u306e\u4e21\u56fd\u306f \u5bfe\u7b49\u306a\u6761\u7d04\u3092\u7de0\u7d50\u3057\u305f,\u3053\u306e\u5f8c\u65e5\u6e05\u6226\u4e89\u306b\u3088\u3063\u3066 \u65e5\u6e05\u9593\u306e\u6761\u7d04\u306f \u3044\u306f\u3086\u308b<\u4e0d\u5e73\u7b49>\u306a\u3082\u306e\u3068\u306a\u3063\u305f(\u65e5\u672c\u306b\u306e\u307f\u6cbb\u5916\u6cd5\u6a29\u3092\u8a8d\u3081 \u6e05\u570b\u306b\u95a2\u7a0e\u81ea\u4e3b\u6a29\u304c\u306a\u3044)\n1875,\u6c5f\u83ef\u5cf6\u4e8b\u4ef6,\u3053\u306e\u4e8b\u4ef6\u306e\u7d50\u679c \u65e5\u9bae\u4fee\u4ea4\u6761\u898f(\u4e0d\u5e73\u7b49\u6761\u7d04\u3068\u3055\u308c\u308b)\u3092\u7de0\u7d50,\u8ecd\u8266\u96f2\u63da\u53f7\u304c\u98f2\u6599\u6c34\u78ba\u4fdd\u306e\u305f\u3081\u6c5f\u83ef\u5cf6\u306b\u63a5\u8fd1\u3057\u305f\u969b \u7a81\u5982\u540c\u5cf6\u306e\u7832\u53f0\u3088\u308a\u5f37\u70c8\u306a\u7832\u6483\u3092\u53d7\u3051\u308b***\u96f2\u63da\u306f\u53cd\u6483\u3057\u9678\u6226\u968a\u3092\u4e0a\u9678\u3055\u305b\u7832\u53f0\u3092\u5360\u62e0 \u6b66\u5668\u3092\u6355\u7372\u3057\u3066\u9577\u5d0e\u3078\u5e30\u7740\n1877,\u897f\u5357\u6226\u4e89,\u620a\u8fb0\u6230\u722d\u3092\u6230\u3063\u305f\u58eb\u65cf\u305f\u3061\u304c \u660e\u6cbb\u7dad\u65b0\u306b\u4e0d\u6e80\u3092\u62b1\u304d \u897f\u90f7\u9686\u76db\u3092\u62c5\u3044\u3067\u8702\u8d77,\u897f\u90f7\u9686\u76db\u3092\u7dcf\u5927\u5c06\u3068\u3059\u308b\u53cd\u4e71\u8ecd\u306f\u653f\u5e9c\u8ecd\u306b\u93ae\u5727\u3055\u308c \u897f\u90f7\u306f\u81ea\u6c7a \u4ee5\u5f8c\u58eb\u65cf\u306e\u53cd\u4e71\u306f\u9014\u7d76\u3078 \u620a\u8fb0\u6226\u4e89\u304b\u3089\u5341\u5e74\u7d9a\u3044\u3066\u3090\u305f\u52d5\u4e71\u306f\u53ce\u675f\u3057\u305f\n1882,\u58ec\u5348\u306e\u5909,\u4ff8\u7d66\u306e\u9045\u914d\u3092\u304d\u3063\u304b\u3051\u3068\u3057\u305f\u65e7\u5175\u306e\u66b4\u52d5\u3092\u5927\u9662\u541b\u304c\u717d\u52d5(\u5927\u9662\u541b\u306f\u65e7\u5b88\u6d3e \u9594\u5983\u4e00\u65cf\u306f\u958b\u5316\u6d3e),\u65e5\u97d3\u4fee\u4ea4\u4ee5\u964d \u9594\u5983\u4e00\u65cf\u306e\u958b\u5316\u6d3e\u304c\u529b\u3092\u306e\u3070\u3057 \u65e5\u672c\u306e\u8fd1\u4ee3\u5316\u306b\u5023\u306f\u3093\u3068 \u5927\u898f\u6a21\u306a\u8996\u5bdf\u56e3\u3092\u6d3e\u9063\u3057\u305f\u308a \u65e5\u672c\u304b\u3089\u5800\u672c\u793c\u9020\u3092\u62db\u3044\u3066\u65b0\u5f0f\u8ecd\u968a\u3092\u7de8\u6210\u3059\u308b\u306a\u3069\u8ecd\u653f\u6539\u9769\u3092\u65ad\u884c\u3057\u3066\u3090\u305f\u304c \u65e7\u5175\u3068\u5927\u9662\u541b\u306e\u53cd\u4e71\u306b\u3088\u308a \u591a\u6570\u306e\u65e5\u672c\u4eba\u304c\u8650\u6bba\u3055\u308c\u65e5\u672c\u516c\u4f7f\u9928\u304c\u8972\u6483\u3055\u308c\u305f(\u5800\u672c\u793c\u9020\u3082\u6bba\u3055\u308c\u308b) \u6e05\u570b\u306f\u7d04\u4e94\u5343\u306e\u5175\u3092\u304a\u304f\u308a\u4e71\u306e\u93ae\u5727\u306b\u5f53\u308b\u3068\u3068\u3082\u306b \u9996\u9b41\u3067\u3042\u308b\u5927\u9662\u541b\u3092\u6e05\u570b\u306b\u62c9\u81f4\u3057\u6291\u7559**\u3053\u306e\u4e8b\u5909\u306e\u5584\u5f8c\u7d04\u5b9a\u3068\u3057\u3066 \u65e5\u672c\u30fb\u671d\u9bae\u9593\u306b\u6e08\u7269\u6d66\u6761\u7d04\u304c\u7d50\u3070\u308c \u671d\u9bae\u5074\u306f\u72af\u4eba\u306e\u53b3\u7f70 \u8ce0\u511f\u91d1 \u516c\u4f7f\u9928\u8b66\u5099\u306e\u305f\u3081\u4eac\u57ce\u306b\u65e5\u672c\u8ecd\u82e5\u5e72\u3092\u7f6e\u304f \u65e5\u672c\u306b\u8b1d\u7f6a\u4f7f\u3092\u6d3e\u9063\u3059\u308b\u3053\u3068\u3092\u7d04\u3057\u305f\n1885,\u5929\u6d25\u6761\u7d04,\u65e5\u672c\u304c\u652f\u63f4\u3057\u671d\u9bae\u306e\u72ec\u7acb\u3092\u3081\u3056\u3059\u52e2\u529b\u3068 \u6e05\u306e\u5f8c\u62bc\u3057\u3067\u305d\u308c\u3092\u963b\u3080\u52e2\u529b\u304c\u885d\u7a81\u3057 \u591a\u6570\u306e\u72a0\u7272\u304c\u51fa\u305f\u304c \u4e00\u61c9\u3053\u306e\u6761\u7d04\u3067\u7d50\u7740\u3059\u308b,\u65e5\u6e05\u4e21\u56fd\u306e\u671d\u9bae\u304b\u3089\u306e\u64a4\u5175 \u4eca\u5f8c\u65e5\u6e05\u4e21\u56fd\u304c\u3084\u3080\u306a\u304f\u51fa\u5175\u3059\u308b\u3068\u304d\u306f\u4e8b\u524d\u901a\u544a\u3059\u308b \u306a\u3069\u304c\u5b9a\u3081\u3089\u308c\u305f\n1894,\u65e5\u6e05\u6226\u4e89,\u671d\u9bae\u3067\u8fb2\u6c11\u4e00\u63c6\u304c\u653f\u6cbb\u66b4\u52d5\u5316(\u6771\u5b66\u515a\u306e\u4e71)***\u304c\u8d77\u7206\u5264\u3068\u306a\u308b,\u8c4a\u5cf6\u6c96\u6d77\u6226\u306f \u6211\u304c\u9023\u5408\u8266\u968a\u7b2c\u4e00\u904a\u6483\u968a\u5409\u91ce\u304c\u793c\u7832\u4ea4\u63db\u306e\u7528\u610f\u3092\u3057\u3066\u8fd1\u63a5\u3057\u305f\u306e\u306b\u5c0d\u3057 \u6e05\u570b\u8ecd\u8266\u6e08\u9060\u306e\u6226\u95d8\u6e96\u5099\u304a\u3088\u3073\u767a\u7832\u3088\u308a\u306f\u3058\u307e\u308b\n1895,\u4e0b\u95a2\u6761\u7d04,\u65e5\u6e05\u6226\u4e89\u306b\u6211\u570b\u304c\u52dd\u5229\u3057\u3066\u7d50\u3070\u308c\u305f\u6761\u7d04***\u4e09\u56fd\u5e72\u6e09\u3092\u53d7\u3051\u308b,\u4e00 \u6e05\u570b\u306f\u671d\u9bae\u570b\u304c\u5b8c\u5168\u7121\u6b20\u306e\u72ec\u7acb\u81ea\u4e3b\u306e\u570b\u3067\u3042\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059\u308b \u4e8c \u6e05\u570b\u306f\u907c\u6771\u534a\u5cf6 \u53f0\u6e7e\u5168\u5cf6\u53ca\u3073\u6f8e\u6e56\u5217\u5cf6\u3092\u6c38\u9060\u306b\u65e5\u672c\u306b\u5272\u8b72\u3059\u308b \u4e09 \u6e05\u570b\u306f\u8ecd\u8cbb\u8ce0\u511f\u91d1\u4e8c\u5104\u4e21\u3092\u652f\u6255\u3075 \u56db \u65e5\u6e05\u9593\u306e\u4e00\u5207\u306e\u6761\u7d04\u306f\u4ea4\u6230\u306e\u305f\u3081\u6d88\u6ec5\u3057\u305f\u306e\u3067\u65b0\u305f\u306b\u901a\u5546\u822a\u6d77\u6761\u7d04\u3092\u7d50\u3076 \u4e94 \u672c\u6761\u7d04\u6279\u51c6\u5f8c \u76f4\u3061\u306b\u4fd8\u865c\u3092\u8fd4\u9084\u3059\u308b \u6e05\u570b\u306f\u9001\u9084\u3055\u308c\u305f\u4fd8\u865c\u3092\u8650\u5f85\u3042\u308b\u3044\u306f\u51e6\u5211\u305b\u306c\u3053\u3068\n1899,\u7fa9\u548c\u56e3\u4e8b\u5909,\u65e5\u9732\u6226\u4e89\u306e\u539f\u56e0\u306e\u3072\u3068\u3064\u3068\u8a00\u3078\u308b,<\u6276\u6e05\u6ec5\u6d0b>\u3092\u9ad8\u5531\u3057\u3066\u6392\u5916\u904b\u52d5\u3092\u8d77\u3057 \u30ad\u30ea\u30b9\u30c8\u6559\u5f92\u6bba\u5bb3 \u6559\u4f1a \u9244\u9053 \u96fb\u7dda\u306a\u3069\u3092\u7834\u58ca\u3059\u308b \u5b97\u6559\u7684\u79d8\u5bc6\u7d50\u793e\u3067\u3042\u308b\u7fa9\u548c\u56e3\u306b\u6e05\u5175\u304c\u52a0\u306f\u308a \u5404\u570b\u516c\u4f7f\u9928\u304c\u5305\u56f2\u3055\u308c\u308b\u306b\u53ca\u3073 \u82f1\u56fd\u304b\u3089\u56db\u56de\u306b\u308f\u305f\u308a\u51fa\u5175\u8981\u8acb\u304c\u3055\u308c\u305f\u65e5\u672c\u3092\u4e3b\u529b\u3068\u3059\u308b\u516b\u30f6\u56fd\u9023\u5408\u8ecd\u304c \u5317\u4eac\u516c\u4f7f\u9928\u533a\u57df\u3092\u7fa9\u548c\u56e3\u30fb\u6e05\u5175\u306e\u5305\u56f2\u304b\u3089\u6551\u51fa \u7fa9\u548c\u56e3\u4e8b\u5909\u6700\u7d42\u8b70\u5b9a\u66f8\u306f1901\u5e74\u9023\u5408\u5341\u4e00\u30f6\u56fd\u3068\u6e05\u570b\u306e\u9593\u3067\u8abf\u5370\u3055\u308c \u6e05\u306f\u8ce0\u511f\u91d1\u306e\u652f\u6255\u3072\u306e\u4ed6 \u5404\u570b\u304c\u5341\u4e8c\u30f6\u6240\u306e\u5730\u70b9\u3092\u5360\u9818\u3059\u308b\u6a29\u5229\u3092\u627f\u8a8d \u3053\u306e\u99d0\u5175\u6a29\u306b\u3088\u3063\u3066\u6211\u570b\u306f\u8af8\u5916\u56fd\u3068\u3068\u3082\u306b\u652f\u90a3\u99d0\u5c6f\u8ecd\u3092\u7f6e\u304f\u3053\u3068\u306b\u306a\u3063\u305f(\u76e7\u6e9d\u6a4b\u3067\u4e2d\u56fd\u5074\u304b\u3089\u4e0d\u6cd5\u5c04\u6483\u3092\u53d7\u3051\u305f\u90e8\u968a\u3082 \u3053\u306e\u6761\u7d04\u306b\u3088\u308b\u99d0\u5175\u6a29\u306b\u57fa\u3065\u304d\u99d0\u5c6f\u3057\u3066\u3090\u305f)\n1900,\u30ed\u30b7\u30a2\u6e80\u6d32\u5360\u9818,\u7fa9\u548c\u56e3\u306e\u4e71\u306b\u4e57\u3058\u3066\u30ed\u30b7\u30a2\u306f\u30b7\u30d9\u30ea\u30a2\u65b9\u9762\u3068\u65c5\u9806\u304b\u3089\u5927\u5175\u3092\u6e80\u6d32\u306b\u9001\u308b***<\u9ed2\u7adc\u6c5f\u4e0a\u306e\u60b2\u5287>\u304c\u3053\u306e\u6642\u8d77\u3053\u308b,\u30ed\u30b7\u30a2\u306f\u7fa9\u548c\u56e3\u4e8b\u5909\u93ae\u5b9a\u5f8c\u3082\u7d04\u306b\u9055\u80cc\u3057\u3066\u64a4\u5175\u305b\u305a \u3084\u3046\u3084\u304f\u9732\u6e05\u9593\u306b\u6e80\u6d32\u9084\u4ed8\u5354\u7d04\u304c\u8abf\u5370\u3055\u308c\u308b\u3082 \u4e0d\u5c65\u884c\n1902,\u65e5\u82f1\u540c\u76df,\u65e5\u9732\u6226\u4e89\u306e\u52dd\u5229\u306b\u852d\u306e\u529b\u3068\u306a\u308b,\u4e00 \u65e5\u82f1\u4e21\u56fd\u306f\u6e05\u97d3\u4e21\u56fd\u306e\u72ec\u7acb\u3092\u627f\u8a8d\u3059\u308b \u3057\u304b\u3057\u82f1\u56fd\u306f\u6e05\u56fd\u3067 \u65e5\u672c\u306f\u6e05\u97d3\u4e21\u56fd\u3067\u653f\u6cbb\u30fb\u7d4c\u6e08\u4e0a\u683c\u6bb5\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u306e\u3067 \u305d\u308c\u3089\u306e\u5229\u76ca\u304c\u7b2c\u4e09\u56fd\u306e\u4fb5\u7565\u3084\u5185\u4e71\u3067\u4fb5\u8feb\u3055\u308c\u305f\u6642\u306f\u5fc5\u8981\u306a\u63aa\u7f6e\u3092\u3068\u308b \u4e8c \u65e5\u82f1\u306e\u4e00\u65b9\u304c\u3053\u306e\u5229\u76ca\u3092\u8b77\u308b\u305f\u3081\u7b2c\u4e09\u56fd\u3068\u6230\u3075\u6642\u306f\u4ed6\u306e\u4e00\u65b9\u306f\u53b3\u6b63\u4e2d\u7acb\u3092\u5b88\u308a \u4ed6\u56fd\u304c\u6575\u5074\u306b\u53c2\u6226\u3059\u308b\u306e\u3092\u9632\u3050 \u4e09 \u4ed6\u56fd\u304c\u540c\u76df\u56fd\u3068\u306e\u4ea4\u6230\u306b\u52a0\u306f\u308b\u6642\u306f \u4ed6\u306e\u540c\u76df\u56fd\u306f \u63f4\u52a9\u3092\u4e0e\u3078\u308b\n1904,\u65e5\u9732\u6226\u4e89,\u6975\u6771\u306e\u30ed\u30b7\u30a2\u8ecd\u306b\u52d5\u54e1\u4ee4\u304c \u6e80\u6d32\u306b\u306f\u6212\u53b3\u4ee4\u304c\u4e0b\u3055\u308c \u5bfe\u9732\u4ea4\u6e09\u306f\u6c7a\u88c2 \u6211\u570b\u306f\u570b\u4ea4\u65ad\u7d76\u3092\u9732\u570b\u306b\u901a\u544a,\u6211\u570b\u806f\u5408\u8266\u968a\u306b\u3088\u308b \u65c5\u9806\u6e2f\u5916\u306e\u653b\u6483 \u4ec1\u5ddd\u6c96\u306b\u3066\u6575\u8266\u306e\u6483\u6c88\u304c\u3042\u308a \u6b21\u306e\u65e5\u306b\u5ba3\u6226***\u907c\u967d\u30fb\u6c99\u6cb3\u306e\u4f1a\u6226\u306b\u52dd\u5229 \u6d77\u4e0a\u6a29\u306e\u7372\u5f97 \u65c5\u9806\u9665\u843d \u5949\u5929\u5360\u9818\u3092\u7d4c\u3066 \u65e5\u672c\u6d77\u6d77\u6226\u306b\u3066\u30d0\u30eb\u30c1\u30c3\u30af\u8266\u968a\u3092\u5168\u6ec5\u3055\u305b \u6a3a\u592a\u5168\u5cf6\u3092\u5360\u9818\n1905,\u30dd\u30fc\u30c4\u30de\u30b9\u6761\u7d04,\u7c73\u56fd\u30cb\u30e5\u30fc\u30fb\u30cf\u30f3\u30d7\u30b7\u30e3\u30fc\u5dde \u6211\u570b\u5168\u6a29\u306f\u5916\u76f8\u5c0f\u6751\u5bff\u592a\u90ce \u9732\u570b\u5168\u6a29\u306f\u524d\u8535\u76f8\u30a6\u30a3\u30c3\u30c6,\u4e00 \u9732\u570b\u306f \u65e5\u672c\u304c\u97d3\u570b\u3067\u653f\u6cbb \u8ecd\u4e8b \u7d4c\u6e08\u4e0a\u306e\u5353\u7d76\u3057\u305f\u5229\u76ca\u3092\u6709\u3057 \u304b\u3064\u5fc5\u8981\u306a\u6307\u5c0e \u4fdd\u8b77 \u76e3\u7406\u3092\u884c\u3075\u6a29\u5229\u3092\u627f\u8a8d\u3059 \u4e8c \u4e21\u56fd\u306f\u5341\u516b\u30f6\u6708\u4ee5\u5185\u306b\u6e80\u6d32\u3088\u308a\u64a4\u5175\u3059 \u4e09 \u9732\u570b\u306f\u907c\u6771\u534a\u5cf6\u79df\u501f\u6a29\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u3053\u308c\u306b\u3064\u304d\u4e21\u56fd\u306f\u6e05\u570b\u306e\u627f\u8afe\u3092\u5f97\u308b\u3053\u3068 \u56db \u9732\u570b\u306f\u6771\u652f\u9244\u9053\u5357\u6e80\u6d32\u652f\u7dda(\u9577\u6625\u30fb\u65c5\u9806\u9593)\u3092\u4ed8\u5c5e\u306e\u70ad\u9271\u3068\u5171\u306b\u65e5\u672c\u306b\u8b72\u6e21\u3059 \u4e94 \u9732\u570b\u306f\u5317\u7def\u4e94\u5341\u5ea6\u4ee5\u5357\u306e\u6a3a\u592a\u3092\u65e5\u672c\u306b\u8b72\u6e21\u3059 (\u6211\u570b\u306f\u8ce0\u511f\u91d1\u8981\u6c42\u3092\u653e\u68c4)\n1910,\u65e5\u97d3\u4f75\u5408,\u674e\u6c0f\u671d\u9bae\u304c\u4e94\u767e\u6709\u4f59\u5e74\u306e\u6b74\u53f2\u3092\u9589\u3058\u308b,\u65e5\u9732\u6226\u4e89\u5f8c \u97d3\u570b\u306f\u65e5\u672c\u306b\u4fdd\u8b77\u5316\u3055\u308c\u308b\u9053\u3092\u9032\u3080\u304c \u4f0a\u85e4\u535a\u6587\u304c\u6697\u6bba\u3055\u308c\u308b\u3084 \u97d3\u570b\u4f75\u5408\u8ad6\u304c\u9ad8\u307e\u308b\n1914,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226,\u5927\u6b633\u5e74,\u30dc\u30b9\u30cb\u30a2\u306e\u9996\u90fd\u30b5\u30e9\u30a8\u30dc\u3067\u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u7687\u592a\u5b50\u592b\u59bb\u304c\u30bb\u30eb\u30d3\u30a2\u306e\u4e00\u9752\u5e74\u306b\u6697\u6bba\u3055\u308c\u308b\u3068 \u30aa\u30fc\u30b9\u30c8\u30ea\u30a2\u304c\u30bb\u30eb\u30d3\u30a2\u306b\u5ba3\u6226 \u30c9\u30a4\u30c4\u304c\u30ed\u30b7\u30a2\u306b\u5ba3\u6226 \u4ecf\u30fb\u82f1\u3082\u5c0d\u72ec\u5ba3\u6226\n1915,\u65e5\u83ef\u6761\u7d04,\u3044\u306f\u3086\u308b<\u4e8c\u5341\u4e00\u30f6\u6761\u306e\u8981\u6c42>,\u3082\u3068\u3082\u3068\u652f\u90a3\u3068\u4ea4\u306f\u3055\u308c\u3066\u3090\u305f\u7d04\u5b9a\u3092\u6b50\u6d32\u5217\u56fd\u306e\u5e72\u6e09\u306a\u3069\u3067\u7834\u58ca\u3055\u308c\u306a\u3044\u3084\u3046\u306b \u62d8\u675f\u529b\u306e\u3042\u308b\u6761\u7d04\u306b\u3059\u308b\u305f\u3081\u306e\u3082\u306e\u3067 \u3082\u3068\u3082\u3068\u306e\u4e03\u30f6\u6761\u306f\u5e0c\u671b\u6761\u9805\u3067\u3042\u308a \u7d50\u5c40\u6761\u7d04\u3068\u3057\u3066\u7d50\u3070\u308c\u305f\u306e\u306f\u5341\u516d\u30f6\u6761\u3067\u3042\u3063\u305f\u304c \u6761\u7d04\u3092\u7d50\u3093\u3060\u4e2d\u83ef\u6c11\u56fd\u306f \u65e5\u672c\u306b\u5f37\u8feb\u3055\u308c\u3066\u7d50\u3093\u3060\u306e\u3060\u3068\u5185\u5916\u306b\u5ba3\u4f1d\u3057 1922\u5e74\u306b\u306f\u6761\u7d04\u3068\u3057\u3066\u5341\u30f6\u6761\u304c\u6b98\u5b58\u3059\u308b\u3060\u3051\u3068\u306a\u308b\u4e2d \u4e2d\u83ef\u6c11\u56fd\u56fd\u4f1a\u306f \u6761\u7d04\u306e\u7121\u52b9\u3092\u5ba3\u8a00 \u6fc0\u70c8\u306a\u53cd\u65e5\u306e\u4e2d\u3067 \u305d\u308c\u3089\u306e\u6761\u7d04\u3082\u4e8b\u5b9f\u4e0a \u7a7a\u6587\u5316\u3057\u305f\n1917,\u77f3\u4e95\u30fb\u30e9\u30f3\u30b7\u30f3\u30b0\u5354\u5b9a,\u7b2c\u4e00\u6b21\u4e16\u754c\u5927\u6226\u4e2d\u65e5\u7c73\u9593\u306b\u7d50\u3070\u308c\u305f\u5354\u5b9a,\u7c73\u56fd\u304c\u57f7\u62d7\u306b\u9580\u6238\u958b\u653e\u4e3b\u7fa9\u3092\u5531\u9053\u3057 \u65e5\u672c\u306e\u6e80\u8499\u9032\u51fa\u3092\u63a3\u8098\u305b\u3093\u3068\u3059\u308b\u52d5\u304d\u304c\u3042\u3063\u305f\u305f\u3081 \u3042\u3089\u305f\u3081\u3066\u652f\u90a3\u306b\u304a\u3051\u308b\u65e5\u672c\u306e\u7279\u6b8a\u5730\u4f4d\u306b\u95a2\u3057\u3066 \u7c73\u56fd\u306e\u627f\u8a8d\u3092\u78ba\u4fdd\u305b\u3093\u3068\u3044\u3075\u8981\u8acb\u304c\u3042\u3063\u305f\u30fc\u30fc\u5ba3\u8a00\u306e\u524d\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5317\u7c73\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f \u9818\u571f\u76f8\u63a5\u8fd1\u3059\u308b\u56fd\u5bb6\u306e\u9593\u306b\u306f\u7279\u6b8a\u306e\u95dc\u4fc2\u3092\u751f\u305a\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u5f93\u3066\u5408\u8846\u56fd\u653f\u5e9c\u306f\u65e5\u672c\u304c\u652f\u90a3\u306b\u65bc\u3066\u7279\u6b8a\u306e\u5229\u76ca\u3092\u6709\u3059\u308b\u3053\u3068\u3092\u627f\u8a8d\u3059 \u65e5\u672c\u306e\u6240\u9818\u306b\u63a5\u58cc\u3059\u308b\u5730\u65b9\u306b\u65bc\u3066\u7279\u306b\u7136\u308a\u3068\u3059>\u30fc\u30fc\u5f8c\u6bb5\u306f<\u65e5\u672c\u56fd\u53ca\u5408\u8846\u56fd\u4e21\u56fd\u653f\u5e9c\u306f\u6beb\u3082\u652f\u90a3\u306e\u72ec\u7acb\u53c8\u306f\u9818\u571f\u4fdd\u5168\u3092\u4fb5\u5bb3\u3059\u308b\u306e\u76ee\u7684\u3092\u6709\u3059\u308b\u3082\u306e\u306b\u975e\u3056\u308b\u3053\u3068\u3092\u58f0\u660e\u3059 \u304b\u3064\u4e21\u56fd\u653f\u5e9c\u306f\u5e38\u306b\u652f\u90a3\u306b\u65bc\u3066\u6240\u8b02\u9580\u6238\u958b\u653e\u53c8\u306f\u5546\u5de5\u696d\u306b\u5c0d\u3059\u308b\u6a5f\u4f1a\u5747\u7b49\u306e\u4e3b\u7fa9\u3092\u652f\u6301\u3059\u308b\u3053\u3068\u3092\u58f0\u660e\u3059>"));}),_1El=new T(function(){return B(_1Ea(_1Ek));}),_1Em=new T(function(){return B(_aj(_1E5,_1El));}),_1En=function(_1Eo,_1Ep){var _1Eq=E(_1Eo);if(!_1Eq._){return __Z;}else{var _1Er=E(_1Ep);return (_1Er._==0)?__Z:new T2(1,new T2(0,new T(function(){return E(_1Eq.a).a;}),_1Er.a),new T(function(){return B(_1En(_1Eq.b,_1Er.b));}));}},_1Es=new T(function(){return eval("(function(k) {localStorage.removeItem(k);})");}),_1Et=new T(function(){return B(unCStr("tail"));}),_1Eu=new T(function(){return B(_rj(_1Et));}),_1Ev=new T(function(){return eval("(function(k,v) {localStorage.setItem(k,v);})");}),_1Ew=new T2(1,_2A,_Z),_1Ex=function(_1Ey){var _1Ez=E(_1Ey);if(!_1Ez._){return E(_1Ew);}else{var _1EA=new T(function(){return B(_H(0,E(_1Ez.a),new T(function(){return B(_1Ex(_1Ez.b));})));});return new T2(1,_2z,_1EA);}},_1EB=function(_1EC){var _1ED=E(_1EC);if(!_1ED._){return E(_1Ew);}else{var _1EE=new T(function(){var _1EF=E(_1ED.a),_1EG=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1EH){return new F(function(){return _1Dg(_1EF.a,_1EH);});},new T2(1,function(_1EI){return new F(function(){return _1Dg(_1EF.b,_1EI);});},_Z)),new T2(1,_F,new T(function(){return B(_1EB(_1ED.b));}))));});return new T2(1,_G,_1EG);});return new T2(1,_2z,_1EE);}},_1EJ=function(_1EK){var _1EL=E(_1EK);if(!_1EL._){return E(_1Ew);}else{var _1EM=new T(function(){return B(_H(0,E(_1EL.a),new T(function(){return B(_1EJ(_1EL.b));})));});return new T2(1,_2z,_1EM);}},_1EN=function(_1EO){var _1EP=E(_1EO);if(!_1EP._){return E(_1Ew);}else{var _1EQ=new T(function(){var _1ER=E(_1EP.a),_1ES=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1ET){return new F(function(){return _1Dg(_1ER.a,_1ET);});},new T2(1,function(_1EU){return new F(function(){return _1Dg(_1ER.b,_1EU);});},_Z)),new T2(1,_F,new T(function(){return B(_1EN(_1EP.b));}))));});return new T2(1,_G,_1ES);});return new T2(1,_2z,_1EQ);}},_1EV=new T(function(){return B(unCStr("True"));}),_1EW=new T(function(){return B(unCStr("False"));}),_1EX=function(_1EY){return E(E(_1EY).b);},_1EZ=function(_1F0,_1F1,_1F2){var _1F3=new T(function(){var _1F4=E(_1F2);if(!_1F4._){return __Z;}else{var _1F5=_1F4.b,_1F6=E(_1F4.a),_1F7=E(_1F6.a);if(_1F7<_1F0){var _1F8=function(_1F9){while(1){var _1Fa=B((function(_1Fb){var _1Fc=E(_1Fb);if(!_1Fc._){return __Z;}else{var _1Fd=_1Fc.b,_1Fe=E(_1Fc.a);if(E(_1Fe.a)<_1F0){_1F9=_1Fd;return __continue;}else{return new T2(1,_1Fe,new T(function(){return B(_1F8(_1Fd));}));}}})(_1F9));if(_1Fa!=__continue){return _1Fa;}}};return B(_1Ff(B(_1F8(_1F5))));}else{var _1Fg=new T(function(){var _1Fh=function(_1Fi){while(1){var _1Fj=B((function(_1Fk){var _1Fl=E(_1Fk);if(!_1Fl._){return __Z;}else{var _1Fm=_1Fl.b,_1Fn=E(_1Fl.a);if(E(_1Fn.a)<_1F0){_1Fi=_1Fm;return __continue;}else{return new T2(1,_1Fn,new T(function(){return B(_1Fh(_1Fm));}));}}})(_1Fi));if(_1Fj!=__continue){return _1Fj;}}};return B(_1Fh(_1F5));});return B(_1EZ(_1F7,_1F6.b,_1Fg));}}}),_1Fo=E(_1F2);if(!_1Fo._){return new F(function(){return _x(_Z,new T2(1,new T2(0,_1F0,_1F1),_1F3));});}else{var _1Fp=_1Fo.b,_1Fq=E(_1Fo.a),_1Fr=E(_1Fq.a);if(_1Fr>=_1F0){var _1Fs=function(_1Ft){while(1){var _1Fu=B((function(_1Fv){var _1Fw=E(_1Fv);if(!_1Fw._){return __Z;}else{var _1Fx=_1Fw.b,_1Fy=E(_1Fw.a);if(E(_1Fy.a)>=_1F0){_1Ft=_1Fx;return __continue;}else{return new T2(1,_1Fy,new T(function(){return B(_1Fs(_1Fx));}));}}})(_1Ft));if(_1Fu!=__continue){return _1Fu;}}};return new F(function(){return _x(B(_1Ff(B(_1Fs(_1Fp)))),new T2(1,new T2(0,_1F0,_1F1),_1F3));});}else{var _1Fz=new T(function(){var _1FA=function(_1FB){while(1){var _1FC=B((function(_1FD){var _1FE=E(_1FD);if(!_1FE._){return __Z;}else{var _1FF=_1FE.b,_1FG=E(_1FE.a);if(E(_1FG.a)>=_1F0){_1FB=_1FF;return __continue;}else{return new T2(1,_1FG,new T(function(){return B(_1FA(_1FF));}));}}})(_1FB));if(_1FC!=__continue){return _1FC;}}};return B(_1FA(_1Fp));});return new F(function(){return _x(B(_1EZ(_1Fr,_1Fq.b,_1Fz)),new T2(1,new T2(0,_1F0,_1F1),_1F3));});}}},_1Ff=function(_1FH){var _1FI=E(_1FH);if(!_1FI._){return __Z;}else{var _1FJ=_1FI.b,_1FK=E(_1FI.a),_1FL=_1FK.a,_1FM=new T(function(){var _1FN=E(_1FJ);if(!_1FN._){return __Z;}else{var _1FO=_1FN.b,_1FP=E(_1FN.a),_1FQ=E(_1FP.a),_1FR=E(_1FL);if(_1FQ<_1FR){var _1FS=function(_1FT){while(1){var _1FU=B((function(_1FV){var _1FW=E(_1FV);if(!_1FW._){return __Z;}else{var _1FX=_1FW.b,_1FY=E(_1FW.a);if(E(_1FY.a)<_1FR){_1FT=_1FX;return __continue;}else{return new T2(1,_1FY,new T(function(){return B(_1FS(_1FX));}));}}})(_1FT));if(_1FU!=__continue){return _1FU;}}};return B(_1Ff(B(_1FS(_1FO))));}else{var _1FZ=new T(function(){var _1G0=function(_1G1){while(1){var _1G2=B((function(_1G3){var _1G4=E(_1G3);if(!_1G4._){return __Z;}else{var _1G5=_1G4.b,_1G6=E(_1G4.a);if(E(_1G6.a)<_1FR){_1G1=_1G5;return __continue;}else{return new T2(1,_1G6,new T(function(){return B(_1G0(_1G5));}));}}})(_1G1));if(_1G2!=__continue){return _1G2;}}};return B(_1G0(_1FO));});return B(_1EZ(_1FQ,_1FP.b,_1FZ));}}}),_1G7=E(_1FJ);if(!_1G7._){return new F(function(){return _x(_Z,new T2(1,_1FK,_1FM));});}else{var _1G8=_1G7.b,_1G9=E(_1G7.a),_1Ga=E(_1G9.a),_1Gb=E(_1FL);if(_1Ga>=_1Gb){var _1Gc=function(_1Gd){while(1){var _1Ge=B((function(_1Gf){var _1Gg=E(_1Gf);if(!_1Gg._){return __Z;}else{var _1Gh=_1Gg.b,_1Gi=E(_1Gg.a);if(E(_1Gi.a)>=_1Gb){_1Gd=_1Gh;return __continue;}else{return new T2(1,_1Gi,new T(function(){return B(_1Gc(_1Gh));}));}}})(_1Gd));if(_1Ge!=__continue){return _1Ge;}}};return new F(function(){return _x(B(_1Ff(B(_1Gc(_1G8)))),new T2(1,_1FK,_1FM));});}else{var _1Gj=new T(function(){var _1Gk=function(_1Gl){while(1){var _1Gm=B((function(_1Gn){var _1Go=E(_1Gn);if(!_1Go._){return __Z;}else{var _1Gp=_1Go.b,_1Gq=E(_1Go.a);if(E(_1Gq.a)>=_1Gb){_1Gl=_1Gp;return __continue;}else{return new T2(1,_1Gq,new T(function(){return B(_1Gk(_1Gp));}));}}})(_1Gl));if(_1Gm!=__continue){return _1Gm;}}};return B(_1Gk(_1G8));});return new F(function(){return _x(B(_1EZ(_1Ga,_1G9.b,_1Gj)),new T2(1,_1FK,_1FM));});}}}},_1Gr=function(_){return new F(function(){return jsMkStdout();});},_1Gs=new T(function(){return B(_3d(_1Gr));}),_1Gt=new T(function(){return B(_PU("Browser.hs:82:24-56|(Right j)"));}),_1Gu=function(_1Gv){var _1Gw=jsParseJSON(toJSStr(E(_1Gv)));return (_1Gw._==0)?E(_1Gt):E(_1Gw.a);},_1Gx=0,_1Gy=function(_1Gz,_1GA,_1GB,_1GC,_1GD){var _1GE=E(_1GD);if(!_1GE._){var _1GF=new T(function(){var _1GG=B(_1Gy(_1GE.a,_1GE.b,_1GE.c,_1GE.d,_1GE.e));return new T2(0,_1GG.a,_1GG.b);});return new T2(0,new T(function(){return E(E(_1GF).a);}),new T(function(){return B(_78(_1GA,_1GB,_1GC,E(_1GF).b));}));}else{return new T2(0,new T2(0,_1GA,_1GB),_1GC);}},_1GH=function(_1GI,_1GJ,_1GK,_1GL,_1GM){var _1GN=E(_1GL);if(!_1GN._){var _1GO=new T(function(){var _1GP=B(_1GH(_1GN.a,_1GN.b,_1GN.c,_1GN.d,_1GN.e));return new T2(0,_1GP.a,_1GP.b);});return new T2(0,new T(function(){return E(E(_1GO).a);}),new T(function(){return B(_6h(_1GJ,_1GK,E(_1GO).b,_1GM));}));}else{return new T2(0,new T2(0,_1GJ,_1GK),_1GM);}},_1GQ=function(_1GR,_1GS){var _1GT=E(_1GR);if(!_1GT._){var _1GU=_1GT.a,_1GV=E(_1GS);if(!_1GV._){var _1GW=_1GV.a;if(_1GU<=_1GW){var _1GX=B(_1GH(_1GW,_1GV.b,_1GV.c,_1GV.d,_1GV.e)),_1GY=E(_1GX.a);return new F(function(){return _78(_1GY.a,_1GY.b,_1GT,_1GX.b);});}else{var _1GZ=B(_1Gy(_1GU,_1GT.b,_1GT.c,_1GT.d,_1GT.e)),_1H0=E(_1GZ.a);return new F(function(){return _6h(_1H0.a,_1H0.b,_1GZ.b,_1GV);});}}else{return E(_1GT);}}else{return E(_1GS);}},_1H1=function(_1H2,_1H3){var _1H4=E(_1H2),_1H5=E(_1H3);if(!_1H5._){var _1H6=_1H5.b,_1H7=_1H5.c,_1H8=_1H5.d,_1H9=_1H5.e;switch(B(_65(_1H4,_1H6))){case 0:return new F(function(){return _6h(_1H6,_1H7,B(_1H1(_1H4,_1H8)),_1H9);});break;case 1:return new F(function(){return _1GQ(_1H8,_1H9);});break;default:return new F(function(){return _78(_1H6,_1H7,_1H8,B(_1H1(_1H4,_1H9)));});}}else{return new T0(1);}},_1Ha=function(_1Hb,_1Hc){while(1){var _1Hd=E(_1Hb);if(!_1Hd._){return E(_1Hc);}else{var _1He=B(_1H1(new T2(1,_1Hd.a,_1ri),_1Hc));_1Hb=_1Hd.b;_1Hc=_1He;continue;}}},_1Hf=function(_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1Hw,_1Hx,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_1HL,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1HS,_1HT,_1HU,_1HV,_1HW,_1HX,_1HY,_1HZ,_1I0,_){var _1I1={_:0,a:E(_1HS),b:E(_1HT),c:E(_1HU),d:E(_1HV),e:E(_1HW),f:E(_1HX),g:E(_1HY),h:E(_1HZ)},_1I2=new T2(0,_1HP,_1HQ),_1I3=new T2(0,_1HD,_1HE),_1I4=new T2(0,_1Hw,_1Hx),_1I5={_:0,a:E(_1Hl),b:E(_1Hm),c:E(_1Hn),d:_1Ho,e:_1Hp,f:_1Hq,g:E(_1Hr),h:_1Hs,i:E(_1Ht),j:E(_1Hu),k:E(_1Hv)},_1I6={_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:_1HK,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};if(!E(_1HX)){if(!E(_1HT)){var _1I7=function(_1I8){if(!E(_1HV)){if(!E(_1HZ)){return _1I6;}else{var _1I9=function(_,_1Ia,_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In,_1Io,_1Ip,_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF,_1IG){var _1IH=function(_){var _1II=function(_){var _1IJ=function(_){var _1IK=B(_1Cz(_1Gs,new T2(1,_aI,new T(function(){return B(_cp(_1Ii,_1Dv));})),_)),_1IL=function(_){var _1IM=B(_1Cz(_1Gs,B(_H(0,_1HI,_Z)),_)),_1IN=B(_1Cz(_1Gs,B(_2C(_1Dj,_1Ig,_Z)),_)),_1IO=function(_){var _1IP=B(_1b7(_1D4,_1Ih,_)),_1IQ=_1IP,_1IR=E(_1Hg),_1IS=_1IR.a,_1IT=_1IR.b,_1IU=new T(function(){return B(_1s8(E(_1Hk)));}),_1IV=new T(function(){var _1IW=E(_1IU),_1IX=E(_1Ia),_1IY=_1IX.a,_1IZ=_1IX.b,_1J0=function(_1J1,_1J2){var _1J3=E(_1J1),_1J4=E(_1J2),_1J5=E(_1IY);if(_1J3<=_1J5){if(_1J5<=_1J3){var _1J6=E(_1IZ);if(_1J4<=_1J6){if(_1J6<=_1J4){var _1J7=4;}else{var _1J7=0;}var _1J8=_1J7;}else{var _1J8=1;}var _1J9=_1J8;}else{var _1J9=2;}var _1Ja=_1J9;}else{var _1Ja=3;}var _1Jb=function(_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj,_1Jk,_1Jl){switch(E(_1Ja)){case 0:if(!E(_1Ic)){var _1Jm=new T2(0,_1IC,_1ID);}else{var _1Jm=new T2(0,_1IC,_1Dz);}var _1Jn=_1Jm;break;case 1:if(E(_1Ic)==1){var _1Jo=new T2(0,_1IC,_1ID);}else{var _1Jo=new T2(0,_1IC,_1Gx);}var _1Jn=_1Jo;break;case 2:if(E(_1Ic)==2){var _1Jp=new T2(0,_1IC,_1ID);}else{var _1Jp=new T2(0,_1IC,_1D3);}var _1Jn=_1Jp;break;case 3:if(E(_1Ic)==3){var _1Jq=new T2(0,_1IC,_1ID);}else{var _1Jq=new T2(0,_1IC,_1D2);}var _1Jn=_1Jq;break;default:if(E(_1Ic)==4){var _1Jr=new T2(0,_1IC,_1ID);}else{var _1Jr=new T2(0,_1IC,_1Gx);}var _1Jn=_1Jr;}var _1Js=B(_1oT(_1Gx,_1Jj,_1Io,{_:0,a:E(_1Jc),b:E(_1Jd),c:E(_1Je),d:_1Jf,e:_1Jg,f:_1Jh,g:E(_1Ji),h:E(E(_1IQ).b),i:E(_1Jj),j:E(_1Jk),k:E(_1Jl)},_1Il,_1Im,_1In,_1Io,_1Ip,_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1Jn,_1IE,_1IF,_1IG)),_1Jt=_1Js.a,_1Ju=_1Js.b,_1Jv=_1Js.c,_1Jw=_1Js.d,_1Jx=_1Js.e,_1Jy=_1Js.f,_1Jz=_1Js.g,_1JA=_1Js.h,_1JB=_1Js.i,_1JC=_1Js.j,_1JD=_1Js.k,_1JE=_1Js.l,_1JF=_1Js.m,_1JG=_1Js.n,_1JH=_1Js.o,_1JI=_1Js.q,_1JJ=_1Js.r,_1JK=_1Js.s,_1JL=_1Js.t,_1JM=_1Js.u,_1JN=_1Js.v,_1JO=E(_1Js.p);if(!_1JO._){return {_:0,a:E(_1Jt),b:E(_1Ju),c:E(_1Jv),d:E(_1Jw),e:E(_1Jx),f:E(_1Jy),g:E(_1Jz),h:E(_1JA),i:_1JB,j:_1JC,k:_1JD,l:_1JE,m:E(_1JF),n:_1JG,o:E(_1JH),p:E(_Z),q:_1JI,r:E(_1JJ),s:E(_1JK),t:_1JL,u:E(_1JM),v:E(_1JN)};}else{var _1JP=B(_qy(_1Jj,0))-2|0,_1JQ=function(_1JR){var _1JS=E(_1Jt);return {_:0,a:E({_:0,a:E(_1JS.a),b:E(_1JS.b),c:E(_1JS.c),d:_1JS.d,e:_1JS.e,f:_1JS.f,g:E(_Z),h:_1JS.h,i:E(_1JS.i),j:E(_1JS.j),k:E(_1JS.k)}),b:E(_1Ju),c:E(_1Jv),d:E(B(_x(B(_0(_Z,B(_1Ha(B(_aj(_1EX,_1JO)),B(_9T(_1Jw)))))),new T(function(){return B(_aj(_1C4,_1JO));},1)))),e:E(_1Jx),f:E(_1Jy),g:E(_1Jz),h:E(_1JA),i:_1JB,j:_1JC,k:_1JD,l:_1JE,m:E(_1JF),n:_1JG,o:E(_1JH),p:E(_Z),q:_1JI,r:E(B(_x(_1JJ,new T2(1,_1JI,_Z)))),s:E(_1JK),t:_1JL,u:E(_1JM),v:E(_1JN)};};if(_1JP>0){if(!B(_vl(B(_1BL(_1JP,_1Jj)),_1D1))){return {_:0,a:E(_1Jt),b:E(_1Ju),c:E(_1Jv),d:E(_1Jw),e:E(_1Jx),f:E(_1Jy),g:E(_1Jz),h:E(_1JA),i:_1JB,j:_1JC,k:_1JD,l:_1JE,m:E(_1JF),n:_1JG,o:E(_1JH),p:E(_1JO),q:_1JI,r:E(_1JJ),s:E(_1JK),t:_1JL,u:E(_1JM),v:E(_1JN)};}else{return new F(function(){return _1JQ(_);});}}else{if(!B(_vl(_1Jj,_1D1))){return {_:0,a:E(_1Jt),b:E(_1Ju),c:E(_1Jv),d:E(_1Jw),e:E(_1Jx),f:E(_1Jy),g:E(_1Jz),h:E(_1JA),i:_1JB,j:_1JC,k:_1JD,l:_1JE,m:E(_1JF),n:_1JG,o:E(_1JH),p:E(_1JO),q:_1JI,r:E(_1JJ),s:E(_1JK),t:_1JL,u:E(_1JM),v:E(_1JN)};}else{return new F(function(){return _1JQ(_);});}}}};if(E(_1IW)==32){var _1JT=B(_1y1(_1J3,_1J4,_1J5,_1IZ,_1Ib,_1Ja,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik)),_1JU=E(_1JT.a),_1JV=B(_1Bm(_1JU.a,E(_1JU.b),_1JT.b,_1JT.c,_1JT.d,_1JT.e,_1JT.f,_1JT.g,_1JT.h,_1JT.i,_1JT.j,_1JT.k));return new F(function(){return _1Jb(_1JV.a,_1JV.b,_1JV.c,_1JV.d,_1JV.e,_1JV.f,_1JV.g,_1JV.i,_1JV.j,_1JV.k);});}else{var _1JW=B(_1y1(_1J3,_1J4,_1J5,_1IZ,_1Ib,_1Ja,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik));return new F(function(){return _1Jb(_1JW.a,_1JW.b,_1JW.c,_1JW.d,_1JW.e,_1JW.f,_1JW.g,_1JW.i,_1JW.j,_1JW.k);});}};switch(E(_1IW)){case 72:var _1JX=E(_1IZ);if(0<=(_1JX-1|0)){return B(_1J0(_1IY,_1JX-1|0));}else{return B(_1J0(_1IY,_1JX));}break;case 75:var _1JY=E(_1IY);if(0<=(_1JY-1|0)){return B(_1J0(_1JY-1|0,_1IZ));}else{return B(_1J0(_1JY,_1IZ));}break;case 77:var _1JZ=E(_1IY);if(E(_1Hw)!=(_1JZ+1|0)){return B(_1J0(_1JZ+1|0,_1IZ));}else{return B(_1J0(_1JZ,_1IZ));}break;case 80:var _1K0=E(_1IZ);if(E(_1Hx)!=(_1K0+1|0)){return B(_1J0(_1IY,_1K0+1|0));}else{return B(_1J0(_1IY,_1K0));}break;case 104:var _1K1=E(_1IY);if(0<=(_1K1-1|0)){return B(_1J0(_1K1-1|0,_1IZ));}else{return B(_1J0(_1K1,_1IZ));}break;case 106:var _1K2=E(_1IZ);if(E(_1Hx)!=(_1K2+1|0)){return B(_1J0(_1IY,_1K2+1|0));}else{return B(_1J0(_1IY,_1K2));}break;case 107:var _1K3=E(_1IZ);if(0<=(_1K3-1|0)){return B(_1J0(_1IY,_1K3-1|0));}else{return B(_1J0(_1IY,_1K3));}break;case 108:var _1K4=E(_1IY);if(E(_1Hw)!=(_1K4+1|0)){return B(_1J0(_1K4+1|0,_1IZ));}else{return B(_1J0(_1K4,_1IZ));}break;default:return B(_1J0(_1IY,_1IZ));}}),_1K5=B(_1bB(_1IS,_1IT,_1Hh,_1Hi,_1Hj,_1IV,_)),_1K6=_1K5,_1K7=E(_1IU),_1K8=function(_,_1K9){var _1Ka=function(_1Kb){var _1Kc=B(_1Cz(_1Gs,B(_cv(_1K9)),_)),_1Kd=E(_1K6),_1Ke=_1Kd.d,_1Kf=_1Kd.e,_1Kg=_1Kd.f,_1Kh=_1Kd.g,_1Ki=_1Kd.i,_1Kj=_1Kd.j,_1Kk=_1Kd.k,_1Kl=_1Kd.l,_1Km=_1Kd.m,_1Kn=_1Kd.n,_1Ko=_1Kd.o,_1Kp=_1Kd.p,_1Kq=_1Kd.q,_1Kr=_1Kd.r,_1Ks=_1Kd.t,_1Kt=_1Kd.v,_1Ku=E(_1Kd.u),_1Kv=_1Ku.a,_1Kw=_1Ku.d,_1Kx=_1Ku.e,_1Ky=_1Ku.f,_1Kz=_1Ku.g,_1KA=_1Ku.h,_1KB=E(_1Kd.a),_1KC=_1KB.c,_1KD=_1KB.f,_1KE=_1KB.g,_1KF=_1KB.h,_1KG=E(_1Kd.h),_1KH=E(_1Kd.s),_1KI=function(_1KJ){var _1KK=function(_1KL){if(_1KL!=E(_1CU)){var _1KM=B(_aW(_1kz,_1KL)),_1KN=_1KM.a,_1KO=E(_1KM.b),_1KP=B(_1fN(_1KN,_1KO,new T(function(){return B(_aW(_1mE,_1KL));})));return new F(function(){return _1Hf(_1IR,_1Hh,_1Hi,_1Hj,_1CT,B(_aW(_1kK,_1KL)),_1KP,_1KC,B(_aW(_1kX,_1KL)),32,_1KL,_1KE,_1KF,B(_x(_1KB.i,new T2(1,_1CS,new T(function(){return B(_H(0,_1KD,_Z));})))),B(_1Cd(_1CR,_1KP)),_B2,_1KN,_1KO,_Z,_1Ke,_1Kf,_1Kg,_1Kh,_1KG.a,_1KG.b,_1Ki,_1Kj,_1Kk, -1,_1Km,_1Kn,_1Ko,_1Kp,_1Kq,_1Kr,_1KH.a,_1KH.b,_1Ks,_B2,_B2,_B2,_1Kw,_1Kx,_1Ky,_1Kz,_1KA,_1Kt,_);});}else{var _1KQ=__app1(E(_rn),_1IT),_1KR=B(A2(_ro,_1IS,_)),_1KS=B(A(_qT,[_1IS,_n8,_1CN,_1CP,_1CO,_])),_1KT=B(A(_qT,[_1IS,_n8,_1CN,_1CM,_1DA,_])),_1KU=B(A(_qT,[_1IS,_n8,_1Dz,_1Dy,_1Dx,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1kB),b:E(_1Dw),c:E(_1KC),d:E(_1Da),e:32,f:0,g:E(_1KE),h:_1KF,i:E(_Z),j:E(_1KB.j),k:E(_B2)}),b:E(_1km),c:E(_1Kd.c),d:E(_1Ke),e:E(_1Kf),f:E(_1Kg),g:E(_1Kh),h:E(_1KG),i:_1Ki,j:_1Kj,k:_1Kk,l:_1Kl,m:E(_1Km),n:_1Kn,o:E(_1Ko),p:E(_1Kp),q:_1Kq,r:E(_1Kr),s:E(_1KH),t:_1Ks,u:E({_:0,a:E(_1Kv),b:E(_B3),c:E(_B2),d:E(_1Kw),e:E(_1Kx),f:E(_1Ky),g:E(_1Kz),h:E(_1KA)}),v:E(_1Kt)};});}};if(_1Kl>=0){return new F(function(){return _1KK(_1Kl);});}else{return new F(function(){return _1KK(_1KD+1|0);});}};if(!E(_1Kv)){if(E(_1K7)==110){return new F(function(){return _1KI(_);});}else{return _1Kd;}}else{return new F(function(){return _1KI(_);});}};if(E(_1K7)==114){if(!B(_ae(_1K9,_1CV))){var _1KV=E(_1K9);if(!_1KV._){return _1K6;}else{var _1KW=_1KV.b;return new T(function(){var _1KX=E(_1K6),_1KY=E(_1KX.a),_1KZ=E(_1KV.a),_1L0=E(_1KZ);if(_1L0==34){var _1L1=B(_Yd(_1KZ,_1KW));if(!_1L1._){var _1L2=E(_1Eu);}else{var _1L3=E(_1L1.b);if(!_1L3._){var _1L4=E(_1De);}else{var _1L5=_1L3.a,_1L6=E(_1L3.b);if(!_1L6._){var _1L7=new T2(1,new T2(1,_1L5,_Z),_Z);}else{var _1L8=E(_1L5),_1L9=new T(function(){var _1La=B(_LC(126,_1L6.a,_1L6.b));return new T2(0,_1La.a,_1La.b);});if(E(_1L8)==126){var _1Lb=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1L9).a);}),new T(function(){return E(E(_1L9).b);})));}else{var _1Lb=new T2(1,new T2(1,_1L8,new T(function(){return E(E(_1L9).a);})),new T(function(){return E(E(_1L9).b);}));}var _1L7=_1Lb;}var _1L4=_1L7;}var _1L2=_1L4;}var _1Lc=_1L2;}else{var _1Ld=E(_1KW);if(!_1Ld._){var _1Le=new T2(1,new T2(1,_1KZ,_Z),_Z);}else{var _1Lf=new T(function(){var _1Lg=B(_LC(126,_1Ld.a,_1Ld.b));return new T2(0,_1Lg.a,_1Lg.b);});if(E(_1L0)==126){var _1Lh=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Lf).a);}),new T(function(){return E(E(_1Lf).b);})));}else{var _1Lh=new T2(1,new T2(1,_1KZ,new T(function(){return E(E(_1Lf).a);})),new T(function(){return E(E(_1Lf).b);}));}var _1Le=_1Lh;}var _1Lc=_1Le;}var _1Li=B(_KK(B(_x7(_1CW,new T(function(){return B(_NR(_1Lc));})))));if(!_1Li._){return E(_1CK);}else{if(!E(_1Li.b)._){var _1Lj=E(_1Li.a),_1Lk=B(_aW(_1kz,_1Lj)),_1Ll=B(_aW(_1Lc,1));if(!_1Ll._){var _1Lm=__Z;}else{var _1Ln=E(_1Ll.b);if(!_1Ln._){var _1Lo=__Z;}else{var _1Lp=E(_1Ll.a),_1Lq=new T(function(){var _1Lr=B(_LC(44,_1Ln.a,_1Ln.b));return new T2(0,_1Lr.a,_1Lr.b);});if(E(_1Lp)==44){var _1Ls=B(_164(_Z,new T(function(){return E(E(_1Lq).a);}),new T(function(){return E(E(_1Lq).b);})));}else{var _1Ls=B(_168(new T2(1,_1Lp,new T(function(){return E(E(_1Lq).a);})),new T(function(){return E(E(_1Lq).b);})));}var _1Lo=_1Ls;}var _1Lm=_1Lo;}var _1Lt=B(_aW(_1Lc,2));if(!_1Lt._){var _1Lu=E(_1Df);}else{var _1Lv=_1Lt.a,_1Lw=E(_1Lt.b);if(!_1Lw._){var _1Lx=B(_aj(_1D7,new T2(1,new T2(1,_1Lv,_Z),_Z)));}else{var _1Ly=E(_1Lv),_1Lz=new T(function(){var _1LA=B(_LC(44,_1Lw.a,_1Lw.b));return new T2(0,_1LA.a,_1LA.b);});if(E(_1Ly)==44){var _1LB=B(_aj(_1D7,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Lz).a);}),new T(function(){return E(E(_1Lz).b);})))));}else{var _1LB=B(_aj(_1D7,new T2(1,new T2(1,_1Ly,new T(function(){return E(E(_1Lz).a);})),new T(function(){return E(E(_1Lz).b);}))));}var _1Lx=_1LB;}var _1Lu=_1Lx;}return {_:0,a:E({_:0,a:E(B(_aW(_1kK,_1Lj))),b:E(B(_1fN(_1Lk.a,E(_1Lk.b),new T(function(){return B(_aW(_1mE,_1Lj));})))),c:E(_1KY.c),d:B(_aW(_1kX,_1Lj)),e:32,f:_1Lj,g:E(_1KY.g),h:_1KY.h,i:E(_1KY.i),j:E(_1KY.j),k:E(_1KY.k)}),b:E(_1Lk),c:E(_1KX.c),d:E(_1KX.d),e:E(_1Lm),f:E(_1Lu),g:E(_1KX.g),h:E(_1KX.h),i:_1KX.i,j:_1KX.j,k:_1KX.k,l:_1KX.l,m:E(_1KX.m),n:_1KX.n,o:E(_1KX.o),p:E(_1KX.p),q:_1KX.q,r:E(_1KX.r),s:E(_1KX.s),t:_1KX.t,u:E(_1KX.u),v:E(_1KX.v)};}else{return E(_1CL);}}});}}else{return new F(function(){return _1Ka(_);});}}else{return new F(function(){return _1Ka(_);});}};switch(E(_1K7)){case 100:var _1LC=__app1(E(_1Es),toJSStr(E(_1CZ)));return new F(function(){return _1K8(_,_1CH);});break;case 114:var _1LD=B(_16j(_aB,toJSStr(E(_1CZ)),_));return new F(function(){return _1K8(_,new T(function(){var _1LE=E(_1LD);if(!_1LE._){return E(_1CI);}else{return fromJSStr(B(_1r8(_1LE.a)));}}));});break;case 115:var _1LF=new T(function(){var _1LG=new T(function(){var _1LH=new T(function(){var _1LI=B(_aj(_aG,_1HB));if(!_1LI._){return __Z;}else{return B(_1CE(new T2(1,_1LI.a,new T(function(){return B(_1DB(_1CX,_1LI.b));}))));}}),_1LJ=new T(function(){var _1LK=function(_1LL){var _1LM=E(_1LL);if(!_1LM._){return __Z;}else{var _1LN=E(_1LM.a);return new T2(1,_1LN.a,new T2(1,_1LN.b,new T(function(){return B(_1LK(_1LM.b));})));}},_1LO=B(_1LK(_1HA));if(!_1LO._){return __Z;}else{return B(_1CE(new T2(1,_1LO.a,new T(function(){return B(_1DB(_1CX,_1LO.b));}))));}});return B(_1DB(_1CY,new T2(1,_1LJ,new T2(1,_1LH,_Z))));});return B(_x(B(_1CE(new T2(1,new T(function(){return B(_H(0,_1Hq,_Z));}),_1LG))),_1Dd));}),_1LP=__app2(E(_1Ev),toJSStr(E(_1CZ)),B(_1r8(B(_1Gu(B(unAppCStr("\"",_1LF)))))));return new F(function(){return _1K8(_,_1CJ);});break;default:return new F(function(){return _1K8(_,_1D0);});}},_1LQ=E(_1HO);if(!_1LQ._){var _1LR=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1IO(_);});}else{var _1LS=new T(function(){return B(_H(0,E(_1LQ.a),new T(function(){return B(_1Ex(_1LQ.b));})));}),_1LT=B(_1Cz(_1Gs,new T2(1,_2B,_1LS),_));return new F(function(){return _1IO(_);});}};if(!E(_1Ik)){var _1LU=B(_1Cz(_1Gs,_1EW,_));return new F(function(){return _1IL(_);});}else{var _1LV=B(_1Cz(_1Gs,_1EV,_));return new F(function(){return _1IL(_);});}},_1LW=E(_1HC);if(!_1LW._){var _1LX=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1IJ(_);});}else{var _1LY=new T(function(){var _1LZ=E(_1LW.a),_1M0=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1M1){return new F(function(){return _1Dg(_1LZ.a,_1M1);});},new T2(1,function(_1M2){return new F(function(){return _1Dg(_1LZ.b,_1M2);});},_Z)),new T2(1,_F,new T(function(){return B(_1EB(_1LW.b));}))));});return new T2(1,_G,_1M0);}),_1M3=B(_1Cz(_1Gs,new T2(1,_2B,_1LY),_));return new F(function(){return _1IJ(_);});}},_1M4=E(_1HB);if(!_1M4._){var _1M5=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1II(_);});}else{var _1M6=new T(function(){return B(_H(0,E(_1M4.a),new T(function(){return B(_1EJ(_1M4.b));})));}),_1M7=B(_1Cz(_1Gs,new T2(1,_2B,_1M6),_));return new F(function(){return _1II(_);});}},_1M8=E(_1HA);if(!_1M8._){var _1M9=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1IH(_);});}else{var _1Ma=new T(function(){var _1Mb=E(_1M8.a),_1Mc=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Md){return new F(function(){return _1Dg(_1Mb.a,_1Md);});},new T2(1,function(_1Me){return new F(function(){return _1Dg(_1Mb.b,_1Me);});},_Z)),new T2(1,_F,new T(function(){return B(_1EN(_1M8.b));}))));});return new T2(1,_G,_1Mc);}),_1Mf=B(_1Cz(_1Gs,new T2(1,_2B,_1Ma),_));return new F(function(){return _1IH(_);});}},_1Mg=E(_1HL);if(!_1Mg._){return new F(function(){return _1I9(_,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1I4,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1I1,_1I0);});}else{var _1Mh=E(_1Mg.b);if(!_1Mh._){return new F(function(){return _1I9(_,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1I4,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1I1,_1I0);});}else{var _1Mi=E(_1Mh.b);if(!_1Mi._){return new F(function(){return _1I9(_,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1I4,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1I1,_1I0);});}else{var _1Mj=_1Mi.a,_1Mk=E(_1Mi.b);if(!_1Mk._){return new F(function(){return _1I9(_,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1I4,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1I1,_1I0);});}else{if(!E(_1Mk.b)._){var _1Ml=B(_1di(B(_qy(_1Mj,0)),_1Hs,new T(function(){var _1Mm=B(_KK(B(_x7(_1CW,_1Mg.a))));if(!_1Mm._){return E(_1Ei);}else{if(!E(_1Mm.b)._){if(E(_1Mm.a)==2){return E(_1Em);}else{return E(_1Ei);}}else{return E(_1Ei);}}}),_)),_1Mn=E(_1Ml),_1Mo=_1Mn.a,_1Mp=new T(function(){var _1Mq=new T(function(){return B(_aj(function(_1Mr){var _1Ms=B(_wS(_3S,_1Mr,B(_KW(_1D6,_1Mj))));return (_1Ms._==0)?E(_1CQ):E(_1Ms.a);},B(_aj(_1EX,B(_1Ff(B(_1En(_1Mo,_1Ej))))))));}),_1Mt=B(_KW(_1Mo,_1Mj)),_1Mu=B(_YD(B(unAppCStr("e.==.m1:",_1Mk.a)),{_:0,a:E(_1Hl),b:E(_1Hm),c:E(_1Hn),d:_1Ho,e:_1Hp,f:_1Hq,g:E(B(_x(_1Hr,new T2(1,new T2(0,new T2(0,_1Mh.a,_1D5),_1Hq),new T2(1,new T2(0,new T2(0,_1Mq,_1D5),_1Hq),_Z))))),h:E(_1Mn.b),i:E(_1Ht),j:E(_1Hu),k:E(_1Hv)},_1I4,_1Hy,B(_x(B(_0(_Z,B(_1Ha(_1Mj,B(_9T(_1Hz)))))),new T(function(){return B(_aj(_1C9,_1Mt));},1))),_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,E(_1Mt),0,_1HO,_1I2,_1HR,_1I1,_1I0)),_1Mv=B(_1rj(_1Mj,_1Mu.a,_1Mu.b,_1Mu.c,_1Mu.d,_1Mu.e,_1Mu.f,_1Mu.g,_1Mu.h,_1Mu.i,_1Mu.j,_1Mu.k,_1Mu.l,_1Mu.m,_1Mu.n,_1Mu.o,_1Mu.p,_1Mu.q,_1Mu.r,_1Mu.s,_1Mu.t,_1Mu.u,_1Mu.v));return {_:0,a:E(_1Mv.a),b:E(_1Mv.b),c:E(_1Mv.c),d:E(_1Mv.d),e:E(_1Mv.e),f:E(_1Mv.f),g:E(_1Mv.g),h:E(_1Mv.h),i:_1Mv.i,j:_1Mv.j,k:_1Mv.k,l:_1Mv.l,m:E(_1Mv.m),n:_1Mv.n,o:E(_1Mv.o),p:E(_1Mv.p),q:_1Mv.q,r:E(_1Mv.r),s:E(_1Mv.s),t:_1Mv.t,u:E(_1Mv.u),v:E(_1Mv.v)};}),_1Mw=function(_){var _1Mx=function(_){var _1My=function(_){var _1Mz=new T(function(){var _1MA=E(E(_1Mp).a);return new T6(0,_1MA,_1MA.a,_1MA.g,_1MA.h,_1MA.i,_1MA.k);}),_1MB=B(_1Cz(_1Gs,new T2(1,_aI,new T(function(){return B(_cp(E(_1Mz).e,_1Dv));})),_)),_1MC=E(_1Mz),_1MD=_1MC.a,_1ME=function(_){var _1MF=B(_1Cz(_1Gs,B(_H(0,_1HI,_Z)),_)),_1MG=B(_1Cz(_1Gs,B(_2C(_1Dj,_1MC.c,_Z)),_)),_1MH=function(_){var _1MI=B(_1b7(_1D4,_1MC.d,_)),_1MJ=E(_1MI).b,_1MK=E(_1Hg),_1ML=_1MK.a,_1MM=_1MK.b,_1MN=new T(function(){return B(_1s8(E(_1Hk)));}),_1MO=new T(function(){var _1MP=E(_1Mp),_1MQ=_1MP.b,_1MR=_1MP.c,_1MS=_1MP.d,_1MT=_1MP.e,_1MU=_1MP.f,_1MV=_1MP.g,_1MW=_1MP.h,_1MX=_1MP.i,_1MY=_1MP.j,_1MZ=_1MP.k,_1N0=_1MP.l,_1N1=_1MP.m,_1N2=_1MP.n,_1N3=_1MP.o,_1N4=_1MP.p,_1N5=_1MP.q,_1N6=_1MP.r,_1N7=_1MP.t,_1N8=_1MP.u,_1N9=_1MP.v,_1Na=E(_1MP.s),_1Nb=_1Na.a,_1Nc=_1Na.b,_1Nd=E(_1MN),_1Ne=E(_1MC.b),_1Nf=_1Ne.a,_1Ng=_1Ne.b,_1Nh=function(_1Ni,_1Nj){var _1Nk=E(_1Ni),_1Nl=E(_1Nf);if(_1Nk<=_1Nl){if(_1Nl<=_1Nk){var _1Nm=E(_1Ng);if(_1Nj<=_1Nm){if(_1Nm<=_1Nj){var _1Nn=4;}else{var _1Nn=0;}var _1No=_1Nn;}else{var _1No=1;}var _1Np=_1No;}else{var _1Np=2;}var _1Nq=_1Np;}else{var _1Nq=3;}var _1Nr=function(_1Ns,_1Nt,_1Nu,_1Nv,_1Nw,_1Nx,_1Ny,_1Nz,_1NA,_1NB){switch(E(_1Nq)){case 0:if(!E(E(_1MD).c)){var _1NC=new T2(0,_1Nb,_1Nc);}else{var _1NC=new T2(0,_1Nb,_1Dz);}var _1ND=_1NC;break;case 1:if(E(E(_1MD).c)==1){var _1NE=new T2(0,_1Nb,_1Nc);}else{var _1NE=new T2(0,_1Nb,_1Gx);}var _1ND=_1NE;break;case 2:if(E(E(_1MD).c)==2){var _1NF=new T2(0,_1Nb,_1Nc);}else{var _1NF=new T2(0,_1Nb,_1D3);}var _1ND=_1NF;break;case 3:if(E(E(_1MD).c)==3){var _1NG=new T2(0,_1Nb,_1Nc);}else{var _1NG=new T2(0,_1Nb,_1D2);}var _1ND=_1NG;break;default:if(E(E(_1MD).c)==4){var _1NH=new T2(0,_1Nb,_1Nc);}else{var _1NH=new T2(0,_1Nb,_1Gx);}var _1ND=_1NH;}var _1NI=B(_1oT(_1Gx,_1Nz,_1MT,{_:0,a:E(_1Ns),b:E(_1Nt),c:E(_1Nu),d:_1Nv,e:_1Nw,f:_1Nx,g:E(_1Ny),h:E(_1MJ),i:E(_1Nz),j:E(_1NA),k:E(_1NB)},_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1MW,_1MX,_1MY,_1MZ,_1N0,_1N1,_1N2,_1N3,_1N4,_1N5,_1N6,_1ND,_1N7,_1N8,_1N9)),_1NJ=_1NI.a,_1NK=_1NI.b,_1NL=_1NI.c,_1NM=_1NI.d,_1NN=_1NI.e,_1NO=_1NI.f,_1NP=_1NI.g,_1NQ=_1NI.h,_1NR=_1NI.i,_1NS=_1NI.j,_1NT=_1NI.k,_1NU=_1NI.l,_1NV=_1NI.m,_1NW=_1NI.n,_1NX=_1NI.o,_1NY=_1NI.q,_1NZ=_1NI.r,_1O0=_1NI.s,_1O1=_1NI.t,_1O2=_1NI.u,_1O3=_1NI.v,_1O4=E(_1NI.p);if(!_1O4._){return {_:0,a:E(_1NJ),b:E(_1NK),c:E(_1NL),d:E(_1NM),e:E(_1NN),f:E(_1NO),g:E(_1NP),h:E(_1NQ),i:_1NR,j:_1NS,k:_1NT,l:_1NU,m:E(_1NV),n:_1NW,o:E(_1NX),p:E(_Z),q:_1NY,r:E(_1NZ),s:E(_1O0),t:_1O1,u:E(_1O2),v:E(_1O3)};}else{var _1O5=B(_qy(_1Nz,0))-2|0,_1O6=function(_1O7){var _1O8=E(_1NJ);return {_:0,a:E({_:0,a:E(_1O8.a),b:E(_1O8.b),c:E(_1O8.c),d:_1O8.d,e:_1O8.e,f:_1O8.f,g:E(_Z),h:_1O8.h,i:E(_1O8.i),j:E(_1O8.j),k:E(_1O8.k)}),b:E(_1NK),c:E(_1NL),d:E(B(_x(B(_0(_Z,B(_1Ha(B(_aj(_1EX,_1O4)),B(_9T(_1NM)))))),new T(function(){return B(_aj(_1C4,_1O4));},1)))),e:E(_1NN),f:E(_1NO),g:E(_1NP),h:E(_1NQ),i:_1NR,j:_1NS,k:_1NT,l:_1NU,m:E(_1NV),n:_1NW,o:E(_1NX),p:E(_Z),q:_1NY,r:E(B(_x(_1NZ,new T2(1,_1NY,_Z)))),s:E(_1O0),t:_1O1,u:E(_1O2),v:E(_1O3)};};if(_1O5>0){if(!B(_vl(B(_1BL(_1O5,_1Nz)),_1D1))){return {_:0,a:E(_1NJ),b:E(_1NK),c:E(_1NL),d:E(_1NM),e:E(_1NN),f:E(_1NO),g:E(_1NP),h:E(_1NQ),i:_1NR,j:_1NS,k:_1NT,l:_1NU,m:E(_1NV),n:_1NW,o:E(_1NX),p:E(_1O4),q:_1NY,r:E(_1NZ),s:E(_1O0),t:_1O1,u:E(_1O2),v:E(_1O3)};}else{return new F(function(){return _1O6(_);});}}else{if(!B(_vl(_1Nz,_1D1))){return {_:0,a:E(_1NJ),b:E(_1NK),c:E(_1NL),d:E(_1NM),e:E(_1NN),f:E(_1NO),g:E(_1NP),h:E(_1NQ),i:_1NR,j:_1NS,k:_1NT,l:_1NU,m:E(_1NV),n:_1NW,o:E(_1NX),p:E(_1O4),q:_1NY,r:E(_1NZ),s:E(_1O0),t:_1O1,u:E(_1O2),v:E(_1O3)};}else{return new F(function(){return _1O6(_);});}}}};if(E(_1Nd)==32){var _1O9=E(_1MD),_1Oa=E(_1O9.a),_1Ob=B(_1y1(_1Nk,_1Nj,_1Oa.a,_1Oa.b,_1O9.b,_1Nq,_1O9.d,_1O9.e,_1O9.f,_1O9.g,_1O9.h,_1O9.i,_1O9.j,_1O9.k)),_1Oc=E(_1Ob.a),_1Od=B(_1Bm(_1Oc.a,E(_1Oc.b),_1Ob.b,_1Ob.c,_1Ob.d,_1Ob.e,_1Ob.f,_1Ob.g,_1Ob.h,_1Ob.i,_1Ob.j,_1Ob.k));return new F(function(){return _1Nr(_1Od.a,_1Od.b,_1Od.c,_1Od.d,_1Od.e,_1Od.f,_1Od.g,_1Od.i,_1Od.j,_1Od.k);});}else{var _1Oe=E(_1MD),_1Of=E(_1Oe.a),_1Og=B(_1y1(_1Nk,_1Nj,_1Of.a,_1Of.b,_1Oe.b,_1Nq,_1Oe.d,_1Oe.e,_1Oe.f,_1Oe.g,_1Oe.h,_1Oe.i,_1Oe.j,_1Oe.k));return new F(function(){return _1Nr(_1Og.a,_1Og.b,_1Og.c,_1Og.d,_1Og.e,_1Og.f,_1Og.g,_1Og.i,_1Og.j,_1Og.k);});}},_1Oh=function(_1Oi,_1Oj){var _1Ok=E(_1Oj),_1Ol=E(_1Nf);if(_1Oi<=_1Ol){if(_1Ol<=_1Oi){var _1Om=E(_1Ng);if(_1Ok<=_1Om){if(_1Om<=_1Ok){var _1On=4;}else{var _1On=0;}var _1Oo=_1On;}else{var _1Oo=1;}var _1Op=_1Oo;}else{var _1Op=2;}var _1Oq=_1Op;}else{var _1Oq=3;}var _1Or=function(_1Os,_1Ot,_1Ou,_1Ov,_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1OB){switch(E(_1Oq)){case 0:if(!E(E(_1MD).c)){var _1OC=new T2(0,_1Nb,_1Nc);}else{var _1OC=new T2(0,_1Nb,_1Dz);}var _1OD=_1OC;break;case 1:if(E(E(_1MD).c)==1){var _1OE=new T2(0,_1Nb,_1Nc);}else{var _1OE=new T2(0,_1Nb,_1Gx);}var _1OD=_1OE;break;case 2:if(E(E(_1MD).c)==2){var _1OF=new T2(0,_1Nb,_1Nc);}else{var _1OF=new T2(0,_1Nb,_1D3);}var _1OD=_1OF;break;case 3:if(E(E(_1MD).c)==3){var _1OG=new T2(0,_1Nb,_1Nc);}else{var _1OG=new T2(0,_1Nb,_1D2);}var _1OD=_1OG;break;default:if(E(E(_1MD).c)==4){var _1OH=new T2(0,_1Nb,_1Nc);}else{var _1OH=new T2(0,_1Nb,_1Gx);}var _1OD=_1OH;}var _1OI=B(_1oT(_1Gx,_1Oz,_1MT,{_:0,a:E(_1Os),b:E(_1Ot),c:E(_1Ou),d:_1Ov,e:_1Ow,f:_1Ox,g:E(_1Oy),h:E(_1MJ),i:E(_1Oz),j:E(_1OA),k:E(_1OB)},_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1MW,_1MX,_1MY,_1MZ,_1N0,_1N1,_1N2,_1N3,_1N4,_1N5,_1N6,_1OD,_1N7,_1N8,_1N9)),_1OJ=_1OI.a,_1OK=_1OI.b,_1OL=_1OI.c,_1OM=_1OI.d,_1ON=_1OI.e,_1OO=_1OI.f,_1OP=_1OI.g,_1OQ=_1OI.h,_1OR=_1OI.i,_1OS=_1OI.j,_1OT=_1OI.k,_1OU=_1OI.l,_1OV=_1OI.m,_1OW=_1OI.n,_1OX=_1OI.o,_1OY=_1OI.q,_1OZ=_1OI.r,_1P0=_1OI.s,_1P1=_1OI.t,_1P2=_1OI.u,_1P3=_1OI.v,_1P4=E(_1OI.p);if(!_1P4._){return {_:0,a:E(_1OJ),b:E(_1OK),c:E(_1OL),d:E(_1OM),e:E(_1ON),f:E(_1OO),g:E(_1OP),h:E(_1OQ),i:_1OR,j:_1OS,k:_1OT,l:_1OU,m:E(_1OV),n:_1OW,o:E(_1OX),p:E(_Z),q:_1OY,r:E(_1OZ),s:E(_1P0),t:_1P1,u:E(_1P2),v:E(_1P3)};}else{var _1P5=B(_qy(_1Oz,0))-2|0,_1P6=function(_1P7){var _1P8=E(_1OJ);return {_:0,a:E({_:0,a:E(_1P8.a),b:E(_1P8.b),c:E(_1P8.c),d:_1P8.d,e:_1P8.e,f:_1P8.f,g:E(_Z),h:_1P8.h,i:E(_1P8.i),j:E(_1P8.j),k:E(_1P8.k)}),b:E(_1OK),c:E(_1OL),d:E(B(_x(B(_0(_Z,B(_1Ha(B(_aj(_1EX,_1P4)),B(_9T(_1OM)))))),new T(function(){return B(_aj(_1C4,_1P4));},1)))),e:E(_1ON),f:E(_1OO),g:E(_1OP),h:E(_1OQ),i:_1OR,j:_1OS,k:_1OT,l:_1OU,m:E(_1OV),n:_1OW,o:E(_1OX),p:E(_Z),q:_1OY,r:E(B(_x(_1OZ,new T2(1,_1OY,_Z)))),s:E(_1P0),t:_1P1,u:E(_1P2),v:E(_1P3)};};if(_1P5>0){if(!B(_vl(B(_1BL(_1P5,_1Oz)),_1D1))){return {_:0,a:E(_1OJ),b:E(_1OK),c:E(_1OL),d:E(_1OM),e:E(_1ON),f:E(_1OO),g:E(_1OP),h:E(_1OQ),i:_1OR,j:_1OS,k:_1OT,l:_1OU,m:E(_1OV),n:_1OW,o:E(_1OX),p:E(_1P4),q:_1OY,r:E(_1OZ),s:E(_1P0),t:_1P1,u:E(_1P2),v:E(_1P3)};}else{return new F(function(){return _1P6(_);});}}else{if(!B(_vl(_1Oz,_1D1))){return {_:0,a:E(_1OJ),b:E(_1OK),c:E(_1OL),d:E(_1OM),e:E(_1ON),f:E(_1OO),g:E(_1OP),h:E(_1OQ),i:_1OR,j:_1OS,k:_1OT,l:_1OU,m:E(_1OV),n:_1OW,o:E(_1OX),p:E(_1P4),q:_1OY,r:E(_1OZ),s:E(_1P0),t:_1P1,u:E(_1P2),v:E(_1P3)};}else{return new F(function(){return _1P6(_);});}}}};if(E(_1Nd)==32){var _1P9=E(_1MD),_1Pa=E(_1P9.a),_1Pb=B(_1y1(_1Oi,_1Ok,_1Pa.a,_1Pa.b,_1P9.b,_1Oq,_1P9.d,_1P9.e,_1P9.f,_1P9.g,_1P9.h,_1P9.i,_1P9.j,_1P9.k)),_1Pc=E(_1Pb.a),_1Pd=B(_1Bm(_1Pc.a,E(_1Pc.b),_1Pb.b,_1Pb.c,_1Pb.d,_1Pb.e,_1Pb.f,_1Pb.g,_1Pb.h,_1Pb.i,_1Pb.j,_1Pb.k));return new F(function(){return _1Or(_1Pd.a,_1Pd.b,_1Pd.c,_1Pd.d,_1Pd.e,_1Pd.f,_1Pd.g,_1Pd.i,_1Pd.j,_1Pd.k);});}else{var _1Pe=E(_1MD),_1Pf=E(_1Pe.a),_1Pg=B(_1y1(_1Oi,_1Ok,_1Pf.a,_1Pf.b,_1Pe.b,_1Oq,_1Pe.d,_1Pe.e,_1Pe.f,_1Pe.g,_1Pe.h,_1Pe.i,_1Pe.j,_1Pe.k));return new F(function(){return _1Or(_1Pg.a,_1Pg.b,_1Pg.c,_1Pg.d,_1Pg.e,_1Pg.f,_1Pg.g,_1Pg.i,_1Pg.j,_1Pg.k);});}},_1Ph=E(_1Nd);switch(_1Ph){case 72:var _1Pi=E(_1Ng);if(0<=(_1Pi-1|0)){return B(_1Nh(_1Nf,_1Pi-1|0));}else{return B(_1Nh(_1Nf,_1Pi));}break;case 75:var _1Pj=E(_1Nf);if(0<=(_1Pj-1|0)){return B(_1Oh(_1Pj-1|0,_1Ng));}else{return B(_1Oh(_1Pj,_1Ng));}break;case 77:var _1Pk=E(_1Nf);if(E(_1Hw)!=(_1Pk+1|0)){return B(_1Oh(_1Pk+1|0,_1Ng));}else{return B(_1Oh(_1Pk,_1Ng));}break;case 80:var _1Pl=E(_1Ng);if(E(_1Hx)!=(_1Pl+1|0)){return B(_1Nh(_1Nf,_1Pl+1|0));}else{return B(_1Nh(_1Nf,_1Pl));}break;case 104:var _1Pm=E(_1Nf);if(0<=(_1Pm-1|0)){return B(_1Oh(_1Pm-1|0,_1Ng));}else{return B(_1Oh(_1Pm,_1Ng));}break;case 106:var _1Pn=E(_1Ng);if(E(_1Hx)!=(_1Pn+1|0)){return B(_1Nh(_1Nf,_1Pn+1|0));}else{return B(_1Nh(_1Nf,_1Pn));}break;case 107:var _1Po=E(_1Ng);if(0<=(_1Po-1|0)){return B(_1Nh(_1Nf,_1Po-1|0));}else{return B(_1Nh(_1Nf,_1Po));}break;case 108:var _1Pp=E(_1Nf);if(E(_1Hw)!=(_1Pp+1|0)){return B(_1Oh(_1Pp+1|0,_1Ng));}else{return B(_1Oh(_1Pp,_1Ng));}break;default:var _1Pq=E(_1Nf),_1Pr=E(_1Ng),_1Ps=function(_1Pt,_1Pu,_1Pv,_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC){if(E(E(_1MD).c)==4){var _1PD=new T2(0,_1Nb,_1Nc);}else{var _1PD=new T2(0,_1Nb,_1Gx);}var _1PE=B(_1oT(_1Gx,_1PA,_1MT,{_:0,a:E(_1Pt),b:E(_1Pu),c:E(_1Pv),d:_1Pw,e:_1Px,f:_1Py,g:E(_1Pz),h:E(_1MJ),i:E(_1PA),j:E(_1PB),k:E(_1PC)},_1MQ,_1MR,_1MS,_1MT,_1MU,_1MV,_1MW,_1MX,_1MY,_1MZ,_1N0,_1N1,_1N2,_1N3,_1N4,_1N5,_1N6,_1PD,_1N7,_1N8,_1N9)),_1PF=_1PE.a,_1PG=_1PE.b,_1PH=_1PE.c,_1PI=_1PE.d,_1PJ=_1PE.e,_1PK=_1PE.f,_1PL=_1PE.g,_1PM=_1PE.h,_1PN=_1PE.i,_1PO=_1PE.j,_1PP=_1PE.k,_1PQ=_1PE.l,_1PR=_1PE.m,_1PS=_1PE.n,_1PT=_1PE.o,_1PU=_1PE.q,_1PV=_1PE.r,_1PW=_1PE.s,_1PX=_1PE.t,_1PY=_1PE.u,_1PZ=_1PE.v,_1Q0=E(_1PE.p);if(!_1Q0._){return {_:0,a:E(_1PF),b:E(_1PG),c:E(_1PH),d:E(_1PI),e:E(_1PJ),f:E(_1PK),g:E(_1PL),h:E(_1PM),i:_1PN,j:_1PO,k:_1PP,l:_1PQ,m:E(_1PR),n:_1PS,o:E(_1PT),p:E(_Z),q:_1PU,r:E(_1PV),s:E(_1PW),t:_1PX,u:E(_1PY),v:E(_1PZ)};}else{var _1Q1=B(_qy(_1PA,0))-2|0,_1Q2=function(_1Q3){var _1Q4=E(_1PF);return {_:0,a:E({_:0,a:E(_1Q4.a),b:E(_1Q4.b),c:E(_1Q4.c),d:_1Q4.d,e:_1Q4.e,f:_1Q4.f,g:E(_Z),h:_1Q4.h,i:E(_1Q4.i),j:E(_1Q4.j),k:E(_1Q4.k)}),b:E(_1PG),c:E(_1PH),d:E(B(_x(B(_0(_Z,B(_1Ha(B(_aj(_1EX,_1Q0)),B(_9T(_1PI)))))),new T(function(){return B(_aj(_1C4,_1Q0));},1)))),e:E(_1PJ),f:E(_1PK),g:E(_1PL),h:E(_1PM),i:_1PN,j:_1PO,k:_1PP,l:_1PQ,m:E(_1PR),n:_1PS,o:E(_1PT),p:E(_Z),q:_1PU,r:E(B(_x(_1PV,new T2(1,_1PU,_Z)))),s:E(_1PW),t:_1PX,u:E(_1PY),v:E(_1PZ)};};if(_1Q1>0){if(!B(_vl(B(_1BL(_1Q1,_1PA)),_1D1))){return {_:0,a:E(_1PF),b:E(_1PG),c:E(_1PH),d:E(_1PI),e:E(_1PJ),f:E(_1PK),g:E(_1PL),h:E(_1PM),i:_1PN,j:_1PO,k:_1PP,l:_1PQ,m:E(_1PR),n:_1PS,o:E(_1PT),p:E(_1Q0),q:_1PU,r:E(_1PV),s:E(_1PW),t:_1PX,u:E(_1PY),v:E(_1PZ)};}else{return new F(function(){return _1Q2(_);});}}else{if(!B(_vl(_1PA,_1D1))){return {_:0,a:E(_1PF),b:E(_1PG),c:E(_1PH),d:E(_1PI),e:E(_1PJ),f:E(_1PK),g:E(_1PL),h:E(_1PM),i:_1PN,j:_1PO,k:_1PP,l:_1PQ,m:E(_1PR),n:_1PS,o:E(_1PT),p:E(_1Q0),q:_1PU,r:E(_1PV),s:E(_1PW),t:_1PX,u:E(_1PY),v:E(_1PZ)};}else{return new F(function(){return _1Q2(_);});}}}};if(E(_1Ph)==32){var _1Q5=E(_1MD),_1Q6=E(_1Q5.a),_1Q7=B(_1y1(_1Pq,_1Pr,_1Q6.a,_1Q6.b,_1Q5.b,_1BR,_1Q5.d,_1Q5.e,_1Q5.f,_1Q5.g,_1Q5.h,_1Q5.i,_1Q5.j,_1Q5.k)),_1Q8=E(_1Q7.a),_1Q9=B(_1Bm(_1Q8.a,E(_1Q8.b),_1Q7.b,_1Q7.c,_1Q7.d,_1Q7.e,_1Q7.f,_1Q7.g,_1Q7.h,_1Q7.i,_1Q7.j,_1Q7.k));return B(_1Ps(_1Q9.a,_1Q9.b,_1Q9.c,_1Q9.d,_1Q9.e,_1Q9.f,_1Q9.g,_1Q9.i,_1Q9.j,_1Q9.k));}else{var _1Qa=E(_1MD),_1Qb=E(_1Qa.a),_1Qc=B(_1y1(_1Pq,_1Pr,_1Qb.a,_1Qb.b,_1Qa.b,_1BR,_1Qa.d,_1Qa.e,_1Qa.f,_1Qa.g,_1Qa.h,_1Qa.i,_1Qa.j,_1Qa.k));return B(_1Ps(_1Qc.a,_1Qc.b,_1Qc.c,_1Qc.d,_1Qc.e,_1Qc.f,_1Qc.g,_1Qc.i,_1Qc.j,_1Qc.k));}}}),_1Qd=B(_1bB(_1ML,_1MM,_1Hh,_1Hi,_1Hj,_1MO,_)),_1Qe=_1Qd,_1Qf=E(_1MN),_1Qg=function(_,_1Qh){var _1Qi=function(_1Qj){var _1Qk=B(_1Cz(_1Gs,B(_cv(_1Qh)),_)),_1Ql=E(_1Qe),_1Qm=_1Ql.d,_1Qn=_1Ql.e,_1Qo=_1Ql.f,_1Qp=_1Ql.g,_1Qq=_1Ql.i,_1Qr=_1Ql.j,_1Qs=_1Ql.k,_1Qt=_1Ql.l,_1Qu=_1Ql.m,_1Qv=_1Ql.n,_1Qw=_1Ql.o,_1Qx=_1Ql.p,_1Qy=_1Ql.q,_1Qz=_1Ql.r,_1QA=_1Ql.t,_1QB=_1Ql.v,_1QC=E(_1Ql.u),_1QD=_1QC.a,_1QE=_1QC.d,_1QF=_1QC.e,_1QG=_1QC.f,_1QH=_1QC.g,_1QI=_1QC.h,_1QJ=E(_1Ql.a),_1QK=_1QJ.c,_1QL=_1QJ.f,_1QM=_1QJ.g,_1QN=_1QJ.h,_1QO=E(_1Ql.h),_1QP=E(_1Ql.s),_1QQ=function(_1QR){var _1QS=function(_1QT){if(_1QT!=E(_1CU)){var _1QU=B(_aW(_1kz,_1QT)),_1QV=_1QU.a,_1QW=E(_1QU.b),_1QX=B(_1fN(_1QV,_1QW,new T(function(){return B(_aW(_1mE,_1QT));})));return new F(function(){return _1Hf(_1MK,_1Hh,_1Hi,_1Hj,_1CT,B(_aW(_1kK,_1QT)),_1QX,_1QK,B(_aW(_1kX,_1QT)),32,_1QT,_1QM,_1QN,B(_x(_1QJ.i,new T2(1,_1CS,new T(function(){return B(_H(0,_1QL,_Z));})))),B(_1Cd(_1CR,_1QX)),_B2,_1QV,_1QW,_Z,_1Qm,_1Qn,_1Qo,_1Qp,_1QO.a,_1QO.b,_1Qq,_1Qr,_1Qs, -1,_1Qu,_1Qv,_1Qw,_1Qx,_1Qy,_1Qz,_1QP.a,_1QP.b,_1QA,_B2,_B2,_B2,_1QE,_1QF,_1QG,_1QH,_1QI,_1QB,_);});}else{var _1QY=__app1(E(_rn),_1MM),_1QZ=B(A2(_ro,_1ML,_)),_1R0=B(A(_qT,[_1ML,_n8,_1CN,_1CP,_1CO,_])),_1R1=B(A(_qT,[_1ML,_n8,_1CN,_1CM,_1DA,_])),_1R2=B(A(_qT,[_1ML,_n8,_1Dz,_1Dy,_1Dx,_]));return new T(function(){return {_:0,a:E({_:0,a:E(_1kB),b:E(_1Dw),c:E(_1QK),d:E(_1Da),e:32,f:0,g:E(_1QM),h:_1QN,i:E(_Z),j:E(_1QJ.j),k:E(_B2)}),b:E(_1km),c:E(_1Ql.c),d:E(_1Qm),e:E(_1Qn),f:E(_1Qo),g:E(_1Qp),h:E(_1QO),i:_1Qq,j:_1Qr,k:_1Qs,l:_1Qt,m:E(_1Qu),n:_1Qv,o:E(_1Qw),p:E(_1Qx),q:_1Qy,r:E(_1Qz),s:E(_1QP),t:_1QA,u:E({_:0,a:E(_1QD),b:E(_B3),c:E(_B2),d:E(_1QE),e:E(_1QF),f:E(_1QG),g:E(_1QH),h:E(_1QI)}),v:E(_1QB)};});}};if(_1Qt>=0){return new F(function(){return _1QS(_1Qt);});}else{return new F(function(){return _1QS(_1QL+1|0);});}};if(!E(_1QD)){if(E(_1Qf)==110){return new F(function(){return _1QQ(_);});}else{return _1Ql;}}else{return new F(function(){return _1QQ(_);});}};if(E(_1Qf)==114){if(!B(_ae(_1Qh,_1CV))){var _1R3=E(_1Qh);if(!_1R3._){return _1Qe;}else{var _1R4=_1R3.b;return new T(function(){var _1R5=E(_1Qe),_1R6=E(_1R5.a),_1R7=E(_1R3.a),_1R8=E(_1R7);if(_1R8==34){var _1R9=B(_Yd(_1R7,_1R4));if(!_1R9._){var _1Ra=E(_1Eu);}else{var _1Rb=E(_1R9.b);if(!_1Rb._){var _1Rc=E(_1De);}else{var _1Rd=_1Rb.a,_1Re=E(_1Rb.b);if(!_1Re._){var _1Rf=new T2(1,new T2(1,_1Rd,_Z),_Z);}else{var _1Rg=E(_1Rd),_1Rh=new T(function(){var _1Ri=B(_LC(126,_1Re.a,_1Re.b));return new T2(0,_1Ri.a,_1Ri.b);});if(E(_1Rg)==126){var _1Rj=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Rh).a);}),new T(function(){return E(E(_1Rh).b);})));}else{var _1Rj=new T2(1,new T2(1,_1Rg,new T(function(){return E(E(_1Rh).a);})),new T(function(){return E(E(_1Rh).b);}));}var _1Rf=_1Rj;}var _1Rc=_1Rf;}var _1Ra=_1Rc;}var _1Rk=_1Ra;}else{var _1Rl=E(_1R4);if(!_1Rl._){var _1Rm=new T2(1,new T2(1,_1R7,_Z),_Z);}else{var _1Rn=new T(function(){var _1Ro=B(_LC(126,_1Rl.a,_1Rl.b));return new T2(0,_1Ro.a,_1Ro.b);});if(E(_1R8)==126){var _1Rp=new T2(1,_Z,new T2(1,new T(function(){return E(E(_1Rn).a);}),new T(function(){return E(E(_1Rn).b);})));}else{var _1Rp=new T2(1,new T2(1,_1R7,new T(function(){return E(E(_1Rn).a);})),new T(function(){return E(E(_1Rn).b);}));}var _1Rm=_1Rp;}var _1Rk=_1Rm;}var _1Rq=B(_KK(B(_x7(_1CW,new T(function(){return B(_NR(_1Rk));})))));if(!_1Rq._){return E(_1CK);}else{if(!E(_1Rq.b)._){var _1Rr=E(_1Rq.a),_1Rs=B(_aW(_1kz,_1Rr)),_1Rt=B(_aW(_1Rk,1));if(!_1Rt._){var _1Ru=__Z;}else{var _1Rv=E(_1Rt.b);if(!_1Rv._){var _1Rw=__Z;}else{var _1Rx=E(_1Rt.a),_1Ry=new T(function(){var _1Rz=B(_LC(44,_1Rv.a,_1Rv.b));return new T2(0,_1Rz.a,_1Rz.b);});if(E(_1Rx)==44){var _1RA=B(_164(_Z,new T(function(){return E(E(_1Ry).a);}),new T(function(){return E(E(_1Ry).b);})));}else{var _1RA=B(_168(new T2(1,_1Rx,new T(function(){return E(E(_1Ry).a);})),new T(function(){return E(E(_1Ry).b);})));}var _1Rw=_1RA;}var _1Ru=_1Rw;}var _1RB=B(_aW(_1Rk,2));if(!_1RB._){var _1RC=E(_1Df);}else{var _1RD=_1RB.a,_1RE=E(_1RB.b);if(!_1RE._){var _1RF=B(_aj(_1D7,new T2(1,new T2(1,_1RD,_Z),_Z)));}else{var _1RG=E(_1RD),_1RH=new T(function(){var _1RI=B(_LC(44,_1RE.a,_1RE.b));return new T2(0,_1RI.a,_1RI.b);});if(E(_1RG)==44){var _1RJ=B(_aj(_1D7,new T2(1,_Z,new T2(1,new T(function(){return E(E(_1RH).a);}),new T(function(){return E(E(_1RH).b);})))));}else{var _1RJ=B(_aj(_1D7,new T2(1,new T2(1,_1RG,new T(function(){return E(E(_1RH).a);})),new T(function(){return E(E(_1RH).b);}))));}var _1RF=_1RJ;}var _1RC=_1RF;}return {_:0,a:E({_:0,a:E(B(_aW(_1kK,_1Rr))),b:E(B(_1fN(_1Rs.a,E(_1Rs.b),new T(function(){return B(_aW(_1mE,_1Rr));})))),c:E(_1R6.c),d:B(_aW(_1kX,_1Rr)),e:32,f:_1Rr,g:E(_1R6.g),h:_1R6.h,i:E(_1R6.i),j:E(_1R6.j),k:E(_1R6.k)}),b:E(_1Rs),c:E(_1R5.c),d:E(_1R5.d),e:E(_1Ru),f:E(_1RC),g:E(_1R5.g),h:E(_1R5.h),i:_1R5.i,j:_1R5.j,k:_1R5.k,l:_1R5.l,m:E(_1R5.m),n:_1R5.n,o:E(_1R5.o),p:E(_1R5.p),q:_1R5.q,r:E(_1R5.r),s:E(_1R5.s),t:_1R5.t,u:E(_1R5.u),v:E(_1R5.v)};}else{return E(_1CL);}}});}}else{return new F(function(){return _1Qi(_);});}}else{return new F(function(){return _1Qi(_);});}};switch(E(_1Qf)){case 100:var _1RK=__app1(E(_1Es),toJSStr(E(_1CZ)));return new F(function(){return _1Qg(_,_1CH);});break;case 114:var _1RL=B(_16j(_aB,toJSStr(E(_1CZ)),_));return new F(function(){return _1Qg(_,new T(function(){var _1RM=E(_1RL);if(!_1RM._){return E(_1CI);}else{return fromJSStr(B(_1r8(_1RM.a)));}}));});break;case 115:var _1RN=new T(function(){var _1RO=new T(function(){var _1RP=new T(function(){var _1RQ=B(_aj(_aG,_1HB));if(!_1RQ._){return __Z;}else{return B(_1CE(new T2(1,_1RQ.a,new T(function(){return B(_1DB(_1CX,_1RQ.b));}))));}}),_1RR=new T(function(){var _1RS=function(_1RT){var _1RU=E(_1RT);if(!_1RU._){return __Z;}else{var _1RV=E(_1RU.a);return new T2(1,_1RV.a,new T2(1,_1RV.b,new T(function(){return B(_1RS(_1RU.b));})));}},_1RW=B(_1RS(_1HA));if(!_1RW._){return __Z;}else{return B(_1CE(new T2(1,_1RW.a,new T(function(){return B(_1DB(_1CX,_1RW.b));}))));}});return B(_1DB(_1CY,new T2(1,_1RR,new T2(1,_1RP,_Z))));});return B(_x(B(_1CE(new T2(1,new T(function(){return B(_H(0,_1Hq,_Z));}),_1RO))),_1Dd));}),_1RX=__app2(E(_1Ev),toJSStr(E(_1CZ)),B(_1r8(B(_1Gu(B(unAppCStr("\"",_1RN)))))));return new F(function(){return _1Qg(_,_1CJ);});break;default:return new F(function(){return _1Qg(_,_1D0);});}},_1RY=E(_1HO);if(!_1RY._){var _1RZ=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1MH(_);});}else{var _1S0=new T(function(){return B(_H(0,E(_1RY.a),new T(function(){return B(_1Ex(_1RY.b));})));}),_1S1=B(_1Cz(_1Gs,new T2(1,_2B,_1S0),_));return new F(function(){return _1MH(_);});}};if(!E(_1MC.f)){var _1S2=B(_1Cz(_1Gs,_1EW,_));return new F(function(){return _1ME(_);});}else{var _1S3=B(_1Cz(_1Gs,_1EV,_));return new F(function(){return _1ME(_);});}},_1S4=E(_1HC);if(!_1S4._){var _1S5=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1My(_);});}else{var _1S6=new T(function(){var _1S7=E(_1S4.a),_1S8=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1S9){return new F(function(){return _1Dg(_1S7.a,_1S9);});},new T2(1,function(_1Sa){return new F(function(){return _1Dg(_1S7.b,_1Sa);});},_Z)),new T2(1,_F,new T(function(){return B(_1EB(_1S4.b));}))));});return new T2(1,_G,_1S8);}),_1Sb=B(_1Cz(_1Gs,new T2(1,_2B,_1S6),_));return new F(function(){return _1My(_);});}},_1Sc=E(_1HB);if(!_1Sc._){var _1Sd=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1Mx(_);});}else{var _1Se=new T(function(){return B(_H(0,E(_1Sc.a),new T(function(){return B(_1EJ(_1Sc.b));})));}),_1Sf=B(_1Cz(_1Gs,new T2(1,_2B,_1Se),_));return new F(function(){return _1Mx(_);});}},_1Sg=E(_1HA);if(!_1Sg._){var _1Sh=B(_1Cz(_1Gs,_1Dc,_));return new F(function(){return _1Mw(_);});}else{var _1Si=new T(function(){var _1Sj=E(_1Sg.a),_1Sk=new T(function(){return B(A3(_wK,_aC,new T2(1,function(_1Sl){return new F(function(){return _1Dg(_1Sj.a,_1Sl);});},new T2(1,function(_1Sm){return new F(function(){return _1Dg(_1Sj.b,_1Sm);});},_Z)),new T2(1,_F,new T(function(){return B(_1EN(_1Sg.b));}))));});return new T2(1,_G,_1Sk);}),_1Sn=B(_1Cz(_1Gs,new T2(1,_2B,_1Si),_));return new F(function(){return _1Mw(_);});}}else{return new F(function(){return _1I9(_,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp,_1Hq,_1Hr,_1Hs,_1Ht,_1Hu,_1Hv,_1I4,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1I3,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_Z,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1I1,_1I0);});}}}}}}}else{if(!E(_1HY)){return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:_1HK,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E({_:0,a:E(_1HS),b:E(_B2),c:E(_1HU),d:E(_B2),e:E(_1HW),f:E(_B2),g:E(_B2),h:E(_1HZ)}),v:E(_1I0)};}else{var _1So=E(_1Hg),_1Sp=new T(function(){var _1Sq=new T(function(){var _1Sr=B(_1rc(_1HJ));return new T2(0,_1Sr.a,_1Sr.b);}),_1Ss=new T(function(){return B(_qy(E(_1Sq).a,0))-1|0;}),_1St=function(_1Su){var _1Sv=E(_1Su);switch(_1Sv){case  -2:return E(_1I6);case  -1:return {_:0,a:E(_1I5),b:E(_1I4),c:E(B(_1k4(_Z,new T(function(){return B(_aW(E(_1Sq).b,_1HK));})))),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:_1HK,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E({_:0,a:E(_1HS),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_1HW),f:E(_B2),g:E(_B2),h:E(_1HZ)}),v:E(_1I0)};default:return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:_1Sv,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};}};switch(E(B(_1s8(E(_1Hk))))){case 32:return {_:0,a:E(_1I5),b:E(_1I4),c:E(B(_1k4(_Z,new T(function(){return B(_aW(E(_1Sq).b,_1HK));})))),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:_1HK,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E({_:0,a:E(_1HS),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_1HW),f:E(_B2),g:E(_B2),h:E(_1HZ)}),v:E(_1I0)};break;case 72:var _1Sw=E(_1HK);if(!_1Sw){return B(_1St(E(_1Ss)));}else{return B(_1St(_1Sw-1|0));}break;case 75:if(_1HK!=E(_1Ss)){return B(_1St(_1HK+1|0));}else{return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:0,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};}break;case 77:var _1Sx=E(_1HK);if(!_1Sx){return B(_1St(E(_1Ss)));}else{return B(_1St(_1Sx-1|0));}break;case 80:if(_1HK!=E(_1Ss)){return B(_1St(_1HK+1|0));}else{return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:0,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};}break;case 104:if(_1HK!=E(_1Ss)){return B(_1St(_1HK+1|0));}else{return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:0,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};}break;case 106:if(_1HK!=E(_1Ss)){return B(_1St(_1HK+1|0));}else{return {_:0,a:E(_1I5),b:E(_1I4),c:E(_1Hy),d:E(_1Hz),e:E(_1HA),f:E(_1HB),g:E(_1HC),h:E(_1I3),i:_1HF,j:_1HG,k:_1HH,l:_1HI,m:E(_1HJ),n:0,o:E(_1HL),p:E(_1HM),q:_1HN,r:E(_1HO),s:E(_1I2),t:_1HR,u:E(_1I1),v:E(_1I0)};}break;case 107:var _1Sy=E(_1HK);if(!_1Sy){return B(_1St(E(_1Ss)));}else{return B(_1St(_1Sy-1|0));}break;case 108:var _1Sz=E(_1HK);if(!_1Sz){return B(_1St(E(_1Ss)));}else{return B(_1St(_1Sz-1|0));}break;default:return E(_1I6);}});return new F(function(){return _1bB(_1So.a,_1So.b,_1Hh,_1Hi,_1Hj,_1Sp,_);});}}};if(!E(_1HU)){return new F(function(){return _1I7(_);});}else{if(!E(_1HV)){return new F(function(){return _14X(_1Hg,_1Hh,_1Hi,_1Hj,_1I5,_1Hw,_1Hx,_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI,_1HJ,_1HK,_1HL,_1HM,_1HN,_1HO,_1I2,_1HR,_1HS,_B2,_B2,_1HW,_B3,_1HY,_1HZ,_1I0,_);});}else{return new F(function(){return _1I7(_);});}}}else{return _1I6;}}else{return _1I6;}},_1SA=function(_1SB,_1SC,_1SD){var _1SE=E(_1SD);if(!_1SE._){return 0;}else{var _1SF=_1SE.b,_1SG=E(_1SE.a),_1SH=_1SG.a,_1SI=_1SG.b;return (_1SB<=_1SH)?1+B(_1SA(_1SB,_1SC,_1SF))|0:(_1SB>=_1SH+_1SG.c)?1+B(_1SA(_1SB,_1SC,_1SF))|0:(_1SC<=_1SI)?1+B(_1SA(_1SB,_1SC,_1SF))|0:(_1SC>=_1SI+_1SG.d)?1+B(_1SA(_1SB,_1SC,_1SF))|0:1;}},_1SJ=function(_1SK,_1SL,_1SM){var _1SN=E(_1SM);if(!_1SN._){return 0;}else{var _1SO=_1SN.b,_1SP=E(_1SN.a),_1SQ=_1SP.a,_1SR=_1SP.b;if(_1SK<=_1SQ){return 1+B(_1SJ(_1SK,_1SL,_1SO))|0;}else{if(_1SK>=_1SQ+_1SP.c){return 1+B(_1SJ(_1SK,_1SL,_1SO))|0;}else{var _1SS=E(_1SL);return (_1SS<=_1SR)?1+B(_1SA(_1SK,_1SS,_1SO))|0:(_1SS>=_1SR+_1SP.d)?1+B(_1SA(_1SK,_1SS,_1SO))|0:1;}}}},_1ST=function(_1SU,_1SV,_1SW){var _1SX=E(_1SW);if(!_1SX._){return 0;}else{var _1SY=_1SX.b,_1SZ=E(_1SX.a),_1T0=_1SZ.a,_1T1=_1SZ.b,_1T2=E(_1SU);if(_1T2<=_1T0){return 1+B(_1SJ(_1T2,_1SV,_1SY))|0;}else{if(_1T2>=_1T0+_1SZ.c){return 1+B(_1SJ(_1T2,_1SV,_1SY))|0;}else{var _1T3=E(_1SV);return (_1T3<=_1T1)?1+B(_1SA(_1T2,_1T3,_1SY))|0:(_1T3>=_1T1+_1SZ.d)?1+B(_1SA(_1T2,_1T3,_1SY))|0:1;}}}},_1T4=function(_1T5,_1T6){return new T2(0,new T(function(){return new T4(0,0,100,100,E(_1T6)-100);}),new T2(1,new T(function(){return new T4(0,0,E(_1T6)-100,E(_1T5),100);}),new T2(1,new T(function(){return new T4(0,0,0,E(_1T5),100);}),new T2(1,new T(function(){return new T4(0,E(_1T5)-100,100,100,E(_1T6)-100);}),new T2(1,new T(function(){return new T4(0,100,100,E(_1T5)-200,E(_1T6)-200);}),_Z)))));},_1T7=32,_1T8=76,_1T9=75,_1Ta=74,_1Tb=72,_1Tc=64,_1Td=function(_1Te,_1Tf,_1Tg,_1Th,_1Ti){var _1Tj=new T(function(){var _1Tk=E(_1Tf),_1Tl=E(_1Tk.a),_1Tm=_1Tl.a,_1Tn=_1Tl.b,_1To=B(_1T4(_1Tm,_1Tn)),_1Tp=new T(function(){var _1Tq=E(_1Tk.b);return new T2(0,new T(function(){return B(_kd(_1Tm,_1Tq.a));}),new T(function(){return B(_kd(_1Tn,_1Tq.b));}));});switch(B(_1ST(new T(function(){return E(_1Th)*E(E(_1Tp).a);},1),new T(function(){return E(_1Ti)*E(E(_1Tp).b);},1),new T2(1,_1To.a,_1To.b)))){case 1:return E(_1Tb);break;case 2:return E(_1Ta);break;case 3:return E(_1T9);break;case 4:return E(_1T8);break;case 5:return E(_1T7);break;default:return E(_1Tc);}});return function(_1Tr,_){var _1Ts=E(E(_1Tf).a),_1Tt=E(_1Tr),_1Tu=E(_1Tt.a),_1Tv=E(_1Tt.b),_1Tw=E(_1Tt.h),_1Tx=E(_1Tt.s),_1Ty=E(_1Tt.u);return new F(function(){return _1Hf(_1Te,_1Ts.a,_1Ts.b,_1Tg,_1Tj,_1Tu.a,_1Tu.b,_1Tu.c,_1Tu.d,_1Tu.e,_1Tu.f,_1Tu.g,_1Tu.h,_1Tu.i,_1Tu.j,_1Tu.k,_1Tv.a,_1Tv.b,_1Tt.c,_1Tt.d,_1Tt.e,_1Tt.f,_1Tt.g,_1Tw.a,_1Tw.b,_1Tt.i,_1Tt.j,_1Tt.k,_1Tt.l,_1Tt.m,_1Tt.n,_1Tt.o,_1Tt.p,_1Tt.q,_1Tt.r,_1Tx.a,_1Tx.b,_1Tt.t,_1Ty.a,_1Ty.b,_1Ty.c,_1Ty.d,_1Ty.e,_1Ty.f,_1Ty.g,_1Ty.h,_1Tt.v,_);});};},_1Tz=0,_1TA=2,_1TB=2,_1TC=0,_1TD=new T(function(){return eval("document");}),_1TE=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1TF=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1TG=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_1TH=function(_1TI){return E(E(_1TI).b);},_1TJ=function(_1TK,_1TL){return new F(function(){return A2(_1TH,_1TK,function(_){var _1TM=E(_1TL),_1TN=__app1(E(_1TG),_1TM);if(!_1TN){return _2U;}else{var _1TO=__app1(E(_1TF),_1TM);return new T1(1,new T2(0,_1TO,_1TM));}});});},_1TP=1,_1TQ=new T(function(){var _1TR=E(_1kX);if(!_1TR._){return E(_rm);}else{return {_:0,a:E(_1kB),b:E(B(_1fN(_1kl,5,_1lr))),c:E(_1TP),d:E(_1TR.a),e:32,f:0,g:E(_Z),h:0,i:E(_Z),j:E(_B2),k:E(_B2)};}}),_1TS=0,_1TT=4,_1TU=new T2(0,_1TT,_1TS),_1TV=new T2(0,_1TS,_1TS),_1TW={_:0,a:E(_B2),b:E(_B2),c:E(_B3),d:E(_B2),e:E(_B2),f:E(_B2),g:E(_B2),h:E(_B2)},_1TX=new T(function(){return {_:0,a:E(_1TQ),b:E(_1km),c:E(_1gY),d:E(_Z),e:E(_Z),f:E(_Z),g:E(_Z),h:E(_1TV),i:0,j:0,k:0,l: -1,m:E(_Z),n:0,o:E(_Z),p:E(_Z),q:0,r:E(_Z),s:E(_1TU),t:0,u:E(_1TW),v:E(_Z)};}),_1TY=32,_1TZ=107,_1U0=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:13:3-10"));}),_1U1=new T6(0,_2U,_2V,_Z,_1U0,_2U,_2U),_1U2=new T(function(){return B(_2S(_1U1));}),_1U3=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:14:3-12"));}),_1U4=new T6(0,_2U,_2V,_Z,_1U3,_2U,_2U),_1U5=new T(function(){return B(_2S(_1U4));}),_1U6=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:15:3-10"));}),_1U7=new T6(0,_2U,_2V,_Z,_1U6,_2U,_2U),_1U8=new T(function(){return B(_2S(_1U7));}),_1U9=104,_1Ua=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:16:3-13"));}),_1Ub=new T6(0,_2U,_2V,_Z,_1Ua,_2U,_2U),_1Uc=new T(function(){return B(_2S(_1Ub));}),_1Ud=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:17:3-12"));}),_1Ue=new T6(0,_2U,_2V,_Z,_1Ud,_2U,_2U),_1Uf=new T(function(){return B(_2S(_1Ue));}),_1Ug=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:18:3-8"));}),_1Uh=new T6(0,_2U,_2V,_Z,_1Ug,_2U,_2U),_1Ui=new T(function(){return B(_2S(_1Uh));}),_1Uj=new T1(1,50),_1Uk=108,_1Ul=106,_1Um=new T1(0,100),_1Un=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:12:3-9"));}),_1Uo=new T6(0,_2U,_2V,_Z,_1Un,_2U,_2U),_1Up=new T(function(){return B(_2S(_1Uo));}),_1Uq=function(_1Ur){return E(E(_1Ur).a);},_1Us=function(_1Ut){return E(E(_1Ut).a);},_1Uu=function(_1Uv){return E(E(_1Uv).b);},_1Uw=function(_1Ux){return E(E(_1Ux).b);},_1Uy=function(_1Uz){return E(E(_1Uz).a);},_1UA=function(_){return new F(function(){return nMV(_2U);});},_1UB=new T(function(){return B(_3d(_1UA));}),_1UC=function(_1UD){return E(E(_1UD).b);},_1UE=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1UF=function(_1UG){return E(E(_1UG).d);},_1UH=function(_1UI,_1UJ,_1UK,_1UL,_1UM,_1UN){var _1UO=B(_1Uq(_1UI)),_1UP=B(_1Us(_1UO)),_1UQ=new T(function(){return B(_1TH(_1UO));}),_1UR=new T(function(){return B(_1UF(_1UP));}),_1US=new T(function(){return B(A1(_1UJ,_1UL));}),_1UT=new T(function(){return B(A2(_1Uy,_1UK,_1UM));}),_1UU=function(_1UV){return new F(function(){return A1(_1UR,new T3(0,_1UT,_1US,_1UV));});},_1UW=function(_1UX){var _1UY=new T(function(){var _1UZ=new T(function(){var _1V0=__createJSFunc(2,function(_1V1,_){var _1V2=B(A2(E(_1UX),_1V1,_));return _3h;}),_1V3=_1V0;return function(_){return new F(function(){return __app3(E(_1UE),E(_1US),E(_1UT),_1V3);});};});return B(A1(_1UQ,_1UZ));});return new F(function(){return A3(_1Uu,_1UP,_1UY,_1UU);});},_1V4=new T(function(){var _1V5=new T(function(){return B(_1TH(_1UO));}),_1V6=function(_1V7){var _1V8=new T(function(){return B(A1(_1V5,function(_){var _=wMV(E(_1UB),new T1(1,_1V7));return new F(function(){return A(_1Uw,[_1UK,_1UM,_1V7,_]);});}));});return new F(function(){return A3(_1Uu,_1UP,_1V8,_1UN);});};return B(A2(_1UC,_1UI,_1V6));});return new F(function(){return A3(_1Uu,_1UP,_1V4,_1UW);});},_1V9=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_1Va=function(_){var _1Vb=rMV(E(_1UB)),_1Vc=E(_1Vb);if(!_1Vc._){var _1Vd=__app1(E(_1V9),E(_3h));return new F(function(){return _kK(_);});}else{var _1Ve=__app1(E(_1V9),E(_1Vc.a));return new F(function(){return _kK(_);});}},_1Vf="src",_1Vg=new T(function(){return B(unCStr("img"));}),_1Vh=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1Vi=function(_1Vj,_1Vk){return new F(function(){return A2(_1TH,_1Vj,function(_){var _1Vl=__app1(E(_1Vh),toJSStr(E(_1Vg))),_1Vm=__app3(E(_m6),_1Vl,E(_1Vf),E(_1Vk));return _1Vl;});});},_1Vn=new T(function(){return B(unCStr(".png"));}),_1Vo=function(_1Vp,_1Vq){var _1Vr=E(_1Vp);if(_1Vr==( -1)){return __Z;}else{var _1Vs=new T(function(){var _1Vt=new T(function(){return toJSStr(B(_x(_1Vq,new T(function(){return B(_x(B(_H(0,_1Vr,_Z)),_1Vn));},1))));});return B(_1Vi(_63,_1Vt));});return new F(function(){return _x(B(_1Vo(_1Vr-1|0,_1Vq)),new T2(1,_1Vs,_Z));});}},_1Vu=new T(function(){return B(unCStr("Images/Wst/wst"));}),_1Vv=new T(function(){return B(_1Vo(120,_1Vu));}),_1Vw=function(_1Vx,_){var _1Vy=E(_1Vx);if(!_1Vy._){return _Z;}else{var _1Vz=B(A1(_1Vy.a,_)),_1VA=B(_1Vw(_1Vy.b,_));return new T2(1,_1Vz,_1VA);}},_1VB=new T(function(){return B(unCStr("Images/Chara/ch"));}),_1VC=new T(function(){return B(_1Vo(56,_1VB));}),_1VD=function(_1VE,_){var _1VF=E(_1VE);if(!_1VF._){return _Z;}else{var _1VG=B(A1(_1VF.a,_)),_1VH=B(_1VD(_1VF.b,_));return new T2(1,_1VG,_1VH);}},_1VI=new T(function(){return B(unCStr("Images/img"));}),_1VJ=new T(function(){return B(_1Vo(5,_1VI));}),_1VK=function(_1VL,_){var _1VM=E(_1VL);if(!_1VM._){return _Z;}else{var _1VN=B(A1(_1VM.a,_)),_1VO=B(_1VK(_1VM.b,_));return new T2(1,_1VN,_1VO);}},_1VP=new T(function(){return eval("(function(t,f){return window.setInterval(f,t);})");}),_1VQ=new T(function(){return eval("(function(t,f){return window.setTimeout(f,t);})");}),_1VR=function(_1VS,_1VT,_1VU){var _1VV=B(_1Uq(_1VS)),_1VW=new T(function(){return B(_1TH(_1VV));}),_1VX=function(_1VY){var _1VZ=function(_){var _1W0=E(_1VT);if(!_1W0._){var _1W1=B(A1(_1VY,_kJ)),_1W2=__createJSFunc(0,function(_){var _1W3=B(A1(_1W1,_));return _3h;}),_1W4=__app2(E(_1VQ),_1W0.a,_1W2);return new T(function(){var _1W5=Number(_1W4),_1W6=jsTrunc(_1W5);return new T2(0,_1W6,E(_1W0));});}else{var _1W7=B(A1(_1VY,_kJ)),_1W8=__createJSFunc(0,function(_){var _1W9=B(A1(_1W7,_));return _3h;}),_1Wa=__app2(E(_1VP),_1W0.a,_1W8);return new T(function(){var _1Wb=Number(_1Wa),_1Wc=jsTrunc(_1Wb);return new T2(0,_1Wc,E(_1W0));});}};return new F(function(){return A1(_1VW,_1VZ);});},_1Wd=new T(function(){return B(A2(_1UC,_1VS,function(_1We){return E(_1VU);}));});return new F(function(){return A3(_1Uu,B(_1Us(_1VV)),_1Wd,_1VX);});},_1Wf=function(_1Wg){var _1Wh=E(_1Wg),_1Wi=E(_1Wh.a),_1Wj=new T(function(){return B(_x(_1Wi.b,new T(function(){return B(unAppCStr(" >>",_1Wi.c));},1)));});return new T2(0,new T2(1,_1Wh.b,_1ri),_1Wj);},_1Wk=function(_){var _1Wl=B(_1VK(_1VJ,_)),_1Wm=_1Wl,_1Wn=B(_1VD(_1VC,_)),_1Wo=_1Wn,_1Wp=B(_1Vw(_1Vv,_)),_1Wq=_1Wp,_1Wr=E(_1TE),_1Ws=__app1(_1Wr,"canvas"),_1Wt=_1Ws,_1Wu=E(_3h),_1Wv=__eq(_1Wt,_1Wu);if(!E(_1Wv)){var _1Ww=__isUndef(_1Wt);if(!E(_1Ww)){var _1Wx=__app1(_1Wr,"up"),_1Wy=__eq(_1Wx,_1Wu),_1Wz=function(_,_1WA){var _1WB=E(_1WA);if(!_1WB._){return new F(function(){return die(_1U2);});}else{var _1WC=__app1(_1Wr,"left"),_1WD=__eq(_1WC,_1Wu),_1WE=function(_,_1WF){var _1WG=E(_1WF);if(!_1WG._){return new F(function(){return die(_1U5);});}else{var _1WH=__app1(_1Wr,"ok"),_1WI=__eq(_1WH,_1Wu),_1WJ=function(_,_1WK){var _1WL=E(_1WK);if(!_1WL._){return new F(function(){return die(_1U8);});}else{var _1WM=__app1(_1Wr,"right"),_1WN=__eq(_1WM,_1Wu),_1WO=function(_,_1WP){var _1WQ=E(_1WP);if(!_1WQ._){return new F(function(){return die(_1Uc);});}else{var _1WR=__app1(_1Wr,"down"),_1WS=__eq(_1WR,_1Wu),_1WT=function(_,_1WU){var _1WV=E(_1WU);if(!_1WV._){return new F(function(){return die(_1Uf);});}else{var _1WW=B(A3(_1TJ,_63,_1Wt,_)),_1WX=E(_1WW);if(!_1WX._){return new F(function(){return die(_1Ui);});}else{var _1WY=E(_1WX.a),_1WZ=_1WY.b,_1X0=B(_a8(_1WZ,_)),_1X1=_1X0,_1X2=nMV(_1TX),_1X3=_1X2,_1X4=new T3(0,_1Wm,_1Wo,_1Wq),_1X5=B(A(_1UH,[_64,_3K,_3J,_1WL.a,_1Tz,function(_1X6,_){var _1X7=rMV(_1X3),_1X8=E(E(_1X1).a),_1X9=E(_1X7),_1Xa=E(_1X9.a),_1Xb=E(_1X9.b),_1Xc=E(_1X9.h),_1Xd=E(_1X9.s),_1Xe=E(_1X9.u),_1Xf=B(_1Hf(_1WY,_1X8.a,_1X8.b,_1X4,_1TY,_1Xa.a,_1Xa.b,_1Xa.c,_1Xa.d,_1Xa.e,_1Xa.f,_1Xa.g,_1Xa.h,_1Xa.i,_1Xa.j,_1Xa.k,_1Xb.a,_1Xb.b,_1X9.c,_1X9.d,_1X9.e,_1X9.f,_1X9.g,_1Xc.a,_1Xc.b,_1X9.i,_1X9.j,_1X9.k,_1X9.l,_1X9.m,_1X9.n,_1X9.o,_1X9.p,_1X9.q,_1X9.r,_1Xd.a,_1Xd.b,_1X9.t,_1Xe.a,_1Xe.b,_1Xe.c,_1Xe.d,_1Xe.e,_1Xe.f,_1Xe.g,_1Xe.h,_1X9.v,_)),_=wMV(_1X3,_1Xf);return _kJ;},_])),_1Xg=B(A(_1UH,[_64,_3K,_3J,_1WB.a,_1Tz,function(_1Xh,_){var _1Xi=rMV(_1X3),_1Xj=E(E(_1X1).a),_1Xk=E(_1Xi),_1Xl=E(_1Xk.a),_1Xm=E(_1Xk.b),_1Xn=E(_1Xk.h),_1Xo=E(_1Xk.s),_1Xp=E(_1Xk.u),_1Xq=B(_1Hf(_1WY,_1Xj.a,_1Xj.b,_1X4,_1TZ,_1Xl.a,_1Xl.b,_1Xl.c,_1Xl.d,_1Xl.e,_1Xl.f,_1Xl.g,_1Xl.h,_1Xl.i,_1Xl.j,_1Xl.k,_1Xm.a,_1Xm.b,_1Xk.c,_1Xk.d,_1Xk.e,_1Xk.f,_1Xk.g,_1Xn.a,_1Xn.b,_1Xk.i,_1Xk.j,_1Xk.k,_1Xk.l,_1Xk.m,_1Xk.n,_1Xk.o,_1Xk.p,_1Xk.q,_1Xk.r,_1Xo.a,_1Xo.b,_1Xk.t,_1Xp.a,_1Xp.b,_1Xp.c,_1Xp.d,_1Xp.e,_1Xp.f,_1Xp.g,_1Xp.h,_1Xk.v,_)),_=wMV(_1X3,_1Xq);return _kJ;},_])),_1Xr=B(A(_1UH,[_64,_3K,_3J,_1WG.a,_1Tz,function(_1Xs,_){var _1Xt=rMV(_1X3),_1Xu=E(E(_1X1).a),_1Xv=E(_1Xt),_1Xw=E(_1Xv.a),_1Xx=E(_1Xv.b),_1Xy=E(_1Xv.h),_1Xz=E(_1Xv.s),_1XA=E(_1Xv.u),_1XB=B(_1Hf(_1WY,_1Xu.a,_1Xu.b,_1X4,_1U9,_1Xw.a,_1Xw.b,_1Xw.c,_1Xw.d,_1Xw.e,_1Xw.f,_1Xw.g,_1Xw.h,_1Xw.i,_1Xw.j,_1Xw.k,_1Xx.a,_1Xx.b,_1Xv.c,_1Xv.d,_1Xv.e,_1Xv.f,_1Xv.g,_1Xy.a,_1Xy.b,_1Xv.i,_1Xv.j,_1Xv.k,_1Xv.l,_1Xv.m,_1Xv.n,_1Xv.o,_1Xv.p,_1Xv.q,_1Xv.r,_1Xz.a,_1Xz.b,_1Xv.t,_1XA.a,_1XA.b,_1XA.c,_1XA.d,_1XA.e,_1XA.f,_1XA.g,_1XA.h,_1Xv.v,_)),_=wMV(_1X3,_1XB);return _kJ;},_])),_1XC=B(A(_1UH,[_64,_3K,_3J,_1WQ.a,_1Tz,function(_1XD,_){var _1XE=rMV(_1X3),_1XF=E(E(_1X1).a),_1XG=E(_1XE),_1XH=E(_1XG.a),_1XI=E(_1XG.b),_1XJ=E(_1XG.h),_1XK=E(_1XG.s),_1XL=E(_1XG.u),_1XM=B(_1Hf(_1WY,_1XF.a,_1XF.b,_1X4,_1Uk,_1XH.a,_1XH.b,_1XH.c,_1XH.d,_1XH.e,_1XH.f,_1XH.g,_1XH.h,_1XH.i,_1XH.j,_1XH.k,_1XI.a,_1XI.b,_1XG.c,_1XG.d,_1XG.e,_1XG.f,_1XG.g,_1XJ.a,_1XJ.b,_1XG.i,_1XG.j,_1XG.k,_1XG.l,_1XG.m,_1XG.n,_1XG.o,_1XG.p,_1XG.q,_1XG.r,_1XK.a,_1XK.b,_1XG.t,_1XL.a,_1XL.b,_1XL.c,_1XL.d,_1XL.e,_1XL.f,_1XL.g,_1XL.h,_1XG.v,_)),_=wMV(_1X3,_1XM);return _kJ;},_])),_1XN=B(A(_1UH,[_64,_3K,_3J,_1WV.a,_1Tz,function(_1XO,_){var _1XP=rMV(_1X3),_1XQ=E(E(_1X1).a),_1XR=E(_1XP),_1XS=E(_1XR.a),_1XT=E(_1XR.b),_1XU=E(_1XR.h),_1XV=E(_1XR.s),_1XW=E(_1XR.u),_1XX=B(_1Hf(_1WY,_1XQ.a,_1XQ.b,_1X4,_1Ul,_1XS.a,_1XS.b,_1XS.c,_1XS.d,_1XS.e,_1XS.f,_1XS.g,_1XS.h,_1XS.i,_1XS.j,_1XS.k,_1XT.a,_1XT.b,_1XR.c,_1XR.d,_1XR.e,_1XR.f,_1XR.g,_1XU.a,_1XU.b,_1XR.i,_1XR.j,_1XR.k,_1XR.l,_1XR.m,_1XR.n,_1XR.o,_1XR.p,_1XR.q,_1XR.r,_1XV.a,_1XV.b,_1XR.t,_1XW.a,_1XW.b,_1XW.c,_1XW.d,_1XW.e,_1XW.f,_1XW.g,_1XW.h,_1XR.v,_)),_=wMV(_1X3,_1XX);return _kJ;},_])),_1XY=B(A(_1UH,[_64,_3K,_t,_1TD,_1TA,function(_1XZ,_){var _1Y0=B(_1Va(_)),_1Y1=rMV(_1X3),_1Y2=E(E(_1X1).a),_1Y3=E(_1Y1),_1Y4=E(_1Y3.a),_1Y5=E(_1Y3.b),_1Y6=E(_1Y3.h),_1Y7=E(_1Y3.s),_1Y8=E(_1Y3.u),_1Y9=B(_1Hf(_1WY,_1Y2.a,_1Y2.b,_1X4,E(_1XZ).a,_1Y4.a,_1Y4.b,_1Y4.c,_1Y4.d,_1Y4.e,_1Y4.f,_1Y4.g,_1Y4.h,_1Y4.i,_1Y4.j,_1Y4.k,_1Y5.a,_1Y5.b,_1Y3.c,_1Y3.d,_1Y3.e,_1Y3.f,_1Y3.g,_1Y6.a,_1Y6.b,_1Y3.i,_1Y3.j,_1Y3.k,_1Y3.l,_1Y3.m,_1Y3.n,_1Y3.o,_1Y3.p,_1Y3.q,_1Y3.r,_1Y7.a,_1Y7.b,_1Y3.t,_1Y8.a,_1Y8.b,_1Y8.c,_1Y8.d,_1Y8.e,_1Y8.f,_1Y8.g,_1Y8.h,_1Y3.v,_)),_=wMV(_1X3,_1Y9);return _kJ;},_])),_1Ya=B(A(_1UH,[_64,_3K,_3J,_1Wt,_1Tz,function(_1Yb,_){var _1Yc=E(E(_1Yb).a),_1Yd=rMV(_1X3),_1Ye=B(A(_1Td,[_1WY,_1X1,_1X4,_1Yc.a,_1Yc.b,_1Yd,_])),_=wMV(_1X3,_1Ye);return _kJ;},_])),_1Yf=B(A(_1UH,[_64,_3K,_5j,_1Wt,_1TC,function(_1Yg,_){var _1Yh=E(_1Yg),_1Yi=rMV(_1X3),_1Yj=E(_1Yi);if(!E(E(_1Yj.u).e)){var _=wMV(_1X3,_1Yj);return _kJ;}else{var _1Yk=B(_1Va(_)),_=wMV(_1X3,_1Yj);return _kJ;}},_])),_1Yl=function(_){var _1Ym=rMV(_1X3),_=wMV(_1X3,new T(function(){var _1Yn=E(_1Ym),_1Yo=E(_1Yn.u);return {_:0,a:E(_1Yn.a),b:E(_1Yn.b),c:E(_1Yn.c),d:E(_1Yn.d),e:E(_1Yn.e),f:E(_1Yn.f),g:E(_1Yn.g),h:E(_1Yn.h),i:_1Yn.i,j:_1Yn.j,k:_1Yn.k,l:_1Yn.l,m:E(_1Yn.m),n:_1Yn.n,o:E(_1Yn.o),p:E(_1Yn.p),q:_1Yn.q,r:E(_1Yn.r),s:E(_1Yn.s),t:_1Yn.t,u:E({_:0,a:E(_1Yo.a),b:E(_1Yo.b),c:E(_1Yo.c),d:E(_1Yo.d),e:E(_B2),f:E(_1Yo.f),g:E(_1Yo.g),h:E(_1Yo.h)}),v:E(_1Yn.v)};}));return _kJ;},_1Yp=function(_1Yq,_){var _1Yr=E(_1Yq),_1Ys=rMV(_1X3),_=wMV(_1X3,new T(function(){var _1Yt=E(_1Ys),_1Yu=E(_1Yt.u);return {_:0,a:E(_1Yt.a),b:E(_1Yt.b),c:E(_1Yt.c),d:E(_1Yt.d),e:E(_1Yt.e),f:E(_1Yt.f),g:E(_1Yt.g),h:E(_1Yt.h),i:_1Yt.i,j:_1Yt.j,k:_1Yt.k,l:_1Yt.l,m:E(_1Yt.m),n:_1Yt.n,o:E(_1Yt.o),p:E(_1Yt.p),q:_1Yt.q,r:E(_1Yt.r),s:E(_1Yt.s),t:_1Yt.t,u:E({_:0,a:E(_1Yu.a),b:E(_1Yu.b),c:E(_1Yu.c),d:E(_1Yu.d),e:E(_B3),f:E(_1Yu.f),g:E(_1Yu.g),h:E(_1Yu.h)}),v:E(_1Yt.v)};})),_1Yv=B(A(_1VR,[_64,_1Um,_1Yl,_]));return _kJ;},_1Yw=B(A(_1UH,[_64,_3K,_5j,_1Wt,_1TB,_1Yp,_])),_1Yx=function(_){var _1Yy=rMV(_1X3),_1Yz=E(_1Yy),_1YA=_1Yz.a,_1YB=_1Yz.b,_1YC=_1Yz.c,_1YD=_1Yz.d,_1YE=_1Yz.e,_1YF=_1Yz.f,_1YG=_1Yz.g,_1YH=_1Yz.h,_1YI=_1Yz.i,_1YJ=_1Yz.j,_1YK=_1Yz.k,_1YL=_1Yz.l,_1YM=_1Yz.m,_1YN=_1Yz.n,_1YO=_1Yz.o,_1YP=_1Yz.p,_1YQ=_1Yz.q,_1YR=_1Yz.r,_1YS=_1Yz.s,_1YT=_1Yz.t,_1YU=_1Yz.v,_1YV=E(_1Yz.u),_1YW=new T(function(){if(_1YT<=298){return _1YT+1|0;}else{return E(_1Gx);}}),_1YX=new T(function(){var _1YY=function(_1YZ){var _1Z0=E(_1YZ);return (_1Z0==30)?{_:0,a:E(_1YA),b:E(_1YB),c:E(_1YC),d:E(B(_x(B(_0(_Z,B(_1Ha(B(_aj(_1EX,_1YP)),B(_9T(_1YD)))))),new T(function(){return B(_aj(_1Wf,_1YP));},1)))),e:E(_1YE),f:E(_1YF),g:E(_1YG),h:E(_1YH),i:_1YI,j:_1YJ,k:_1YK,l:_1YL,m:E(_1YM),n:_1YN,o:E(_1YO),p:E(_1YP),q:30,r:E(_1YR),s:E(_1YS),t:E(_1YW),u:E(_1YV),v:E(_1YU)}:{_:0,a:E(_1YA),b:E(_1YB),c:E(_1YC),d:E(_1YD),e:E(_1YE),f:E(_1YF),g:E(_1YG),h:E(_1YH),i:_1YI,j:_1YJ,k:_1YK,l:_1YL,m:E(_1YM),n:_1YN,o:E(_1YO),p:E(_1YP),q:_1Z0,r:E(_1YR),s:E(_1YS),t:E(_1YW),u:E(_1YV),v:E(_1YU)};};if(!E(_1YP)._){return B(_1YY(_1YQ));}else{if(!B(_et(E(_1YW),20))){return B(_1YY(_1YQ+1|0));}else{return B(_1YY(_1YQ));}}});if(!E(_1YV.b)){if(!E(_1YV.h)){var _1Z1=E(E(_1X1).a),_1Z2=E(_1YX),_1Z3=E(_1Z2.b),_1Z4=E(_1Z2.h),_1Z5=E(_1Z2.u),_1Z6=B(_12L(_1WY,_1Z1.a,_1Z1.b,_1X4,_1Z2.a,_1Z3.a,_1Z3.b,_1Z2.c,_1Z2.d,_1Z2.e,_1Z2.f,_1Z2.g,_1Z4.a,_1Z4.b,_1Z2.i,_1Z2.j,_1Z2.k,_1Z2.l,_1Z2.m,_1Z2.n,_1Z2.o,_1Z2.p,_1Z2.q,_1Z2.r,_1Z2.s,_1Z2.t,_1Z5.a,_1Z5.b,_1Z5.c,_1Z5.d,_1Z5.e,_1Z5.f,_1Z5.g,_1Z5.h,_1Z2.v,_)),_=wMV(_1X3,_1Z6);return _kJ;}else{if(!B(_et(E(_1YW),10))){if(!E(_1YV.c)){var _1Z7=E(E(_1X1).a),_1Z8=B(_1bB(_1WY.a,_1WZ,_1Z7.a,_1Z7.b,_1X4,_1YX,_)),_=wMV(_1X3,_1Z8);return _kJ;}else{var _1Z9=E(E(_1X1).a),_1Za=E(_1YX),_1Zb=E(_1Za.b),_1Zc=E(_1Za.h),_1Zd=E(_1Za.u),_1Ze=B(_12L(_1WY,_1Z9.a,_1Z9.b,_1X4,_1Za.a,_1Zb.a,_1Zb.b,_1Za.c,_1Za.d,_1Za.e,_1Za.f,_1Za.g,_1Zc.a,_1Zc.b,_1Za.i,_1Za.j,_1Za.k,_1Za.l,_1Za.m,_1Za.n,_1Za.o,_1Za.p,_1Za.q,_1Za.r,_1Za.s,_1Za.t,_1Zd.a,_1Zd.b,_1Zd.c,_1Zd.d,_1Zd.e,_1Zd.f,_1Zd.g,_1Zd.h,_1Za.v,_)),_=wMV(_1X3,_1Ze);return _kJ;}}else{var _1Zf=E(E(_1X1).a),_1Zg=E(_1YX),_1Zh=E(_1Zg.b),_1Zi=E(_1Zg.h),_1Zj=E(_1Zg.u),_1Zk=B(_12L(_1WY,_1Zf.a,_1Zf.b,_1X4,_1Zg.a,_1Zh.a,_1Zh.b,_1Zg.c,_1Zg.d,_1Zg.e,_1Zg.f,_1Zg.g,_1Zi.a,_1Zi.b,_1Zg.i,_1Zg.j,_1Zg.k,_1Zg.l,_1Zg.m,_1Zg.n,_1Zg.o,_1Zg.p,_1Zg.q,_1Zg.r,_1Zg.s,_1Zg.t,_1Zj.a,_1Zj.b,_1Zj.c,_1Zj.d,_1Zj.e,_1Zj.f,_1Zj.g,_1Zj.h,_1Zg.v,_)),_=wMV(_1X3,_1Zk);return _kJ;}}}else{var _=wMV(_1X3,_1YX);return _kJ;}},_1Zl=B(A(_1VR,[_64,_1Uj,_1Yx,_]));return _kJ;}}};if(!E(_1WS)){var _1Zm=__isUndef(_1WR);if(!E(_1Zm)){return new F(function(){return _1WT(_,new T1(1,_1WR));});}else{return new F(function(){return _1WT(_,_2U);});}}else{return new F(function(){return _1WT(_,_2U);});}}};if(!E(_1WN)){var _1Zn=__isUndef(_1WM);if(!E(_1Zn)){return new F(function(){return _1WO(_,new T1(1,_1WM));});}else{return new F(function(){return _1WO(_,_2U);});}}else{return new F(function(){return _1WO(_,_2U);});}}};if(!E(_1WI)){var _1Zo=__isUndef(_1WH);if(!E(_1Zo)){return new F(function(){return _1WJ(_,new T1(1,_1WH));});}else{return new F(function(){return _1WJ(_,_2U);});}}else{return new F(function(){return _1WJ(_,_2U);});}}};if(!E(_1WD)){var _1Zp=__isUndef(_1WC);if(!E(_1Zp)){return new F(function(){return _1WE(_,new T1(1,_1WC));});}else{return new F(function(){return _1WE(_,_2U);});}}else{return new F(function(){return _1WE(_,_2U);});}}};if(!E(_1Wy)){var _1Zq=__isUndef(_1Wx);if(!E(_1Zq)){return new F(function(){return _1Wz(_,new T1(1,_1Wx));});}else{return new F(function(){return _1Wz(_,_2U);});}}else{return new F(function(){return _1Wz(_,_2U);});}}else{return new F(function(){return die(_1Up);});}}else{return new F(function(){return die(_1Up);});}},_1Zr=function(_){return new F(function(){return _1Wk(_);});};
var hasteMain = function() {B(A(_1Zr, [0]));};window.onload = hasteMain;