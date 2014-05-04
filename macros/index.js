// sparkler.js
macro $sparkler__compile {
  case { $$mac $ctx $name { $body ... } } => {
    var ctx = #{ $ctx };
    var here = #{ here };
    var fnName = #{ $name };

    let letstx = macro {
      case { $mac $id:ident $punc = $rhs:expr } => {
        var mac = #{ $mac };
        var id  = #{ $id };
        var val = #{ $val };
        var arg = #{ $($rhs) };
        var punc = #{ $punc };
        var here = #{ here };
        if (punc[0].token.type !== parser.Token.Punctuator ||
            punc[0].token.value !== '...') {
          throw new SyntaxError('Unexpected token: ' + punc[0].token.value +
                                ' (expected ...)');
        }
        if (id[0].token.value[0] !== '$') {
          throw new SyntaxError('Syntax identifiers must start with $: ' + 
                                id[0].token.value);
        }
        return [
          makeIdent('match', mac),
          makePunc('.', here),
          makeIdent('patternEnv', here),
          makeDelim('[]', [makeValue(id[0].token.value, here)], here),
          makePunc('=', here),
          makeDelim('{}', [
            makeIdent('level', here), makePunc(':', here), makeValue(1, here), makePunc(',', here),
            makeIdent('match', here), makePunc(':', here), makeDelim('()', #{
              (function(exp) {
                return exp.length
                  ? exp.map(function(t) { return { level: 0, match: [t] } })
                  : [{ level: 0, match: [] }];
              })
            }, here), makeDelim('()', arg, here)
          ], here)
        ];
      }
      case { $mac $id:ident = $rhs:expr } => {
        var mac = #{ $mac };
        var id  = #{ $id };
        var val = #{ $val };
        var arg = #{ $($rhs) };
        var here = #{ here };
        if (id[0].token.value[0] !== '$') {
          throw new SyntaxError('Syntax identifiers must start with $: ' + 
                                id[0].token.value);
        }
        return [
          makeIdent('match', mac),
          makePunc('.', here),
          makeIdent('patternEnv', here),
          makeDelim('[]', [makeValue(id[0].token.value, here)], here),
          makePunc('=', here),
          makeDelim('{}', [
            makeIdent('level', here), makePunc(':', here), makeValue(0, here), makePunc(',', here),
            makeIdent('match', here), makePunc(':', here), arg[0]
          ], here)
        ];
      }
    }
    function syntaxError(tok, err, info) {
      if (!err) err = 'Unexpected token';
      if (info) err += ' (' + info + ')';
      throwSyntaxError('sparkler', err, tok);
    }
    var refId = 0;
    function makeRef(rhs, ctx) {
      if (!ctx) ctx = here;
      var name = makeIdent('r' + (refId++), ctx);
      var stx = makeAssign(name, rhs, ctx);
      return {
        name: [name],
        stx: stx
      };
    }
    function makeAssign(name, rhs, ctx) {
      if (!ctx) ctx = here;
      return _.flatten([
        makeKeyword('var', ctx), name, rhs ? [makePunc('=', ctx), rhs] : [], makePunc(';', ctx)
      ]);
    }
    function makeArgument(i, env, ctx) {
      if (!ctx) ctx = here;
      if (env.argNames.length) {
        return { name: [env.argNames[i]] };
      }
      var index = i < 0
        ? [makeIdent('arguments', ctx), makePunc('.', ctx), makeIdent('length', ctx), 
           makePunc('-', ctx), makeValue(Math.abs(i), ctx)]
        : [makeValue(i, ctx)];
      return makeRef([makeIdent('arguments', ctx), makeDelim('[]', index, ctx)]);
    }
    function indexOfRest(patt) {
      for (var i = 0; i < patt.children.length; i++) {
        if (patt.children[i].type === 'rest') return i;
      }
      return -1;
    }
    function joinPatterns(j, cs) {
      return cs.map(function(c) { return c.pattern }).join(j);
    }
    function joinRefs(refs) {
      if (!refs.length) return [];
      refs = _.flatten(intercalate(makePunc(',', here), refs.map(function(r) {
        return r.stx ? r.stx.slice(1, -1) : r.slice(1, -1);
      })));
      return [makeKeyword('var', here)].concat(refs, makePunc(';', here));
    }
    function joinAlternates(alts) {
      if (alts.length === 1) return alts[0][2].token.inner;
      return alts.reduce(function(acc, alt, i) {
        if (i === alts.length - 1) {
          alt = [makeKeyword('else', here)].concat(alt[2]);
        } else if (i > 0) {
          alt = [makeKeyword('else', here)].concat(alt);
        }
        return acc.concat(alt);
      }, []);
    }
    function findIdents(patt) {
      return patt.reduce(function(a, p) {
        if (p.type === 'identifier' || p.type === 'binder') a = a.concat(p);
        if (p.children) a = a.concat(findIdents(p.children));
        return a;
      }, []);
    }
    function replaceIdents(guard, names) {
      names = names.reduce(function(acc, n) {
        acc[n[0]] = n[1].name ? n[1].name[0] : n[1].stx[0];
        return acc;
      }, {});
      function traverse(arr) {
        for (var i = 0, s; s = arr[i]; i++) {
          if (s.token.type === T.Delimiter) traverse(s.token.inner);
          if (s.token.type === T.Identifier && 
              names.hasOwnProperty(s.token.value)) {
            arr.splice(i, 1, names[s.token.value]);
          }
        }
        return arr;
      }
      return traverse(guard);
    }
    function wrapBlock(toks) {
      if (matchesToken(BRACES, toks[0])) {
        return toks;
      }
      return [makeDelim('{}', toks, here)];
    }
    function intercalate(x, a) {
      var arr = [];
      for (var i = 0; i < a.length; i++) {
        if (i > 0) arr.push(x);
        arr.push(a[i]);
      }
      return arr;
    }
    function shouldStateBacktrack(args) {
      if (args.length === 1) return false;
      return shouldArgBacktrack(args[0]);
    }
    function shouldArgBacktrack(arg) {
      var patt = arg.pattern;
      var child = arg.children[0];
      if (patt === '$' || patt === '*' || patt === '...' ||
          child.type === 'literal' && !matchesToken(STRING, child.stx[0])) return false;
      return true;
    }
    function shouldCompileBacktrack(cases) {
      var len = cases.reduce(function(acc, c) {
        return c.args.children.length > acc ? c.args.children.length : acc;
      }, 0);
      for (var j = 0; j < len; j++) {
        var patts = [];
        for (var i = 0, c; c = cases[i]; i++) {
          var arg = c.args.children[j];
          if (arg && patts.indexOf(arg.pattern) > 0 && shouldArgBacktrack(arg)) {
            return true;
          }
          patts.unshift(arg ? arg.pattern : null);
        }
      }
      return false;
    }
    var T        = parser.Token;
    var EQ       = { type: T.Punctuator, value: '=' };
    var ARROW    = { type: T.Punctuator, value: '=>' };
    var REST     = { type: T.Punctuator, value: '...' };
    var COLON    = { type: T.Punctuator, value: ':' };
    var AT       = { type: T.Punctuator, value: ':' };
    var COMMA    = { type: T.Punctuator, value: ',' };
    var PERIOD   = { type: T.Punctuator, value: '.' };
    var WILDCARD = { type: T.Punctuator, value: '*' };
    var SCOLON   = { type: T.Punctuator, value: ';' };
    var UNDEF    = { type: T.Identifier, value: 'undefined' };
    var VOID     = { type: T.Keyword,    value: 'void' };
    var CASE     = { type: T.Keyword,    value: 'case' };
    var VAR      = { type: T.Keyword,    value: 'var' };
    var IF       = { type: T.Keyword,    value: 'if' };
    var ELSE     = { type: T.Keyword,    value: 'else' };
    var FOR      = { type: T.Keyword,    value: 'for' };
    var RETURN   = { type: T.Keyword,    value: 'return' };
    var CONTINUE = { type: T.Keyword,    value: 'continue' };
    var BRACKETS = { type: T.Delimiter,  value: '[]' };
    var PARENS   = { type: T.Delimiter,  value: '()' };
    var BRACES   = { type: T.Delimiter,  value: '{}' };
    var IDENT    = { type: T.Identifier };
    var BOOL     = { type: T.BooleanLiteral };
    var NULL     = { type: T.NullLiteral };
    var STRING   = { type: T.StringLiteral };
    var NUMBER   = { type: T.NumericLiteral };
    function input(stx) {
      var pos = 0;
      var inp = {
        length: stx.length,
        buffer: stx,
        peek: peek,
        take: take,
        takeAPeek: takeAPeek,
        back: back,
        rest: rest
      };
      return inp;
      function peek() {
        if (arguments.length === 0) {
          return [stx[pos]];
        }
        if (typeof arguments[0] === 'number') {
          if (inp.length < arguments[0]) return;
          return stx.slice(pos, pos + arguments[0]);
        }
        var res = [];
        for (var i = 0, j = pos, t, a, m; i < arguments.length; i++) {
          a = arguments[i];
          t = stx[j++];
          if (!matchesToken(a, t)) return;
          res.push(t);
        }
        return res;
      }
      function take(len) {
        var res = stx.slice(pos, pos + (len || 1));
        pos += len || 1;
        inp.length -= len || 1;
        return res;
      }
      function takeAPeek() {
        var res = peek.apply(null, arguments);
        if (res) return take(res.length);
      }
      function back(len) {
        pos -= len || 1;
        inp.length += len || 1;
      }
      function rest() {
        return stx.slice(pos);
      }
    }
    function parse(stx) {
      var inp = input(stx);
      var cases = [];
      var patts = {};
      while (inp.length) {
        var list = scanArgumentList(inp);
        var first = list[0]; 
        var guard = scanGuard(inp);
        var body = scanCaseBody(inp);
        var args = parseArgumentList(input(list));
        if (!guard.length) {
          if (patts.hasOwnProperty(args.pattern)) {
            syntaxError(first, 'Duplicate argument case: (' + args.pattern + ')');
          } else {
            patts[args.pattern] = true;
          }
        }
        cases.push({
          args: args,
          guard: guard,
          body: body.map(function(b) {
            b.userCode = true;
            return b;
          })
        });
      }
      return cases;
    }
    function scanArgumentList(inp) {
      var tok = inp.takeAPeek(CASE);
      if (!tok) syntaxError(inp.take(), null, 'expected case');
      var res = inp.takeAPeek(PARENS);
      if (res) {
        if (inp.peek(IF) || inp.peek(ARROW)) return res[0].expose().token.inner;
        if (inp.peek(EQ)) syntaxError(inp.take(), null, 'maybe you meant =>');
        throw syntaxError(inp.take());
      }
      res = [];
      while (inp.length) {
        if (inp.peek(IF) || inp.peek(ARROW)) return res;
        if (inp.peek(EQ)) syntaxError(inp.take(), null, 'maybe you meant =>');
        if (inp.peek(COMMA)) syntaxError(inp.take(), null, 'multiple parameters require parens');
        res.push(inp.take()[0]);
      }
      if (res.length) syntaxError(res[res.length - 1], 'Case body required');
      else syntaxError(tok, 'Argument list required');
    }
    function scanGuard(inp) {
      var tok = inp.takeAPeek(IF);
      if (!tok) return [];
      var res = [];
      while (inp.length) {
        if (inp.peek(ARROW)) {
          if (!res.length) syntaxError(tok, 'Guard required');
          return res;
        }
        res.push(inp.take()[0]);
      }
      if (res.length) syntaxError(res[res.length - 1], 'Case body required');
      else syntaxError(tok, 'Guard required');
    }
    function scanCaseBody(inp) {
      inp.take(1);
      var res = inp.takeAPeek(BRACES);
      if (res) {
        if (inp.peek(CASE) || !inp.length) {
          return forceReturn(res[0].expose().token.inner);
        }
        syntaxError(inp.take(), null, 'maybe you meant case');
      }
      res = [];
      while (inp.length) {
        if (inp.peek(CASE)) break;
        res.push(inp.take(1)[0]);
      }
      return prependReturn(res);
    }
    function matchesToken(tmpl, t) {
      if (t && t.length === 1) t = t[0];
      if (!t || tmpl.type && t.token.type !== tmpl.type 
             || tmpl.value && t.token.value !== tmpl.value) return false;
      return true;
    }
    function prependReturn(stx) {
      if (matchesToken({ type: T.Keyword, value: 'return' }, stx[0])) {
        return stx;
      }
      var ret = makeKeyword('return', stx[0])
      return [ret].concat(stx);
    }
    function forceReturn(stx) {
      var needsReturn = true;
      var inp = input(stx);
      var res = [], toks;
      while (inp.length) {
        if (toks = inp.takeAPeek({ type: T.Keyword }, PARENS, RETURN)) {
          res = res.concat(toks);
        } else if (toks = inp.takeAPeek(RETURN)) {
          needsReturn = false;
          res.push(toks[0]);
        } else {
          res.push(inp.take()[0]);
        }
      }
      if (needsReturn) res.push(makeKeyword('return', here));
      return res;
    }
    function parseArgumentList(inp) {
      return inp.length
        ? $arguments(parseRestPatterns(inp).map($argument))
        : $arguments([$unit()]);
    }
    function parseRestPatterns(inp) {
      return commaSeparated(parseRestPattern, inp, multiRestCallback());
    }
    function parseRestPattern(inp) {
      return parseRest(inp) || parsePattern(inp);
    }
    function parsePattern(inp) {
      return parseWildcard(inp)
          || parseUndefined(inp)
          || parseLiteral(inp)
          || parseArray(inp)
          || parseObject(inp)
          || parseExtractor(inp)
          || parseBinder(inp)
          || parseIdentifier(inp);
    }
    function parseRest(inp) {
      var res = inp.takeAPeek(REST);
      if (res) return $rest(res, parsePattern(inp) || $wildcard());
    }
    function parseWildcard(inp) {
      var res = inp.takeAPeek(WILDCARD);
      if (res) return $wildcard(res);
    }
    function parseUndefined(inp) {
      var res = inp.takeAPeek(VOID);
      if (res) {
        var stx = inp.peek(1);
        if (stx[0].token.type !== T.Punctuator) {
          inp.take(1);
          return $undefined(res);
        }
      }
      res = inp.takeAPeek(UNDEF);
      if (res) return $undefined(res);
    }
    function parseLiteral(inp) {
      var stx = inp.peek(1);
      if (matchesToken(NULL, stx) || matchesToken(NUMBER, stx) ||
          matchesToken(STRING, stx) || matchesToken(BOOL, stx)) {
        return $literal(inp.take(1));
      }
    }
    function parseExtractor(inp) {
      var stx = [], tok;
      while (tok = inp.peek()) {
        if (stx.length === 0 && matchesToken(IDENT, tok) ||
            stx.length && matchesToken(IDENT, stx[0]) && matchesToken(PERIOD, tok) ||
            stx.length && matchesToken(IDENT, tok) && matchesToken(PERIOD, stx[0])) {
          stx.unshift(inp.take()[0]);
        } else break;
      }
      if (stx.length) {
        if (matchesToken(PERIOD, stx[0])) syntaxError(stx[0]);
        var name = stx[0].token.value;
        if (name[0].toUpperCase() === name[0] &&
            name[0] !== '$' && name[0] !== '_') {
          var ext = parseUnapply(inp) || parseObject(inp);
          return $extractor(stx.reverse(), ext);
        } else {
          inp.back(stx.length);
        }
      }
    }
    function parseArray(inp) {
      var stx = inp.takeAPeek(BRACKETS);
      if (stx) {
        var inp2 = input(stx[0].token.inner);
        return $array(parseRestPatterns(inp2));
      }
    }
    function parseUnapply(inp) {
      var stx = inp.takeAPeek(PARENS);
      if (stx) {
        var inp2 = input(stx[0].token.inner);
        return $unapply(parseRestPatterns(inp2));
      }
    }
    function parseObject(inp) {
      var stx = inp.takeAPeek(BRACES);
      if (stx) {
        var inp2 = input(stx[0].token.inner);
        return $object(commaSeparated(parseObjectPattern, inp2));
      }
    }
    function parseObjectPattern(inp) {
      var res = parseBinder(inp);
      if (res) return $key(res);
      var tok = inp.takeAPeek({ type: T.Identifier }) ||
                inp.takeAPeek({ type: T.StringLiteral });
      if (tok) {
        var key = tok[0].token.type === T.Identifier
          ? $identifier(tok)
          : $literal(tok)
        if (inp.takeAPeek(COLON)) {
          var patt = parsePattern(inp);
          if (patt) return $keyValue(key, patt);
          syntaxError(inp.take(), null, 'not a pattern');
        }
        return $key(key);
      }
    }
    function parseBinder(inp) {
      var res = inp.takeAPeek({ type: T.Identifier }, AT);
      if (res) {
        var patt = parsePattern(inp);
        if (patt) return $binder([res[0]], patt);
        syntaxError(inp.take(), null, 'not a pattern');
      }
    }
    function parseIdentifier(inp) {
      var res = inp.takeAPeek({ type: T.Identifier });
      if (res) return $identifier(res);
    }
    function commaSeparated(parser, inp, cb) {
      var all = [], res;
      while (inp.length) {
        res = parser(inp);
        if (res && !cb || res && cb(res, inp)) {
          all.push(res);
          if (!inp.takeAPeek(COMMA) && inp.length) {
            syntaxError(inp.take(), null, 'maybe you meant ,');
          }
        } else if (!res) {
          syntaxError(inp.take());
        }
      }
      return all;
    }
    function multiRestCallback() {
      var count = 0;
      return function(res, inp) {
        if (res.type === 'rest' && count++) {
          syntaxError(res.stx, 'Multiple ...s are not allowed');
        }
        return true;
      }
    }
    function $wildcard() {
      return { 
        type: 'wildcard',
        pattern: '*'
      };
    }
    function $undefined() {
      return { 
        type: 'undefined', 
        pattern: 'undefined'
      };
    }
    function $literal(stx) {
      var val  = stx[0].token.value;
      var type = stx[0].token.type;
      return {
        type: 'literal',
        pattern: type === T.BooleanLiteral || 
                 type === T.NullLiteral ? val : JSON.stringify(val),
        stx: stx
      };
    }
    function $extractor(name, extractor) {
      var namePatt = name.reduce(function(acc, n) {
        return acc + n.token.value;
      }, '');
      return {
        type: 'extractor',
        pattern: namePatt + (extractor ? extractor.pattern : ''),
        stx: name,
        children: extractor && [extractor]
      };
    }
    function $arguments(args) {
      args.forEach(function(x, i) {
        if (x.pattern.indexOf('...') === 0 && i !== args.length - 1) {
          syntaxError(x.children[0].stx, 'Rest arguments are only allowed at the end');
        }
      });
      return {
        type: 'arguments',
        pattern: joinPatterns(',', args),
        children: args
      };
    }
    function $argument(patt) {
      return {
        type: 'argument',
        pattern: patt.pattern,
        children: [patt]
      };
    }
    function $rest(stx, patt) {
      return {
        type: 'rest',
        pattern: '...' + patt.pattern,
        children: [patt],
        stx: stx
      };
    }
    function $array(items) {
      return {
        type: 'array',
        pattern: '[' + joinPatterns(',', items) + ']',
        children: items
      };
    }
    function $unapply(items) {
      return {
        type: 'unapply',
        pattern: '(' + joinPatterns(',', items) + ')',
        children: items
      };
    }
    function $object(items) {
      items = _.sortBy(items, function(i) {
        return i.pattern;
      });
      return {
        type: 'object',
        pattern: '{' + joinPatterns(',', items) + '}',
        children: items
      };
    }
    function $keyValue(key, value) {
      var pattern = key.type === 'literal'
        ? key.pattern
        : JSON.stringify(key.name)
      return {
        type: 'keyValue',
        pattern: pattern + ':' + value.pattern,
        stx: key.stx,
        children: [value]
      };
    }
    function $key(key) {
      var pattern = key.type === 'literal'
        ? key.pattern + ':*'
        : JSON.stringify(key.name) + ':' + key.pattern;
      return {
        type: 'key',
        pattern: pattern,
        children: [key]
      };
    }
    function $binder(ident, patt) {
      return {
        type: 'binder',
        pattern: '$:' + patt.pattern,
        name: ident[0].token.value,
        stx: ident,
        children: [patt] 
      };
    }
    function $identifier(ident) {
      return {
        type: 'identifier',
        pattern: '$',
        name: ident[0].token.value,
        stx: ident
      };
    }
    function $unit() {
      return {
        type: 'unit',
        pattern: '',
        children: []
      };
    }
    function environment(vars) {
      var env = _.extend({
        set: set,
        addName: addName,
        addHead: addHead
      }, vars);
      return env;
      function set(mod) {
        return environment(_.extend({}, vars, mod));
      }
      function addName(stx) {
        return set({
          names: vars.names.concat({ stx: stx })
        });
      }
      function addHead(name, stx) {
        if (!vars.head[name]) vars.head[name] = stx;
        return env;
      }
    }
    var TO_STR_REF = makeRef(#{ Object.prototype.toString });
    var natives = {
      'Boolean'    : makeRef(#{ '[object Boolean]' }),
      'Number'     : makeRef(#{ '[object Number]' }),
      'String'     : makeRef(#{ '[object String]' }),
      'RegExp'     : makeRef(#{ '[object RegExp]' }),
      'Date'       : makeRef(#{ '[object Date]' }),
      'Array'      : makeRef(#{ '[object Array]' }),
      'Object'     : makeRef(#{ '[object Object]' }),
      'Function'   : makeRef(#{ '[object Function]' }),
      'Undefined'  : makeRef(#{ '[object Undefined]' }),
      'Null'       : makeRef(#{ '[object Null]' }),
      'Math'       : makeRef(#{ '[object Math]' }),
      'Arguments'  : makeRef(#{ '[object Arguments]' }),
    }
    var compilers = {
      'argument'   : compileArgument,
      'unit'       : compileUnit,
      'wildcard'   : compileWildcard,
      'undefined'  : compileUndefined,
      'literal'    : compileLiteral,
      'identifier' : compileIdentifier,
      'binder'     : compileBinder,
      'extractor'  : compileExtractor,
      'object'     : compileObject,
      'keyValue'   : compileKeyValue,
      'key'        : compileKey,
      'unapply'    : compileArray,
      'array'      : compileArray,
      'rest'       : compileRest,
    };
    function compile(cases) {
      return shouldCompileBacktrack(cases)
        ? compileBacktrack(cases)
        : compileSimple(cases);
    }
    function compilePattern(patt, env, cont) {
      return compilers[patt.type](patt, env, cont);
    }
    function compileArgument(patt, env, cont) {
      var child = patt.children[0];
      if (child.type === 'rest') {
        var childEnv = env.set({
          ref: { name: #{ arguments }},
          start: env.level,
          stop: 0,
          level: env.level + 1
        });
        return compilePattern(child, childEnv, cont);
      }
      else {
        var ref = makeArgument(env.level, env);
        var childEnv = env.set({ ref: ref, level: env.level + 1 });
        var bod = compilePattern(child, childEnv, cont);
        return ref.stx && patt.pattern !== '*' ? ref.stx.concat(bod) : bod;
      }
    }
    function compileUnit(patt, env, cont) {
      letstx $bod ... = cont(env);
      return #{
        if (arguments.length === 0) { $bod ...  }
      }
    }
    function compileWildcard(patt, env, cont) {
      return cont(env);
    }
    function compileUndefined(patt, env, cont) {
      letstx $bod ... = cont(env);
      letstx $ref = env.ref.name;
      return #{
        if ($ref === void 0) { $bod ... }
      }
    }
    function compileLiteral(patt, env, cont) {
      letstx $bod ... = cont(env);
      letstx $ref = env.ref.name;
      letstx $lit = patt.stx;
      return #{
        if ($ref === $lit) { $bod ... }
      }
    }
    function compileIdentifier(patt, env, cont) {
      env = env.addName(env.ref.name);
      return cont(env);
    }
    function compileBinder(patt, env, cont) {
      env = env.addName(env.ref.name);
      return compilePattern(patt.children[0], env, cont);
    }
    function compileExtractor(patt, env, cont) {
      var child = patt.children && patt.children[0];
      var clsName = patt.stx[patt.stx.length - 1].token.value;
      if (child && child.type === 'unapply') {
        var arrRef = makeRef();
        var childEnv = env.set({ ref: arrRef });
        letstx $bod ... = compilePattern(child, childEnv, cont);
        letstx $cls ... = patt.stx;
        letstx $arr = arrRef.name;
        letstx $ref = env.ref.name;
        return #{
          var $arr = $cls ... .unapply($ref);
          $bod ...
        }
      }
      else if (child && child.type === 'object') {
        var objRef = makeRef();
        var childEnv = env.set({ hasOwn: true, ref: objRef });
        letstx $bod ... = compilePattern(child, childEnv, cont);
        letstx $cls ... = patt.stx;
        letstx $obj = objRef.name;
        letstx $ref = env.ref.name;
        return #{
          var $obj = $cls ... .unapplyObject($ref);
          $bod ...
        }
      }
      else if (patt.stx.length === 1 && natives[clsName]) {
        env = env
          .addHead('toStr', TO_STR_REF)
          .addHead(clsName, natives[clsName]);
        letstx $bod ... = cont(env);
        letstx $toStr = TO_STR_REF.name;
        letstx $natStr = natives[clsName].name;
        letstx $ref = env.ref.name;
        return #{
          if ($toStr.call($ref) === $natStr) { $bod ... }
        }
      }
      else if (patt.stx.length === 1 && clsName === 'NaN') {
        env = env
          .addHead('toStr', TO_STR_REF)
          .addHead(clsName, natives.Number);
        letstx $bod ... = cont(env);
        letstx $toStr = TO_STR_REF.name;
        letstx $natStr = natives.Number.name;
        letstx $ref = env.ref.name;
        return #{
          if ($toStr.call($ref) === $natStr && $ref !== +$ref) { $bod ... }
        }
      }
      else {
        letstx $bod ... = cont(env);
        letstx $cls ... = patt.stx;
        letstx $ref = env.ref.name;
        return #{
          if ($cls ... .hasInstance
              ? $cls ... .hasInstance($ref)
              : $ref instanceof $cls ...) { $bod ... }
        }
      }
    }
    function compileObject(patt, env, cont) {
      var primRef = env.ref;
      env = env.set({ ref: makeRef() });
      cont = patt.children.reduceRight(function(c, p) {
        return function() {
          return compilePattern(p, env, function(e) {
            env = env.set({ names: e.names });
            return c(env);
          });
        };
      }, cont);
      letstx $bod ... = cont(env);
      letstx $ref = primRef.name;
      letstx $box = env.ref.name;
      return #{
        if ($ref != null) {
          var $box = Object($ref);
          $bod ...
        }
      }
    }
    function makeObjectCheck(ref, key, bod, env) {
      letstx $bod ... = bod;
      letstx $key = key;
      letstx $ref = ref;
      if (env.hasOwn) {
        return #{
          if ($ref.hasOwnProperty($key)) { $bod ... }
        }
      } else {
        return #{
          if ($key in $ref) { $bod ... }
        }
      }
    }
    function compileKeyValue(patt, env, cont) {
      var key = [makeValue(patt.stx[0].token.value, here)];
      var ref = makeRef([env.ref.name, makeDelim('[]', key, here)]);
      var childEnv = env.set({ ref: ref, hasOwn: false });
      var bod = ref.stx.concat(compilePattern(patt.children[0], childEnv, cont));
      return makeObjectCheck(env.ref.name, key, bod, env);
    }
    function compileKey(patt, env, cont) {
      var child = patt.children[0];
      if (child.type === 'literal') {
        return makeObjectCheck(env.ref.name, child.stx, cont(env), env);
      }
      var key = [makeValue(child.name, here)];
      var ref = makeRef([env.ref.name, makeDelim('[]', key, here)]);
      var childEnv = env.set({ ref: ref, hasOwn: false });
      var bod = ref.stx.concat(compilePattern(child, childEnv, cont));
      return makeObjectCheck(env.ref.name, [makeValue(child.name, here)], bod, env);
    }
    function compileArray(patt, env, cont) {
      env = env
        .addHead('toStr', TO_STR_REF)
        .addHead('Array', natives.Array)
        .set({ start: 0 });
      var len = patt.children.length;
      var restIndex = indexOfRest(patt);
      var hasRest = restIndex >= 0;
      if (hasRest) len -= 1;
      if (len >= 0) {
        cont = patt.children.reduceRight(function(c, p) {
          return function(e) {
            var ref, env2;
            if (p.type === 'rest') {
              var stop = -1;
              if (restIndex === 0) stop = len;
              if (restIndex < len) stop = len - restIndex;
              env2 = env.set({ stop: stop });
            }
            else {
              var start = env.start < 0
                ? env.ref.name.concat(makePunc('.', here), makeIdent('length', here),
                    makePunc('-', here), makeValue(Math.abs(env.start), here))
                : [makeValue(env.start, here)];
              ref = makeRef([env.ref.name, makeDelim('[]', start, here)]);
              env2 = env.set({ ref: ref, start: e.start + 1 });
            }
            var bod = compilePattern(p, env2, function(e) {
              env = env.set({ start: e.start, names: e.names });
              return c(e);
            });
            return ref ? ref.stx.concat(bod) : bod;
          }
        }, cont);
        if (hasRest && len > 0 || !hasRest) {
          cont = function(c) {
            return function() {
              var op = hasRest ? #{ >= } : #{ === };
              letstx $bod ... = c(env);
              letstx $ref = env.ref.name;
              letstx $len = [makeValue(len, here)];
              letstx $op  = op;
              return #{
                if ($ref.length $op $len) { $bod ... }
              }
            }
          }(cont);
        }
      }
      letstx $bod ... = cont(env);
      letstx $toStr = TO_STR_REF.name;
      letstx $arrStr = natives.Array.name;
      letstx $ref = env.ref.name;
      return #{
        if ($toStr.call($ref) === $arrStr) { $bod ... }
      }
    }
    function compileRest(patt, env, cont) {
      var child = patt.children[0];
      var start = env.start;
      var stop  = env.stop;
      env = env.set({ start: -stop });
      if (child.type === 'wildcard') {
        return cont(env);
      }
      var okRef  = makeRef(makeValue(true, here)); 
      var iRef   = makeRef(); 
      var lenRef = makeRef(); 
      var inRef  = makeRef(); 
      var isRootRest = !env.restRefs;
      if (isRootRest) env.restRefs = [];
      var childEnv = env.set({ 
        ref: inRef, 
        names: [], 
        restRefs: []
      });
      var loopBody = compilePattern(child, childEnv, function(env2) {
        function reducer(acc, n) {
          var ref = makeRef(makeDelim('[]', [], here));
          env.restRefs.push(ref);
          return acc.concat(ref.name,
            makeDelim('[]', ref.name.concat(makePunc('.', here), makeIdent('length', here)), here), 
            makePunc('=', here), n.name || n.stx, makePunc(';', here));
        }
        var stx = env2.names.reduceRight(reducer, []);
        if (env2.restRefs) stx = env2.restRefs.reduceRight(reducer, stx);
        return stx.concat(#{ continue; });
      });
      var restRefs = env.restRefs.map(function(r) {
        if (isRootRest) env = env.addName(r.name);
        return r.stx;
      });
      var stopRef = env.ref.name.concat(makePunc('.', here), makeIdent('length', here));
      if (stop > 0) stopRef.push(makePunc('-', here), makeValue(stop, here));
      letstx $bod ... = cont(env);
      letstx $loopBod ... = loopBody;
      letstx $start = [makeValue(start, here)];
      letstx $stop  = [makeDelim('()', stopRef, here)];
      letstx $ok    = okRef.name;
      letstx $i     = iRef.name;
      letstx $len   = lenRef.name;
      letstx $in    = inRef.name;
      letstx $ref   = env.ref.name;
      var loop = #{
        for (var $i = $start, $len = $stop, $in; $i < $len; $i++) {
          $in = $ref[$i];
          $loopBod ...
          $ok = false;
          break;
        }
      };
      if (child.type === 'identifier') {
        letstx $rrefs ... = joinRefs(restRefs);
        letstx $loop ... = loop;
        return #{
          $rrefs ...
          $loop ...
          $bod ...
        }
      } else {
        letstx $rrefs ... = joinRefs([okRef].concat(restRefs));
        letstx $loop ... = loop;
        return #{
          $rrefs ...
          $loop ...
          if ($ok) { $bod ... }
        }
      }
    }
    function compileSimple(cases) {
      cases.forEach(function(c) {
        c.names = findIdents(c.args.children).map(function(i) {
          return i.name;
        });
      });
      var argCount = cases.reduce(function(acc, c) {
        if (!c.args.pattern || c.args.pattern === '*') return acc;
        var count = c.args.children.length;
        var hasRest = _.any(c.args.children, function(a) {
          return a.children[0].type === 'rest';
        });
        if (hasRest) count -= 1;
        return count > acc ? count : acc;
      }, 0);
      var argNames = [];
      while (argCount--) {
        argNames.unshift(makeIdent('a' + argCount, here));
      }
      var env = environment({
        cases: cases,
        head: {},
        names: [],
        argNames: argNames,
        level: 0
      });
      var branches = optimizeBranches(cases);
      var body = compileBranches(branches, env);
      var err  = #{ throw new TypeError('No match') };
      var head = joinRefs(_.values(env.head));
      letstx $name ... = fnName[0].token.value === 'anonymous' ? [] : fnName;
      letstx $args ... = intercalate(makePunc(',', here), argNames);
      letstx $code ... = optimizeSyntax(head.concat(body).concat(err));
      return #{
        function $name ... ($args ...) {
          $code ...
        }
      }
    }
    function optimizeBranches(cases) {
      var branches = cases.map(function(c) {
        var patts = c.args.children;
        var last = patts[patts.length - 1];
        if (c.guard.length) {
          last.guards = [{ guard: c.guard, body: c.body, names: c.names }];
        } else {
          last.body = c.body;
          last.names = c.names;
        }
        return patts.reduceRight(function(acc, patt) {
          patt.branches = [acc];
          return patt;
        });
      });
      function graft(bs) {
        for (var i = 1; i < bs.length; i++) {
          for (var j = i - 1; j >= 0; j--) {
            if (bs[i].pattern === bs[j].pattern) {
              if (bs[i].branches) {
                if (!bs[j].branches) bs[j].branches = [];
                bs[j].branches = bs[j].branches.concat(bs[i].branches);
              } else if (bs[i].guards) {
                if (!bs[j].guards) bs[j].guards = [];
                bs[j].guards = bs[j].guards.concat(bs[i].guards);
              } else {
                bs[j].body = bs[i].body;
                bs[j].names = bs[i].names;
              }
              bs.splice(i, 1);
              i--;
            } else break;
          }
        }
        bs.forEach(function(b) {
          if (b.branches) graft(b.branches);
        });
        return bs;
      }
      return graft(branches);
    }
    function compileBranches(branches, env) {
      return branches.reduce(function(acc, b) {
        return acc.concat(compileBranch(b, env));
      }, []);
    }
    function compileBranch(patt, env) {
      return compilePattern(patt, env, function (env2) {
        var branchBody, guardBody, pattBody, names;
        if (patt.branches) {
          branchBody = compileBranches(patt.branches, env2);
        }
        if (patt.guards) {
          guardBody = patt.guards.reduceRight(function(rest, g) {
            var names = _.zip(g.names, env2.names);
            var body = joinRefs(names.reduceRight(nameReducer, [])).concat(g.body);
            var guard = [makeKeyword('if', here), makeDelim('()', replaceIdents(g.guard, names), here), 
              makeDelim('{}', body, here)];
            return guard.concat(rest);
          }, []);
        }
        if (patt.body) {
          names = _.zip(patt.names, env2.names);
          pattBody = joinRefs(names.reduceRight(nameReducer, []))
            .concat(wrapBlock(patt.body));
        } 
        return (branchBody  || [])
          .concat(guardBody || [])
          .concat(pattBody  || []);
      });
      function nameReducer(bod, n) {
        var id = makeIdent(n[0], ctx);
        return [makeAssign(id, n[1].stx)].concat(bod);
      }
    }
    function compileBacktrack(cases) {
      var argLen  = 0;
      var nameLen = 0;
      var stateId = 1;
      var stateIdMap = {};
      var states = {};
      function getStateId(arg, argN) {
        var key = argN + ':' + arg.pattern;
        if (!stateIdMap.hasOwnProperty(key)) {
          stateIdMap[key] = stateId;
          states[stateId] = [];
          stateId++;
        }
        return stateIdMap[key];
      }
      cases.forEach(function(c, i) {
        var names = [];
        var len = c.args.children.length;
        var last = c.args.children[c.args.children.length - 1];
        if (last.children[0] === 'rest') len--;
        c.args.children.forEach(function(arg, j) {
          var id = getStateId(arg, j);
          var nextArg = c.args.children[j + 1];
          var nextCase = cases[i + 1];
          var argNames = findIdents(arg.children);
          arg.offset = names.length;
          arg.level = j;
          arg.case = i + 1; 
          arg.succ = nextArg  ? getStateId(nextArg, j + 1) : 0;
          arg.fail = nextCase ? getStateId(nextCase.args.children[0], 0) : 0;
          if (!nextArg) {
            arg.body = c.body;
            arg.guard = c.guard;
          }
          states[id].push(arg);
          names = names.concat(argNames);
        });
        if (len > argLen) argLen = len;
        if (names.length > nameLen) nameLen = names.length;
        last.names = names.map(function(n) {
          return n.name;
        });
      });
      var argNames = [];
      var nameRefs = [];
      while (argLen--) argNames.unshift(makeIdent('a' + argLen, here));
      while (nameLen--) nameRefs.push(makeRef());
      var stx = [];
      var env = environment({
        head: {},
        argNames: argNames,
        nameRefs: nameRefs,
        backRefs: [],
      });
      var stxStates = _.map(states, function(patts, id) {
        return compileState(parseInt(id), patts, env);
      });
      letstx $name ... = fnName[0].token.value === 'anonymous' ? [] : fnName;
      letstx $args ... = intercalate(makePunc(',', here), argNames);
      letstx $head ... = joinRefs(_.values(env.head));
      letstx $refs ... = joinRefs(nameRefs.concat(env.backRefs));
      letstx $code ... = optimizeSyntax(joinAlternates(stxStates));
      return #{
        function $name ... ($args ...) {
          var s = 1, c = 1;
          $head ...
          $refs ...
          while (true) {
            $code ...
          }
          throw new TypeError('No match');
        }
      }
    }
    function compileState(id, patts, env) {
      var pattBody, succBody, failBody;
      function compileSucc(patt, body) {
        if (patt.body) {
          var names = _.zip(patt.names, env.nameRefs.slice(0, patt.names.length));
          var code  = names.reduce(function(acc, pair) {
            return acc.concat(makeKeyword('var', here), makeIdent(pair[0], ctx),
              makePunc('=', here), pair[1].name, makePunc(';', here));
          }, []).concat(patt.body);
          if (patt.guard.length) {
            letstx $guard ... = replaceIdents(patt.guard, names);
            letstx $refBod ... = body;
            letstx $caseBod ... = code;
            body = #{
              $refBod ...
              if ($guard ...) {
                $caseBod ...
              }
            }
          } else {
            body = body.concat(code);
          }
        }
        else {
          letstx $nextState = [makeValue(patt.succ, here)];
          body = body.concat(#{
            s = $nextState;
            continue;
          });
        }
        letstx $caseBod ... = body;
        letstx $currCase = [makeValue(patt.case, here)];
        return #{
          if (c === $currCase) {
            $caseBod ...
          }
        }
      }
      var childEnv = env.set({
        level: patts[0].level,
        names: []
      });
      if (shouldStateBacktrack(patts)) {
        var backRef = makeRef();
        var nameLen = 0; 
        env.backRefs.push(backRef);
        pattBody = compilePattern(patts[0], childEnv, function(env2) {
          nameLen = env2.names.length;
          if (nameLen) {
            return env2.names.reduce(function(acc, name, i) {
              return acc.concat(backRef.name, makeDelim('[]', [makeValue(i, here)], here),
                makePunc('=', here), name.stx, makePunc(';', here));
            }, []);
          } else {
            return backRef.name.concat(makePunc('.', here), makeIdent('length', here),
              makePunc('=', here), makeValue(1, here), makePunc(';', here));
          }
        });
        letstx $bod ... = pattBody;
        letstx $back = backRef.name;
        pattBody = #{
          if (!$back) {
            $back = [];
            $bod ...
          }
        };
        succBody = joinAlternates(patts.map(function(patt) {
          var refs = env.nameRefs.slice(patt.offset, patt.offset + nameLen);
          var body = refs.reduce(function(acc, ref, i) {
            return acc.concat(ref.name, makePunc('=', here), backRef.name,
              makeDelim('[]', [makeValue(i, here)], here), makePunc(';', here));
          }, []);
          return compileSucc(patt, body);
        }));
        letstx $bod ... = succBody;
        succBody = #{
          if ($back.length) {
            $bod ...
          }
        };
      }
      else {
        succBody = [];
        pattBody = compilePattern(patts[0], childEnv, function(env2) {
          return joinAlternates(patts.map(function(patt) {
            var refs = env.nameRefs.slice(patt.offset, patt.offset + env2.names.length);
            var body = _.zip(refs, env2.names).reduce(function(acc, pair) {
              return acc.concat(pair[0].name, makePunc('=', here), pair[1].stx, makePunc(';', here));
            }, []);
            return compileSucc(patt, body);
          }));
        });
      }
      failBody = joinAlternates(patts.map(function(patt) {
        letstx $currCase = [makeValue(patt.case, here)];
        if (!patt.fail) {
          return #{
            if (c === $currCase) {
              break;
            }
          }
        } else {
          letstx $nextCase = [makeValue(patt.case + 1, here)];
          letstx $nextState = [makeValue(patt.fail, here)];
          return #{
            if (c === $currCase) {
              s = $nextState, c = $nextCase;
            }
          }
        }
      }));
      letstx $bod ... = pattBody.concat(succBody).concat(failBody);
      letstx $id = [makeValue(id, here)];
      return #{
        if (s === $id) {
          $bod ...
        }
      }
    }
    function optimizeSyntax(stx) {
      var inp = input(stx);
      var res = [];
      var toks, opt;
      while (inp.length) {
        if (inp.peek()[0].userCode) {
          res.push(inp.take()[0]);
        } else if (toks = inp.takeAPeek({ type: T.Keyword }, PARENS, BRACES)) {
          if (matchesToken(IF, toks[0])) {
            opt = optimizeIfs(toks);
          } else if (matchesToken(FOR, toks[0])) {
            opt = optimizeFors(toks);
          } else {
            toks[2].token.inner = optimizeSyntax(toks[2].token.inner);
            opt = toks;
          }
          res = res.concat(opt);
        } else if (toks = inp.takeAPeek(ELSE, BRACES)) {
          res = res.concat(optimizeElses(toks));
        } else if (toks = inp.takeAPeek(BRACES)) {
          res = res.concat(optimizeSyntax(toks[0].token.inner));
          break;
        } else if (toks = inp.takeAPeek(CONTINUE)) {
          res.push(toks[0]);
          break;
        } else {
          res.push(inp.take()[0]);
        }
      }
      return res;
    }
    function optimizeIfs(stx) {
      var pred  = stx[1];
      var block = stx[2];
      var inner = input(optimizeSyntax(block.token.inner));
      var toks  = inner.takeAPeek(IF, PARENS, BRACES);
      if (toks && inner.length === 0) {
        pred.token.inner = pred.token.inner.concat(makePunc('&&', here), toks[1]);
        stx[2] = toks[2];
      } else if (toks) {
        block.token.inner = toks.concat(inner.rest());
      } else {
        block.token.inner = inner.rest();
      }
      return stx;
    }
    function optimizeElses(stx) {
      var block = stx[1];
      var inner = input(optimizeSyntax(block.token.inner));
      var toks  = inner.takeAPeek(IF, PARENS, BRACES);
      if (toks && inner.length === 0) {
        return [stx[0]].concat(toks);
      } else if (toks) {
        block.token.inner = toks.concat(inner.rest());
      } else {
        block.token.inner = inner.rest();
      }
      return stx;
    }
    function optimizeFors(stx) {
      var inner = optimizeSyntax(stx[2].token.inner);
      for (var i = 0, t; t = inner[i]; i++) {
        if (matchesToken({ type: T.Keyword, value: 'continue' }, t)) {
          inner = inner.slice(0, i);
          break;
        }
      }
      stx[2].token.inner = inner;
      return stx;
    }

    return compile(parse(#{ $body ... }));
  }
}

let cond = macro {
	case { $ctx $arg { $body ... } } => {
		return #{
			($sparkler__compile $ctx anonymous { $body ... })($arg)
		}
	}

  case { _ } => {
    return #{ cond }
  }
}

export cond;

let ƒ = macro {
	case { $ctx $name:ident () = { $( ( $args ... ) -> $retTyp:ident { $body ... } ) ... } } => {
		return #{
			$sparkler__compile $ctx $name {
				$( case ( $args ... ) => { $body ... } ) ...
			}
		}
	}

	case { $ctx $name:ident ($arg (,) ...) = { $body ... } } => {
		return #{
			$sparkler__compile $ctx $name {
				case ($arg (,) ...) => { $body ... }
			}
		}
	}

	case { $ctx $name:ident ($arg (,) ...) = $body:expr } => {
		return #{
			$sparkler__compile $ctx $name {
				case ($arg (,) ...) => $body
			}
		}
	}
	
	case { _ } => { return #{ function } }
}

export ƒ;

// lambda chop
macro $lc__error {
  case { _ $tok } => {
    throwSyntaxError('lambda-chop', 'Unexpected token', #{ $tok });
  }
}

macro $lc__curry {
  case { _ ( $args ... ) ( $symbol ... ) ( $body ... ) } => {
    var here = #{ here };
    var args = #{ $args ... };
    var symbol = #{ $symbol ... };
    var body = #{ $body ... };

    if (!args.length) {
      args.push(makeDelim('()', [], here));
    }

    return args.reduceRight(function(bod, alist, i) {
      var func = makeKeyword('function', here);
      var ret  = i > 0 ? [makeKeyword('return', here)] : [];
      var code = ret.concat(func, alist, makeDelim('{}', bod, here));

      return symbol[0].token.value === '=>'
        ? code.concat(
            makePunc('.', here), 
            makeIdent('bind', here), 
            makeDelim('()', [makeKeyword('this', here)], here))
        : code;
    }, body);
  }
}

macro $lc__placeholders {
  case { _ ( $body ... ) } => {
    var here = #{ here };
    var res = makePlaceholders(#{ $body ... });
    return [
      makeKeyword('function', here),
      makeDelim('()', res[1], here),
      makeDelim('{}', [makeKeyword('return', res[0][0])].concat(res[0]), here)
    ];

    function makePlaceholders(stx) {
      var args = [];
      var code = 97;
      return [go(stx), args];

      function go(ss) {
        return ss.map(function(s) {
          if (s.token.type === parser.Token.Punctuator &&
              s.token.value === '#') {
            var ident = makeIdent(String.fromCharCode(code++), here);
            if (args.length) args.push(makePunc(',', here));
            args.push(ident);
            return ident;
          }
          if (s.token.type === parser.Token.Delimiter) {
            s.expose();
            s.token.inner = go(s.token.inner);
          }
          return s;
        });
      }
    }
  }
}

macro $lc__args {
  rule { ( $prev ... ) $name:ident } => {
    $lc__args ( $prev ... ( $name ) )
  }
  rule { ( $prev ... ) ( $name:ident (,) ... ) } => {
    $lc__args ( $prev ... ( $name (,) ... ) )
  }
  rule { ( $prev ... ) => { $body ... } } => {
    $lc__curry ( $prev ... ) ( => ) ( $body ... )
  }
  rule { ( $prev ... ) -> { $body ... } } => {
    $lc__curry ( $prev ... ) ( -> ) ( $body ... )
  }
  rule { ( $prev ... ) => $body:expr } => {
    $lc__curry ( $prev ... ) ( => ) ( return $body )
  }
  rule { ( $prev ... ) -> $body:expr } => {
    $lc__curry ( $prev ... ) ( -> ) ( return $body )
  }
  rule { $tok } => {
    $lc__error $tok
  }
}

macro λ {
	case { $ctx ($arg (,) ...) -> { $body ... } } => {
		return #{
			$sparkler__compile $ctx anonymous {
				case ($arg (,) ...) => { $body ... }
			}
		}
	}

	case { $ctx ($arg (,) ...) -> $body:expr } => {
		return #{
			$sparkler__compile $ctx anonymous {
				case ($arg (,) ...) => $body
			}
		}
	}

  case { _ [ $body ... ] } => {
		return #{
			$lc__placeholders ( $body ... )
		}
  }
  case { _ } => {
		return #{
			$lc__args ()
		}
  }
}

export λ;

// rustyscript
let import = macro {
	rule { $prop:ident from $mod:lit } => {
		var $prop = require($mod);
	}
	rule { { $($prop:ident (,) ...)} from $mod:lit } => {
		var mod = require($mod);
		$(var $prop = mod.$prop;) ...
	}
}

export import;

let var = macro {
	rule { {$name:ident (,) ...} = $value } => {
		var object = $value
		$(, $name = object.$name) ...
	}
 
	rule { [$name:ident (,) ...] = $value } => {
		var array = $value, index = 0
		$(, $name = array[index++]) ...
	}
	
	rule { $name = $value } => {
		var $name = $value
	}

	rule { $name:ident } => {
		var $name
	}
}

export var;

let @ = macro {
	rule { $name:ident } => {
		this.$name
	}
}

export @;

let ~ = macro {
	rule { $key:ident } => {
		$key:$key
	}
}

export ~;

/*
macro $type__check {
	rule { $val String } => {
		typeof $val === 'string'
	}
	
	rule { $val Number } => {
		typeof $val === 'number'
	}

	rule { $val $typ:ident } => {
		$val instanceof $typ
	}
}

macro $type__name {
	case { _ $name:ident } => {
		return [makeValue(#{$name}[0].token.value, #{$name})]
	}
}

let type = macro {
	rule { $name:ident = { $($key:ident : $typ:ident) (,) ... } } => {
		var $name = (function(){
			var constructor = function(){};
			var names = [
				$($type__name $key) (,) ...
			]
			var proto = {
				toJSON: λ -> {
					var obj = {_type: $type__name $name};
					for (var key in this) {
						if (this.hasOwnProperty(key) && names.indexOf(key) > -1) obj[key] = this[key]
					}
					return obj;
				}
			}

			constructor.create = λ(props) -> {
				var store = {};
				var instance = Object.create(constructor.prototype, {
					$($key : {
						enumerable: true,
						set: λ(val) -> {
							if ($type__check val $typ) {
								store.$key = val
							} else {
								throw new TypeError()
							}
						},
						get: λ[store.$key]
					}) (,) ...
				})
				for (var key in props) {
					if (props.hasOwnProperty(key) && names.indexOf(key) > -1) instance[key] = props[key];
				}
				return instance
			}

			constructor.unapply = λ(x) -> {
				var arr = [];
				for (var key in x) {
					if (x.hasOwnProperty(key) && names.indexOf(key)) arr.push(x[key])
				}
				return arr
			}

			constructor.unapplyObject = λ[#]

			constructor.prototype = proto;
			return constructor
		})();
	}
}

export type;

macro __enumbody {
	// Array type
	case { $ctx $parent:ident , $subtype:ident ( $propTyp:ident (,) ... ) $body ... } => {
		var ctx = #{$ctx};
		var typs = #{$propTyp ...};
		letstx $keys ... = typs.map(λ(val, i) -> {
			return makeValue(i, ctx);
		});
		letstx $desc = #{{ $($keys : $val) (,) ... }};
		console.log(aaaa)
		return #{
			type $subtype = $desc;
			var newproto = Object.create($parent.prototype);
			Object.keys($subtype.prototype).forEach(λ(val, key) -> { newproto[key] = val });
			$subtype.prototype = newproto;
			__enumbody $parent $body ...
		}
	}

	// Struct type
	case { $ctx $parent:ident , $subtype:ident { $($propName:ident : $proptyp:ident) (,) ... } $body ... } => {
		return #{
			type $subtype = { $($propName : $proptyp) (,) ... }
			var newproto = Object.create($parent.prototype);
			Object.keys($subtype.prototype).forEach(λ(val, key) -> { newproto[key] = val });
			$subtype.prototype = newproto;
			__enumbody $parent $body ...
		}
	}

	// val enum
	case { $ctx $parent:ident , $subtype:ident = $val:lit  $body ... } => {
		return #{
			var $subtype = (function(){
				var constructor = function () {};
				constructor.value = $val;
				constructor.isa = $parent;
				constructor.hasInstance = λ(x) -> {
					return x === this
				}
				constructor.toJSON = λ -> {
					return { _type: $type__name $subtype, value: $val }
				}
				return constructor
			})()
			__enumbody $parent $body ...
		}
	}

	case { $body } => { return #{} }
}

let enum = macro {
	rule { $name:ident = { $body ... } } => {
		var $name = function(){};
		$name.prototype = {};
		$name.hasInstance = λ(x) -> {
			if (x.isa === this || x instanceof this) {
				return true
			} else {
				return false
			}
		}
		__enumbody $name , $body ...
	}
}

export enum;
*/
macro do {
	rule { $monad:ident { $body ... } } => {
		(function () {
			var __monad__ = $monad;
			do __monad__ $body ...
		})()
	}

	rule { $monad:ident $x:ident <- $y:expr $body ... } => {
		return $monad.bind($y, function($x){do $monad $body ...})
	}

	rule { $monad return $body ... } => {
		return $monad.return($body ...)
	}

	rule { $body } => { $body }
}

export do;

macro $for {
  rule { ($value:ident, $index:ident, $items:expr) { $body... } } => {
    var items = $items;
    for(var $index = 0; $index < items.length; $index++) {
      var $value = items[$index];
      $body...
    }
    items = undefined;
  }
}

macro $range {
  rule { ($index:ident, $start:expr, $end:expr, $incr:expr) { $body... } } = {
    var end = $end;
    for(var i = $start; i < end; i += $incr) {
      var $index = i;
      $body...
    }
  }
}

let for = macro {

  // for(value, index <- items)

  rule { ($($value:ident, $index:ident <- $items:expr)) { $body... } } => { $for($value, $index, $items) { $body... } }

  rule { ($value:ident, $index:ident <- $items:expr) $body:expr } => { $for($value, $index, $items) { $body } }

  // for(value <- items)

  rule { ($($value:ident <- $items:expr)) { $body... } } => { $for($value, i, $items) { $body... } }

  rule { ($value:ident <- $items) $body:expr } => { $for($value, i, $items) { $body } }

  // for(value <- start:end)

  rule { ($index:ident <- $start:expr : $end:expr) { $body ... } } => { $range($index, $start, $end, 1) { $body... } }

  rule { ($index:ident <- $start:expr : $end:expr) $body:expr } => { $range($index, $start, $end, 1) { $body } }

  // for(value <- start:end:step)

  rule { ($index:ident <- $start:expr : $end:expr : $step:expr) { $body ... } } => { $range($index, $start, $end, $step) { $body... } }

  rule { ($index:ident <- $start:expr : $end:expr : $step:expr) $body:expr } => { $range($index, $start, $end, $step) { $body } }

  // Default syntax

	rule {} => { for }
}

export for;

macro __expandAccessors {
  case { _ $tokens ... } => {

    function expand(tokens, func) {
      var result = [];

      for (var i = 0, len = tokens.length; i < len; i++) {
        var tok = tokens[i];
        var news = func(tok, tokens[i + 1]);

        if (news) {
          result = result.concat(news);
        } else if (tok.token.inner) {
          tok.token.inner = expand(tok.token.inner, func);
          result.push(tok);
        } else {
          result.push(tok);
        }
      }

      return result;
    }

    return expand(#{$tokens ...}, function(tok, ntok) {
      if (ntok &&
          ntok.token.type === parser.Token.Identifier &&
          // guarantee tokens have no spaces between
          ntok.token.range[0] == tok.token.range[1]) {
        if (tok.token.type === parser.Token.Punctuator && tok.token.value === '@') {
          return #{this.state.}
        }
        if (tok.token.type === parser.Token.Punctuator && tok.token.value === '>') {
          return #{this.props.}
        }
      }
    });
  }
}

macro __componentBody {

  rule { $React:ident $spec:ident { } } => {}

  // methods
  rule { $React:ident $spec:ident { $($mname($args ...) { $mbody ... }) $body ... } } => {
    $spec.$mname = function($args ...) { __expandAccessors $mbody ... };
    __componentBody $React $spec { $body ... }
  }

  // prop definition
  rule { $React:ident $spec:ident { $(prop $name:ident required $typ:expr) $body ... } } => {
    $spec.propTypes.$name = $React.PropTypes.$typ.isRequired;
    __componentBody $React $spec { $body ... }
  }
  rule { $React:ident $spec:ident { $(prop $name:ident $typ:expr) $body ... } } => {
    $spec.propTypes.$name = $React.PropTypes.$typ;
    __componentBody $React $spec { $body ... }
  }

  // mixin definitions
  rule { $React:ident $spec:ident { $(mixin $($mixin:expr (,) ...)) $body ... } } => {
    $spec.mixins = $spec.mixins.concat($mixin (,) ...);
    __componentBody $React $spec { $body ... }
  }
}

macro component {

  case { _ $name:ident { $body ... } } => {
    letstx $displayName = [makeValue(#{$name}[0].token.value, #{here})];
    letstx $React = [makeIdent('React', #{$name})];
    return #{
      var $name = (function() {
        var spec = {displayName: $displayName, propTypes: {}, mixins: []};
        __componentBody $React spec { $body ... }
        return $React.createClass(spec);
      })();
    }
  }
}

export component;

/**
 * React.hiccup hiccup notation for React.js
 * MIT license http://www.opensource.org/licenses/mit-license.php/
 * Copyright (C) 2014 Luca Antiga http://lantiga.github.io
 */

macro _restargs {
  rule { () } => { null }
  rule { ($first) } => { hiccup $first }
  rule { ($first $rest ...) } => { hiccup $first, _restargs ($rest ...) }
}

macro _tag {
  case { _ $t } => { 
    var knownTags = {
      a:true, abbr:true, address:true, area:true, article:true, aside:true, audio:true, 
      b:true, base:true, bdi:true, bdo:true, big:true, blockquote:true, body:true, br:true, 
      button:true, canvas:true, caption:true, cite:true, code:true, col:true, colgroup:true, 
      data:true, datalist:true, dd:true, del:true, details:true, dfn:true,
      div:true, dl:true, dt:true, em:true, embed:true, fieldset:true, figcaption:true, 
      figure:true, footer:true, form:true, h1:true, h2:true, h3:true, h4:true, h5:true, h6:true,
      head:true, header:true, hr:true, html:true, i:true, iframe:true, img:true, input:true, 
      ins:true, kbd:true, keygen:true, label:true, legend:true, li:true, link:true, main:true,
      map:true, mark:true, menu:true, menuitem:true, meta:true, meter:true, nav:true, noscript:true, 
      object:true, ol:true, optgroup:true, option:true, output:true,
      p:true, param:true, pre:true, progress:true, q:true, rp:true, rt:true, ruby:true, s:true, 
      samp:true, script:true, section:true, select:true, small:true, source:true,
      span:true, strong:true, style:true, sub:true, summary:true, sup:true, table:true, 
      tbody:true, td:true, textarea:true, tfoot:true, th:true, thead:true, time:true,
      title:true, tr:true, track:true, u:true, ul:true, "var":true, video:true, wbr:true,
      circle:true, g:true, line:true, path:true, polygon:true, polyline:true, rect:true, 
      svg:true, text:true
    };
    var tagStr = unwrapSyntax(#{$t});
    if (knownTags[tagStr]) {
      return #{React.DOM.$t}
    }
    return #{$t} 
  }
}

macro _args {

  case { $name $x ... } => { 

    var x = #{$x ...};

    var getRange = function(token) {
      return token.sm_startRange || token.sm_range || token.startRange || token.range;
    }

    var getIdentifier = function(x) {
      var identifier = '';
      var pend = null;
      while (x.length > 0 
          && (pend == null || getRange(x[0].token) === undefined || pend == getRange(x[0].token)[0]) 
          && x[0].token.type != 11
          && x[0].token.value != '.') {
        pend = getRange(x[0].token)[1];
        identifier += x.shift().token.value;
      }
      return identifier;
    }

    var id = "", className = "";
    if (x.length > 0 && x[0].token.value == '#') {
      x.shift();
      id = getIdentifier(x);
    }
    while (x.length > 0 && x[0].token.value == '.') {
      x.shift();
      className += " " + getIdentifier(x);
    }
    
    var hmap;
    if (x.length > 0 && x[0].token.value == '{}') {
      hmap = x.shift();
    }

    letstx $id = [makeValue(id,#{$name})], 
           $c = [makeValue(className,#{$id})];

    var children = x;
    letstx $children ... = children;

    if (hmap === undefined && children.length == 0) {
      if (id != "" && className != "") {
        return #{ {className: $c, id: $id} } 
      }
      else if (id == "" && className == "") {
        return #{ null } 
      }
      else if (className != "") {
        return #{ {className: $c} } 
      }
      else {
        return #{ {id: $id} } 
      }
    }

    if (hmap === undefined) {
      if (id != "" && className != "") {
        return #{ {className: $c, id: $id}, _restargs($children ...) } 
      }
      else if (id == "" && className == "") {
        return #{ null, _restargs($children ...) } 
      }
      else if (className != "") {
        return #{ {className: $c}, _restargs($children ...) } 
      }
      else {
        return #{ {id: $id}, _restargs($children ...) } 
      }
    }

    var classNameIndex;

    for (var i=0; i<hmap.token.inner.length; i++) {
      if (hmap.token.inner[i].token.value == 'className') {
        classNameIndex = i+2;
        break;
      }
    }

    if (classNameIndex !== undefined) {
      hmap.token.inner[classNameIndex].token.value += className;
    }
    else if (className != "") {
      hmap.token.inner = hmap.token.inner.concat([makePunc(',',#{$c}),makeIdent("className",#{$c}),makePunc(":",#{$c}),makeValue(className,#{$c})]);
    }
  
    if (id != "") {
      hmap.token.inner = hmap.token.inner.concat([makePunc(',',#{$id}),makeIdent("id",#{$id}),makePunc(":",#{$id}),makeValue(id,#{$id})]);
    }

    letstx $hmap = [hmap];

    return #{ $hmap, _restargs($children ...) } 
  }
}

macro _value {
  case {_ $x} => {
    var temp = #{$x}[0];
    if (temp.token.type == 10) {
      var tempString = temp.token.value.raw;
      letstx $newTemp = [makeValue(tempString, #{x})];
      return #{$newTemp}
    }
    return #{$x}
  }
}

macro hiccup {

  rule { [ $t $args ... ] } => {
    _tag $t(_args $args ...) 
  }

  rule { $x } => { _value $x }
}

macro rclass {
  rule { $n.$m(.)... = {$x...} } => { $n.$m(.)... = React.createClass({$x...}); }
  rule { $n:ident = {$x...} } => { var $n = React.createClass({$x...}); }
}

export hiccup;

export rclass;

// TODO
// * better error handling in _args
// * allow attribute object to be an identifier; in this case merge className and id using a function
// * allow property access without brackets by improving _restargs


/*
macro __tco {
	rule { $tcor:ident return $func:ident ( $arg (,) ... ) $body ... } => {
		
	}
	
	rule { $tcor:ident return $retval $body ... } => {
		$tcor = $retval;
		break tco
		__tco $tcor $body ...
	}

	//rule { $body } => { $body }
}

let tail = macro {
	rule { ƒ $name:ident ( $arg:ident (,) ... ) { $body ... } } => {
		function $name ( $arg (,) ... ) {
			var __tcor;
			tco:
				while (true) {
					__tco __tcor $body ...
				}
			return __tcor
		}
	}
}

export tail;
*/
/*
function count(from, to) {
    if(from >= to)
        return from;

    return count(from + 1, to);
}

console.log(count(0, 1000000));

Is rewritten into:

function count(from, to) {
    var __tcor;
    tco:
        while (true) {
            if (from >= to) {
                __tcor = from;
                break tco;
            }
            {
                var __from = from + 1, __to = to;
                from = __from;
                to = __to;
                continue tco;
            }
        }
    return __tcor;
}
console.log(count(0, 1000000));
*/
