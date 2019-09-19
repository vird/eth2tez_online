(function() {
  var Ti_context, Type, class_prepare, config, is_not_a_type, module, v, _i, _j, _len, _len1, _ref, _ref1;

  config = window.config;

  Type = window.Type;

  module = this;

  this.default_var_hash_gen = function() {
    return {
      msg: (function() {
        var ret;
        ret = new Type("struct");
        ret.field_hash['sender'] = new Type("t_address");
        return ret;
      })(),
      require: (function() {
        var ret, type_i, type_o;
        ret = new Type("function2");
        ret.nest_list.push(type_i = new Type("function"));
        ret.nest_list.push(type_o = new Type("function"));
        type_i.nest_list.push("bool");
        return ret;
      })()
    };
  };

  this.default_type_hash_gen = function() {
    return {};
  };

  this.bin_op_ret_type_hash_list = {};

  this.un_op_ret_type_hash_list = {
    MINUS: [['t_int256', 't_int256']]
  };

  _ref = "ADD SUB MUL POW".split(/\s+/g);
  for (_i = 0, _len = _ref.length; _i < _len; _i++) {
    v = _ref[_i];
    this.bin_op_ret_type_hash_list[v] = [['t_uint256', 't_uint256', 't_uint256']];
  }

  _ref1 = "EQ NE GT LT GTE LTE".split(/\s+/g);
  for (_j = 0, _len1 = _ref1.length; _j < _len1; _j++) {
    v = _ref1[_j];
    this.bin_op_ret_type_hash_list[v] = [['t_uint256', 't_uint256', 'bool']];
  }

  Ti_context = (function() {
    Ti_context.prototype.parent = null;

    Ti_context.prototype.var_hash = {};

    Ti_context.prototype.type_hash = {};

    function Ti_context() {
      this.var_hash = module.default_var_hash_gen();
      this.type_hash = module.default_type_hash_gen();
    }

    Ti_context.prototype.mk_nest = function() {
      var ret;
      ret = new Ti_context;
      ret.parent = this;
      return ret;
    };

    Ti_context.prototype.check_id = function(id) {
      var ret, state_class;
      if (ret = this.var_hash[id]) {
        return ret;
      }
      if (state_class = this.type_hash[config.storage]) {
        if (ret = state_class._prepared_field2type[id]) {
          return ret;
        }
      }
      if (this.parent) {
        return this.parent.check_id(id);
      }
      throw new Error("can't find decl for id '" + id + "'");
    };

    Ti_context.prototype.check_type = function(_type) {
      var ret;
      if (ret = this.type_hash[_type]) {
        return ret;
      }
      if (this.parent) {
        return this.parent.check_type(_type);
      }
      throw new Error("can't find type '" + _type + "'");
    };

    return Ti_context;

  })();

  class_prepare = function(ctx, t) {
    var _k, _len2, _ref2;
    ctx.type_hash[t.name] = t;
    _ref2 = t.scope.list;
    for (_k = 0, _len2 = _ref2.length; _k < _len2; _k++) {
      v = _ref2[_k];
      switch (v.constructor.name) {
        case "Var_decl":
          t._prepared_field2type[v.name] = v.type;
          break;
        case "Fn_decl":
          t._prepared_field2type[v.name] = v.type;
      }
    }
  };

  is_not_a_type = function(type) {
    return !type || type.main === 'number';
  };

  this.gen = function(ast_tree, opt) {
    var change_count, i, walk, _k;
    walk = function(t, ctx) {
      var a, arg, b, class_decl, complex_type, ctx_nest, field_hash, field_type, found, k, key, list, name, root_type, tuple, type, _k, _l, _len2, _len3, _len4, _len5, _len6, _len7, _len8, _m, _n, _o, _p, _q, _ref2, _ref3, _ref4, _ref5, _ref6, _ref7;
      switch (t.constructor.name) {
        case "Var":
          return t.type = ctx.check_id(t.name);
        case "Const":
          return t.type;
        case "Bin_op":
          list = module.bin_op_ret_type_hash_list[t.op];
          a = (walk(t.a, ctx) || '').toString();
          b = (walk(t.b, ctx) || '').toString();
          found = false;
          if (list) {
            for (_k = 0, _len2 = list.length; _k < _len2; _k++) {
              tuple = list[_k];
              if (tuple[0] !== a) {
                continue;
              }
              if (tuple[1] !== b) {
                continue;
              }
              found = true;
              t.type = new Type(tuple[2]);
            }
          }
          if (!found) {
            if (t.op === 'ASSIGN') {
              t.type = t.a.type;
              found = true;
            } else if ((_ref2 = t.op) === 'EQ' || _ref2 === 'NE') {
              t.type = new Type('bool');
              found = true;
            } else if (t.op === 'INDEX_ACCESS') {
              switch (t.a.type.main) {
                case 'string':
                  t.type = new Type('string');
                  found = true;
                  break;
                case 'map':
                  key = t.a.type.nest_list[0];
                  if (!key.cmp(t.b.type)) {
                    throw new Error("bad index access to '" + t.a.type + "' with index '" + t.b.type + "'");
                  }
                  t.type = t.a.type.nest_list[1];
                  found = true;
              }
            }
          }
          return t.type;
        case "Un_op":
          list = module.un_op_ret_type_hash_list[t.op];
          a = walk(t.a, ctx).toString();
          found = false;
          if (list) {
            for (_l = 0, _len3 = list.length; _l < _len3; _l++) {
              tuple = list[_l];
              if (tuple[0] !== a) {
                continue;
              }
              found = true;
              t.type = new Type(tuple[1]);
            }
          }
          if (!found) {
            throw new Error("unknown un_op=" + t.op + " a=" + a);
          }
          return t.type;
        case "Field_access":
          root_type = walk(t.t, ctx);
          if (root_type.main === 'struct') {
            field_hash = root_type.field_hash;
          } else {
            class_decl = ctx.check_type(root_type.main);
            field_hash = class_decl._prepared_field2type;
          }
          if (!(field_type = field_hash[t.name])) {
            throw new Error("unknown field. '" + t.name + "' at type '" + root_type + "'. Allowed fields [" + (Object.keys(field_hash).join(', ')) + "]");
          }
          t.type = field_type;
          return t.type;
        case "Fn_call":
          root_type = walk(t.fn, ctx);
          _ref3 = t.arg_list;
          for (_m = 0, _len4 = _ref3.length; _m < _len4; _m++) {
            arg = _ref3[_m];
            walk(arg, ctx);
          }
          return t.type = root_type.nest_list[0].nest_list[0];
        case "Var_decl":
          if (t.assign_value) {
            walk(t.assign_value, ctx);
          }
          ctx.var_hash[t.name] = t.type;
          return null;
        case "Scope":
          ctx_nest = ctx.mk_nest();
          _ref4 = t.list;
          for (_n = 0, _len5 = _ref4.length; _n < _len5; _n++) {
            v = _ref4[_n];
            if (v.constructor.name === "Class_decl") {
              class_prepare(ctx, v);
            }
          }
          _ref5 = t.list;
          for (_o = 0, _len6 = _ref5.length; _o < _len6; _o++) {
            v = _ref5[_o];
            walk(v, ctx_nest);
          }
          return null;
        case "Ret_multi":
          _ref6 = t.t_list;
          for (_p = 0, _len7 = _ref6.length; _p < _len7; _p++) {
            v = _ref6[_p];
            walk(v, ctx);
          }
          return null;
        case "Class_decl":
          class_prepare(ctx, t);
          ctx_nest = ctx.mk_nest();
          walk(t.scope, ctx_nest);
          return t.type;
        case "Fn_decl_multiret":
          complex_type = new Type('function2');
          complex_type.nest_list.push(t.type_i);
          complex_type.nest_list.push(t.type_o);
          ctx.var_hash[t.name] = complex_type;
          ctx_nest = ctx.mk_nest();
          _ref7 = t.arg_name_list;
          for (k = _q = 0, _len8 = _ref7.length; _q < _len8; k = ++_q) {
            name = _ref7[k];
            type = t.type_i.nest_list[k];
            ctx_nest.var_hash[name] = type;
          }
          walk(t.scope, ctx_nest);
          return t.type;
        case "If":
          walk(t.cond, ctx);
          walk(t.t, ctx.mk_nest());
          walk(t.f, ctx.mk_nest());
          return null;
        case "While":
          walk(t.cond, ctx.mk_nest());
          walk(t.scope, ctx.mk_nest());
          return null;
        default:

          /* !pragma coverage-skip-block */
          p(t);
          throw new Error("ti phase 1 unknown node '" + t.constructor.name + "'");
      }
    };
    walk(ast_tree, new Ti_context);
    change_count = 0;
    walk = function(t, ctx) {
      var a_type, a_type_list, arg, b_type, b_type_list, bruteforce_a, bruteforce_b, can_bruteforce, candidate_list, class_decl, cmp_a_type, cmp_b_type, cmp_ret_type, complex_type, ctx_nest, expected_type, field_hash, field_type, i, k, list, name, pair, refined_list, root_type, type, _k, _l, _len2, _len3, _len4, _len5, _len6, _len7, _len8, _len9, _m, _n, _o, _p, _q, _r, _ref2, _ref3, _ref4, _ref5, _ref6;
      switch (t.constructor.name) {
        case "Var":
          return t.type = ctx.check_id(t.name);
        case "Const":
          return t.type;
        case "Bin_op":
          bruteforce_a = is_not_a_type(t.a.type);
          bruteforce_b = is_not_a_type(t.b.type);
          list = module.bin_op_ret_type_hash_list[t.op];
          can_bruteforce = t.type != null;
          can_bruteforce && (can_bruteforce = bruteforce_a || bruteforce_b);
          can_bruteforce && (can_bruteforce = list != null);
          if (t.op === 'ASSIGN') {
            if (bruteforce_a && !bruteforce_b) {
              change_count++;
              t.a.type = t.b.type;
            } else if (!bruteforce_a && bruteforce_b) {
              change_count++;
              t.b.type = t.a.type;
            }
          } else {
            if (list == null) {
              perr("can't type inference bin_op=  '" + t.op + "'");
            }
          }
          if (can_bruteforce) {
            a_type_list = bruteforce_a ? [] : [t.a.type.toString()];
            b_type_list = bruteforce_b ? [] : [t.b.type.toString()];
            refined_list = [];
            cmp_ret_type = t.type.toString();
            for (_k = 0, _len2 = list.length; _k < _len2; _k++) {
              v = list[_k];
              if (cmp_ret_type !== v[2]) {
                continue;
              }
              if (bruteforce_a) {
                a_type_list.push(v[0]);
              }
              if (bruteforce_b) {
                b_type_list.push(v[1]);
              }
              refined_list.push(v);
            }
            candidate_list = [];
            for (_l = 0, _len3 = a_type_list.length; _l < _len3; _l++) {
              a_type = a_type_list[_l];
              for (_m = 0, _len4 = b_type_list.length; _m < _len4; _m++) {
                b_type = b_type_list[_m];
                for (_n = 0, _len5 = refined_list.length; _n < _len5; _n++) {
                  pair = refined_list[_n];
                  cmp_a_type = pair[0], cmp_b_type = pair[1];
                  if (a_type !== cmp_a_type) {
                    continue;
                  }
                  if (b_type !== cmp_b_type) {
                    continue;
                  }
                  candidate_list.push(pair);
                }
              }
            }
            if (candidate_list.length === 1) {
              change_count++;
              _ref2 = candidate_list[0], a_type = _ref2[0], b_type = _ref2[1];
              t.a.type = new Type(a_type);
              t.b.type = new Type(b_type);
            } else {
              p("candidate_list=" + candidate_list.length);
            }
          }
          walk(t.a, ctx);
          walk(t.b, ctx);
          return t.type;
        case "Un_op":
          walk(t.a, ctx);
          return t.type;
        case "Field_access":
          root_type = walk(t.t, ctx);
          if (root_type.main === 'struct') {
            field_hash = root_type.field_hash;
          } else {
            class_decl = ctx.check_type(root_type.main);
            field_hash = class_decl._prepared_field2type;
          }
          if (!(field_type = field_hash[t.name])) {
            throw new Error("unknown field. '" + t.name + "' at type '" + root_type + "'. Allowed fields [" + (Object.keys(field_hash).join(', ')) + "]");
          }
          t.type = field_type;
          return t.type;
        case "Fn_call":
          root_type = walk(t.fn, ctx);
          _ref3 = t.arg_list;
          for (i = _o = 0, _len6 = _ref3.length; _o < _len6; i = ++_o) {
            arg = _ref3[i];
            walk(arg, ctx);
            expected_type = t.fn.type.nest_list[0].nest_list[i];
            if (is_not_a_type(arg.type)) {
              change_count++;
              arg.type = expected_type;
            }
          }
          return t.type = root_type.nest_list[0].nest_list[0];
        case "Var_decl":
          if (t.assign_value) {
            if (is_not_a_type(t.assign_value.type)) {
              change_count++;
              t.assign_value.type = t.type;
            }
            walk(t.assign_value, ctx);
          }
          ctx.var_hash[t.name] = t.type;
          return null;
        case "Scope":
          ctx_nest = ctx.mk_nest();
          _ref4 = t.list;
          for (_p = 0, _len7 = _ref4.length; _p < _len7; _p++) {
            v = _ref4[_p];
            walk(v, ctx_nest);
          }
          return null;
        case "Ret_multi":
          _ref5 = t.t_list;
          for (_q = 0, _len8 = _ref5.length; _q < _len8; _q++) {
            v = _ref5[_q];
            walk(v, ctx);
          }
          return null;
        case "Class_decl":
          class_prepare(ctx, t);
          ctx_nest = ctx.mk_nest();
          walk(t.scope, ctx_nest);
          return t.type;
        case "Fn_decl_multiret":
          complex_type = new Type('function2');
          complex_type.nest_list.push(t.type_i);
          complex_type.nest_list.push(t.type_o);
          ctx.var_hash[t.name] = complex_type;
          ctx_nest = ctx.mk_nest();
          _ref6 = t.arg_name_list;
          for (k = _r = 0, _len9 = _ref6.length; _r < _len9; k = ++_r) {
            name = _ref6[k];
            type = t.type_i.nest_list[k];
            ctx_nest.var_hash[name] = type;
          }
          walk(t.scope, ctx_nest);
          return t.type;
        case "If":
          walk(t.cond, ctx);
          walk(t.t, ctx.mk_nest());
          walk(t.f, ctx.mk_nest());
          return null;
        case "While":
          walk(t.cond, ctx.mk_nest());
          walk(t.scope, ctx.mk_nest());
          return null;
        default:

          /* !pragma coverage-skip-block */
          p(t);
          throw new Error("ti phase 2 unknown node '" + t.constructor.name + "'");
      }
    };
    for (i = _k = 0; _k < 100; i = ++_k) {
      walk(ast_tree, new Ti_context);
      if (change_count === 0) {
        break;
      }
      change_count = 0;
    }
    return ast_tree;
  };
}).call(window.type_inference = {})