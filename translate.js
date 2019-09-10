(function() {
  var Type, config, gen, mod_ast, module, reserved_hash, smart_bracket, translate_type, type2default_value, var_name_trans;

  config = window.config;

  Type = window.Type;

  mod_ast = window.mod_ast;

  module = this;

  translate_type = function(type) {
    var key, value;
    switch (type.main) {
      case 't_bool':
        return 'bool';
      case 't_uint256':
        return 'nat';
      case 't_int256':
        return 'int';
      case 't_address':
        return 'address';
      case 't_string_memory_ptr':
        return 'string';
      case 't_bytes_memory_ptr':
        return 'bytes';
      case config.storage:
        return config.storage;
      case 'map':
        key = translate_type(type.nest_list[0]);
        value = translate_type(type.nest_list[1]);
        return "map(" + key + ", " + value + ")";
      default:
        throw new Error("unknown solidity type '" + type + "'");
    }
  };

  type2default_value = function(type) {
    switch (type.toString()) {
      case 't_bool':
        return 'false';
      case 't_uint256':
        return '0n';
      case 't_int256':
        return '0';
      case 't_address':
        return '0';
      case 't_string_memory_ptr':
        return '""';
      default:
        throw new Error("unknown solidity type '" + type + "'");
    }
  };

  this.bin_op_name_map = {
    ADD: '+',
    SUB: '-',
    MUL: '*',
    DIV: '/',
    MOD: 'mod',
    EQ: '=',
    NE: '=/=',
    GT: '>',
    LT: '<',
    GTE: '>=',
    LTE: '<=',
    BOOL_AND: 'and',
    BOOL_OR: 'or'
  };

  this.bin_op_name_cb_map = {
    ASSIGN: function(a, b) {
      return "" + a + " := " + b;
    },
    BIT_AND: function(a, b) {
      return "bitwise_and(" + a + ", " + b + ")";
    },
    BIT_OR: function(a, b) {
      return "bitwise_or(" + a + ", " + b + ")";
    },
    BIT_XOR: function(a, b) {
      return "bitwise_xor(" + a + ", " + b + ")";
    },
    ASS_ADD: function(a, b) {
      return "" + a + " := " + a + " + " + b;
    },
    ASS_SUB: function(a, b) {
      return "" + a + " := " + a + " - " + b;
    },
    ASS_MUL: function(a, b) {
      return "" + a + " := " + a + " * " + b;
    },
    ASS_DIV: function(a, b) {
      return "" + a + " := " + a + " / " + b;
    },
    INDEX_ACCESS: function(a, b, ctx, ast) {
      var ret, val;
      return ret = ctx.lvalue ? "" + a + "[" + b + "]" : (val = type2default_value(ast.type), "(case " + a + "[" + b + "] of | None -> " + val + " | Some(x) -> x end)");
    }
  };

  this.un_op_name_cb_map = {
    MINUS: function(a) {
      return "-(" + a + ")";
    },
    PLUS: function(a) {
      return "+(" + a + ")";
    },
    BIT_NOT: function(a) {
      return "not (" + a + ")";
    }
  };

  smart_bracket = function(t) {
    if (t[0] === '(' && t[t.length - 1] === ')') {
      return t;
    } else {
      return "(" + t + ")";
    }
  };

  this.Gen_context = (function() {
    Gen_context.prototype.fn_hash = {};

    Gen_context.prototype.var_hash = {};

    Gen_context.prototype.expand_hash = false;

    Gen_context.prototype.in_fn = false;

    Gen_context.prototype.tmp_idx = 0;

    Gen_context.prototype.sink_list = [];

    Gen_context.prototype.lvalue = false;

    Gen_context.prototype.trim_expr = '';

    function Gen_context() {
      this.fn_hash = {};
      this.var_hash = {};
      this.sink_list = [];
    }

    Gen_context.prototype.mk_nest = function() {
      var t;
      t = new module.Gen_context;
      t.var_hash = clone(this.var_hash);
      t.fn_hash = this.fn_hash;
      return t;
    };

    return Gen_context;

  })();

  reserved_hash = {
    sender: true,
    source: true,
    amount: true,
    now: true
  };

  var_name_trans = function(name) {
    if (reserved_hash[name]) {
      return "reserved__" + name;
    } else {
      return name;
    }
  };

  this.gen = function(ast, opt) {
    var ctx, v, _i, _len, _ref;
    if (opt == null) {
      opt = {};
    }
    ctx = new module.Gen_context;
    _ref = ast.list;
    for (_i = 0, _len = _ref.length; _i < _len; _i++) {
      v = _ref[_i];
      if (v.constructor.name === 'Fn_decl_multiret') {
        ctx.fn_hash[v.name] = v;
      }
    }
    return module._gen(ast, opt, ctx);
  };

  this._gen = gen = function(ast, opt, ctx) {
    var append, arg_jl, arg_list, body, cb, cond, craft_a, ctx_lvalue, f, failtext, fn, fn_decl, idx, is_assign, jl, name, op, ret, ret_jl, scope, sink, t, tmp_a, tmp_type, tmp_var, type, type_jl, v, val, _a, _b, _craft_a, _i, _j, _k, _l, _len, _len1, _len2, _len3, _len4, _len5, _len6, _len7, _m, _n, _o, _p, _proxy_a, _ref, _ref1, _ref2, _ref3, _ref4, _ref5, _ref6, _ref7;
    switch (ast.constructor.name) {
      case "Var":
        name = var_name_trans(ast.name);
        if (ctx.var_hash[name] || name === config.contractStorage) {
          return name;
        } else {
          return "" + config.contractStorage + "." + name;
        }
        break;
      case 'Bin_op':
        ctx_lvalue = ctx.mk_nest();
        is_assign = 0 === ast.op.indexOf('ASS');
        if (is_assign) {
          ctx_lvalue.lvalue = true;
        }
        _a = gen(ast.a, opt, ctx_lvalue);
        _b = gen(ast.b, opt, ctx);
        if (is_assign) {
          if (ast.a.constructor.name === 'Bin_op' && ast.a.op === 'INDEX_ACCESS') {
            if (ast.a.a.type.main === 'map') {
              tmp_var = "tmp_" + (ctx.tmp_idx++);
              ctx_lvalue.var_hash[tmp_var] = true;
              tmp_type = translate_type(ast.a.a.type);
              _proxy_a = gen(ast.a.a, opt, ctx_lvalue);
              ctx.sink_list.push("const " + tmp_var + " : " + tmp_type + " = " + _proxy_a);
              craft_a = new mod_ast.Bin_op;
              craft_a.op = 'INDEX_ACCESS';
              craft_a.a = tmp_a = new mod_ast.Var;
              tmp_a.type = ast.a.a.type;
              tmp_a.name = tmp_var;
              craft_a.b = ast.a.b;
              craft_a.type = ast.type;
              _craft_a = gen(craft_a, opt, ctx_lvalue);
              ctx.sink_list.push((function() {
                if (op = module.bin_op_name_map[ast.op]) {
                  return "(" + _craft_a + " " + op + " " + _b + ")";
                } else if (cb = module.bin_op_name_cb_map[ast.op]) {
                  return cb(_craft_a, _b, ctx, ast);
                } else {
                  throw new Error("Unknown/unimplemented bin_op " + ast.op);
                }
              })());
              _a = _proxy_a;
              _b = tmp_var;
            }
          }
        }
        ret = (function() {
          if (op = module.bin_op_name_map[ast.op]) {
            return "(" + _a + " " + op + " " + _b + ")";
          } else if (cb = module.bin_op_name_cb_map[ast.op]) {
            return cb(_a, _b, ctx, ast);
          } else {
            throw new Error("Unknown/unimplemented bin_op " + ast.op);
          }
        })();
        return ret;
      case "Un_op":
        if (cb = module.un_op_name_cb_map[ast.op]) {
          return cb(gen(ast.a, opt, ctx), ctx);
        } else {
          throw new Error("Unknown/unimplemented un_op " + ast.op);
        }
        break;
      case "Const":
        switch (ast.type.main) {
          case "t_uint256":
            return "" + ast.val + "n";
          case 'string':
            return JSON.stringify(ast.val);
          default:
            return ast.val;
        }
        break;
      case "Field_access":
        t = gen(ast.t, opt, ctx);
        ret = "" + t + "." + ast.name;
        if (ret === 'contractStorage.msg.sender') {
          ret = 'sender';
        }
        return ret;
      case "Fn_call":
        fn = gen(ast.fn, opt, ctx);
        arg_list = [];
        _ref = ast.arg_list;
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          v = _ref[_i];
          arg_list.push(gen(v, opt, ctx));
        }
        if (fn === ("" + config.contractStorage + ".require")) {
          arg_list[0];
          failtext = arg_list[1] || "";
          return "if (not " + (smart_bracket(arg_list[0])) + ") then begin\n  fail(" + failtext + ");\nend";
        }
        fn_decl = ctx.fn_hash[fn];
        if (!fn_decl) {
          return "" + fn + "(" + (arg_list.join(', '));
        } else {
          type_jl = [];
          _ref1 = fn_decl.type_o.nest_list;
          for (_j = 0, _len1 = _ref1.length; _j < _len1; _j++) {
            v = _ref1[_j];
            type_jl.push(translate_type(v));
          }
          arg_list.push(config.contractStorage);
          tmp_var = "tmp_" + (ctx.tmp_idx++);
          ctx.sink_list.push("const " + tmp_var + " : (" + (type_jl.join(' * ')) + ") = " + fn + "(" + (arg_list.join(', ')) + ")");
          ctx.sink_list.push("" + config.contractStorage + " := " + tmp_var + ".1");
          ctx.trim_expr = tmp_var;
          return tmp_var;
        }
        break;
      case "Scope":
        jl = [];
        append = function(t) {
          if (t && t[t.length - 1] !== ";") {
            t += ";";
          }
          if (t !== '') {
            jl.push(t);
          }
        };
        _ref2 = ast.list;
        for (_k = 0, _len2 = _ref2.length; _k < _len2; _k++) {
          v = _ref2[_k];
          t = gen(v, opt, ctx);
          _ref3 = ctx.sink_list;
          for (_l = 0, _len3 = _ref3.length; _l < _len3; _l++) {
            sink = _ref3[_l];
            append(sink);
          }
          ctx.sink_list.clear();
          if (ctx.trim_expr === t) {
            ctx.trim_expr = '';
            continue;
          }
          append(t);
        }
        ret = jl.pop() || '';
        if (0 !== ret.indexOf('with')) {
          jl.push(ret);
          ret = '';
        }
        jl = jl.filter(function(t) {
          return t !== '';
        });
        if (ctx.in_fn && !ast._phantom) {
          body = "";
          if (jl.length) {
            body = "block {\n  " + (join_list(jl, '  ')) + "\n}";
          } else {
            body = "block {\n  skip\n}";
          }
          if (ret) {
            ret = " " + ret;
          }
          return "" + body + ret;
        } else {
          return join_list(jl, '');
        }
        break;
      case "Var_decl":
        name = var_name_trans(ast.name);
        ctx.var_hash[name] = true;
        type = translate_type(ast.type);
        if (ast.assign_value) {
          val = gen(ast.assign_value, opt, ctx);
          return "const " + name + " : " + type + " = " + val;
        } else {
          return "const " + name + " : " + type + " = " + (type2default_value(ast.type));
        }
        break;
      case "Ret_multi":
        jl = [];
        _ref4 = ast.t_list;
        for (_m = 0, _len4 = _ref4.length; _m < _len4; _m++) {
          v = _ref4[_m];
          jl.push(gen(v, opt, ctx));
        }
        return "with (" + (jl.join(', ')) + ")";
      case "If":
        cond = gen(ast.cond, opt, ctx);
        t = gen(ast.t, opt, ctx);
        f = gen(ast.f, opt, ctx);
        return "if " + (smart_bracket(cond)) + " then " + t + " else " + f + ";";
      case "While":
        cond = gen(ast.cond, opt, ctx);
        scope = gen(ast.scope, opt, ctx);
        return "while " + (smart_bracket(cond)) + " " + scope + ";";
      case "Class_decl":
        jl = [];
        _ref5 = ast.scope.list;
        for (_n = 0, _len5 = _ref5.length; _n < _len5; _n++) {
          v = _ref5[_n];
          switch (v.constructor.name) {
            case 'Var_decl':
              jl.push("" + v.name + ": " + (translate_type(v.type)) + ";");
              break;
            default:
              throw new Error("unimplemented v.constructor.name=" + v.constructor.name);
          }
        }
        return "type " + ast.name + " is record\n  " + (join_list(jl, '  ')) + "\nend";
      case "Fn_decl_multiret":
        ctx.var_hash[ast.name] = true;
        ctx = ctx.mk_nest();
        ctx.in_fn = true;
        arg_jl = [];
        _ref6 = ast.arg_name_list;
        for (idx = _o = 0, _len6 = _ref6.length; _o < _len6; idx = ++_o) {
          v = _ref6[idx];
          v = var_name_trans(v);
          ctx.var_hash[v] = true;
          type = translate_type(ast.type_i.nest_list[idx]);
          arg_jl.push("const " + v + " : " + type);
        }
        ret_jl = [];
        _ref7 = ast.type_o.nest_list;
        for (_p = 0, _len7 = _ref7.length; _p < _len7; _p++) {
          v = _ref7[_p];
          type = translate_type(v);
          ret_jl.push("" + type);
        }
        body = gen(ast.scope, opt, ctx);
        return "\nfunction " + ast.name + " (" + (arg_jl.join('; ')) + ") : (" + (ret_jl.join(' * ')) + ") is\n  " + (make_tab(body, '  '));
      default:
        if (opt.next_gen != null) {
          return opt.next_gen(ast, opt, ctx);
        }

        /* !pragma coverage-skip-block */
        perr(ast);
        throw new Error("unknown ast.constructor.name=" + ast.constructor.name);
    }
  };

}).call(window.translate = {})

