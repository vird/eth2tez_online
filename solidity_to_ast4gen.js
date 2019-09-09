var Context, Type, ast, bin_op_map, config, is_complex_assign_op, un_op_map;

config = window.config;

Type = window.Type;

ast = window.mod_ast;

bin_op_map = {
  '+': 'ADD',
  '-': 'SUB',
  '*': 'MUL',
  '/': 'DIV',
  '%': 'MOD',
  '&': 'BIT_AND',
  '|': 'BIT_OR',
  '^': 'BIT_XOR',
  '&&': 'BOOL_AND',
  '||': 'BOOL_OR',
  '==': 'EQ',
  '!=': 'NE',
  '>': 'GT',
  '<': 'LT',
  '>=': 'GTE',
  '<=': 'LTE',
  '=': 'ASSIGN',
  '+=': 'ASS_ADD',
  '-=': 'ASS_SUB',
  '*=': 'ASS_MUL',
  '/=': 'ASS_DIV'
};

is_complex_assign_op = {
  'ASS_ADD': true,
  'ASS_SUB': true,
  'ASS_MUL': true,
  'ASS_DIV': true
};

un_op_map = {
  '-': 'MINUS',
  '+': 'PLUS',
  '~': 'BIT_NOT'
};

Context = (function() {
  Context.prototype.current_contract = null;

  Context.prototype.contract_list = [];

  function Context() {
    this.contract_list = [];
  }

  return Context;

})();

window.solidity_to_ast4gen = function(root) {
  var contract, ctx, fn_list, last, main_fn, node, postprocess_bin_op, ret, storage_decl, t, tmp, walk, walk_exec, walk_param, walk_type, _i, _j, _k, _len, _len1, _len2, _ref, _ref1, _ref2;
  postprocess_bin_op = function(ast_ready) {
    var inter, ret;
    if (!is_complex_assign_op[ast_ready.op]) {
      return ast_ready;
    }
    ret = new ast.Bin_op;
    ret.op = 'ASSIGN';
    ret.a = ast_ready.a;
    ret.b = inter = new ast.Bin_op;
    inter.op = ast_ready.op.replace(/^ASS_/, '');
    inter.a = ast_ready.a;
    inter.b = ast_ready.b;
    return ret;
  };
  walk_type = function(ast_tree, ctx) {
    var ret;
    switch (ast_tree.nodeType) {
      case 'ElementaryTypeName':
        return new Type(ast_tree.typeDescriptions.typeIdentifier);
      case 'Mapping':
        ret = new Type("map");
        ret.nest_list.push(walk_type(ast_tree.keyType, ctx));
        ret.nest_list.push(walk_type(ast_tree.valueType, ctx));
        return ret;
      default:
        p(ast_tree);
        throw new Error("walk_type unknown nodeType '" + ast_tree.nodeType + "'");
    }
  };
  walk_param = function(ast_tree, ctx) {
    var ret, t, v, _i, _len, _ref;
    switch (ast_tree.nodeType) {
      case 'ParameterList':
        ret = [];
        _ref = ast_tree.parameters;
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          v = _ref[_i];
          ret.append(walk_param(v, ctx));
        }
        return ret;
      case 'VariableDeclaration':
        if (ast_tree.value) {
          throw new Error("ast_tree.value not implemented");
        }
        ret = [];
        t = new Type(ast_tree.typeDescriptions.typeIdentifier);
        t._name = ast_tree.name;
        ret.push(t);
        return ret;
      default:
        p(ast_tree);
        throw new Error("walk_param unknown nodeType '" + ast_tree.nodeType + "'");
    }
  };
  walk_exec = function(ast_tree, ctx) {
    var decl, inner, loc, node, ret, v, _i, _j, _len, _len1, _ref, _ref1;
    switch (ast_tree.nodeType) {
      case 'Identifier':
        ret = new ast.Var;
        ret.name = ast_tree.name;
        ret.type = new Type(ast_tree.typeDescriptions.typeIdentifier);
        return ret;
      case 'Literal':
        ret = new ast.Const;
        ret.type = new Type(ast_tree.kind);
        ret.val = ast_tree.value;
        return ret;
      case 'Assignment':
        ret = new ast.Bin_op;
        ret.op = bin_op_map[ast_tree.operator];
        if (!ret.op) {
          throw new Error("unknown bin_op " + ast_tree.operator);
        }
        ret.a = walk_exec(ast_tree.leftHandSide, ctx);
        ret.b = walk_exec(ast_tree.rightHandSide, ctx);
        return postprocess_bin_op(ret);
      case 'BinaryOperation':
        ret = new ast.Bin_op;
        ret.op = bin_op_map[ast_tree.operator];
        if (!ret.op) {
          throw new Error("unknown bin_op " + ast_tree.operator);
        }
        ret.a = walk_exec(ast_tree.leftExpression, ctx);
        ret.b = walk_exec(ast_tree.rightExpression, ctx);
        return postprocess_bin_op(ret);
      case 'MemberAccess':
        ret = new ast.Field_access;
        ret.t = walk_exec(ast_tree.expression, ctx);
        ret.name = ast_tree.memberName;
        return ret;
      case 'IndexAccess':
        ret = new ast.Bin_op;
        ret.op = 'INDEX_ACCESS';
        ret.a = walk_exec(ast_tree.baseExpression, ctx);
        ret.b = walk_exec(ast_tree.indexExpression, ctx);
        return ret;
      case 'UnaryOperation':
        ret = new ast.Un_op;
        ret.op = un_op_map[ast_tree.operator];
        if (!ret.op) {
          throw new Error("unknown un_op " + ast_tree.operator);
        }
        ret.a = walk_exec(ast_tree.subExpression, ctx);
        return ret;
      case 'FunctionCall':
        ret = new ast.Fn_call;
        ret.fn = new ast.Var;
        ret.fn.name = ast_tree.expression.name;
        _ref = ast_tree["arguments"];
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          v = _ref[_i];
          ret.arg_list.push(walk_exec(v, ctx));
        }
        return ret;
      case 'ExpressionStatement':
        return walk_exec(ast_tree.expression, ctx);
      case 'VariableDeclarationStatement':
        if (ast_tree.declarations.length !== 1) {
          throw new Error("ast_tree.declarations.length != 1");
        }
        decl = ast_tree.declarations[0];
        if (decl.value) {
          throw new Error("decl.value not implemented");
        }
        ret = new ast.Var_decl;
        ret.name = decl.name;
        ret.type = new Type(decl.typeDescriptions.typeIdentifier);
        if (ast_tree.initialValue) {
          ret.assign_value = walk_exec(ast_tree.initialValue, ctx);
        }
        return ret;
      case "Block":
        ret = new ast.Scope;
        _ref1 = ast_tree.statements;
        for (_j = 0, _len1 = _ref1.length; _j < _len1; _j++) {
          node = _ref1[_j];
          ret.list.push(walk_exec(node, ctx));
        }
        return ret;
      case "IfStatement":
        ret = new ast.If;
        ret.cond = walk_exec(ast_tree.condition, ctx);
        ret.t = walk_exec(ast_tree.trueBody, ctx);
        if (ast_tree.falseBody) {
          ret.f = walk_exec(ast_tree.falseBody, ctx);
        }
        return ret;
      case 'WhileStatement':
        ret = new ast.While;
        ret.cond = walk_exec(ast_tree.condition, ctx);
        ret.scope = walk_exec(ast_tree.body, ctx);
        return ret;
      case 'ForStatement':
        ret = new ast.Scope;
        ret._phantom = true;
        if (ast_tree.initializationExpression) {
          ret.list.push(walk_exec(ast_tree.initializationExpression, ctx));
        }
        ret.list.push(inner = new ast.While);
        inner.cond = walk_exec(ast_tree.condition, ctx);
        loc = walk_exec(ast_tree.body, ctx);
        if (loc.constructor.name === 'Scope') {
          inner.scope = loc;
        } else {
          inner.scope.list.push(loc);
        }
        inner.scope.list.push(walk_exec(ast_tree.loopExpression, ctx));
        return ret;
      case 'Return':
        ret = new ast.Ret_multi;
        ret.t_list.push(walk_exec(ast_tree.expression, ctx));
        return ret;
      default:
        p(ast_tree);
        throw new Error("walk_exec unknown nodeType '" + ast_tree.nodeType + "'");
    }
  };
  walk = function(ast_tree, ctx) {
    var fn, name, node, ret, v, _i, _j, _len, _len1, _ref, _ref1;
    switch (ast_tree.nodeType) {
      case "PragmaDirective":
        name = ast_tree.literals[0];
        if (name === 'solidity') {
          return;
        }
        if (name === 'experimental') {
          return;
        }
        throw new Error("unknown pragma '" + name + "'");
        break;
      case "VariableDeclaration":
        ret = new ast.Var_decl;
        ret._const = ast_tree.constant;
        ret.name = ast_tree.name;
        ret.type = walk_type(ast_tree.typeName, ctx);
        if (ast_tree.value) {
          ret.assign_value = walk_exec(ast_tree.value, ctx);
        }
        return ret;
      case "FunctionDefinition":
        fn = ctx.current_function = new ast.Fn_decl_multiret;
        fn.name = ast_tree.name || 'constructor';
        fn.type_i = new Type('function');
        fn.type_o = new Type('function');
        fn.type_i.nest_list = walk_param(ast_tree.parameters, ctx);
        fn.type_o.nest_list = walk_param(ast_tree.returnParameters, ctx);
        _ref = fn.type_i.nest_list;
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          v = _ref[_i];
          fn.arg_name_list.push(v._name);
        }
        if (ast_tree.modifiers.length) {
          throw new "ast_tree.modifiers not implemented";
        }
        if (ast_tree.body) {
          fn.scope = walk_exec(ast_tree.body, ctx);
        } else {
          fn.scope = new ast.Scope;
        }
        return fn;
      case "ContractDefinition":
        ctx.contract_list.push(ctx.current_contract = new ast.Class_decl);
        ctx.current_contract.name = ast_tree.name;
        _ref1 = ast_tree.nodes;
        for (_j = 0, _len1 = _ref1.length; _j < _len1; _j++) {
          node = _ref1[_j];
          ctx.current_contract.scope.list.push(walk(node, ctx));
        }
        return null;
      default:
        p(ast_tree);
        throw new Error("walk unknown nodeType '" + ast_tree.nodeType + "'");
    }
  };
  ctx = new Context;
  _ref = root.nodes;
  for (_i = 0, _len = _ref.length; _i < _len; _i++) {
    node = _ref[_i];
    walk(node, ctx);
  }
  storage_decl = new ast.Class_decl;
  storage_decl.name = config.storage;
  fn_list = [];
  _ref1 = ctx.contract_list;
  for (_j = 0, _len1 = _ref1.length; _j < _len1; _j++) {
    contract = _ref1[_j];
    _ref2 = contract.scope.list;
    for (_k = 0, _len2 = _ref2.length; _k < _len2; _k++) {
      node = _ref2[_k];
      switch (node.constructor.name) {
        case 'Var_decl':
          storage_decl.scope.list.push(node);
          break;
        case 'Fn_decl_multiret':
          fn_list.push(node);
          node.arg_name_list.push(config.contractStorage);
          node.type_i.nest_list.push(new Type(config.storage));
          node.type_o.nest_list.push(new Type(config.storage));
          last = node.scope.list.last();
          t = new ast.Var;
          t.name = config.contractStorage;
          if ((last != null ? last.constructor.name : void 0) === 'Ret_multi') {
            last.t_list.push(t);
          } else {
            node.scope.list.push(last = new ast.Ret_multi);
            last.t_list.push(t);
          }
          break;
        default:
          throw new Error("bad type node.constructor.name=" + node.constructor.name);
      }
    }
  }
  ret = new ast.Scope;
  ret.list.push(storage_decl);
  ret.list.append(fn_list);
  main_fn = new ast.Fn_decl_multiret;
  main_fn.name = 'main';
  main_fn.arg_name_list.push('dummy_int', config.contractStorage);
  main_fn.type_i = new Type("function<t_int256," + config.storage + ">");
  main_fn.type_o = new Type("function<" + config.storage + ">");
  main_fn.scope = new ast.Scope;
  main_fn.scope.list.push(tmp = new ast.Ret_multi);
  tmp.t_list.push(t = new ast.Var);
  t.name = config.contractStorage;
  ret.list.push(main_fn);
  return ret;
};
