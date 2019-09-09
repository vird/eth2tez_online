var ast, k, module, v;

module = window.mod_ast = {};

ast = window.ast4gen;

for (k in ast) {
  v = ast[k];
  module[k] = v;
}

module.Fn_decl_multiret = (function() {
  Fn_decl_multiret.prototype.is_closure = false;

  Fn_decl_multiret.prototype.name = '';

  Fn_decl_multiret.prototype.type_i = null;

  Fn_decl_multiret.prototype.type_o = null;

  Fn_decl_multiret.prototype.arg_name_list = [];

  Fn_decl_multiret.prototype.scope = null;

  Fn_decl_multiret.prototype.line = 0;

  Fn_decl_multiret.prototype.pos = 0;

  function Fn_decl_multiret() {
    this.arg_name_list = [];
  }

  return Fn_decl_multiret;

})();

module.Ret_multi = (function() {
  Ret_multi.prototype.t_list = [];

  function Ret_multi() {
    this.t_list = [];
  }

  return Ret_multi;

})();
