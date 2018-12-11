// implies is right associative, unlike others
Expression1
  = head:Expression2 _ ("⇒" / "->" / "=>") _ right:Expression1 {
      return new Implies(head, right);
    }
  / Expression2


Expression2
  = ("∀" / "forall") _ name:Name _ "." _ expr:Expression3 {
      return new Forall(name, expr)
    }
  / ("∃" / "exists") _ name:Name _ "." _ expr:Expression3 {
      return new Exists(name, expr)
    }
  / Expression3

Expression3
  = head:Expression4 tail:(_ ("∨" / "\\/" / "||" / "|") _ Expression4)* {
      return tail.reduce(function(result, element) {
        if (["∨", "\\/", "||", "|"].includes(element[1])) { return new Or(result, element[3]); }
      }, head);
    }

Expression4
  = head:Expression5 tail:(_ ("∧" / "/\\" / "&&" / "&") _ Expression5)* {
      return tail.reduce(function(result, element) {
        if (["∧", "/\\", "&&", "&"].includes(element[1])) {
          return new And(result, element[3]);
        }
      }, head);
    }

Expression5
  = ("¬" / "!" / "~") _ expr:Atom { return new Not(expr); }
  / Atom



Term
  = name:Name { return new TermVar(name); }
  / name:Name _ "(" _ ")" { return new TermFun(name, []); }
  / name:Name _ "(" _ first:Term _ rest:("," _ Term)* ")" {
      return new TermFun(name, [first].concat(rest.filter(x => x instanceof Term)));
    }

Atom
  = name:Name _ "(" _ ")" { return new Relation(name, []); }
  / name:Name _ "(" _ first:Term _ rest:("," _ Term)* ")" {
      return new Relation(name, [first].concat(rest.filter(x => x instanceof Term)));
    }
  / name:Name { return new Var(name); }
  / Parens

Parens
  = "(" _ expr:Expression1 _ ")" { return expr; }

Name
  = ([a-z] / [A-Z])([a-z] / [A-Z] / [0-9])* { return text() }

Integer "integer"
  = _ [0-9]+ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*
