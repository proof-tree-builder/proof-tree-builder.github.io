Sequent
  = precedents:Formulas _ ("⊢" / "|-") _ antecedents:Formulas {
      return new Sequent(precedents, antecedents);
    }

Formulas
  = first:Formula _ rest:("," _ Formula)* {
      return [first].concat(rest.map(l => l.find(x => x instanceof Formula)));
    }
  / _ { return [] }

Formula = Formula1

// implies is right associative, unlike others
Formula1
  = head:Formula2 _ ("⇒" / "->" / "=>") _ right:Formula1 {
      return new Implies(head, right);
    }
  / Formula2

Formula2
  = ("∀" / "forall") _ names:Names1 _ "." _ expr:Formula2 {
      return names.reduceRight((acc,v) => new Forall(v, acc), expr)
    }
  / ("∃" / "exists") _ names:Names1 _ "." _ expr:Formula2 {
      return names.reduceRight((acc,v) => new Exists(v, acc), expr)
    }
  / Formula3

Formula3
  = head:Formula4 tail:(_ ("∨" / "\\/" / "||" / "|") _ Formula4)* {
      return tail.reduce(function(result, element) {
        if (["∨", "\\/", "||", "|"].includes(element[1])) { return new Or(result, element[3]); }
      }, head);
    }

Formula4
  = head:Formula5 tail:(_ ("∧" / "/\\" / "&&" / "&") _ Formula5)* {
      return tail.reduce(function(result, element) {
        if (["∧", "/\\", "&&", "&"].includes(element[1])) {
          return new And(result, element[3]);
        }
      }, head);
    }

Formula5
  = ("¬" / "!" / "~") _ expr:Atom { return new Not(expr); }
  / Atom

Term
  = name:Name { return new TermVar(name); }
  / name:Name _ "(" _ terms:Terms _ ")" { return new TermFun(name, terms); }

Terms
  = first:Term _ rest:("," _ Term)* {
      return [first].concat(rest.map(l => l.find(x => x instanceof Term)));
    }
  / _ { return [] }

Atom
  = name:Name _ "(" _ terms:Terms _ ")" { return new Relation(name, terms); }
  / name:Name { return new Var(name); }
  / Parens

Parens
  = "(" _ expr:Formula1 _ ")" { return expr; }

Names1
  = first:Name _ rest:("," _ Name)* {
      return [first].concat(rest.map(l => l[2]));
    }
  / first:Name { return [first] }

Name
  = ([a-z] / [A-Z])([a-z] / [A-Z] / [0-9])* { return text() }

Integer "integer"
  = _ [0-9]+ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*
