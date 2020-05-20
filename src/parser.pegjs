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
  = head:Formula2 _ ("⇒" / "→" / "->" / "=>") _ right:Formula1 {
      return new Implies(head, right);
    }
  / Formula2

Formula2
  = ("∀" / "forall") _ names:Names1 _ "." _ expr:Formula2 {
      return names.reduceRight((acc,v) => new Forall(new TermVar(v), acc), expr)
    }
  / ("∃" / "exists") _ names:Names1 _ "." _ expr:Formula2 {
      return names.reduceRight((acc,v) => new Exists(new TermVar(v), acc), expr)
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

// Entry point for terms
Term
  = head:Term2 tail:(_ ("+" / "-") _ Term2)* {
      return tail.reduce(function(result, element) {
        if (element[1] === "+") { return new AddTerms(result, element[3]); }
        if (element[1] === "-") { return new SubtractTerms(result, element[3]); }
      }, head);
    }

// Lower precedence operators for terms
Term2
  = head:Term1 tail:(_ ("*" / "/") _ Term1)* {
      return tail.reduce(function(result, element) {
        if (element[1] === "*") { return new MultiplyTerms(result, element[3]); }
        if (element[1] === "/") { return new DivideTerms(result, element[3]); }
      }, head);
    }

// Literals for terms
Term1
  = name:Name { return new TermVar(name); }
  / i:Integer { return new TermInt(i); }
  / name:Name _ "(" _ terms:Terms _ ")" { return new TermFun(name, terms); }
  / "(" _ t:Term _ ")" { return t; }

Terms
  = first:Term _ rest:("," _ Term)* {
      return [first].concat(rest.map(l => l.find(x => x instanceof Term)));
    }
  / _ { return [] }

Atom
  = ("true" / "⊤") { return new Truth(); }
  / ("false" / "⊥") { return new Falsity(); }
  / first:Term _ ( "<=" / "≤" ) _ second:Term { return new LeqThan(first, second) }
  / first:Term _ "<" _ second:Term { return new LessThan(first, second) }
  / first:Term _ ( ">=" / "≥" ) _ second:Term { return new GeqThan(first, second) }
  / first:Term _ ">" _ second:Term { return new GreaterThan(first, second) }
  / first:Term _ "=" _ second:Term { return new Equal(first, second) }
  / name:Name _ "(" _ terms:Terms _ ")" { return new Relation(name, terms); }
  / name:Name { return new Var(name); }
  / Parens

HoareTriple
  = ("|-" / "⊢")? _ "{" _ pre:Formula _ "}" _ cmd:Command _ "{" _ post:Formula _ "}" { return new HoareTriple(pre, cmd, post) }

// top level command to avoid left recursion
Command
  = head:Command1 tail:(_ (";") _ Command1)* {
      return tail.reduce(function(result, element) {
        return new CmdSeq(result, element[3]);
      }, head);
    }

Command1
  = name:Name _ ":=" _ t:Term { return new CmdAssign(new TermVar(name), t) }
  / "if" _ cond:Formula _ "then" _ cmd1:Command _ "else" _ cmd2:Command { return new CmdIf(cond, cmd1, cmd2) }
  / "while" _ cond:Formula _ "do" _ cmd:Command { return new CmdWhile(cond, cmd) }
  / "(" _ cmd:Command _ ")" { return cmd }

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
  / _ "-" [0-9]+ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*
