## WebAssembly Compositions (WAC)

WAC is a superset of the [WIT language](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md).

In addition to being able to declare types, interfaces, and worlds, WAC
also allows for defining a _composition_.

In the simplest terms, a composition is a collection of components that
are instantiated in a topological order and certain exports from those
instances are made available as exports of the composition itself.

WAC currently has three statements that extend the WIT language: imports,
`let`, and exports.

### Import Statements

A composition may explicitly import an item in the resulting composition;
this is done with the `import` statement.

Assume a `greeter` interface definition published to a registry:

```wit
package example:greeter;

interface greeter {
  greet: func() -> string;
}
```

If we want to import an _instance_ of this interface in our composition, we can
use the `import` statement in WAC:

```wac
import greeter: example:greeter/greeter;
```

Items imported by a package path use the path as the name of the import in the
resulting composition; in the above example, the import name would be
`example:greeter/greeter`.

The `as` keyword can be used to rename the imported item:

```wac
import greeter as "my-greeter": example:greeter/greeter;
```

Here the name of the import becomes `my-greeter`; the name may be any valid import
name in the component model.

The local name `greeter` can then be used to refer to the imported item from
the rest of the composition.

Imports may also use inline interface and function type declarations:

```wac
import greeter: interface {
    greet: func() -> string;
};

import greet: func() -> string;
```

As these imports are not by package path, the name of the import will be the
same as the local name, by default. In the above example, this would be
`greeter` and `greet`, respectively. As previously mentioned, the `as` keyword
can be used to specify a different import name.

#### Implicit Imports

While the `import` statement is used to define an _explicit_ import, the `new`
expression (covered below) can be used to _implicitly_ import items from the
composition.

A special syntax of the `new` expression allows for omitting instantiation
arguments in favor of simply importing the arguments directly from the
composition and passing them through to the instantiation.

Let's assume there exists a component named `example:my-component` with the
following world (i.e. component type):

```wit
world my-component {
    import i: interface {
        f: func();
    };
}
```

We can instantiate this component using the `new` expression without having to
explicitly specify the `i` argument:

```wac
let my-instance = new example:my-component { ... };
```

The special `...` syntax indicates that any arguments that were not specified
as part of the `new` expression should be imported from the composition and
passed through to the instantiation.

The above is equivalent to:

```wac
import i: interface {
    f: func();
};

let my-instance = new example:my-component { i };
```

Note that implicit imports may not conflict with explicit imports of the same
name.

Additionally, the WAC parser will attempt to merge implicit imports; if a merge
cannot be performed, an error will be emitted about the conflicting definitions.

Let's assume there exists an `example:my-other-component` with the following
world:

```wit
world my-other-component {
    import i: interface {
        g: func() -> string;
    };
}
```

If we attempt to instantiate both `example:my-component` and
`example:my-other-component` using implicit imports:

```wac
let my-instance = new example:my-component { ... };
let my-other-instance = new example:my-other-component { ... };
```

Then the parser will _merge_ the two implicit imports of `i` together,
resulting in the following equivalent composition:

```wac
import i: interface {
    f: func();
    g: func() -> string;
};

let my-instance = new example:my-component { i };
let my-other-instance = new example:my-other-component { i };
```

As seen above, items that are implicitly imported are _shared_ between any
instantiations that refer to them.

### Let Statements

The `let` statement allows for binding a local name in the composition to the
result of an expression.

Note that local names are not variables and cannot be reassigned; a
redefinition of a name is an error.

There are currently four expressions in WAC:

* The `new` expression (e.g `new a:b { }`)
* The postfix access expression (e.g. `a.b`).
* The postfix named access expression (e.g. `a["b"]`)
* The nested expression (e.g. `(<expr>)`).

#### New Expressions

A `new` expression instantiates a component and returns an instance
representing the _exports_ of the component.

The `new` expression takes the name of the package (i.e. component) to
instantiate and a list of instantiation arguments (i.e. imports).

The last argument may be the special `...` argument that implies any missing
arguments should be imported from the composition and implicitly passed as
arguments to the instantiation.

If `...` is not specified, then all instantiation arguments must be explicitly
specified.

There are two forms of instantiation arguments: implicitly named and explicitly
named.

An implicitly named argument is passed by identifier alone:

```wac
let i = new a:b { c };
```

Where `i` is the name of the bound instance, `a:b` is the package being
instantiated, and `c` is the instantiation argument.

The name of the instantiation argument is inferred according to these rules (in
order of precedence):

* If `c` is an instance of an interface with an associated package path (e.g.
`x:y/z`) and package `a:b` has an import with a matching path, then the path
will be used as the argument name.

* If `c` is an explicit import or an access of an instance export and the
package `a:b` has an import with a matching name, then the import/export name
will be used as the argument name.

* If component `a:b` has exactly one import with `c` as the final component of
a path (e.g. `x:y/c`), then the path will be used as the argument name.

* Lastly, `c` will be used as the argument name.

Explicitly named arguments are passed as a name/value pair:

```wac
let i = new a:b { c: d };
```

Where `i` is the name of the bound instance, `a:b` is the package being
instantiated, `c` is the name of the instantiation argument, and `d` is the
value of the argument.

Even with this form, the name of the instantiation argument is inferred
according to the last two rules stated above; for example, the explicit
argument `input-stream: stream` may be used to refer to an import of `wasi:io/
input-stream` or an import of `input-stream`.

Explicit argument names may also be strings:

```wac
let i = new a:b { "c": d };
```

This is equivalent to the previous example except that the argument name `c` is
_always_ used; no inference is performed.

#### Access Expressions

The postfix access expression allows for accessing an export of an instance.

An example of instantiating component `a:b` and then binding the `wasi:io/outgoing-stream`
export of the instance to `s`.

```wac
let i = new a:b { ... };
let s = i.outgoing-stream;
``````

Access expressions use the following rules to determine the name of the export:

* If component `a:b` has exactly one export with `outgoing-stream` as the final
component of a path (e.g. `wasi:io/outgoing-stream`), then the path will be
used as the export name.

* Otherwise, `outgoing-stream` will be used as the export name.

#### Named Access Expressions

Similar to the postfix access expression, the postfix named access expression
is used to access an export of an instance.

However, this form allows for the export name to be explicitly specified as a
string:

```wac
let i = new a:b { ... };
let s = i["wasi:io/outgoing-stream"];
```

This is equivalent to the previous example except that the export name is
_exactly_ what was specified; no inference is performed.

The string may be any legal export name in the component model.

### Export Statements

Export statements are used to export the result of an expression from the
composition itself.

The export statement can be used to export the item represented by a local name:

```wac
let i = new a:b { ... };
let s = i.streams;
export s;
```

In the above example, component `a:b` is instantiated and `s` is bound to the
export of `wasi:io/streams` from the instance.

The `export` statement is then used to export `s` from the composition.

The name of the export is inferred according to these rules (in order of
precedence):

* If the item is an instance of an interface with an associated package path (e.g.
`x:y/z`), then the path is used as the export name.

* If the item is an explicit import or an access of an instance export, then
that name is used.

In the above example, the export will be named `wasi:io/streams` as that is
ultimately the name of the export that was accessed from instance `i`.

If the export name cannot be inferred, then the export name must be explicitly
specified with the `as` keyword:

```wac
let i = new a:b { ... };
export i as "my-instance";
```

### WAC Grammar

The current WAC grammar:

```ebnf
document  ::= package-decl statement*
statement ::= import-statement
            | type-statement
            | let-statement
            | export-statement

package-decl ::= `package` package-name `;`
package-name ::= id (':' id)+ ('@' version)?
version      ::= <SEMVER>

import-statement ::= 'import' id ('as' (id | string))? ':' import-type ';'
import-type      ::= package-path | func-type | inline-interface | id
package-path     ::= id (':' id)+ ('/' id)+ ('@' version)?

type-statement      ::= interface-decl | world-decl | type-decl
interface-decl      ::= 'interface' id '{' interface-item* '}'
interface-item      ::= use-type | item-type-decl | interface-export
use-type            ::= 'use' use-path '.' '{' use-items '}' ';'
use-path            ::= package-path | id
use-items           ::= use-item (',' use-item)* ','?
use-item            ::= id ('as' id)?
interface-export    ::= id ':' func-type-ref ';'
world-decl          ::= 'world' id '{' world-item* '}'
world-item          ::= use-type
                      | item-type-decl
                      | world-import
                      | world-export
                      | world-include
world-import        ::= 'import' world-item-path ';'
world-export        ::= 'export' world-item-path ';'
world-item-path     ::= named-world-item | package-path | id
named-world-item    ::= id ':' extern-type
extern-type         ::= func-type | inline-interface | id
inline-interface    ::= 'interface' '{' interface-item* '}'
world-include       ::= 'include' world-ref ('with' '{' world-include-items '}')? ';'
world-include-items ::= world-include-item (',' world-include-item)* ','?
world-include-item  ::= id 'as' id
world-ref           ::= package-path | id
type-decl           ::= variant-decl | record-decl | flags-decl | enum-decl | type-alias
item-type-decl      ::= resource-decl | type-decl
resource-decl       ::= 'resource' id '{' resource-item* '}'
resource-item       ::= constructor | method
constructor         ::= 'constructor' param-list
method              ::= id ':' 'static'? func-type
variant-decl        ::= 'variant' id '{' variant-cases '}'
variant-cases       ::= variant-case (',' variant-case)* ','?
variant-case        ::= id ('(' type ')')?
record-decl         ::= 'record' id '{' fields '}'
fields              ::= named-type (',' named-type)* ','?
flags-decl          ::= 'flags' id '{' ids '}'
ids                 ::= id (',' id)* ','?
enum-decl           ::= 'enum' id '{' ids '}'
type-alias          ::= 'type' id '=' (func-type | type) ';'
func-type-ref       ::= func-type | id
func-type           ::= '(' params? ')' ('->' results)?
params              ::= named-type (',' named-type)* ','?
results             ::= type
                      | '(' named-type (',' named-type)* ','? ')'
named-type          ::= id ':' type
type                ::= u8
                      | s8
                      | u16
                      | s16
                      | u32
                      | s32
                      | u64
                      | s64
                      | float32
                      | float64
                      | char
                      | bool
                      | string
                      | tuple
                      | list
                      | option
                      | result
                      | borrow
                      | id
tuple               ::= 'tuple' '<' type (',' type)* ','? '>'
list                ::= 'list' '<' type '>'
option              ::= 'option' '<' type '>'
result              ::= 'result'
                      | 'result' '<' type '>'
                      | 'result' '<' '_' ',' type '>'
                      | 'result' '<' type ',' type '>'
borrow              ::= 'borrow' '<' type '>'

let-statement           ::= 'let' id '=' expr ';'
expr                    ::= primary-expr postfix-expr*
primary-expr            ::= new-expr | nested-expr | id
new-expr                ::= 'new' package-name '{' instantiation-args '}'
instantiation-args      ::= instantiation-arg (',' instantiation-arg)* (',' '...'?)?
instantiation-arg       ::= named-instantiation-arg | id
named-instantiation-arg ::= (id | string) ':' expr
nested-expr             ::= '(' expr ')'
postfix-expr            ::= access-expr | named-access-expr
access-expr             ::= '.' id
named-access-expr       ::= '[' string ']'

export-statement        ::= 'export' expr ('as' (id | string))? ';'

id     ::= '%'?[a-z][a-z0-9]*('-'[a-z][a-z0-9]*)*
string ::= '"' character-that-is-not-a-double-quote* '"'
```

Whitespace (may appear anywhere between tokens):

```ebnf
whitespace ::= ' ' | '\n' | '\r' | '\t' | comment
comment    ::= '//' character-that-is-not-a-newline*
             | '/*' any-unicode-character* '*/'
```

Note: block comments are allowed to be nested.
