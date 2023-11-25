# WAC grammar

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

import-statement ::= 'import' id ('with' string)? ':' import-type ';'
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

export-statement        ::= 'export' expr ('with' string)? ';'

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
