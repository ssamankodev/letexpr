# letexpr

letexpr is a program that lets you write let expressions on the command line. Given a let expression, it prints the beta-reduced let expression (i.e., with all of the variables subsituted by their values), but does not execute it.

**Note: In this README, I will refer to each binding of a variable to a body as a let binding, and the combination of the let bindings and the final expression as a let expression. If any terminology is used incorrectly, please open an issue in the issue tracker.**

## Let binding

letexpr defines three different types of let bindings that bind a variable to a body.

### Normal

The first is a normal let binding that allows a body to contain references to other let bindings.

> let \<variable\> = \<body\>

### Raw

The second is a let binding that, by fiat, does not contain references to any other let binding.

> let raw \<variable\> = \<body\>

### Recursive

The third is a let binding that contains a reference to itself.

> let rec \<variable\> = \<body\>

## Let expression

letexpr defines two different types of let expressions that contain a collection of let bindings and a final expression whose variables should be replaced by the corresponding let binding’s body.

### Nested let expressions

The first is a let expression where the final expression is either an expression or itself a let expression.

```
let expression = let <let binding> in <let expression> | let <let binding> in <final expression>
let binding = <var> = <body> | raw <var> = <body> | rec <var> = <body>
```

Each let expression separates the let binding from the final expression with the token “in”.

### Mutually recursive let bindings

The second is a let binding where each let binding is in scope of all of the other let bindings, regardless of their syntactic order.

```
let expression = let <declarations> in <final expression>
declarations = <let binding> , <declarations> | <let binding>
let binding = <var> = <body> | raw <var> = <body> | rec <var> = <body>
```

## Sample invocations
```
# This outputs an infinite stream of 1s.

> letexpr let x = 1x in x
```
```
# This outputs an infinite stream of “12”s

> letexpr let x = 1y , y = 2x in x
```
```
# This prints “echo hello”
> letexpr let binding = “echo hello” in binding
```
```
# This prints “hello” as the subshell executes the letexpr command, which prints “echo hello” and that in turn is interpreted by the current shell, which runs the “echo” command on the input “hello” and prints “hello”.

> $(letexpr let binding = “echo hello” in binding)
```
```
# This changes the current directory to /path/to/project

> cd $(letexpr let raw x = “/path/to/project” in let raw y = “/path/to/other/project” in x)
```
```
# This prints the result of replacing all instances of the string literal “pattern” with the string literal “PATTERN” in the output of “cat /some/text/file”

> cat /some/text/file | letexpr let pattern = “PATTERN” in
```

## Potential use cases
- Namespace shell aliases or variables by creating a shell alias of a prepared letexpr invocation, so that they are accessible but don’t pollute the alias or variable namespace when unused.
- Tightly scope variable declarations so that they are only available when necessary, thereby reducing the risk of incorrectly using a .
- Generate text. As it is a let expression, it allows the construction of complex strings in a principled manner.

## FAQ
- Why use this instead of my preferred shell’s native variables?
  - For most cases, it is recommended that you use your shell’s native variables. This program is meant to enable more complex or stringent use cases where the user wants to have more control about which variables are in scope for a given command and how they are constructed.
- Why can’t I declare functions with the let bindings?
  - Currently, letexpr assumes that all let bindings are a binding of a variable to a singular value, and as such, it does not have a notion of function application syntactically or semantically. This may be revisted, but for now, letexpr will operate under this assumption.
- Why are variables identified by matching without considering surrounding context instead of only matching on words/tokens?
  - letexpr is expected to interoperate with external tools and the shell (e.g., the final expression being the output of a piped command), which means being able to work with input as is without modifying it to demarcate variables. As such, it is assumed that all matching text is meant to be substituted.
- Why not add the ability to execute the beta-reduced expression?
  - Primarily, this can be already be done by wrapping the letexpr invocation in a subshell. This orthogonality and separation of concerns allows letexpr to focus solely on beta reduction. Additionally, having a program like letexpr that rewrites the user’s input also execute commands requires giving said program a certain level of trust; by reducing its capabilities to printing a string, its output can be inspected and used as desired.
