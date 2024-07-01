//
// Analyzer for SimpleC programs.  This component performs
// semantic analysis, in particular collecting variable
// names and their types. The analysis also checks to ensure
// variable names are unique --- no duplicates.
//
// If all is well, a "symbol table" is built and returned,
// containing all variables and their types. A symbol table
// is a list of tuples of the form (name, type).  Example:
//
//   [("x", "int"); ("y", "int"); ("z", "real")]
//
// Modified by:
//   Viraj Saudagar
//
// Original author:
//   Prof. Joe Hummel
//   University of Illinois Chicago
//   CS 341, Spring 2022
// Modified by:
//   Ellen Kidane
//   University of Illinois Chicago
//   CS 341, Spring 2024
//

namespace compiler

module analyzer =

  // Returns true if the string beings with the pattern provided and false if not
  let beginswith (pattern: string) (literal: string) = 
    literal.StartsWith (pattern)

  // Given the populated symbol table and a variable name, returns the type associated with it in the symbol table. 
  // Assumes the given variable is a valid variable within the program. 
  let getVariableName (strToParse: string) = 
    let splitIndex = strToParse.IndexOf(":")
    let result = strToParse.Substring(splitIndex+1)
    result
  
  let private matchToken expected_token tokens =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation
    // at the first error.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" then
      // we are expecting identifier:_
      if beginswith "identifier" next_token then
        List.tail tokens
      else
        []
    elif expected_token = "int_literal" then
      // expecting int_literal:_ 
      if beginswith "int_literal" next_token then
        List.tail tokens
      else
        []
    elif expected_token = "str_literal" then
      // expecting str_literal:_
      if beginswith "str_literal" next_token then
        List.tail tokens
      else
        []
    elif expected_token = "real_literal" then
      // expecting real_literal:_ 
      if beginswith "real_literal" next_token then
        List.tail tokens
      else
        []
    else
      if expected_token = next_token then  
        List.tail tokens
      else
        []


  // First calls stmt to handle initial stmt then calls morestmts from result of last call
  let rec private stmts tokens =
    let symbolTable = []     
    let (T2, newTable) = stmt tokens symbolTable
    morestmts T2 newTable

  // all possible stmt options and their recursive descent functions are called depending on which one is matched with
  and private stmt tokens symbolTable = 
    let nextToken = List.head tokens

    if nextToken = ";" then
      let T2 = empty tokens 
      (T2, symbolTable)
    elif nextToken = "int" then
      let (T3, newTable) = vardeclInt tokens symbolTable
      (T3, newTable)
    elif nextToken = "cin" then
      let T4 = input tokens symbolTable
      (T4, symbolTable)
    elif nextToken = "cout" then
      let T5 = output tokens symbolTable
      (T5, symbolTable)
    elif beginswith "identifier" nextToken then
      let T6 = assignment tokens symbolTable
      (T6, symbolTable)
    elif nextToken = "if" then
      let T7 = ifstmt tokens symbolTable
      (T7, symbolTable)
    elif nextToken = "real" then
      let (T8, newTable) = vardeclReal tokens symbolTable
      (T8, newTable)
    else
      ([], [])

  and private vardeclReal tokens currSymbolTable = 
    let T2 = matchToken "real" tokens

    // need to get the identifier (variable name) name
    let nextToken = List.head T2 // next token should contain something like: "identifier:x"
    let varName = getVariableName nextToken

    // check if duplicate variable 
    if List.contains (varName, "int") currSymbolTable then
        failwith ("redefinition of variable '" + varName + "'")
    else if List.contains (varName, "real") currSymbolTable then
        failwith ("redefinition of variable '" + varName + "'")
    else
        ()

    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    (T4, (varName, "real")::currSymbolTable)
    

  and private vardeclInt tokens currSymbolTable = 
    let T2 = matchToken "int" tokens

    // need to get the identifier (variable name) name
    let nextToken = List.head T2 // next token should contain something like: "identifier:x"
    let varName = getVariableName nextToken

    // check if duplicate variable 
    if List.contains (varName, "int") currSymbolTable then
        failwith ("redefinition of variable '" + varName + "'")
    else if List.contains (varName, "real") currSymbolTable then
        failwith ("redefinition of variable '" + varName + "'")
    else
        ()

    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    (T4, (varName, "int")::currSymbolTable)
  
  and private ifstmt tokens symbolTable = 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3 symbolTable
    let T5 = matchToken ")" T4
    let (T6, _) = thenpart T5 symbolTable
    let T7 = elsepart T6 symbolTable
    T7
  
  and private condition tokens symbolTable = 
    expr tokens symbolTable
  
  and private thenpart tokens symbolTable = 
    stmt tokens symbolTable
  
  and private elsepart tokens symbolTable = 
    let nextToken = List.head tokens

    if nextToken = "else" then
      let T2 = matchToken "else" tokens
      let (T3, _) = stmt T2 symbolTable
      T3
    else
      tokens

  and private assignment tokens symbolTable = 
    let nextToken = List.head tokens

    // check left side of assignment 
    let leftVarName = getVariableName nextToken
    if List.contains (leftVarName, "int") symbolTable then
        ()
    else if List.contains (leftVarName, "real") symbolTable then
        ()
    else
        failwith ("variable '" + leftVarName + "' undefined")

    let T2 = matchToken "identifier" tokens
    let T3 = matchToken "=" T2
    let T4 = expr T3 symbolTable
    let T5 = matchToken ";" T4
    T5
  
  and private expr tokens symbolTable = 
    // match first required exprvalue
    let T2 = exprvalue tokens symbolTable
    let nextToken = List.head T2

    if nextToken = "+" || nextToken = "-" || nextToken = "*" || nextToken = "/" || nextToken = "^" || nextToken = "<" || nextToken = "<=" || nextToken = ">" || nextToken = ">=" || nextToken = "==" || nextToken = "!=" then
      let T3 = exprop T2
      let T4 = exprvalue T3 symbolTable
      T4
    else
      T2
      

  and private exprop tokens = 
    let nextToken = List.head tokens

    match nextToken with
    | "+" -> matchToken "+" tokens
    | "-" -> matchToken "-" tokens
    | "*" -> matchToken "*" tokens   
    | "/" -> matchToken "/" tokens               
    | "^" -> matchToken "^" tokens             
    | "<" -> matchToken "<" tokens                 
    | "<=" -> matchToken "<=" tokens                
    | ">" -> matchToken ">" tokens               
    | ">=" -> matchToken ">=" tokens               
    | "==" -> matchToken "==" tokens               
    | "!=" -> matchToken "!=" tokens 
    | _ -> []
  
  and private output tokens symbolTable = 
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = outputvalue T3 symbolTable
    let T5 = matchToken ";" T4
    T5
  
  and private outputvalue tokens symbolTable = 
    let nextToken = List.head tokens

    if nextToken = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else
      let T3 = exprvalue tokens symbolTable
      T3
  
  and private exprvalue tokens symbolTable = 
    let nextToken = List.head tokens

    if beginswith "identifier" nextToken then
      
      let varName = getVariableName nextToken
      if List.contains (varName, "int") symbolTable then
        ()
      else if List.contains (varName, "real") symbolTable then
        ()
      else
        failwith ("variable '" + varName + "' undefined")

      let T2 = matchToken "identifier" tokens
      T2
    elif beginswith "int_literal" nextToken then
      let T3 = matchToken "int_literal" tokens
      T3
    elif beginswith "str_literal" nextToken then
      let T4 = matchToken "str_literal" tokens
      T4
    elif nextToken = "true" then
      let T5 = matchToken "true" tokens
      T5
    elif nextToken = "false" then 
      let T6 = matchToken "false" tokens
      T6
    elif beginswith "real_literal" nextToken then
      let T7 = matchToken "real_literal" tokens
      T7
    else
      []

  and private input tokens symbolTable = 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2

    // check if variable being input to exists. 
    let nextToken = List.head T3
    let varName = getVariableName nextToken

    if List.contains (varName, "int") symbolTable then
        ()
    else if List.contains (varName, "real") symbolTable then
        ()
    else
        failwith ("variable '" + varName + "' undefined")

    let T4 = matchToken "identifier" T3
    let T5 = matchToken ";" T4
    T5

  and private morestmts tokens newTable =
    let nextToken = List.head tokens
    if nextToken = "}" then
      (tokens, newTable)
    else 
      let (T2, nextTable) = stmt tokens newTable
      morestmts T2 nextTable


  and private empty tokens  = 
    matchToken ";" tokens


  
  //
  // simpleC
  //
  let private simpleC tokens = 
    let T2 = matchToken "void" tokens 
    let T3 = matchToken "main" T2 
    let T4 = matchToken "(" T3 
    let T5 = matchToken ")" T4 
    let T6 = matchToken "{" T5 
    let (T7, symbolTable) = stmts T6
    let T8 = matchToken "}" T7 
    let T9 = matchToken "$" T8   // $ => EOF, there should be no more tokens T9
    (T9, symbolTable)





  //
  // build_symboltable tokens
  //
  // Given a list of tokens, analyzes the program by looking
  // at variable declarations and collecting them into a
  // list. This list is known as a symbol table. Returns
  // a tuple (result, symboltable), where result is a string 
  // denoting "success" if valid, otherwise a string of the 
  // form "semantic_error:...".
  //
  // On success, the symboltable is a list of tuples of the
  // form (name, type), e.g. [("x","int"); ("y","real")]. On 
  // an error, the returned list is empty [].
  //
  let build_symboltable tokens = 
    try
      let (T2, symboltable) = simpleC tokens
      ("success", symboltable)
    with 
      | ex -> ("semantic_error: " + ex.Message, [])