//
// Analyzer for SimpleC programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid SimpleC program.
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

module checker =

  // Given a token that is a literal will return the variable name associated with it by splicing the string 
  let getVariableName (strToParse: string) = 
    let splitIndex = strToParse.IndexOf(":")
    let result = strToParse.Substring(splitIndex+1)
    result

  // Given the populated symbol table and a variable name, returns the type associated with it in the symbol table. 
  // Assumes the given variable is a valid variable within the program. 
  let getVariableType symbolTable (varName: string) =
    let result = List.filter (fun (name, _) -> if name = varName then true else false) symbolTable
    let (varName, varType) = List.head result
    varType
    

  // Returns true if the string beings with the pattern provided and false if not
  let beginswith (pattern: string) (literal: string) = 
    literal.StartsWith (pattern)

  // returns type from exprValue if it is not int or real returns wrongtype 
  let getVariableTypeFromExprValue symbolTable (token: string) = 
    if beginswith "identifier" token then
        let varName = getVariableName token
        let varType = getVariableType symbolTable varName
        varType
    else 
        if beginswith "int" token then
            // it is a int literal
            "int"
        else if beginswith "real" token then
            "real"
        else if beginswith "str" token then
            "str"
        else
            "bool"


  
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
        failwith ("expecting identifier, but found " + next_token)
    elif expected_token = "int_literal" then
      // expecting int_literal:_ 
      if beginswith "int_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    elif expected_token = "str_literal" then
      // expecting str_literal:_
      if beginswith "str_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    elif expected_token = "real_literal" then
      // expecting real_literal:_ 
      if beginswith "real_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    else
      if expected_token = next_token then  
        List.tail tokens
      else
        failwith ("expecting " + expected_token + ", but found " + next_token)


  // First calls stmt to handle initial stmt then calls morestmts from result of last call
  let rec private stmts tokens symbolTable =     
    let T2 = stmt tokens symbolTable
    morestmts T2 symbolTable

  // all possible stmt options and their recursive descent functions are called depending on which one is matched with
  and private stmt tokens symbolTable = 
    let nextToken = List.head tokens

    if nextToken = ";" then
      let T2 = empty tokens symbolTable
      T2
    elif nextToken = "int" then
      let T3 = vardeclInt tokens symbolTable
      T3
    elif nextToken = "cin" then
      let T4 = input tokens symbolTable
      T4
    elif nextToken = "cout" then
      let T5 = output tokens symbolTable
      T5
    elif beginswith "identifier" nextToken then
      let T6 = assignment tokens symbolTable
      T6
    elif nextToken = "if" then
      let T7 = ifstmt tokens symbolTable
      T7
    elif nextToken = "real" then
      let T8 = vardeclReal tokens symbolTable
      T8
    else
      failwith ("expecting statement, but found " + nextToken)

  and private vardeclReal tokens symbolTable = 
    let T2 = matchToken "real" tokens
    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    T4
    

  and private vardeclInt tokens symbolTable = 
    let T2 = matchToken "int" tokens
    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    T4
  
  and private ifstmt tokens symbolTable = 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3 symbolTable
    let T5 = matchToken ")" T4
    let T6 = thenpart T5 symbolTable
    let T7 = elsepart T6 symbolTable
    T7
  
  and private condition tokens symbolTable = 

    let firstToken = List.head tokens
    let expr_type = getVariableTypeFromExprValue symbolTable firstToken

    let (T2, _, _, _, result) = expr tokens symbolTable

    // check if condition evaluated to bool. 
    if result = "true" then
        ()
    else
        failwith("if condition must be 'bool', but found '" + expr_type + "'")

    T2
  
  and private thenpart tokens symbolTable = 
    stmt tokens symbolTable
  
  and private elsepart tokens symbolTable = 
    let nextToken = List.head tokens

    if nextToken = "else" then
      let T2 = matchToken "else" tokens
      let T3 = stmt T2 symbolTable
      T3
    else
      tokens

  and private assignment tokens symbolTable = 
    let nextToken = List.head tokens // should be like identifier:_ 

    // get the variable type of the left side of assignment 
    let leftSideVarName = getVariableName nextToken // will result in string following identifier:
    let leftSideVarType = getVariableType symbolTable leftSideVarName

    let T2 = matchToken "identifier" tokens
    let T3 = matchToken "=" T2
    let (T4, foundVarType, operator, exprType, _) = expr T3 symbolTable 

    if exprType = "a+n" then
        // operation involved int (+) int or real (+) real
        if leftSideVarType = "real" then
            if foundVarType = "real" || foundVarType = "int" then
                ()
            else
                failwith("cannot assign '" + foundVarType + "' to variable of type '" + leftSideVarType + "'")
        else
            if leftSideVarType = foundVarType then
                ()
            else
                failwith("cannot assign '" + foundVarType + "' to variable of type '" + leftSideVarType + "'")
    else if exprType = "single" then
        // operation was single assignment
        // left is real
        if leftSideVarType = "real" then
            // right side can be int or real
            if foundVarType = "real" || foundVarType = "int" then
                ()
            else
                failwith("cannot assign '" + foundVarType + "' to variable of type '" + leftSideVarType + "'")
        else
            // left not real so has to be same no matter what
            if leftSideVarType = foundVarType then
                ()
            else
                failwith("cannot assign '" + foundVarType + "' to variable of type '" + leftSideVarType + "'")
    else
        // other cases
        ()


    let T5 = matchToken ";" T4
    T5
  
  and private expr tokens symbolTable = 

    let firstToken = List.head tokens
    let firstVarType = getVariableTypeFromExprValue symbolTable firstToken // if it is not a int or real firstVarType = wrongtype 

    // match first required exprvalue
    let T2 = exprvalue tokens symbolTable
    let nextToken = List.head T2

    if nextToken = "+" || nextToken = "-" || nextToken = "*" || nextToken = "/" || nextToken = "^" || nextToken = "<" || nextToken = "<=" || nextToken = ">" || nextToken = ">=" || nextToken = "==" || nextToken = "!=" then
      
      let operationToken = nextToken
      let T3 = exprop T2 symbolTable

      if operationToken = "+" || operationToken = "-" || operationToken = "*" || operationToken = "/" || operationToken = "^" then
        
        // 1st check if left type was int or real 
        if firstVarType = "str" || firstVarType = "bool" then
            failwith("operator " + operationToken + " must involve 'int' or 'real'")
        else
            // 1st type was int or real so need to check 2nd type now 
            let secondToken = List.head T3
            let secondVarType = getVariableTypeFromExprValue symbolTable secondToken
            
            if secondVarType = firstVarType then
                let T4 = exprvalue T3 symbolTable
                (T4, firstVarType, operationToken, "a+n", "false")
            else
                failwith("operator " + operationToken + " must involve 'int' or 'real'")
      else if operationToken = "<" || operationToken = "<=" || operationToken = ">" || operationToken = ">=" || operationToken = "==" || operationToken = "!=" then
        
        // comparison operators must involve same type 
        let secondToken = List.head T3
        let secondVarType = getVariableTypeFromExprValue symbolTable secondToken

        if firstVarType = secondVarType then
            
            // special case for real comparison 
            if operationToken = "==" && firstVarType = "real" then
                printfn "warning: comparing real numbers with == may never be true"
                let T4 = exprvalue T3 symbolTable
                (T4, firstVarType, operationToken, "comparison", "true")
            else 
                let T4 = exprvalue T3 symbolTable
                (T4, firstVarType, operationToken, "comparison", "true")

        else 
            failwith("type mismatch '" + firstVarType + "' " + operationToken + " '" + secondVarType + "'")

      else
        let T4 = exprvalue T3 symbolTable
        (T4, "", operationToken, "", "false")

    else
      // this case is no <expr-op> 
      (T2, firstVarType, "", "single", "false")
      

  and private exprop tokens symbolTable = 
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
    | _ -> failwith ("expecting expression operator, but found " + nextToken)
  
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
      failwith ("expecting identifier or literal, but found " + nextToken)

  and private input tokens symbolTable = 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let T4 = matchToken "identifier" T3
    let T5 = matchToken ";" T4
    T5

  and private morestmts tokens symbolTable =
    let nextToken = List.head tokens
    if nextToken = "}" then
      tokens
    else 
      let T2 = stmt tokens symbolTable
      morestmts T2 symbolTable

  and private empty tokens symbolTable = 
    matchToken ";" tokens


  
  //
  // simpleC
  //
  let private simpleC tokens symbolTable = 
    let T2 = matchToken "void" tokens 
    let T3 = matchToken "main" T2 
    let T4 = matchToken "(" T3 
    let T5 = matchToken ")" T4 
    let T6 = matchToken "{" T5 
    let T7 = stmts T6 symbolTable// calls recursive descent starting with stmts
    let T8 = matchToken "}" T7 
    let T9 = matchToken "$" T8   // $ => EOF, there should be no more tokens T9
    T9



  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable = 
    try
      let T2 = simpleC tokens symboltable
      "success"
    with 
      | ex -> "type_error: " + ex.Message

