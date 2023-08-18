#include "llvm/Analysis/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/MCJIT.h"
#include "llvm/ExecutionEngine/ObjectCache.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include <cctype>
#include <cstdio>
#include <map>
#include <string>
#include <vector>


#include <iostream>
#include <map>
#include <memory>
#include <vector>
#include "KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"


using namespace llvm;


//===----------------------------------------------------------------------===//
// Command-line options
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// 如果不是以下5种情况，Lexer返回[0-255]的ASCII值，否则返回以下枚举值
enum Token {
  TOKEN_EOF = -1,         // 文件结束标识符
  TOKEN_DEF = -2,         // 关键字def
  TOKEN_EXTERN = -3,      // 关键字extern
  TOKEN_IDENTIFIER = -4,  // 名字
  TOKEN_NUMBER = -5,      // 数值
  TOKEN_IF = -6,          // if
  TOKEN_THEN = -7,        // then
  TOKEN_ELSE = -8,        // else
  TOKEN_FOR = -9,         // for
  TOKEN_IN = -10,         // in
  TOKEN_BINARY = -11,     // binary
  TOKEN_UNARY = -12,      // unary
};



std::string g_identifier_str;  // Filled in if TOKEN_IDENTIFIER
double g_number_val;           // Filled in if TOKEN_NUMBER



// 从标准输入解析一个Token并返回
int GetToken() {
  static int last_char = ' ';
  // 忽略空白字符
  while (isspace(last_char)) {
    last_char = getchar();
  }
  // 识别字符串
  if (isalpha(last_char)) {
    g_identifier_str = last_char;
    while (isalnum((last_char = getchar()))) {
      g_identifier_str += last_char;
    }
    if (g_identifier_str == "def") {
      return TOKEN_DEF;
    } else if (g_identifier_str == "extern") {
      return TOKEN_EXTERN;
    } else if (g_identifier_str == "if") {
      return TOKEN_IF;
    } else if (g_identifier_str == "then") {
      return TOKEN_THEN;
    } else if (g_identifier_str == "else") {
      return TOKEN_ELSE;
    } else if (g_identifier_str == "for") {
      return TOKEN_FOR;
    } else if (g_identifier_str == "in") {
      return TOKEN_IN;
    } else if (g_identifier_str == "binary") {
      return TOKEN_BINARY;
    } else if (g_identifier_str == "unary") {
      return TOKEN_UNARY;
    } else {
      return TOKEN_IDENTIFIER;
    }
  }
  // 识别数值
  if (isdigit(last_char) || last_char == '.') {
    std::string num_str;
    do {
      num_str += last_char;
      last_char = getchar();
    } while (isdigit(last_char) || last_char == '.');
    g_number_val = strtod(num_str.c_str(), nullptr);
    return TOKEN_NUMBER;
  }
  // 忽略注释
  if (last_char == '#') {
    do {
      last_char = getchar();
    } while (last_char != EOF && last_char != '\n' && last_char != '\r');
    if (last_char != EOF) {
      return GetToken();
    }
  }
  // 识别文件结束
  if (last_char == EOF) {
    return TOKEN_EOF;
  }
  // 直接返回ASCII
  int this_char = last_char;
  last_char = getchar();
  return this_char;
}


//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

// 所有 `表达式` 节点的基类
class ExprAST {
 public:
  virtual ~ExprAST() {}
  virtual llvm::Value* CodeGen() = 0;
};



// 字面值表达式
class NumberExprAST : public ExprAST {
 public:
  NumberExprAST(double val) : val_(val) {}
  llvm::Value* CodeGen() override;

 private:
  double val_;
};



// 变量表达式
class VariableExprAST : public ExprAST {
 public:
  VariableExprAST(const std::string& name) : name_(name) {}
  llvm::Value* CodeGen() override;

 private:
  std::string name_;
};



// 二元操作表达式
class BinaryExprAST : public ExprAST {
 public:
  BinaryExprAST(char op, std::unique_ptr<ExprAST> lhs,
                std::unique_ptr<ExprAST> rhs)
      : op_(op), lhs_(std::move(lhs)), rhs_(std::move(rhs)) {}
  llvm::Value* CodeGen() override;

 private:
  char op_;
  std::unique_ptr<ExprAST> lhs_;
  std::unique_ptr<ExprAST> rhs_;
};



// 函数调用表达式
class CallExprAST : public ExprAST {
 public:
  CallExprAST(const std::string& callee,
              std::vector<std::unique_ptr<ExprAST>> args)
      : callee_(callee), args_(std::move(args)) {}
  llvm::Value* CodeGen() override;

 private:
  std::string callee_;
  std::vector<std::unique_ptr<ExprAST>> args_;
};



// if then else
class IfExprAST : public ExprAST {
 public:
  IfExprAST(std::unique_ptr<ExprAST> cond, std::unique_ptr<ExprAST> then_expr,
            std::unique_ptr<ExprAST> else_expr)
      : cond_(std::move(cond)),
        then_expr_(std::move(then_expr)),
        else_expr_(std::move(else_expr)) {}

  llvm::Value* CodeGen() override;

 private:
  std::unique_ptr<ExprAST> cond_;
  std::unique_ptr<ExprAST> then_expr_;
  std::unique_ptr<ExprAST> else_expr_;
};



// for in
class ForExprAST : public ExprAST {
 public:
  ForExprAST(const std::string& var_name, std::unique_ptr<ExprAST> start_expr,
             std::unique_ptr<ExprAST> end_expr,
             std::unique_ptr<ExprAST> step_expr,
             std::unique_ptr<ExprAST> body_expr)
      : var_name_(var_name),
        start_expr_(std::move(start_expr)),
        end_expr_(std::move(end_expr)),
        step_expr_(std::move(step_expr)),
        body_expr_(std::move(body_expr)) {}

  llvm::Value* CodeGen() override;

 private:
  std::string var_name_;
  std::unique_ptr<ExprAST> start_expr_;
  std::unique_ptr<ExprAST> end_expr_;
  std::unique_ptr<ExprAST> step_expr_;
  std::unique_ptr<ExprAST> body_expr_;
};



// 函数接口
class PrototypeAST {
 public:
  PrototypeAST(const std::string& name, std::vector<std::string> args,
               bool is_operator = false, int op_precedence = 0)
      : name_(name),
        args_(std::move(args)),
        is_operator_(is_operator),
        op_precedence_(op_precedence) {}
  llvm::Function* CodeGen();

  const std::string& name() const { return name_; }
  int op_precedence() const { return op_precedence_; }
  bool IsUnaryOp() const { return is_operator_ && args_.size() == 1; }
  bool IsBinaryOp() const { return is_operator_ && args_.size() == 2; }

  // like `|` in `binary|`
  char GetOpName() { return name_[name_.size() - 1]; }

 private:
  std::string name_;
  std::vector<std::string> args_;
  bool is_operator_;
  int op_precedence_;
};



// 函数自身
class FunctionAST {
 public:
  FunctionAST(std::unique_ptr<PrototypeAST> proto,
              std::unique_ptr<ExprAST> body)
      : proto_(std::move(proto)), body_(std::move(body)) {}
  llvm::Value* CodeGen();

 private:
  std::unique_ptr<PrototypeAST> proto_;
  std::unique_ptr<ExprAST> body_;
};

int g_current_token;  // 当前待处理的Token
int GetNextToken() {
  return g_current_token = GetToken();
}



// identifierexpr
//   ::= identifier
//   ::= identifier ( expression, expression, ..., expression )
std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  std::string id = g_identifier_str;
  GetNextToken();
  if (g_current_token != '(') {
    return std::make_unique<VariableExprAST>(id);
  } else {
    GetNextToken();  // eat (
    std::vector<std::unique_ptr<ExprAST>> args;
    while (g_current_token != ')') {
      args.push_back(ParseExpression());
      if (g_current_token == ')') {
        break;
      } else {
        GetNextToken();  // eat ,
      }
    }
    GetNextToken();  // eat )
    return std::make_unique<CallExprAST>(id, std::move(args));
  }
}



// numberexpr ::= number
std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto result = std::make_unique<NumberExprAST>(g_number_val);
  GetNextToken();
  return result;
}



// parenexpr ::= ( expression )
std::unique_ptr<ExprAST> ParseParenExpr() {
  GetNextToken();  // eat (
  auto expr = ParseExpression();
  GetNextToken();  // eat )
  return expr;
}



std::unique_ptr<ExprAST> ParseIfExpr() {
  GetNextToken();  // eat if
  std::unique_ptr<ExprAST> cond = ParseExpression();
  GetNextToken();  // eat then
  std::unique_ptr<ExprAST> then_expr = ParseExpression();
  GetNextToken();  // eat else
  std::unique_ptr<ExprAST> else_expr = ParseExpression();
  return std::make_unique<IfExprAST>(std::move(cond), std::move(then_expr),
                                     std::move(else_expr));
}



// forexpr ::= for var_name = start_expr, end_expr, step_expr in body_expr
std::unique_ptr<ExprAST> ParseForExpr() {
  GetNextToken();  // eat for
  std::string var_name = g_identifier_str;
  GetNextToken();  // eat var_name
  GetNextToken();  // eat =
  std::unique_ptr<ExprAST> start_expr = ParseExpression();
  GetNextToken();  // eat ,
  std::unique_ptr<ExprAST> end_expr = ParseExpression();
  GetNextToken();  // eat ,
  std::unique_ptr<ExprAST> step_expr = ParseExpression();
  GetNextToken();  // eat in
  std::unique_ptr<ExprAST> body_expr = ParseExpression();
  return std::make_unique<ForExprAST>(var_name, std::move(start_expr),
                                      std::move(end_expr), std::move(step_expr),
                                      std::move(body_expr));
}



// primary
//   ::= identifierexpr
//   ::= numberexpr
//   ::= parenexpr
std::unique_ptr<ExprAST> ParsePrimary() {
  switch (g_current_token) {
    case TOKEN_IDENTIFIER: return ParseIdentifierExpr();
    case TOKEN_NUMBER: return ParseNumberExpr();
    case '(': return ParseParenExpr();
    case TOKEN_IF: return ParseIfExpr();
    case TOKEN_FOR: return ParseForExpr();
    default: return nullptr;
  }
}



// 定义优先级
std::map<char, int> g_binop_precedence = {
    {'<', 10}, {'+', 20}, {'-', 20}, {'*', 40}};



// 获得当前Token的优先级
int GetTokenPrecedence() {
  auto it = g_binop_precedence.find(g_current_token);
  if (it != g_binop_precedence.end()) {
    return it->second;
  } else {
    return -1;
  }
}



// parse
//   lhs [binop primary] [binop primary] ...
// 如遇到优先级小于min_precedence的操作符，则停止
std::unique_ptr<ExprAST> ParseBinOpRhs(int min_precedence,
                                       std::unique_ptr<ExprAST> lhs) {
  while (true) {
    int current_precedence = GetTokenPrecedence();
    if (current_precedence < min_precedence) {
      // 如果当前token不是二元操作符，current_precedence为-1, 结束任务
      // 如果遇到优先级更低的操作符，也结束任务
      return lhs;
    }
    int binop = g_current_token;
    GetNextToken();  // eat binop
    auto rhs = ParsePrimary();
    // 现在我们有两种可能的解析方式
    //    * (lhs binop rhs) binop unparsed
    //    * lhs binop (rhs binop unparsed)
    int next_precedence = GetTokenPrecedence();
    if (current_precedence < next_precedence) {
      // 将高于current_precedence的右边的操作符处理掉返回
      rhs = ParseBinOpRhs(current_precedence + 1, std::move(rhs));
    }
    lhs =
        std::make_unique<BinaryExprAST>(binop, std::move(lhs), std::move(rhs));
    // 继续循环
  }
}



std::unique_ptr<ExprAST> ParseExpression();



// expression
//   ::= primary [binop primary] [binop primary] ...
std::unique_ptr<ExprAST> ParseExpression() {
  auto lhs = ParsePrimary();
  return ParseBinOpRhs(0, std::move(lhs));
}



// prototype
//   ::= id ( id id ... id)
//   ::= binary binop precedence (id id)
std::unique_ptr<PrototypeAST> ParsePrototype() {
  std::string function_name;
  bool is_operator = false;
  int precedence = 0;
  switch (g_current_token) {
    case TOKEN_IDENTIFIER: {
      function_name = g_identifier_str;
      is_operator = false;
      GetNextToken();  // eat id
      break;
    }
    case TOKEN_BINARY: {
      GetNextToken();  // eat binary
      function_name = "binary";
      function_name += (char)(g_current_token);
      is_operator = true;
      GetNextToken();  // eat binop
      precedence = g_number_val;
      GetNextToken();  // eat precedence
      break;
    }
  }
  std::vector<std::string> arg_names;
  while (GetNextToken() == TOKEN_IDENTIFIER) {
    arg_names.push_back(g_identifier_str);
  }
  GetNextToken();  // eat )
  return std::make_unique<PrototypeAST>(function_name, arg_names, is_operator,
                                        precedence);
}



void ReCreateModule() {
  g_module = std::make_unique<llvm::Module>("my cool jit", g_llvm_context);
  g_module->setDataLayout(g_jit->getTargetMachine().createDataLayout());
  g_fpm = std::make_unique<llvm::legacy::FunctionPassManager>(g_module.get());
  g_fpm->add(llvm::createInstructionCombiningPass());
  g_fpm->add(llvm::createReassociatePass());
  g_fpm->add(llvm::createGVNPass());
  g_fpm->add(llvm::createCFGSimplificationPass());
  g_fpm->add(llvm::createPromoteMemoryToRegisterPass());
  g_fpm->add(llvm::createInstructionCombiningPass());
  g_fpm->add(llvm::createReassociatePass());
  g_fpm->doInitialization();
}



void ParseDefinitionToken() {
  auto ast = ParseDefinition();
  std::cout << "parsed a function definition" << std::endl;
  ast->CodeGen()->print(llvm::errs());
  std::cerr << std::endl;
  g_jit->addModule(std::move(g_module));
  ReCreateModule();
}



void ParseExternToken() {
  auto ast = ParseExtern();
  std::cout << "parsed a extern" << std::endl;
  ast->CodeGen()->print(llvm::errs());
  std::cerr << std::endl;
  name2proto_ast[ast->name()] = std::move(ast);
}



void ParseTopLevel() {
  auto ast = ParseTopLevelExpr();
  std::cout << "parsed a top level expr" << std::endl;
  ast->CodeGen()->print(llvm::errs());
  std::cout << std::endl;
  auto h = g_jit->addModule(std::move(g_module));
  // 重新创建g_module在下次使用
  ReCreateModule();
  // 通过名字找到编译的函数符号
  auto symbol = g_jit->findSymbol("__anon_expr");
  // 强转为C函数指针
  double (*fp)() = (double (*)())(symbol.getAddress().get());
  // 执行输出
  std::cout << fp() << std::endl;
  g_jit->removeModule(h);
}


//===----------------------------------------------------------------------===//
// "Library" functions that can be "extern'd" from user code.
//===----------------------------------------------------------------------===//

/// putchard - putchar that takes a double and returns 0.
extern "C" double putchard(double x) {
  fputc((char)x, stdout);
  return 0.0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" double printd(double x) {
  printf("%lf\n", x);
  return 0.0;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//


int main() {
  llvm::InitializeNativeTarget();
  llvm::InitializeNativeTargetAsmPrinter();
  llvm::InitializeNativeTargetAsmParser();
  g_jit.reset(new llvm::orc::KaleidoscopeJIT);
  ReCreateModule();
  g_module->setDataLayout(g_jit->getTargetMachine().createDataLayout());

  GetNextToken();
  while (true) {
    switch (g_current_token) {
      case TOKEN_EOF: return 0;
      case TOKEN_DEF: ParseDefinitionToken(); break;
      case TOKEN_EXTERN: ParseExternToken(); break;
      default: ParseTopLevel(); break;
    }
  }
  return 0;
}
