#pragma once
#include <string>
#include <vector>
#include <set>
#include <map>
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/text/SourceLocation.h"

struct VariableInfo {
    std::string fullName;
    std::string type;
    std::string fileName;
    int line = 0;
    std::string direction;
    size_t bitWidth = 0;
    
    // --- 新增字段 ---
    std::set<std::string> fanInControl; // 存储控制依赖信号

    std::set<std::string> fanInData;
    std::set<std::string> fanOut;
};

class DataDependencyVisitor : public slang::ast::ASTVisitor<DataDependencyVisitor, true, true> {
public:
    DataDependencyVisitor() = default;

    template<typename T>
    void handle(const T& node) {
        visitDefault(node);
    }

    void handle(const slang::ast::VariableSymbol& symbol);
    void handle(const slang::ast::PortSymbol& symbol);
    void handle(const slang::ast::AssignmentExpression& expr);
    void handle(const slang::ast::InstanceSymbol& symbol);

    const std::map<std::string, VariableInfo>& getResults() const {
        return variables;
    }
    std::map<std::string, VariableInfo>& getMutableResults() {
        return variables;
    }

private:
    VariableInfo& getOrAddVariable(const slang::ast::Symbol& symbol);
    std::map<std::string, VariableInfo> variables;
};