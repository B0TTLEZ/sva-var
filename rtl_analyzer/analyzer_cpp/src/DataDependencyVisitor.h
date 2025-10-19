#pragma once
#include <string>
#include <vector>
#include <set>
#include <map>

#include "DataModel.h" 

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/text/SourceLocation.h"



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