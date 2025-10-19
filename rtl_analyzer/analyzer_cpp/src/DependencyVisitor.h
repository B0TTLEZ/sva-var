#pragma once
#include "DataModel.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/statements/ConditionalStatements.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"

using AnalysisResultMap = std::map<std::string, VariableInfo>;

class DependencyVisitor : public slang::ast::ASTVisitor<DependencyVisitor, true, true> {
public:
    DependencyVisitor();

    // 简化模板处理 - 使用您工作代码中的模式
    template<typename T>
    void handle(const T& node) {
        visitDefault(node);
    }
    
    // 显式声明需要处理的节点类型
    void handle(const slang::ast::VariableSymbol& symbol);
    void handle(const slang::ast::PortSymbol& symbol);
    void handle(const slang::ast::AssignmentExpression& expr);
    void handle(const slang::ast::ConditionalStatement& stmt);
    void handle(const slang::ast::CaseStatement& stmt);
    void handle(const slang::ast::InstanceSymbol& symbol);

    void postProcess();

    const AnalysisResultMap& getResults() const { return results; }

private:
    VariableInfo& getOrAddVariable(const slang::ast::Symbol& symbol);
    std::vector<ConditionPath> pathStack;
    AnalysisResultMap results;
};