#include "ControlFlowVisitor.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/VariableSymbols.h"

// 辅助 Visitor 1: 收集表达式中的所有控制信号
class ControlSignalVisitor : public slang::ast::ASTVisitor<ControlSignalVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }
    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            controlSignals.insert(symbol->getHierarchicalPath());
        }
    }
    std::set<std::string> controlSignals;
};

// 辅助 Visitor 2: 收集语句块中所有被赋值的信号 (被控信号)
class ControlledSignalVisitor : public slang::ast::ASTVisitor<ControlledSignalVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }
    void handle(const slang::ast::AssignmentExpression& expr) {
        const slang::ast::Symbol* lhsSymbol = expr.left().getSymbolReference();
        if (lhsSymbol) {
            controlledSignals.insert(lhsSymbol->getHierarchicalPath());
        }
        visitDefault(expr);
    }
    std::set<std::string> controlledSignals;
};

// --- 主 Visitor 的实现 ---

void ControlFlowVisitor::handle(const slang::ast::ConditionalStatement& stmt) {
    ControlSignalVisitor conditionVisitor;
    for (const auto& cond : stmt.conditions) {
        cond.expr->visit(conditionVisitor);
    }

    ControlledSignalVisitor ifTrueVisitor;
    stmt.ifTrue.visit(ifTrueVisitor);

    for (const auto& controlledSig : ifTrueVisitor.controlledSignals) {
        controlMap[controlledSig].insert(conditionVisitor.controlSignals.begin(), 
                                           conditionVisitor.controlSignals.end());
    }

    if (stmt.ifFalse) {
        stmt.ifFalse->visit(*this);
    }
}

void ControlFlowVisitor::handle(const slang::ast::CaseStatement& stmt) {
    ControlSignalVisitor conditionVisitor;
    stmt.expr.visit(conditionVisitor);
    const auto& controlSignals = conditionVisitor.controlSignals;

    for (const auto& item : stmt.items) {
        ControlledSignalVisitor itemVisitor;
        item.stmt->visit(itemVisitor);

        for (const auto& controlledSig : itemVisitor.controlledSignals) {
            controlMap[controlledSig].insert(controlSignals.begin(), controlSignals.end());
        }
    }

    if (stmt.defaultCase) {
        stmt.defaultCase->visit(*this);
    }
}