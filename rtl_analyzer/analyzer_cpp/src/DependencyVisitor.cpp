#include "DependencyVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/text/SourceManager.h"

// 辅助函数：将端口方向枚举转换为字符串
static std::string directionToString(slang::ast::ArgumentDirection dir) {
    switch (dir) {
        case slang::ast::ArgumentDirection::In: return "input";
        case slang::ast::ArgumentDirection::Out: return "output";
        case slang::ast::ArgumentDirection::InOut: return "inout";
        default: return "unknown";
    }
}

// 辅助 Visitor 1: 提取条件表达式中的信号和极性
class ConditionClauseVisitor : public slang::ast::ASTVisitor<ConditionClauseVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }

    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            std::string signalName = symbol->getHierarchicalPath();
            clauses.insert({signalName, true});
        }
    }

    void handle(const slang::ast::UnaryExpression& expr) {
        if (expr.op == slang::ast::UnaryOperator::LogicalNot) {
            ConditionClauseVisitor subVisitor;
            expr.operand().visit(subVisitor);
            for (auto& clause : subVisitor.clauses) {
                clauses.insert({clause.signal, !clause.polarity});
            }
        } else {
            visitDefault(expr);
        }
    }

    std::set<ConditionClause> clauses;
};

// 辅助 Visitor 2: 仅提取数据依赖信号的名称
class DataSignalVisitor : public slang::ast::ASTVisitor<DataSignalVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }

    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            std::string signalName = symbol->getHierarchicalPath();
            signals.insert(signalName);
        }
    }

    std::set<std::string> signals;
};

// --- 主 Visitor 的实现 ---

DependencyVisitor::DependencyVisitor() {
    pathStack.push_back({}); // 初始化路径栈，包含一个空的根路径
}

VariableInfo& DependencyVisitor::getOrAddVariable(const slang::ast::Symbol& symbol) {  
    std::string path = symbol.getHierarchicalPath();  
    if (results.find(path) == results.end()) {  
        VariableInfo info;  
        info.fullName = path;  
  
        // 对于端口
        if (const auto* portSymbol = symbol.as_if<slang::ast::PortSymbol>()) {  
            info.direction = directionToString(portSymbol->direction);  
              
            // 获取端口的内部符号  
            if (portSymbol->internalSymbol) {  
                const auto* internalValue = portSymbol->internalSymbol->as_if<slang::ast::ValueSymbol>();  
                if (internalValue) {  
                    const slang::ast::Type& type = internalValue->getType();  
                    info.type = type.toString();  
                    info.bitWidth = type.getBitWidth();  
                }  
            }  
        }  
        // 对于普通变量  
        else if (const auto* valueSymbol = symbol.as_if<slang::ast::ValueSymbol>()) {  
            const slang::ast::Type& type = valueSymbol->getType();  
            info.type = type.toString();  
            info.bitWidth = type.getBitWidth();  
        }  
  
        // 提取位置信息  
        const slang::ast::Scope* scope = symbol.getParentScope();  
        if (scope) {  
            auto& comp = scope->getCompilation();  
            auto* sm = comp.getSourceManager();  
            if (sm && symbol.location) {  
                info.fileName = std::string(sm->getFileName(symbol.location));  
                info.line = sm->getLineNumber(symbol.location);  
            }  
        }  
        results[path] = info;  
    }  
    return results.at(path);  
}

void DependencyVisitor::handle(const slang::ast::VariableSymbol& symbol) {
    getOrAddVariable(symbol);
    visitDefault(symbol);
}

void DependencyVisitor::handle(const slang::ast::PortSymbol& symbol) {
    getOrAddVariable(symbol);
    visitDefault(symbol);
}

void DependencyVisitor::handle(const slang::ast::AssignmentExpression& expr) {
    const slang::ast::Symbol* lhsSymbol = expr.left().getSymbolReference();
    if (!lhsSymbol) {
        visitDefault(expr);
        return;
    }
    
    VariableInfo& lhsInfo = getOrAddVariable(*lhsSymbol);
        
    DataSignalVisitor rhsVisitor;
    expr.right().visit(rhsVisitor);

    AssignmentInfo assignInfo;
    assignInfo.path = pathStack.back();
    assignInfo.drivingSignals = rhsVisitor.signals;
    assignInfo.type = "direct"; // 直接赋值

    const slang::ast::Scope* scope = lhsSymbol->getParentScope();
    if (scope) {
        auto& comp = scope->getCompilation();
        auto* sm = comp.getSourceManager();
        if (sm && expr.sourceRange.start()) {
            assignInfo.file = std::string(sm->getFileName(expr.sourceRange.start()));
            assignInfo.line = sm->getLineNumber(expr.sourceRange.start());
        }
    }
    lhsInfo.assignments.insert(assignInfo);
    
    visitDefault(expr);
}

void DependencyVisitor::handle(const slang::ast::ConditionalStatement& stmt) {
    ConditionPath parentPath = pathStack.back();
    
    // 处理每个条件分支
    for (size_t i = 0; i < stmt.conditions.size(); ++i) {
        const auto& cond = stmt.conditions[i];
        
        ConditionClauseVisitor clauseVisitor;
        cond.expr->visit(clauseVisitor);

        ConditionPath truePath = parentPath;
        truePath.insert(clauseVisitor.clauses.begin(), clauseVisitor.clauses.end());
        pathStack.push_back(truePath);
        
        // 直接访问 ifTrue 语句（不是指针）
        stmt.ifTrue.visit(*this);

        pathStack.pop_back();

        // 为下一个条件添加当前条件的否定
        for (const auto& clause : clauseVisitor.clauses) {
            parentPath.insert({clause.signal, !clause.polarity});
        }
    }

    // 处理 else 分支
    if (stmt.ifFalse) {
        pathStack.push_back(parentPath);
        stmt.ifFalse->visit(*this);  // ifFalse 是指针，需要解引用
        pathStack.pop_back();
    }
}

void DependencyVisitor::handle(const slang::ast::CaseStatement& stmt) {
    ConditionClauseVisitor clauseVisitor;
    stmt.expr.visit(clauseVisitor);
    
    ConditionPath parentPath = pathStack.back();
    ConditionPath casePath = parentPath;
    casePath.insert(clauseVisitor.clauses.begin(), clauseVisitor.clauses.end());
    
    pathStack.push_back(casePath);

    for (const auto& item : stmt.items) {
        if (item.stmt)
            item.stmt->visit(*this);
    }
    
    if (stmt.defaultCase) {
        stmt.defaultCase->visit(*this);
    }

    pathStack.pop_back();
}

void DependencyVisitor::handle(const slang::ast::InstanceSymbol& symbol) {
    // 获取实例化的位置信息
    const slang::ast::Scope* scope = symbol.getParentScope();
    std::string instanceFile;
    int instanceLine = 0;
    if (scope) {
        auto& comp = scope->getCompilation();
        auto* sm = comp.getSourceManager();
        if (sm && symbol.location) {
            instanceFile = std::string(sm->getFileName(symbol.location));
            instanceLine = sm->getLineNumber(symbol.location);
        }
    }

    // 遍历端口连接
    for (auto* portConnection : symbol.getPortConnections()) {
        const slang::ast::Symbol& internalPort = portConnection->port;
        const slang::ast::Expression* externalExpr = portConnection->getExpression();
        
        // 确保端口被注册
        VariableInfo& internalPortInfo = getOrAddVariable(internalPort);
        
        if (!externalExpr) continue;
        
        // 分析外部表达式中的信号
        DataSignalVisitor externalSignalVisitor;
        externalExpr->visit(externalSignalVisitor);

        // 建立端口连接的依赖关系
        for (const auto& externalSignalName : externalSignalVisitor.signals) {
            if (results.count(externalSignalName)) {
                VariableInfo& externalInfo = results[externalSignalName];
                
                // 根据端口方向建立依赖关系
                auto direction = internalPort.as<slang::ast::PortSymbol>().direction;
                
                if (direction != slang::ast::ArgumentDirection::In) { 
                    // 输出或输入输出端口：外部信号 <- 内部端口
                    AssignmentInfo assignInfo;
                    assignInfo.path = pathStack.back();
                    assignInfo.drivingSignals = {internalPortInfo.fullName};
                    assignInfo.file = instanceFile;
                    assignInfo.line = instanceLine;
                    assignInfo.type = "port_connection";
                    externalInfo.assignments.insert(assignInfo);
                    
                    internalPortInfo.fanOut.insert(externalInfo.fullName);
                }
                if (direction != slang::ast::ArgumentDirection::Out) { 
                    // 输入或输入输出端口：内部端口 <- 外部信号  
                    AssignmentInfo assignInfo;
                    assignInfo.path = pathStack.back();
                    assignInfo.drivingSignals = {externalSignalName};
                    assignInfo.file = instanceFile;
                    assignInfo.line = instanceLine;
                    assignInfo.type = "port_connection";
                    internalPortInfo.assignments.insert(assignInfo);
                    
                    externalInfo.fanOut.insert(internalPortInfo.fullName);
                }
            }
        }
    }

    visitDefault(symbol);
}

void DependencyVisitor::postProcess() {
    // 清理空的赋值并识别常量赋值
    for (auto& [varName, info] : results) {
        std::set<AssignmentInfo> cleanedAssignments;
        
        for (const auto& assignment : info.assignments) {
            // 如果 drivingSignals 为空，标记为常量赋值
            if (assignment.drivingSignals.empty() && assignment.type == "direct") {
                AssignmentInfo constAssignment = assignment;
                constAssignment.type = "constant";
                cleanedAssignments.insert(constAssignment);
            } else {
                cleanedAssignments.insert(assignment);
            }
        }
        
        info.assignments = cleanedAssignments;
    }

    // 构建 fanOut 关系
    for (auto& [lhsName, info] : results) {
        for (const auto& assignment : info.assignments) {
            for (const auto& rhsName : assignment.drivingSignals) {
                if (results.count(rhsName)) {
                    results[rhsName].fanOut.insert(lhsName);
                }
            }
        }
    }
}