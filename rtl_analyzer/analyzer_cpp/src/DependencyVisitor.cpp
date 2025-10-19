#include "DependencyVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/text/SourceManager.h"
#include <sstream>
#include <iostream>
// 新增辅助函数：检查是否是自增操作
bool isIncrementOperation(const slang::ast::Expression& expr, const slang::ast::Symbol& lhsSymbol) {
    // 检查是否是二元加法表达式
    if (const auto* binaryExpr = expr.as_if<slang::ast::BinaryExpression>()) {
        if (binaryExpr->op == slang::ast::BinaryOperator::Add) {
            std::cout << "DEBUG: Found binary add operation" << std::endl;
            
            // 检查左操作数是否是同一个信号
            if (const auto* leftValue = binaryExpr->left().as_if<slang::ast::NamedValueExpression>()) {
                std::cout << "DEBUG: Left operand: " << leftValue->symbol.name 
                          << ", LHS symbol: " << lhsSymbol.name << std::endl;
                          
                if (&leftValue->symbol == &lhsSymbol) {
                    std::cout << "DEBUG: Left operand matches LHS" << std::endl;
                    
                    // 检查右操作数是否是常量
                    if (binaryExpr->right().as_if<slang::ast::IntegerLiteral>()) {
                        std::cout << "DEBUG: Right operand is integer literal - INCREMENT DETECTED" << std::endl;
                        return true;
                    } else {
                        std::cout << "DEBUG: Right operand is not integer literal" << std::endl;
                        // 修复：使用正确的类型检查方法
                        std::cout << "DEBUG: Right operand kind: " << static_cast<int>(binaryExpr->right().kind) << std::endl;
                    }
                }
            }
        }
    }
    return false;
}

// 新增辅助函数：检查是否是自引用
bool isSelfReference(const slang::ast::Expression& expr, const slang::ast::Symbol& symbol) {
    if (const auto* namedValue = expr.as_if<slang::ast::NamedValueExpression>()) {
        return &namedValue->symbol == &symbol;
    }
    return false;
}

// 新增辅助函数：检查是否是常量
bool isConstant(const slang::ast::Expression& expr) {
    return expr.as_if<slang::ast::IntegerLiteral>() != nullptr;
}

// 辅助函数实现
bool isEnumConstant(const slang::ast::Symbol& symbol) {
    // 只过滤真正的枚举常量（EnumValue），保留枚举变量
    return symbol.kind == slang::ast::SymbolKind::EnumValue;
}

// 辅助函数：将端口方向枚举转换为字符串
static std::string directionToString(slang::ast::ArgumentDirection dir) {
    switch (dir) {
        case slang::ast::ArgumentDirection::In: return "input";
        case slang::ast::ArgumentDirection::Out: return "output";
        case slang::ast::ArgumentDirection::InOut: return "inout";
        default: return "unknown";
    }
}

// 修复的 DataSignalVisitor - 过滤枚举常量
class DataSignalVisitor : public slang::ast::ASTVisitor<DataSignalVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }

    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            // 过滤掉枚举常量
            if (!isEnumConstant(*symbol)) {
                std::string signalName = symbol->getHierarchicalPath();
                signals.insert(signalName);
            }
        }
    }

    std::set<std::string> signals;
};

// 修复的 ConditionClauseVisitor - 过滤枚举常量
class ConditionClauseVisitor : public slang::ast::ASTVisitor<ConditionClauseVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { 
        visitDefault(node); 
    }

    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            // 过滤枚举常量，但保留在表达式中
            std::string signalName = symbol->getHierarchicalPath();
            
            if (!isEnumConstant(*symbol)) {
                // 只有非枚举常量才添加到 involvedSignals
                involvedSignals.insert(signalName);
            }
            
            // 但表达式文本中仍然包含完整名称
            if (!currentExpression.empty()) {
                currentExpression += " ";
            }
            currentExpression += signalName;
        }
    }

    void handle(const slang::ast::BinaryExpression& expr) {
        // 处理二元操作符
        expr.left().visit(*this);
        
        // 添加操作符
        std::string opStr;
        switch (expr.op) {
            case slang::ast::BinaryOperator::Equality: opStr = " == "; break;
            case slang::ast::BinaryOperator::Inequality: opStr = " != "; break;
            case slang::ast::BinaryOperator::LogicalAnd: opStr = " && "; break;
            case slang::ast::BinaryOperator::LogicalOr: opStr = " || "; break;
            case slang::ast::BinaryOperator::GreaterThanEqual: opStr = " >= "; break;
            case slang::ast::BinaryOperator::GreaterThan: opStr = " > "; break;
            case slang::ast::BinaryOperator::LessThanEqual: opStr = " <= "; break;
            case slang::ast::BinaryOperator::LessThan: opStr = " < "; break;
            default: opStr = " op "; break;
        }
        currentExpression += opStr;
        
        expr.right().visit(*this);
    }

    void handle(const slang::ast::UnaryExpression& expr) {
        // 处理一元操作符
        std::string opStr;
        switch (expr.op) {
            case slang::ast::UnaryOperator::LogicalNot: opStr = "!"; break;
            case slang::ast::UnaryOperator::BitwiseAnd: opStr = "&"; break;  // 归约与
            case slang::ast::UnaryOperator::BitwiseOr: opStr = "|"; break;   // 归约或
            case slang::ast::UnaryOperator::BitwiseXor: opStr = "^"; break;  // 归约异或
            default: opStr = "unary_op "; break;
        }
        currentExpression += opStr;
        
        expr.operand().visit(*this);
    }

    void handle(const slang::ast::IntegerLiteral& literal) {
        // 添加常量值
        if (!currentExpression.empty()) {
            currentExpression += " ";
        }
        currentExpression += literal.getValue().toString();
    }

    void handle(const slang::ast::ElementSelectExpression& expr) {
        // 处理位选择，如 config_bits[3]
        expr.value().visit(*this);
        currentExpression += "[";
        expr.selector().visit(*this);
        currentExpression += "]";
    }

    void handle(const slang::ast::RangeSelectExpression& expr) {
        // 处理范围选择，如 config_bits[3:2]
        expr.value().visit(*this);
        currentExpression += "[";
        expr.left().visit(*this);
        currentExpression += ":";
        expr.right().visit(*this);
        currentExpression += "]";
    }

    std::string getExpressionString() const {
        return currentExpression;
    }

    std::set<std::string> getInvolvedSignals() const {
        return involvedSignals;
    }

    void reset() {
        currentExpression.clear();
        involvedSignals.clear();
    }

private:
    std::string currentExpression;
    std::set<std::string> involvedSignals;
};

// 修复的 CaseItemExpressionVisitor - 过滤枚举常量
class CaseItemExpressionVisitor : public slang::ast::ASTVisitor<CaseItemExpressionVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { 
        visitDefault(node); 
    }

    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            // 过滤枚举常量
            if (!isEnumConstant(*symbol)) {
                std::string signalName = symbol->getHierarchicalPath();
                if (!currentExpression.empty()) {
                    currentExpression += " ";
                }
                currentExpression += signalName;
            } else {
                // 对于枚举常量，仍然在表达式中显示，但不作为信号
                std::string enumName = symbol->getHierarchicalPath();
                if (!currentExpression.empty()) {
                    currentExpression += " ";
                }
                currentExpression += enumName;
            }
        }
    }

    void handle(const slang::ast::IntegerLiteral& literal) {
        if (!currentExpression.empty()) {
            currentExpression += " ";
        }
        currentExpression += literal.getValue().toString();
    }

    void handle(const slang::ast::BinaryExpression& expr) {
        if (expr.op == slang::ast::BinaryOperator::LogicalOr) {
            expr.left().visit(*this);
            currentExpression += " || ";
            expr.right().visit(*this);
        } else {
            visitDefault(expr);
        }
    }

    void handle(const slang::ast::UnaryExpression& expr) {
        if (expr.op == slang::ast::UnaryOperator::LogicalNot) {
            currentExpression += "!";
            expr.operand().visit(*this);
        } else {
            visitDefault(expr);
        }
    }

    std::string getExpressionString() const {
        return currentExpression;
    }

    void reset() {
        currentExpression.clear();
    }

private:
    std::string currentExpression;
};

// --- 主 Visitor 的实现 ---

DependencyVisitor::DependencyVisitor() {
    pathStack.push_back({}); // 初始化路径栈，包含一个空的根路径
}

// 提取 case 项的表达式
std::string DependencyVisitor::extractCaseItemExpression(const slang::ast::Expression& caseExpr, const slang::ast::CaseStatement::ItemGroup& item) {
    CaseItemExpressionVisitor visitor;
    
    // 处理 case 项的表达式
    if (item.expressions.empty()) {
        return "default"; // default case
    }
    
    // 处理单个或多个表达式（用 || 连接）
    for (size_t i = 0; i < item.expressions.size(); ++i) {
        if (i > 0) {
            visitor.reset();
        }
        item.expressions[i]->visit(visitor);
        if (i > 0) {
            // 对于多个表达式，需要构建 OR 条件
            // 这里简化处理，只取第一个表达式
            break;
        }
    }
    
    return visitor.getExpressionString();
}

// 构建 case 语句的所有条件路径
std::vector<ConditionPath> DependencyVisitor::buildCasePaths(const slang::ast::CaseStatement& stmt, const ConditionPath& parentPath) {
    std::vector<ConditionPath> casePaths;
    
    // 处理 case 表达式
    ConditionClauseVisitor caseExprVisitor;
    stmt.expr.visit(caseExprVisitor);
    
    ConditionExpression caseExpr;
    caseExpr.expression = caseExprVisitor.getExpressionString();
    caseExpr.involvedSignals = caseExprVisitor.getInvolvedSignals();
    
    bool hasDefault = false;
    
    // 为每个 case 项创建条件路径
    for (const auto& item : stmt.items) {
        std::string itemExpression = extractCaseItemExpression(stmt.expr, item);
        
        if (itemExpression == "default") {
            hasDefault = true;
            continue; // default 单独处理
        }
        
        // 创建 case 项的条件：case_expr == case_item_value
        ConditionExpression fullCondition;
        fullCondition.expression = caseExpr.expression + " == " + itemExpression;
        fullCondition.involvedSignals = caseExpr.involvedSignals;
        
        ConditionClause conditionClause;
        conditionClause.expr = fullCondition;
        conditionClause.polarity = true;
        
        ConditionPath itemPath = parentPath;
        itemPath.insert(conditionClause);
        casePaths.push_back(itemPath);
    }
    
    // 处理 default case
    if (hasDefault || stmt.defaultCase) {
        // default case 的条件是前面所有 case 项条件的否定
        ConditionPath defaultPath = parentPath;
        
        for (const auto& item : stmt.items) {
            std::string itemExpression = extractCaseItemExpression(stmt.expr, item);
            if (itemExpression == "default") continue;
            
            ConditionExpression fullCondition;
            fullCondition.expression = caseExpr.expression + " == " + itemExpression;
            fullCondition.involvedSignals = caseExpr.involvedSignals;
            
            ConditionClause conditionClause;
            conditionClause.expr = fullCondition;
            conditionClause.polarity = false; // 否定条件
            
            defaultPath.insert(conditionClause);
        }
        
        casePaths.push_back(defaultPath);
    }
    
    return casePaths;
}

void DependencyVisitor::handle(const slang::ast::CaseStatement& stmt) {
    ConditionPath parentPath = pathStack.back();
    
    // 构建所有 case 路径
    std::vector<ConditionPath> casePaths = buildCasePaths(stmt, parentPath);
    
    // 处理各个 case 项
    size_t pathIndex = 0;
    for (const auto& item : stmt.items) {
        if (pathIndex < casePaths.size()) {
            pathStack.push_back(casePaths[pathIndex]);
            if (item.stmt) {
                item.stmt->visit(*this);
            }
            pathStack.pop_back();
            pathIndex++;
        }
    }
    
    // 处理 default case（如果有）
    if (stmt.defaultCase && pathIndex < casePaths.size()) {
        pathStack.push_back(casePaths[pathIndex]);
        stmt.defaultCase->visit(*this);
        pathStack.pop_back();
    }
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
        
    // 检查是否是自增操作
    bool isIncrement = isIncrementOperation(expr.right(), *lhsSymbol);

    DataSignalVisitor rhsVisitor;
    if (!isIncrement) {
        // 如果不是自增操作，正常分析右侧表达式
        expr.right().visit(rhsVisitor);
    }
    // 如果是自增操作，rhsVisitor.signals 保持为空

    AssignmentInfo assignInfo;
    assignInfo.path = pathStack.back();
    assignInfo.drivingSignals = rhsVisitor.signals;
    assignInfo.type = isIncrement ? "increment" : "direct";

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
        
        // 使用修复后的 ConditionClauseVisitor，它会过滤枚举常量
        ConditionClauseVisitor clauseVisitor;
        cond.expr->visit(clauseVisitor);

        // 创建完整的条件表达式
        ConditionExpression condExpr;
        condExpr.expression = clauseVisitor.getExpressionString();
        condExpr.involvedSignals = clauseVisitor.getInvolvedSignals();

        ConditionClause trueClause;
        trueClause.expr = condExpr;
        trueClause.polarity = true;

        ConditionPath truePath = parentPath;
        truePath.insert(trueClause);
        pathStack.push_back(truePath);
        
        stmt.ifTrue.visit(*this);
        pathStack.pop_back();

        // 为 else 路径创建否定条件
        ConditionClause falseClause;
        falseClause.expr = condExpr;
        falseClause.polarity = false;
        parentPath.insert(falseClause);
    }

    // 处理 else 分支
    if (stmt.ifFalse) {
        pathStack.push_back(parentPath);
        stmt.ifFalse->visit(*this);
        pathStack.pop_back();
    }
}

void DependencyVisitor::handle(const slang::ast::InstanceSymbol& symbol) {
    // 获取实例化的位置信息
    std::string instanceFile;
    int instanceLine = 0;
    
    const slang::ast::Scope* scope = symbol.getParentScope();
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
        
        // 使用修复后的 DataSignalVisitor，它会过滤枚举常量
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
                    assignInfo.drivingSignals = std::set<std::string>{externalSignalName};
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
            // 跳过完全空的赋值
            if (assignment.drivingSignals.empty() && 
                assignment.file.empty() && 
                assignment.line == 0) {
                continue;
            }
            
            AssignmentInfo newAssignment = assignment;
            
            // 改进的常量检测：
            if (assignment.drivingSignals.empty() && 
                !assignment.file.empty() && 
                assignment.line > 0 &&
                assignment.type == "direct") {
                
                if (assignment.path.empty()) {
                    // 无条件常量赋值
                    newAssignment.type = "constant";
                } else {
                    // 条件常量赋值 - 有控制依赖！
                    newAssignment.type = "conditional_constant";
                }
            }
            
            cleanedAssignments.insert(newAssignment);
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