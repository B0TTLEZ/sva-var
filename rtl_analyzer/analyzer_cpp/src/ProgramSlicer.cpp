#include "ProgramSlicer.h"  
#include "json.hpp"  
#include <fstream>  
#include <iostream>  
#include <sstream>  
#include "slang/text/SourceManager.h"

using json = nlohmann::json;  
  
ProgramSlicer::ProgramSlicer(const AnalysisResultMap& analysisResults)  
    : results(analysisResults) {}  
  
SliceResult ProgramSlicer::backwardSlice(const SlicingCriterion& criterion,  
                                         const SliceConfig& config) {  
    SliceResult result;  
    std::queue<std::string> worklist;  
    std::set<std::string> visited;  
      
    worklist.push(criterion.variableName);  
    visited.insert(criterion.variableName);  
      
    std::cout << "[INFO] Starting backward slice from: " << criterion.variableName << std::endl;  

    // 【修正 1: 显式初始化目标变量的记录】
    // 确保目标变量的键存在，防止报告函数查找失败。
    result.dependencyMap[criterion.variableName]; 
      
    while (!worklist.empty()) {  
        std::string currentVar = worklist.front();  
        worklist.pop();  
          
        auto it = results.find(currentVar);  
        if (it == results.end()) {  
            std::cout << "[WARNING] Variable not found: " << currentVar << std::endl;  
            continue;  
        }  
          
        const VariableInfo& varInfo = it->second;  
        result.relevantVariables.insert(currentVar);  
          
        for (const auto& assignment : varInfo.assignments) {  
            if (!matchesCriterion(currentVar, assignment, criterion)) {  
                continue;  
            }  
              
            result.relevantAssignments[currentVar].insert(assignment);  
            
            // 【修正 2: 添加赋值来源记录】
            std::string assignmentKey = assignment.file + ":" + std::to_string(assignment.line);
            result.dependencyMap[currentVar].fanInAssignments.insert(assignmentKey);
              
            // 添加数据依赖  
            for (const auto& drivingSignal : assignment.drivingSignals) {  
                if (visited.find(drivingSignal) == visited.end()) {  
                    worklist.push(drivingSignal);  
                    visited.insert(drivingSignal);  
                }
                // 【修正 3: 记录数据依赖】
                result.dependencyMap[currentVar].dataDependencies.insert(drivingSignal);
            }  
              
            // 添加控制依赖  
            for (const auto& clause : assignment.path) {  
                for (const auto& signal : clause.expr.involvedSignals) {  
                    if (visited.find(signal) == visited.end()) {  
                        worklist.push(signal);  
                        visited.insert(signal);  
                        result.controlVariables.insert(signal);  
                    }
                    // 【修正 4: 记录控制依赖】
                    result.dependencyMap[currentVar].controlDependencies.insert(signal);
                }  
            }  
        }  
    }  
      
    std::cout << "[INFO] Backward slice complete. Found " << result.relevantVariables.size()  
              << " relevant variables" << std::endl;  
      
    return result;  
} 
SliceResult ProgramSlicer::forwardSlice(const SlicingCriterion& criterion,  
                                        const SliceConfig& config) {  
    SliceResult result;  
    std::queue<std::string> worklist;  
    std::set<std::string> visited;  
      
    worklist.push(criterion.variableName);  
    visited.insert(criterion.variableName);  
      
    std::cout << "[INFO] Starting forward slice from: " << criterion.variableName << std::endl;  

    // 【修正 1: 显式初始化目标变量的记录】
    result.dependencyMap[criterion.variableName]; 
      
    while (!worklist.empty()) {  
        std::string currentVar = worklist.front();  
        worklist.pop();  
          
        auto it = results.find(currentVar);  
        if (it == results.end()) {  
            continue;  
        }  
          
        const VariableInfo& varInfo = it->second;  
        result.relevantVariables.insert(currentVar);  
          
        // 添加该变量的所有赋值  
        for (const auto& assignment : varInfo.assignments) {  
            if (matchesCriterion(currentVar, assignment, criterion)) {  
                result.relevantAssignments[currentVar].insert(assignment);  
            }
            // 【修正 2: 记录赋值来源 (Fan-In Assignments)】
            std::string assignmentKey = assignment.file + ":" + std::to_string(assignment.line);
            result.dependencyMap[currentVar].fanInAssignments.insert(assignmentKey);
        }  
          
        // 前向追踪:找出所有使用该变量的地方(数据依赖)  
        for (const auto& fanOutVar : varInfo.fanOut) {  
            if (visited.find(fanOutVar) == visited.end()) {  
                worklist.push(fanOutVar);  
                visited.insert(fanOutVar);  
            }
            // 【修正 3: 记录数据输出依赖】
            result.dependencyMap[currentVar].fanOutVariables.insert(fanOutVar);
        }  
          
        // 新增:前向追踪控制依赖  
        // 如果currentVar出现在条件表达式中,所有受该条件控制的赋值都应该包含在切片中  
        for (const auto& [otherVar, otherInfo] : results) {  
            for (const auto& assignment : otherInfo.assignments) {  
                for (const auto& clause : assignment.path) {  
                    if (clause.expr.involvedSignals.count(currentVar)) {  
                        // 这个赋值受currentVar控制,应该包含在切片中  
                        if (visited.find(otherVar) == visited.end()) {  
                            worklist.push(otherVar);  
                            visited.insert(otherVar);  
                            result.controlVariables.insert(currentVar);  // 标记为控制变量  
                        }
                        // 【修正 4: 记录控制输出依赖】
                        // currentVar 控制 otherVar 的赋值
                        result.dependencyMap[currentVar].fanOutConditions.insert(otherVar);
                    }  
                }  
            }  
        }  
    }  
      
    std::cout << "[INFO] Forward slice complete. Found " << result.relevantVariables.size()  
              << " relevant variables" << std::endl;  
      
    return result;  
}

bool ProgramSlicer::matchesCriterion(const std::string& varName,  
                                     const AssignmentInfo& assignment,  
                                     const SlicingCriterion& criterion) {  
    if (criterion.fileName.empty() && criterion.lineNumber < 0) {  
        return true;  
    }  
      
    if (!criterion.fileName.empty() && assignment.file != criterion.fileName) {  
        return false;  
    }  
      
    if (criterion.lineNumber >= 0 && assignment.line != criterion.lineNumber) {  
        return false;  
    }  
      
    return true;  
}  
  
void ProgramSlicer::exportSliceToJson(const SliceResult& result, const std::string& outputPath) {  
    json j;  
      
    j["relevantVariables"] = result.relevantVariables;  
    j["controlVariables"] = result.controlVariables;  
      
    json assignmentsJson = json::object();  
    for (const auto& [varName, assignments] : result.relevantAssignments) {  
        json varAssignments = json::array();  
        for (const auto& assignment : assignments) {  
            json assignJson;  
            assignJson["file"] = assignment.file;  
            assignJson["line"] = assignment.line;  
            assignJson["type"] = assignment.type;  
            assignJson["logicType"] = assignment.logicType;  
            assignJson["drivingSignals"] = assignment.drivingSignals;  
            assignJson["conditionDepth"] = assignment.conditionDepth;  
              
            json pathJson = json::array();  
            for (const auto& clause : assignment.path) {  
                json clauseJson;  
                clauseJson["expression"] = clause.expr.expression;  
                clauseJson["involvedSignals"] = clause.expr.involvedSignals;  
                clauseJson["polarity"] = clause.polarity;  
                pathJson.push_back(clauseJson);  
            }  
            assignJson["conditionPath"] = pathJson;  
              
            varAssignments.push_back(assignJson);  
        }  
        assignmentsJson[varName] = varAssignments;  
    }  
    j["relevantAssignments"] = assignmentsJson;  
      
    std::ofstream outFile(outputPath);  
    if (outFile.is_open()) {  
        outFile << j.dump(4);  
        outFile.close();  
        std::cout << "[SUCCESS] Slice result written to: " << outputPath << std::endl;  
    } else {  
        std::cerr << "[ERROR] Could not open output file: " << outputPath << std::endl;  
    }  
}  
  
void ProgramSlicer::exportSliceWithSourceCode(const SliceResult& result,  
                                              const slang::SourceManager& sourceManager,  
                                              const std::string& outputPath,  
                                              const SliceConfig& config) {  
    json j;  
      
    j["relevantVariables"] = result.relevantVariables;  
    j["controlVariables"] = result.controlVariables;  
      
    // 提取完整的代码块  
    auto completeBlocks = extractCompleteBlocks(result, sourceManager);  
      
    json blocksJson = json::array();  
    for (const auto& block : completeBlocks) {  
        json blockJson;  
        blockJson["blockType"] = block.blockType;  
        blockJson["file"] = block.file;  
        blockJson["affectedVariables"] = block.affectedVariables;  
        blockJson["sourceCode"] = block.sourceCode;  
        blocksJson.push_back(blockJson);  
    }  
      
    j["completeCodeBlocks"] = blocksJson;  
      
    std::ofstream outFile(outputPath);  
    if (outFile.is_open()) {  
        outFile << j.dump(4);  
        outFile.close();  
    }  
}
    
std::vector<CompleteCodeBlock> ProgramSlicer::extractCompleteBlocks(    
    const SliceResult& result,    
    const slang::SourceManager& sourceManager) {    
        
    std::map<std::string, CompleteCodeBlock> uniqueBlocks;    
    std::vector<CompleteCodeBlock> blocks;    
        
    for (const auto& [varName, assignments] : result.relevantAssignments) {    
        for (const auto& assignment : assignments) {    
            slang::SourceRange rangeToExtract;    
            std::string blockType;    
                
            // 根据赋值类型决定提取范围    
            if (assignment.type == "port_connection") {    
                // 模块实例化:需要特殊处理以包含模块类型名称  
                blockType = "module_instance";  
                  
                // 使用 extractModuleInstance 方法来获取完整的实例化语句  
                CompleteCodeBlock block;  
                block.file = assignment.file;  
                block.blockType = blockType;  
                block.sourceCode = extractModuleInstance(assignment.file, assignment.line);  
                block.startLine = assignment.line;  
                block.endLine = assignment.line;  
                  
                // 使用文件名+行号作为唯一键  
                std::string blockKey = assignment.file + ":" + std::to_string(assignment.line);  
                  
                if (uniqueBlocks.find(blockKey) == uniqueBlocks.end()) {  
                    uniqueBlocks[blockKey] = block;  
                }  
                uniqueBlocks[blockKey].affectedVariables.insert(varName);  
                continue;  // 跳过后续的通用处理  
            }  
            else if (assignment.logicType == "combinational" &&     
                !assignment.proceduralBlockRange.start()) {    
                // 连续赋值(assign语句):只提取赋值表达式    
                rangeToExtract = assignment.sourceRange;    
                blockType = "assign";    
            }    
            else if (assignment.proceduralBlockRange.start()) {    
                // 过程块赋值:提取整个过程块    
                rangeToExtract = assignment.proceduralBlockRange;    
                blockType = assignment.logicType == "sequential" ? "always_ff" : "always_comb";    
            }    
            else {    
                // 其他情况:提取赋值表达式    
                rangeToExtract = assignment.sourceRange;    
                blockType = assignment.type;    
            }    
                
            std::string blockKey = assignment.file + ":" +     
                                  std::to_string(rangeToExtract.start().offset());    
                
            if (uniqueBlocks.find(blockKey) == uniqueBlocks.end()) {    
                CompleteCodeBlock block;    
                block.file = assignment.file;    
                block.blockType = blockType;    
                block.sourceCode = extractCodeFromSourceRange(rangeToExtract, sourceManager);    
                block.startLine = sourceManager.getLineNumber(rangeToExtract.start());    
                block.endLine = sourceManager.getLineNumber(rangeToExtract.end());    
                uniqueBlocks[blockKey] = block;    
            }    
                
            uniqueBlocks[blockKey].affectedVariables.insert(varName);    
        }    
    }    
        
    for (const auto& [key, block] : uniqueBlocks) {    
        blocks.push_back(block);    
    }    
        
    return blocks;    
}

std::string ProgramSlicer::extractModuleInstance(const std::string& fileName, int targetLine) {    
    std::ifstream file(fileName);    
    if (!file.is_open()) {    
        return "// Error: Could not open file";    
    }    
        
    std::vector<std::string> lines;    
    std::string line;    
    while (std::getline(file, line)) {    
        lines.push_back(line);    
    }    
    file.close();    
        
    if (targetLine < 1 || targetLine > static_cast<int>(lines.size())) {    
        return "// Error: Invalid line number";    
    }    
        
    int startLine = targetLine - 1;    
    int endLine = targetLine - 1;    
        
    // 向上查找模块实例化的开始(包含模块类型名称)  
    // 模块实例化格式: module_type_name instance_name (  
    for (int i = targetLine - 1; i >= 0; i--) {    
        std::string trimmed = lines[i];    
        // 移除前导空白    
        size_t firstNonSpace = trimmed.find_first_not_of(" \t");    
        if (firstNonSpace != std::string::npos) {    
            trimmed = trimmed.substr(firstNonSpace);    
        }    
            
        // 检查是否包含实例化的开始标记  
        // 寻找包含标识符和左括号的行,但排除关键字  
        if (trimmed.find('(') != std::string::npos) {  
            // 确保不是模块定义或其他关键字  
            if (trimmed.find("module ") == std::string::npos &&    
                trimmed.find("endmodule") == std::string::npos &&  
                trimmed.find("function") == std::string::npos &&  
                trimmed.find("task") == std::string::npos &&  
                trimmed.find("always") == std::string::npos) {  
                startLine = i;  
                break;  
            }  
        }  
            
        // 如果遇到分号,说明已经超出了当前实例化语句的范围  
        if (trimmed.find(';') != std::string::npos && i < targetLine - 1) {    
            break;    
        }    
    }    
        
    // 向下查找模块实例化的结束(分号)    
    for (int i = targetLine - 1; i < static_cast<int>(lines.size()); i++) {    
        if (lines[i].find(");") != std::string::npos) {    
            endLine = i;    
            break;    
        }    
    }    
        
    // 提取完整的模块实例化语句    
    std::stringstream result;    
    for (int i = startLine; i <= endLine; i++) {    
        result << lines[i];    
        if (i < endLine) {    
            result << "\n";    
        }    
    }    
        
    return result.str();    
}


std::string ProgramSlicer::generateMergedCodeForVariable(    
    const SliceResult& result,    
    const std::string& targetVariable,    
    const slang::SourceManager& sourceManager) {    
        
    std::stringstream mergedCode;    
        
    // 1. 添加注释说明  
    mergedCode << "// ========================================\n";    
    mergedCode << "// Program Slice for: " << targetVariable << "\n";    
    mergedCode << "// ========================================\n\n";    
        
    // 2. 提取完整代码块  
    auto completeBlocks = extractCompleteBlocks(result, sourceManager);  
      
    // 3. 按类型分组输出  
    // 先输出时序逻辑块  
    for (const auto& block : completeBlocks) {  
        if (block.blockType == "always_ff") {  
            mergedCode << "// Sequential logic\n";  
            mergedCode << block.sourceCode << "\n\n";  
        }  
    }  
      
    // 再输出组合逻辑块  
    for (const auto& block : completeBlocks) {  
        if (block.blockType == "always_comb" || block.blockType == "always") {  
            mergedCode << "// Combinational logic\n";  
            mergedCode << block.sourceCode << "\n\n";  
        }  
    }  
      
    // 最后输出assign语句  
    for (const auto& block : completeBlocks) {  
        if (block.blockType == "assign") {  
            mergedCode << "// Continuous assignment\n";  
            mergedCode << block.sourceCode << "\n\n";  
        }  
    }  
      
    // 输出模块实例化(如果有)  
    for (const auto& block : completeBlocks) {  
        if (block.blockType == "module_instance") {  
            mergedCode << "// Module instantiation\n";  
            mergedCode << block.sourceCode << "\n\n";  
        }  
    }  
        
    return mergedCode.str();    
}
  
  
// 新增辅助方法:从源文件提取信号声明  
std::string ProgramSlicer::extractSignalDeclarationsFromSource(  
    const std::string& fileName,  
    const std::string& moduleName,  
    const std::set<std::string>& relevantVariables) {  
      
    std::ifstream file(fileName);  
    if (!file.is_open()) {  
        return "// Error: Could not open file";  
    }  
      
    std::string line;  
    std::stringstream declarations;  
    bool inModule = false;  
    bool inDeclarationSection = true;  
      
    while (std::getline(file, line)) {  
        // 检测模块开始  
        if (line.find("module " + moduleName) != std::string::npos) {  
            inModule = true;  
            continue;  
        }  
          
        if (!inModule) continue;  
          
        // 检测声明区域结束(遇到always/assign等)  
        if (line.find("always") != std::string::npos ||   
            line.find("assign") != std::string::npos ||  
            line.find("initial") != std::string::npos) {  
            inDeclarationSection = false;  
            break;  
        }  
          
        // 提取相关的信号声明  
        if (inDeclarationSection) {  
            // 检查这一行是否声明了相关变量  
            for (const auto& varName : relevantVariables) {  
                std::string shortName = varName.substr(varName.find_last_of('.') + 1);  
                if (line.find(shortName) != std::string::npos &&  
                    (line.find("logic") != std::string::npos ||  
                     line.find("reg") != std::string::npos ||  
                     line.find("wire") != std::string::npos)) {  
                    declarations << "    " << line << "\n";  
                    break;  
                }  
            }  
        }  
    }  
      
    return declarations.str();  
}  
  
std::map<std::string, std::string> ProgramSlicer::generateAllMergedCode(  
    const std::map<std::string, SliceResult>& allSlices,  
    const slang::SourceManager& sourceManager) {  
      
    std::map<std::string, std::string> mergedCodeMap;  
      
    for (const auto& [varName, sliceResult] : allSlices) {  
        std::string mergedCode = generateMergedCodeForVariable(  
            sliceResult, varName, sourceManager);  
        mergedCodeMap[varName] = mergedCode;  
    }  
      
    return mergedCodeMap;  
}

std::string ProgramSlicer::extractCodeFromSourceRange(  
    const slang::SourceRange& range,  
    const slang::SourceManager& sourceManager) {  
      
    if (!range.start() || !range.end()) {  
        return "// Error: Invalid source range";  
    }  
      
    // 直接从SourceLocation获取buffer和offset  
    auto bufferID = range.start().buffer();  
    std::string_view sourceText = sourceManager.getSourceText(bufferID);  
      
    // SourceLocation已经包含offset信息  
    size_t startOffset = range.start().offset();  
    size_t endOffset = range.end().offset();  
      
    if (startOffset >= sourceText.length() || endOffset > sourceText.length()) {  
        return "// Error: Offset out of range";  
    }  
      
    return std::string(sourceText.substr(startOffset, endOffset - startOffset));  
}

std::string ProgramSlicer::generateDependencyReport(const std::string& targetVariable, 
                                                     const SliceResult& result, 
                                                     bool isBackward) const {
    // ... (generateDependencyReport 的实现保持不变，如上一个回答中的 Step 3 所述)
    // ...
    std::stringstream report;
    report << "----------------------------------------\n";
    report << "Dependency Report for: " << targetVariable << "\n";
    report << "----------------------------------------\n";

    auto it = result.dependencyMap.find(targetVariable);
    if (it == result.dependencyMap.end()) {
        report << "No structured dependency data found.\n";
        return report.str();
    }

    const DependencyRecord& record = it->second;

    if (isBackward) {
        report << "Direction: BACKWARD SLICE (Looking for inputs)\n";
        report << "----------------------------------------\n";
        
        report << "DATA DEPENDENCIES (Driven By):\n";
        if (record.dataDependencies.empty()) {
            report << "  - None\n";
        } else {
            for (const auto& dep : record.dataDependencies) {
                report << "  - Data from: " << dep << "\n";
            }
        }

        report << "\nCONTROL DEPENDENCIES (Controlled By):\n";
        if (record.controlDependencies.empty()) {
            report << "  - None\n";
        } else {
            for (const auto& dep : record.controlDependencies) {
                report << "  - Condition on: " << dep << "\n";
            }
        }
    } else { // Forward Slice
        report << "Direction: FORWARD SLICE (Looking for outputs)\n";
        report << "----------------------------------------\n";
        
        report << "DATA FAN-OUT (Directly Affects Variable Assignments):\n";
        if (record.fanOutVariables.empty()) {
            report << "  - None\n";
        } else {
            for (const auto& dep : record.fanOutVariables) {
                report << "  - Affects variable: " << dep << "\n";
            }
        }

        report << "\nCONTROL FAN-OUT (Controls Assignments in Variables):\n";
        if (record.fanOutConditions.empty()) {
            report << "  - None\n";
        } else {
            for (const auto& dep : record.fanOutConditions) {
                report << "  - Controls assignment to: " << dep << "\n";
            }
        }
    }
    
    report << "\nASSIGNMENTS IN SLICE (Sources/Uses in Current File):\n";
    if (record.fanInAssignments.empty()) {
        report << "  - None\n";
    } else {
        for (const auto& assign : record.fanInAssignments) {
            report << "  - Assignment at: " << assign << "\n";
        }
    }

    report << "----------------------------------------\n";
    return report.str();
}


// [新的公共函数] - 导出所有变量的依赖关系图
void ProgramSlicer::exportAllDependenciesToTxt(
    const std::map<std::string, SliceResult>& allBackwardSlices,
    const std::map<std::string, SliceResult>& allForwardSlices,
    const std::string& outputPath) const 
{
    std::ofstream txtFile(outputPath);
    if (!txtFile.is_open()) {
        std::cerr << "[ERROR] Could not open dependency output file for writing: " << outputPath << std::endl;
        return;
    }

    txtFile << "================================================\n";
    txtFile << "Unified Variable Dependency Report\n";
    txtFile << "================================================\n\n";

    // 遍历所有变量（使用 Backward Slices 的键作为主列表）
    for (const auto& [varName, backwardResult] : allBackwardSlices) {
        txtFile << "################################################\n";
        txtFile << "## VARIABLE: " << varName << "\n";
        txtFile << "################################################\n\n";
        
        // 1. 后向依赖（Fan-In）
        // 我们可以确定 backwardResult 的 targetVariable 是 varName
        txtFile << generateDependencyReport(varName, backwardResult, true) << "\n";

        // 2. 前向依赖（Fan-Out）
        auto forwardIt = allForwardSlices.find(varName);
        if (forwardIt != allForwardSlices.end()) {
            txtFile << generateDependencyReport(varName, forwardIt->second, false) << "\n";
        } else {
            txtFile << "!!! WARNING: Forward slice data missing for " << varName << " !!!\n\n";
        }

        txtFile << "\n\n";
    }

    std::cout << "[SUCCESS] Dependency report written to: " << outputPath << std::endl;
}