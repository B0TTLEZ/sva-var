#pragma once  
#include "DataModel.h"  
#include "DependencyVisitor.h"  
#include <queue>  
#include <set>  
#include <string>  
#include "json.hpp"  
// 切片粒度级别  
enum class SliceGranularity {  
    Statement,      // 仅赋值语句  
    ControlBlock,   // 包含直接控制结构(if/case)  
    ProceduralBlock,// 完整的always/assign块  
    Module          // 完整模块定义  
};  
  
// 过滤选项  
enum class SliceFilterOptions {  
    None = 0,  
    RemoveUnrelatedAssignments = 1 << 0,  
    RemoveConstantAssignments = 1 << 1,  
    RemoveResetLogic = 1 << 2,  
    KeepControlStructure = 1 << 3,  
    IncludeComments = 1 << 4,  
    IncludeContext = 1 << 5  
};  
  
// 位运算符重载  
inline SliceFilterOptions operator|(SliceFilterOptions a, SliceFilterOptions b) {  
    return static_cast<SliceFilterOptions>(static_cast<int>(a) | static_cast<int>(b));  
}  
  
inline SliceFilterOptions& operator|=(SliceFilterOptions& a, SliceFilterOptions b) {  
    a = a | b;  
    return a;  
}  
  
inline SliceFilterOptions operator&(SliceFilterOptions a, SliceFilterOptions b) {  
    return static_cast<SliceFilterOptions>(static_cast<int>(a) & static_cast<int>(b));  
}  
  
// 辅助函数:检查位标志  
inline bool hasFlag(SliceFilterOptions flags, SliceFilterOptions flag) {  
    return (static_cast<int>(flags) & static_cast<int>(flag)) != 0;  
}  
  
// 切片配置  
struct SliceConfig {  
    SliceGranularity granularity = SliceGranularity::ControlBlock;  
    SliceFilterOptions filterOptions = SliceFilterOptions::RemoveUnrelatedAssignments;  
    int contextLines = 2;  
    bool includeSourceInfo = true;  
    bool includeConditionPaths = true;  
};  
  
// 切片准则  
struct SlicingCriterion {  
    std::string variableName;  
    std::string fileName;  
    int lineNumber = -1;  
};  
  
// 切片结果  
struct SliceResult {  
    std::set<std::string> relevantVariables;  
    std::map<std::string, std::set<AssignmentInfo>> relevantAssignments;  
    std::set<std::string> controlVariables;  
};  

struct CompleteCodeBlock {  
    std::string blockType;  // "always_ff", "always_comb", "assign"  
    std::string sourceCode;  
    std::set<std::string> affectedVariables;  
    std::string file;  
    int startLine;  
    int endLine;  
}; 

class   ProgramSlicer {  
public:  
    explicit ProgramSlicer(const AnalysisResultMap& analysisResults);  
      
    // 后向切片  
    SliceResult backwardSlice(const SlicingCriterion& criterion,  
                             const SliceConfig& config = SliceConfig());  
      
    // 前向切片  
    SliceResult forwardSlice(const SlicingCriterion& criterion,  
                            const SliceConfig& config = SliceConfig());  
    std::vector<CompleteCodeBlock> extractCompleteBlocks(  
                                                        const SliceResult& result,  
                                                        const slang::SourceManager& sourceManager);  
    // 导出为JSON  
    void exportSliceToJson(const SliceResult& result, const std::string& outputPath);  
      
    // 导出包含源代码  
    void exportSliceWithSourceCode(const SliceResult& result,  
                                   const slang::SourceManager& sourceManager,  
                                   const std::string& outputPath,  
                                   const SliceConfig& config = SliceConfig());  
    std::string extractCodeFromSourceRange(  
        const slang::SourceRange& range,  
        const slang::SourceManager& sourceManager); 
    // 新增:为单个变量生成合并的代码片段  
    std::string generateMergedCodeForVariable(  
        const SliceResult& result,  
        const std::string& targetVariable,  
        const slang::SourceManager& sourceManager);  
      
    // 新增:为所有变量生成合并的代码片段  
    std::map<std::string, std::string> generateAllMergedCode(  
        const std::map<std::string, SliceResult>& allSlices,  
        const slang::SourceManager& sourceManager);  
  
private:  
    const AnalysisResultMap& results;  
      
    // 辅助方法  
    bool matchesCriterion(const std::string& varName,  
                         const AssignmentInfo& assignment,  
                         const SlicingCriterion& criterion);  
      
    std::string extractCodeWithConfig(const AssignmentInfo& assignment,  
                                     const SliceConfig& config,  
                                     const std::set<std::string>& relevantVars);  
      
    std::string extractSourceLine(const std::string& fileName, int lineNumber);  
    std::string extractControlBlock(const std::string& fileName, int lineNumber);  
    std::string extractProceduralBlock(const std::string& fileName, int lineNumber);  
    std::string extractModuleDefinition(const std::string& fileName);  
    std::string extractSourceLines(const std::string& fileName, int startLine, int endLine);  
    std::string filterUnrelatedAssignments(const std::string& code,  
                                          const std::set<std::string>& relevantVars);
    int findProceduralBlockStart(const std::string& fileName, int targetLine); 
    std::string extractModuleInstance(const std::string& fileName, int lineNumber);   
    // 新增:从源文件提取模块头部  
    std::string extractModuleHeaderFromSource(  
        const std::string& fileName,  
        const std::string& moduleName);  
      
    // 新增:从源文件提取信号声明  
    std::string extractSignalDeclarationsFromSource(  
        const std::string& fileName,  
        const std::string& moduleName,  
        const std::set<std::string>& relevantVariables);  
};
inline void to_json(nlohmann::json& j, const CompleteCodeBlock& block) {  
    j = nlohmann::json{  
        {"blockType", block.blockType},  
        {"file", block.file},  
        {"sourceCode", block.sourceCode},  
        {"affectedVariables", block.affectedVariables}  
    };  
}