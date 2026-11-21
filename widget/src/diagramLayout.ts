import {
  JSONDataInstance, Layout, LayoutInstance, parseLayoutSpec, SGraphQueryEvaluator,
  type SystemError, type Translators,
} from 'spytial-core';
import { inspectionDisplayData, withLeanScalarTypes, type InspectionPoint } from './inspection.js';
import { renderedFactHighlights } from './factHighlights.js';

function layoutDiagnostic({ error, selectorErrors }: ReturnType<LayoutInstance['generateLayout']>):
    SystemError | undefined {
  if (!error) return selectorErrors.length ? { type: 'selector-error', errors: selectorErrors } : undefined;
  if (Layout.isHiddenNodeConflictError(error))
    return { type: 'hidden-node-conflict', messages: error.errorMessages };
  if (Layout.isPositionalConstraintError(error) && error.errorMessages)
    return { type: 'positional-error', messages: error.errorMessages };
  if (Layout.isGroupOverlapError(error))
    return { type: 'group-overlap-error', message: error.message };
  return { type: 'general-error', message: error.message || 'Layout error' };
}

/** Evaluate selectors on Lean's original labels. Inspection numbers are presentation only. */
export function prepareDiagram(point: InspectionPoint, pointNumber?: number) {
  const data = point.dataInstance;
  const instance = new JSONDataInstance(withLeanScalarTypes(data));
  const evaluator = new SGraphQueryEvaluator();
  evaluator.initialize({ sourceData: instance });
  const engine = new LayoutInstance(parseLayoutSpec(point.cndSpec ?? ''), evaluator, 0, true);
  const display = inspectionDisplayData(data, point.inspection, pointNumber);
  const displayInstance = display === data ? instance : new JSONDataInstance(withLeanScalarTypes(display));
  const result = engine.generateLayout(displayInstance);
  return {
    layout: result.layout,
    hasConflict: !!result.error,
    diagnostic: layoutDiagnostic(result),
    factHighlights(graph: Translators.WebColaCnDGraph) {
      const targets = point.inspection?.factTargets;
      if (targets?.length) return renderedFactHighlights(graph, display, targets,
        displayInstance.generateGraph(false, false), engine);
    },
  };
}
