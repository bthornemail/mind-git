/**
 * Transform Controls Component
 * Provides transform controls (translate, rotate, scale) for selected 3D objects
 */
import React, { useRef, useEffect } from 'react';
import { useThree, useFrame } from '@react-three/fiber';
import { TransformControls as ThreeTransformControls } from 'three/examples/jsm/controls/TransformControls.js';
import * as THREE from 'three';

interface TransformControlsProps {
  object?: THREE.Object3D;
  mode?: 'translate' | 'rotate' | 'scale';
  enabled?: boolean;
  onTransformChange?: (object: THREE.Object3D) => void;
  onObjectChange?: (object: THREE.Object3D) => void;
}

export const TransformControls: React.FC<TransformControlsProps> = ({
  object,
  mode = 'translate',
  enabled = true,
  onTransformChange,
  onObjectChange
}) => {
  const { camera, gl, scene } = useThree();
  const controlsRef = useRef<ThreeTransformControls>();
  const groupRef = useRef<THREE.Group>();

  useEffect(() => {
    if (!camera || !gl || !scene) return;

    const controls = new ThreeTransformControls(camera, gl.domElement);
    controlsRef.current = controls;
    scene.add(controls);

    // Set up event handlers
    const handleTransformChange = () => {
      if (onTransformChange && controls.object) {
        onTransformChange(controls.object);
      }
    };

    const handleObjectChange = () => {
      if (onObjectChange && controls.object) {
        onObjectChange(controls.object);
      }
    };

    controls.addEventListener('change', handleTransformChange);
    controls.addEventListener('objectChange', handleObjectChange);

    // Disable orbit controls when transforming
    const handleDraggingChanged = (event: any) => {
      const orbitControls = (window as any).__orbitControls;
      if (orbitControls) {
        orbitControls.enabled = !event.value;
      }
    };

    controls.addEventListener('dragging-changed', handleDraggingChanged);

    return () => {
      controls.removeEventListener('change', handleTransformChange);
      controls.removeEventListener('objectChange', handleObjectChange);
      controls.removeEventListener('dragging-changed', handleDraggingChanged);
      scene.remove(controls);
      controls.dispose();
    };
  }, [camera, gl, scene, onTransformChange, onObjectChange]);

  useEffect(() => {
    if (controlsRef.current) {
      controlsRef.current.setMode(mode);
    }
  }, [mode]);

  useEffect(() => {
    if (controlsRef.current) {
      controlsRef.current.enabled = enabled;
    }
  }, [enabled]);

  useEffect(() => {
    if (controlsRef.current && object) {
      controlsRef.current.attach(object);
    } else if (controlsRef.current) {
      controlsRef.current.detach();
    }
  }, [object]);

  // Update controls in animation loop
  useFrame(() => {
    if (controlsRef.current) {
      controlsRef.current.updateMatrixWorld();
    }
  });

  return <group ref={groupRef} />;
};